// Port of src/Compile/Optimize.hs -- the per-module core optimization
// pipeline (runs after Compile/TypeCheck, before code generation).
// Pretty.Env parameters are tracing-only in this port and dropped.
//
// The pipeline runs unconditionally. The KOKA_NO_GEN_INLINE
// / KOKA_NO_CTAIL / KOKA_NO_PRIM_INLINE env gates that used to bracket the
// inline, ctail and primitive-inline passes were A/B bisection aids; they are
// retired (see the comments at each pass) because an env var that silently
// changes generated code has no place in a drop-in upstream replacement.
module compiler/compile/optimize
import std/os/env
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/error
import compiler/common/unique
import compiler/platform/config
import compiler/kind/newtypes
import compiler/type/type
import compiler/type/assumption
import compiler/core/core
import compiler/core/corevar
import compiler/core/simplify
import compiler/core/fun-lift
import compiler/core/monadic
import compiler/core/monadic-lift
import compiler/core/open-resolve
import compiler/core/uniquefy
import compiler/core/inlines
import compiler/core/inline
import compiler/core/unroll
import compiler/core/ctail
import compiler/core/specialize
import compiler/core/check
import compiler/compile/options
import std/data/rb-map
import compiler/common/name-collections

pub fun core-optimize(fl: flags, nt: newtypes, gamma0: gamma, inls: inlines, coreProgram: core): _ (core, list<inline-def>)
  with common/unique/run-unique(10000)
  // DIAGNOSTIC (KOKA_UNIQ_TRACE=1): this pass has its OWN counter starting at
  // 10000, so the entry module's outer counter cannot show what happens here.
  // DIAGNOSTIC (KOKA_UNIQ_TRACE=1): fingerprint the CURRENT def-groups by
  // top-level name, in order. The nondeterminism shows up as one generated
  // name's id off by one with identical unique totals, so names are exactly the
  // right thing to hash -- and hashing names is cheap enough to do per pass,
  // where rendering whole cores would not be.
  fun opt-fp(label: string): _ ()
    if get-env-value("KOKA_UNIQ_TRACE").is-just then
      val names = get-core-defs().flatmap fn(g)
        match g
          DefRec(ds)   -> ds.map(fn(d) d.def-name.show-plain)
          DefNonRec(d) -> [d.def-name.show-plain]
      val h = names.join("|").list.foldl(7) fn(a, c) (a * 31 + c.int) % 1000000007
      println("OPT-FP " ++ label.pad-right(22) ++ " " ++ coreProgram.coreName.show-plain
              ++ " n=" ++ names.length.show ++ " fp=" ++ h.show)
  fun opt-uniq(label: string): _ ()
    if get-env-value("KOKA_UNIQ_TRACE").is-just then
      println("UNIQ-OPT " ++ label ++ " " ++ coreProgram.coreName.show-plain ++ " = " ++ get-unique().show)
  var dgs := coreProgram.defs
  with handler
    fun get-core-defs() dgs
    fun set-core-defs(d) dgs := d
    fun phaseError(s) throw("core optimize: " ++ s)
  with handler
    fun get-gamma() gamma0
  val progName = coreProgram.coreName
  val primitiveModule = progName.is-primitive-module
  val ndebug = fl.optimize > 0
  fun simplifyX(dupMax: int)
    simplify-defs(False, ndebug, fl.simplify, dupMax)
  fun simplifyDupN()
    if fl.simplify >= 0 then simplifyX(fl.simplifyMaxDup)
  fun simplifyNoDup()
    simplifyX(0)
  // (the title is upstream's own unused parameter, kept for the call sites)
  fun checkCoreDefs(_title: string)
    if fl.coreCheck then check-core(False, False, gamma0)

  // unroll recursive definitions (before inline so generated wrappers can be inlined)
  opt-uniq("start")
  opt-fp("00-start")
  if fl.optUnroll > 0 then
    unroll(fl.optUnroll)
  opt-uniq("after-unroll")
  opt-fp("01-unroll")

  // inline: inline local definitions more aggressively (2x)
  // (A/B bisection aid retired: was `&& get-env-value("KOKA_NO_GEN_INLINE").is-nothing`)
  if fl.optInlineMax > 0 then
    val inlinesX = if primitiveModule then inls
                   else inls.inlines-filter(fn(nm) nameCoreHnd.qualifier != nm.qualifier)
    inline-defs(2 * fl.optInlineMax, inlinesX)
  opt-fp("02-inline")

  simplifyDupN()
  opt-fp("03-simplify")

  // specialize
  val specializeDefs =
    if primitiveModule then [] else extract-specialize-defs(inls, dgs)
  if fl.use-specialize && !primitiveModule then
    specialize(inls.extends(specializeDefs), fl.coreProvenance)
    simplifyDupN()
    // lift remaining recursive functions to top level (must be after
    // specialize as that can generate local recursive definitions)
    lift-functions()
  opt-fp("04-specialize-lift")

  // simplify once more
  simplifyDupN()
  opt-uniq("after-specialize")
  val coreDefsInlined = dgs

  //------------------------------
  // backend optimizations

  // tail-call-modulo-cons optimization (context paths are C-only upstream)
  // (A/B bisection aid retired: was `&& get-env-value("KOKA_NO_CTAIL").is-nothing`)
  if fl.optctail then
    val isC = match fl.target
      C -> True
      _ -> False
    ctail-optimize(fl.tpl, nt, fl.optctailCtxPath && isC)
  opt-fp("05-ctail")

  // transform effects to explicit monadic binding (and resolve .open calls)
  if fl.enableMon && !primitiveModule then
    mon-transform()
    open-resolve() // must be after monTransform
  opt-fp("06-mon-transform")
  checkCoreDefs("monadic transform")

  // simplify open applications (needed before inlining open defs)
  simplifyNoDup()

  // monadic lifting to create fast inlined paths
  monadic-lift()
  opt-uniq("after-monadic-lift")
  opt-fp("07-monadic-lift")
  checkCoreDefs("monadic lifting")

  // now inline primitive definitions (like yield-bind). Runs unconditionally
  // upstream. Was opt-in here pending investigation of a historical
  // "regresses handler-heavy tests" report; re-tested after the uniquefy
  // add-vs-set fix (the actual root cause of that regression class) and the
  // C backend needs it inlined to produce the `if (kk_yielding())` dual-path
  // branch std/core/hnd's `yield-bind` is written to expand into -- calling
  // it as an opaque external instead leaves the C codegen with no way to
  // give the wrapper a concrete (non-`kk_function_t`) return type.
  // (A/B bisection aid retired: was gated on `get-env-value("KOKA_NO_PRIM_INLINE").is-nothing`)
  inline-defs(2 * fl.optInlineMax, inls.inlines-filter(is-primitive-name))
  opt-fp("08-prim-inline")

  // remove remaining open calls; this may change effect types
  simplify-defs(True, ndebug, fl.simplify, 0) // unsafe

  // final simplification
  simplifyDupN()
  checkCoreDefs("final")

  opt-fp("09-final")
  // assemble core program and return
  val coreDefsFinal = dgs
  val localInlineDefs = coreDefsInlined.extract-inlines(fl.optInlineMax)
  // give priority to specializeDefs, since inlining can prevent specialize opportunities
  val allInlineDefs = specializeDefs ++ localInlineDefs

  // add extra required imports for inlined definitions
  val inlineDeps = extract-deps-from-inline-defs(allInlineDefs)
  val regularDeps = extract-deps-from-defs(coreDefsFinal)
  val allDeps = (inlineDeps ++ regularDeps).names-nub
  val currentImports = coreProgram.imports.map(importName)
  val inlineImports = allDeps.filter(fn(nm) !currentImports.any(fn(i) i == nm) && nm != progName)
                            .map(fn(nm) Kimport(nm, "", Private, "", provenance = ImportCompiler))
  val coreFinal = coreProgram(defs = coreDefsFinal,
                              imports = coreProgram.imports ++ inlineImports).core/uniquefy
  (coreFinal, allInlineDefs)
