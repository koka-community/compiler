// Ported as of 2026-01-18; approx upstream baseline commit d3b244c of Backend/C/FromCore.hs (backfilled 2026-07-23)
module compiler/backend/c/from-core

import compiler/core/core
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/nice
import compiler/common/unique
import compiler/core/corevar
import compiler/core/borrowed
import compiler/type/type
import compiler/type/pretty
import compiler/kind/kind
import compiler/kind/newtypes
import compiler/kind/repr
import compiler/lib/pprint
import compiler/platform/config
import compiler/common/file
import std/pretty/printer
import compiler/backend/c/helpers
import compiler/backend/c/dup-drops
import compiler/backend/c/constructors
import compiler/backend/c/expr
import compiler/backend/c/box
import compiler/backend/c/parc
import compiler/backend/c/parc-reuse
import compiler/backend/c/parc-reuse-spec
import std/os/path
import std/os/env
import std/core/debug
import std/data/rb-set

fun externalNames(): _ list<(tName, doc)>
  [(exprTrue.con-name, "true".text), (exprFalse.con-name, "false".text)]

// Generate C code from System-F core language
pub fun cFromCore(cTarget: cTarget, b: buildType, sourceDir: path,
              platform: platform, nt: newtypes, borrowed: borrowed, enableReuse: bool,
              enableSpecialize: bool, enableReuseSpecialize: bool, enableBorrowInference: bool,
              eagerPatBind: bool, stackSize: int, mbMain: maybe<(name, bool)>,
              core: core): _ (doc, doc, core)
  with handler
    val cdefToHeader = False
    val substEnv = externalNames()
    val cdef-name = core.coreName
  var rhdoc := []
  var rcdoc := []
  var ridoc := [] // initialization expressions
  var rtdoc := [] // toplevel (goes to either H or C)
  var rddoc := [] // done expressions
  var canonicalLamTypes := []
  with handler
    fun emit-to-h(d: doc) rhdoc := Cons(d, rhdoc)
    fun emit-to-c(d: doc) rcdoc := Cons(d, rcdoc)
    fun emitToInit(d: doc) ridoc := Cons(d, ridoc)
    fun emitToTop(d: doc) rtdoc := Cons(d, rtdoc)
    fun emitToDone(d: doc) rddoc := Cons(d, rddoc)
    fun getInit() ridoc.reverse.vcat
    fun getDone() rddoc.vcat
    fun getTop() 
      val res = rtdoc.reverse.vcat
      rtdoc := []
      res
    fun addCanonical(c: canonicalLambda) 
      if canonicalLamTypes.any(fn(x) x == c) then False
      else
        canonicalLamTypes := Cons(c, canonicalLamTypes)
        True
    val modName = core.coreName
    val prettyModName = core.coreName.pp-mod-name
    val targetPlatform = platform
    val eagerPatBind = eagerPatBind
    val enableReuse = enableReuse
    val enableSpecialize = enableSpecialize
    val enableReuseSpecialize = enableReuseSpecialize
    val enableBorrowInference = enableBorrowInference
    val cTarget = cTarget
    val borrowed = borrowed
    val stackSize = stackSize
    val sourceDir = sourceDir
    val buildType = b
    val debug = False
  // run genModule first (it emits into rcdoc/rhdoc via the handlers above);
  // the emit handlers prepend (Cons), so reverse before concatenating
  val core1 = genModule(core, mbMain, nt)
  (rcdoc.reverse.vcat, rhdoc.reverse.vcat, core1)

// Thread-safe module-init guard. Upstream (`src/Backend/C/FromCore.hs:107-109`) emits
// a plain `static bool _kk_initialized` double-checked-init with no synchronization --
// safe for upstream's own single-threaded compiler, but this port's RPC orchestrator
// runs codegen for multiple modules concurrently on real OS threads (spawn-thread),
// and any module can be first-touched by two worker threads at once. Both threads then
// pass the unguarded `if (_kk_initialized) return;` check before either publishes
// `true`, and both proceed to (re)build this module's toplevel constants -- e.g. two
// threads racing to build+overwrite the same `kk_std_core_types__list` global, one
// freeing cons cells the other is still reading. Confirmed via lldb: `EXC_BAD_ACCESS` in
// memcmp comparing a corrupted string pointer, both crashing threads inside this same
// class of module-init path (`compiler/backend/c/helpers.kk`'s `reserved` list, built and
// published via `kk_box_mark_static` -- but that mark_static only protects READS of the
// already-published value, not this construction race itself). This is a DISTINCT gap
// from the already-ported `pr/uv-thread-safety` fix (`kk_box_mark_static`/`kk_block_make_stuck`/
// `kk_string_literal_init`), which secures already-initialized globals but not concurrent
// entry into the initializer.
//
// Fixed with a proper CAS-guarded init: the losing thread(s) spin-wait for the winner to
// finish (not just skip past), since later code in this function depends on the toplevel
// constants this init constructs.
val checkInitDoc = [
  "static _Atomic(int32_t) _kk_init_state = 0; // 0=not started, 1=in progress, 2=done".text,
  "{ int32_t _kk_init_expected = 0;".text,
  "  if (kk_atomic_cas_strong_acq_rel(&_kk_init_state, &_kk_init_expected, 1)) {".text,
  "    // this thread won the race and performs initialization below".text,
  "  } else {".text,
  "    while (kk_atomic_load_acquire(&_kk_init_state) != 2) { kk_atomic_yield(); }".text,
  "    return;".text,
  "  }".text,
  "}".text].vcat

val publishInitDoneDoc = "kk_atomic_store_release(&_kk_init_state, 2);".text

fun initImport(i: kimport)
  i.importName.qualify("@init".new-name).cpp-name |.| emptyArgs |.| semi

fun doneImport(i: kimport)
  i.importName.qualify("@done".new-name).cpp-name |.| emptyArgs |.| semi

val customInitDoc = [
  "#if defined(KK_CUSTOM_INIT)".text,
  "  KK_CUSTOM_INIT".text |+| emptyArgs |.| semi,
  "#endif".text].vcat

// run the parc-reuse pass (a core-phase pass) over a whole core
fun run-parc-reuse(enableReuse: bool, platform: platform, nt: newtypes, c: core): _ core
  var dgs := c.defs
  with handler
    fun get-core-defs() dgs
    fun set-core-defs(d) dgs := d
    fun phaseError(s) throw("parc-reuse: " ++ s)
  parc-reuse-core(enableReuse, platform, nt)
  c(defs = dgs)

fun genModule(core0: core, mbMain: maybe<(name, bool)>, nt: newtypes): _ core
  // upstream genModule runs these under liftUnique (the ambient unique effect
  // serves that role here): box/unbox transform, then the Perceus passes
  if get-env-value("KOKA_SHOW_PREBOX_CORE").is-just then
    trace(core0.defs.map(dg/show).join("\n"))
  val bcore = box-core(core0)
  // `KOKA_SHOW_BOX_CORE=1`: dump the core right after box-core (before parc)
  // for debugging box-coercion issues -- plain .show, not the pretty printer
  if get-env-value("KOKA_SHOW_BOX_CORE").is-just then
    trace(bcore.defs.map(dg/show).join("\n"))
  val borrowed1 = bcore.core/extend(helpers/borrowed) // borrowedExtendICore
  val pcore = parc-core(targetPlatform, nt, borrowed1, enableSpecialize, bcore)
  // `KOKA_SHOW_PARC_CORE=1`: dump the core right after parc (before parc-reuse)
  // for debugging dup/drop insertion issues -- plain .show, not the pretty printer
  if get-env-value("KOKA_SHOW_PARC_CORE").is-just then
    trace(pcore.defs.map(dg/show).join("\n"))
  val rcore = run-parc-reuse(enableReuse, targetPlatform, nt, pcore)
  val core = if enableReuse && enableReuseSpecialize then parc-reuse-specialize(rcore) else rcore
  // `KOKA_SHOW_FINAL_CORE=1`: dump the fully final backend core (after
  // parc-reuse/specialize, right before C emission) -- plain .show
  if get-env-value("KOKA_SHOW_FINAL_CORE").is-just then
    trace(core.defs.map(dg/show).join("\n"))

  val headComment = "// Koka generated module:".text |+| modName.show.pretty |+| ", koka version:".text |+| comp-flags.version.pretty |.| ", platform:".text |+| (targetPlatform.ptrSize * 8).pretty |.| "-bit".text
  val initSignature = "void".text |+| modName.qualify("@init".new-name).cpp-name |.| emptyParams
  val doneSignature = "void".text |+| modName.qualify("@done".new-name).cpp-name |.| emptyParams

  [checkInitDoc, core.imports.map(initImport).vcat, customInitDoc].vcat.emitToInit
  
  core.imports.reverse.map(doneImport).vcat.emitToDone

  emit-to-c(
    vcat([
      headComment,
      "#include".text |+| dquotes(modName.module-name-to-path.text |.| ".h".text)] ++
      core.externals.map(importExternalInclude).concat ++ 
      core.externals.map(includeExternalC).concat
    ))
  
  emit-to-h(
    vcat([
      "#pragma once".text,
      "#ifndef".text |+| prettyModName |.| "_H".text,
      "#define".text |+| prettyModName |.| "_H".text,
      headComment,
      "#include <kklib.h>".text] ++ 
      core.imports.map(moduleImport) ++ 
      core.externals.map(includeExternalH).concat
    ))

  emit-to-h(
    linebreak |.| 
    "// type declarations".text)

  gen-typedefs(core.typedefs)
  emit-to-h(
    linebreak |.| 
    "// value declarations".text)

  gen-top-groups(core.defs)

  genMain(mbMain)

  // publish "done" only after every emitToInit call above (this module's own toplevel
  // constants, plus its dependency @init calls) has completed -- see checkInitDoc.
  publishInitDoneDoc.emitToInit

  emitToDone(
    vcat([
      "static bool _kk_done = false;".text,
      "if (_kk_done) return;".text,
      "_kk_done = true;".text,
      pprint/empty,
      "#if defined(KK_CUSTOM_DONE)".text,
      "  KK_CUSTOM_DONE".text |+| emptyArgs |.| semi,
      "#endif".text,
    ]))

  val init = getInit()
  val done = getDone()
  emit-to-c(
    linebreak |.| 
    "// initialization".text |-|
    initSignature |.|
    init.block |-|
    "\n// termination".text |-|
    doneSignature |.|
    done.block)
  
  emit-to-h(
    vcat([
      linebreak |.| initSignature |.| semi |.| linebreak,
      linebreak |.| doneSignature |.| semi |.| linebreak] ++
      core.externals.map(includeEndExternalH).concat ++
      ["#endif // header".text]
    ))
  core

// TODO: more
fun moduleImport(imp: kimport): doc
  "#include".text |+|
  (if imp.package == "" then dquotes(imp.importName.module-name-to-path.text |.| ".h".text)
  else brackets(imp.package.text) |.| "/".text |.| imp.importName.module-name-to-path.text |.| ".h".text)

fun includeExternalC(ext: external)
  match external-import-lookup(buildType, "include-inline", ext)
    Just(content) -> [content.list.drop-while(is-white).string.text]
    _ -> []

fun includeExternalH(ext: external)
  match external-import-lookup(buildType, "header-include-inline", ext)
    Just(content) -> [content.list.drop-while(is-white).string.text]
    _ -> []

fun includeEndExternalH(ext: external)
  match external-import-lookup(buildType, "header-end-include-inline", ext)
    Just(content) -> [content.list.drop-while(is-white).string.text]
    _ -> []

fun importExternalInclude(ext: external): _ list<doc>
  match external-import-lookup(buildType, "include", ext)
    Just(includePath) -> 
      [
        "#include".text |+| 
        (
          if includePath.head-char.map(_=='<').is-just then includePath.text 
          else 
            dquotes(
              if sourceDir.string == "" then includePath.text 
              else (sourceDir / includePath.path).normalize-with('/').text)
      )]
    _ -> []

fun genMain(mbMain: maybe<(name, bool)>): _ ()
  match mbMain
    Nothing -> ()
    Just((name, _)) ->
      emit-to-c(
        "\n// main exit\n static void _kk_main_exit(void)".text |+| block(
          vcat([
            "kk_context_t* _ctx = kk_get_context();".text,
            cpp-name(modName.qualify("@done".new-name)) |.| parens("_ctx".text) |.| semi
          ])
        ) |-|
        "\n// main entry \nint main(int argc, char** argv)".text |+| block(vcat([
          text("kk_assert(sizeof(size_t) == " ++ targetPlatform.sizeSize.show ++ " && sizeof(void*) == " ++ targetPlatform.ptrSize.show ++ ");"),
          (if stackSize == 0 then pprint/empty else ("kk_os_set_stack_size(KK_IZ(" ++ stackSize.show ++ "));").text),
          "kk_context_t* _ctx = kk_main_start(argc, argv);".text,
          cpp-name(modName.qualify("@init".new-name)) |.| parens("_ctx".text) |.| semi,
          "atexit(&_kk_main_exit);".text,
          cpp-name(name) |.| parens("_ctx".text) |.| semi,
          cpp-name(modName.qualify("@done".new-name)) |.| parens("_ctx".text) |.| semi,
          "kk_main_end(_ctx);".text,
          "return 0;".text
        ]))
      )
