// Port of src/Compile/TypeCheck.hs -- the per-module front-end pipeline:
// fixity resolution, kind inference, type inference, then the initial core
// passes (unreturn -> simplify -> liftFunctions -> uniquefy) and the extra
// type-dependency imports.
//
// Divergences from upstream (documented, not silent):
//  - Pretty.Env / colorScheme parameters are ambient effects in this port.
//  - Core.Check (coreCheck) is not ported; the `--checkcore` flag is parsed
//    but never consulted (upstream default is False anyway), so the port has
//    no inter-pass Core-IR well-formedness checking. CheckFBIP IS ported and
//    wired -- see `check-fbip(...)` below.
//  - range maps: the port's infer-types always builds one via the ambient
//    build-range-map handler installed by the caller (upstream threads a
//    Maybe RangeMap).
// The caller must install: current-program, modname, uctx, unique,
// comp-error, colors, comp-flags, build-range-map (same as driver.kk today).
module compiler/compile/type-check
import compiler/lib/log
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/error
import compiler/common/unique
import compiler/platform/config
import compiler/kind/import-map
import compiler/kind/newtypes
import compiler/kind/synonyms
import compiler/kind/assumption
import compiler/kind/infer
import compiler/type/type
import compiler/type/assumption
import compiler/type/infer
import compiler/syntax/syntax
import compiler/static/fixity-resolve
import compiler/core/core
import compiler/core/corevar
import compiler/core/unreturn
import compiler/core/check-fbip
import compiler/core/borrowed
import compiler/core/simplify
import compiler/core/fun-lift
import compiler/core/uniquefy
import compiler/compile/options
import compiler/syntax/range-map
import compiler/compile/module
import std/os/env
import compiler/common/nice
import compiler/core/pretty
import compiler/lib/pprint
import compiler/type/pretty
import std/data/rb-map
import compiler/common/name-collections

// upstream `typeCheck :: Flags -> Definitions -> [Core.Import] -> UserProgram
//                     -> Error () (Core.Core, Maybe RangeMap)`
// also returns the gamma (upstream re-derives it in Build; the port's caller
// needs it for inline parsing and optimize) and the extended newtypes.
pub fun type-check(fl: flags, defs: definitions, coreImports: list<core/core/kimport>, program0: user-program)
  : _ (core, gamma, newtypes, kGamma)
  val progName = program0.name

  // import map
  val importMap = import-map-from-core-imports(program0.imports, coreImports)

  // binding groups and fixities
  // (named `progFixities` -- a local `fixities` would shadow the
  // `definitions.fixities` field accessor used just below)
  val progFixities = fixities-new(program0.fix-defs.map(fn(fd) (fd.name, fd.fixity)))
  val (program2, _, _) = fixity-resolve(fixities-compose(defs.fixities, progFixities), program0)

  // kind inference
  with val current-program = program2
  // upstream flushes kind-inference warnings at the END of typeCheck (after
  // the core phases): e.g. lazy/queue/bankers prints the checkFBIP warnings
  // BEFORE kind inference's "Cannot update the lazy constructor" warning.
  // Buffer them here and re-add after the core phases below.
  var kindWarns := []
  val (dgroups, kgamma1, (syns1, data1, _cons1, _gamma1), coreProgram) =
    with override
      ctl add-errors(errs) add-errors(errs)
      fun add-warnings(w) kindWarns := kindWarns ++ w
      fun add-infos(w) add-infos(w)
    infer-kinds(data/is-value, fl.tpl, importMap, defs.defs-kgamma, defs.defs-synonyms, defs.defs-newtypes)

  // initial gamma: upstream `gammaUnions [defsGamma defs, extractGamma
  // Core.dataInfoIsValue True coreProgram, extractGammaImports ...]`. Not
  // `gamma1` (kind inference's own constructor-only gamma, upstream
  // `constructorGamma`): only `extractGamma` also pulls in the module's own
  // `extern` declarations, without which a module cannot resolve its own
  // extern functions during its own type inference.
  val gamma0 = type/assumption/unions([defs.defs-gamma,
                                       extract-gamma(data/is-value, True, coreProgram),
                                       extract-gamma-imports(importMap.list, progName)])

  // type inference. The range map it returns is the REAL one -- inference
  // installs its own `build-range-map` internally, so the caller's ambient
  // handler only ever sees the handful of entries added outside inference.
  // Publish it so a language server can answer hover/definition from it.
  val (cgroups, rangemap) =
    infer-types(fl.tpl, 10000, importMap, gamma0, progName, syns1, data1, dgroups)
  // MERGE, do not replace: KIND inference already added entries to the ambient
  // map (module names on imports, type declarations), and inference installs
  // its own map internally for everything it infers. Publishing only the latter
  // silently loses go-to-definition on an import statement.
  set-range-map(get-range-map() ++ rangemap)

  // KOKA_SHOW_RAWCORE=1: dump the core immediately after type inference,
  // BEFORE unreturn/simplify-defs/lift-functions run -- to distinguish
  // "type inference never inserted this" from "unreturn/simplify/lift
  // stripped it afterward"
  if get-env-value("KOKA_SHOW_RAWCORE").is-just then
    with nice-env
    with default-doc-env
    with val pp-prec = precTopTop
    with val indent = 0
    with handler
      val ranked = rankedDefault
      val moduleContext = progName
      val importsMap = importMap
    with val pp-env = PrettyEnv(coreIface=False)
    val coreFixities0 = program0.fix-defs.filter(fn(fd) fd.vis.is-public)
                                        .map(fn(fd) core/core/FixDef(fd.name, fd.fixity))
    val rawCore = coreProgram(imports = coreImports, defs = cgroups, fix-defs = coreFixities0)
    emit-line(pretty-core(fl.target, [], rawCore).show)

  // --showicore (upstream TypeCheck.hs:111 `traceDefGroups "initial"`):
  // print the core right after type inference, before any core phase runs.
  // Divergence: upstream prints via trace with a "-----initial-----" header;
  // this port reuses the same pretty-core printer as --showcore/--showfcore.
  if fl.showInitialCore then
    with nice-env
    with default-doc-env
    with val pp-prec = precTopTop
    with val indent = 0
    with handler
      val ranked = rankedDefault
      val moduleContext = progName
      val importsMap = importMap
    with val pp-env = PrettyEnv(coreIface=False, coreShowDef=True)
    val icoreFixities = program0.fix-defs.filter(fn(fd) fd.vis.is-public)
                                         .map(fn(fd) core/core/FixDef(fd.name, fd.fixity))
    emit-line(pretty-core(fl.target, [], coreProgram(imports = coreImports, defs = cgroups, fix-defs = icoreFixities)).show)

  // initial core phases (unreturn -> simplify -> liftFunctions), then uniquefy
  var dgs := cgroups
  with handler
    fun get-core-defs() dgs
    fun set-core-defs(d) dgs := d
    fun phaseError(s) throw("type check: " ++ s)
  unreturn()
  // FBIP/FIP check (upstream TypeCheck.hs: `checkFBIP` runs between
  // unreturn and the initial simplify). Upstream passes the gamma RETURNED
  // by inferTypes (gamma0 extended with the module's own inferred defs);
  // the port's infer-types does not return it, so reconstruct it the same
  // way driver.kk builds `ownCoreGamma`.
  val fbipBorrowed = core/extend(coreProgram(defs = dgs), defs.borrowed)
  val fbipGamma = type/assumption/union(gamma0, gamma/new(dgs.flatten.map(fn(d) core-def-info(d, 0))))
  check-fbip(fl.targetPlatform, data1, fbipBorrowed, fbipGamma, progName, dgs)
  val ndebug = fl.optimize > 0
  if fl.simplify >= 0 then
    simplify-defs(False, ndebug, fl.simplify, 0) // simplifyNoDup
  // lift recursive functions to top-level before specialize
  // (so specializeDefs do not contain local recursive definitions)
  lift-functions()

  val coreFixities = program0.fix-defs.filter(fn(fd) fd.vis.is-public)
                                      .map(fn(fd) core/core/FixDef(fd.name, fd.fixity))
  val coreUnique = coreProgram(imports = coreImports,
                               defs = dgs,
                               fix-defs = coreFixities).core/uniquefy

  // KOKA_SHOW_TCCORE=1: dump the core immediately after type-check (before
  // ANY optimize.kk pass runs), for diffing against upstream's own core at
  // an equivalent point -- distinguishes "type inference never inserted
  // this" from "an optimize pass removed it later"
  if get-env-value("KOKA_SHOW_TCCORE").is-just then
    with nice-env
    with default-doc-env
    with val pp-prec = precTopTop
    with val indent = 0
    with handler
      val ranked = rankedDefault
      val moduleContext = progName
      val importsMap = importMap
    with val pp-env = PrettyEnv(coreIface=False)
    emit-line(pretty-core(fl.target, [], coreUnique).show)

  // add extra imports needed to resolve types in this module
  val typeDeps = extract-deps-from-signatures(coreUnique)
  val currentImports = coreImports.map(importName)
  val typeImports = typeDeps.filter(fn(nm) !currentImports.any(fn(i) i == nm) && nm != progName)
                            .map(fn(nm) Kimport(nm, "", Private, "", provenance = ImportTypes))
  val coreFinal = coreUnique(imports = coreUnique.imports ++ typeImports)
  // flush the buffered kind-inference warnings LAST (see the note at the
  // infer-kinds call above)
  add-warnings(kindWarns)
  (coreFinal, gamma0, data1, kgamma1)

// The program imports provide aliases
pub fun import-map-from-core-imports(progImports: list<syntax/syntax/kimport>, cimports: list<core/core/kimport>): import-map
  cimports.map(importName).foldl(imports-empty) fn(im, modname)
    val alias0 = match progImports.find(fn(imp) imp.fullName == modname)
      Just(imp) -> imp.name
      Nothing -> modname
    match im.extend(alias0, modname)
      Just(im') -> im'
      Nothing -> im
