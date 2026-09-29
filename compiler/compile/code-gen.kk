// Port of src/Compile/CodeGen.hs (sequential subset): write the module
// interface (this port uses the .kki core-interface format for its own
// output), dispatch to the target backend (JS or C), and -- for the C
// target -- link a runnable executable (upstream `codeGenLinkExe`; see
// compiler/compile/link.kk for what's ported vs. simplified).
//
// Not ported (documented): the C# backend, html/doc generation, C library
// search (conan/vcpkg) -- linking uses a prebuilt reference object cache
// rather than building kklib/the std libraries fresh (see link.kk).
module compiler/compile/code-gen
import std/os/path
import std/os/file
import std/os/dir
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/unique
import compiler/common/nice
import compiler/common/color-scheme
import compiler/platform/config
import compiler/kind/newtypes
import compiler/kind/import-map
import compiler/type/type
import compiler/type/pretty
import compiler/core/core
import compiler/core/borrowed
import compiler/core/pretty
import compiler/backend/js/from-core
import compiler/backend/c/from-core
import compiler/lib/pprint
import compiler/compile/options
import compiler/common/file
import compiler/lib/log
import compiler/compile/link
import std/os/env
import std/data/rb-map
import compiler/common/name-collections

// The pretty-environment fields that come
// from command-line flags (--showkinds via type sigs, --showsynonyms,
// --showcoretypes, --showtypeids); colors/html fields are handled elsewhere
pub fun pp-env-from-flags(fl: flags, coreIface: bool = False, coreShowDef: bool = False): pretty-env
  PrettyEnv(showKinds = fl.showKinds, expandSynonyms = fl.showSynonyms,
            coreShowTypes = fl.showCoreTypes, showIds = fl.showTypeIds,
            coreIface = coreIface, coreShowDef = coreShowDef)

// handler-installing wrapper for `pp-env-from-flags`: driver.kk installing
// `with val pp-env = pp-env-from-flags(fl)` directly (a DYNAMIC initializer,
// unlike every other `with val pp-env = PrettyEnv(...)` literal in the tree)
// trips a reference-compiler C-codegen bug inside its monadic-lift wrappers
// (an undefined `kk_type_pretty__value_pp_env_l<line>_c<col>` cache symbol);
// installing the handler here in code-gen's own translation unit avoids it.
pub fun with-pp-env-from-flags(fl: flags, action: () -> <pp-env|e> a): e a
  with val pp-env = pp-env-from-flags(fl)
  action()

// Writes `<outBase>.kki` (interface,
// WITH the inline-definition section) and the target sources. A module's
// import list comes from the CORE program's own imports -- never from the loaded
// module map, whose aliased entries (a module under both its canonical name
// and an as-written relative-import name) the JS backend would turn into two
// real `import ... from './<name>.mjs'` statements.
pub fun code-gen(fl: flags, nt: newtypes, brw: borrowed, mbMain: maybe<(name, bool)>,
                 outBase: path, importsMap0: import-map,
                 inlineDefs: list<inline-def>, modContext: name, c: core,
                 // locally-compiled imported modules in build order, linked
                 // into the entry executable (upstream `codeGenLinkC`'s objs)
                 cImports: list<c-unit> = [],
                 // the entry's own compile's library declarations
                 entryEimports: list<(string, maybe<string>, maybe<string>)> = [],
                 // every `library` of the closure and every `syslib` of the
                 // imported modules (upstream `libs` / `syslibs`)
                 clibs: list<(string, maybe<string>, maybe<string>)> = [],
                 csyslibs: list<string> = [],
                 // reports the executable that was linked. The language server's
                 // `koka/compile` command has to hand the path back to the client
                 // (which then runs or debugs it), and nothing else in the build
                 // returns it -- it is computed here and used here.
                 on-exe: (path) -> _ () = fn(_p) ()): _ ()
  phase-verbose(2, "codegen", modContext.show-plain)
  // pretty environment (upstream penv from flags with the module context)
  with nice-env
  with default-doc-env
  with val pp-prec = precTopTop
  with val indent = 0
  with handler
    val ranked = rankedDefault
    val moduleContext = modContext
    val importsMap = importsMap0
  // KOKA_SHOW_FCORE=1: dump the final core (post-optimize, pre-codegen) in
  // the format `--showfcore` prints, for direct diffing against the
  // reference compiler's output
  if get-env-value("KOKA_SHOW_FCORE").is-just then
    val fcoreDoc =
      with val pp-env = PrettyEnv(coreIface=False)
      pretty-core(fl.target, inlineDefs, c)
    emit-line(fcoreDoc.show)
  // --showcore prints the final OPTIMIZE core (with
  // definition bodies); --showfcore does too but only on non-C targets (on C
  // the BACKEND core after box/parc is printed instead, see the C branch)
  val isCTarget = match fl.target
    C -> True
    _ -> False
  if fl.showCore || (fl.showFinalCore && !isCTarget) then
    val coreDoc =
      with val pp-env = pp-env-from-flags(fl, coreShowDef=fl.showCore)
      pretty-core(fl.target, inlineDefs, c)
    emit-line(coreDoc.show)
  // interface: coreIface=True, including the inline section
  val ifaceDoc =
    with val pp-env = PrettyEnv(coreIface=True)
    pretty-core(fl.target, inlineDefs, c)
  val outname = outBase.change-ext("kki")
  // The files this module's `extern import`s inlined, beside the interface, for
  // the rebuild check (`module-input-time`). Written first: a crash between the
  // two leaves an older interface, which is only stale.
  val kkd = outBase.change-ext("kkd")
  val file-deps = c.externals.flatmap fn(e)
    match e
      ExternalImport(imports, _) ->
        imports.filter-map(fn((k, v)) if k == file-dependency-key then Just(v.path.realpath.string) else Nothing)
      _ -> []
  if file-deps.is-cons || kkd.dir/is-file then write-text-file(kkd, file-deps.unlines)
  write-text-file-atomic(outname, ifaceDoc.show)
  // upstream never prints per-file "wrote" progress at all (only the final
  // "created :" executable, gated on `verbose > 1` -- CodeGen.hs:404); match
  // that threshold here so `-v0`/default test-harness output isn't polluted
  // with build-progress lines that would never appear in a real `.kk.out`
  phase-verbose(2, "wrote", outname.string)
  // target code
  match fl.target
    JS ->
      val jsDoc =
        with val pp-env = PrettyEnv()
        javascript-from-core(fl.build-type, mbMain, c.imports, c)
      val jsname = outBase.change-ext("mjs")
      write-text-file(jsname, jsDoc.show)
      phase-verbose(2, "wrote", jsname.string)
      if fl.showAsmJS then emit-line(jsDoc.show)  // --showjs
      // generated modules import their dependencies SIBLING-relative
      // (`./std_core_types.mjs`), which is upstream's emission: every .mjs
      // goes in ONE shared output directory, so the imports resolve against
      // the sibling modules this build already emitted there.
      val runname = outBase.dirname.path / (modContext.module-name-to-path ++ ".mjs").path
      write-text-file(runname, jsDoc.show)
      // upstream `codeGenLinkExe`'s non-C branch: `-e`/evaluate runs the
      // program (via `node`) and its stdout is what --run-mode output compares
      // against; a library module (no mbMain) has nothing to run
      match mbMain
        Just(_) | fl.evaluate ->
          val (out, exitcode) = run-js(fl.node, runname, fl.execOpts)
          print(out)
          if exitcode != 0 then throw("command failed:\n " ++ fl.node ++ " " ++ runname.string)
        _ -> ()
    C ->
      val (cdoc, hdoc, ccore) =
        with val pp-env = PrettyEnv()
        with withNewtypes(nt)
        cFromCore(CDefault, fl.build-type, outBase.dirname.path, fl.targetPlatform, nt, brw,
                  fl.parcReuse, fl.parcSpecialize, fl.parcReuseSpecialize, fl.parcBorrowInference,
                  fl.optEagerPatBind, fl.stackSize, mbMain, c)
      // --showfcore on the C
      // target prints the BACKEND core (after box/parc/reuse -- this is what
      // the parc test suite inspects), with definition bodies, no inlines
      if fl.showFinalCore then
        val bcoreDoc =
          // upstream builds this env from `prettyEnvFromFlags flags` directly
          // (CodeGen.hs:291) WITHOUT the module context/imports of the outer
          // penv -- so names (notably type constructors) print fully qualified
          with override
            val ranked = rankedDefault
            val moduleContext = name/nil
            val importsMap = imports-empty
          with val pp-env = pp-env-from-flags(fl, coreShowDef=True)
          pretty-core(fl.target, [], ccore)
        emit-line(bcoreDoc.show)
      // the generated .c's OWN `#include "<modname>.h"` (genModule) uses the
      // MODULE-NAME-encoded filename (e.g. `overload/eta1` -> `overload_eta1`),
      // which can differ from outBase's plain file stem whenever the module
      // was named with a parent-dir prefix (the entry-naming logic in
      // driver.kk, needed so JS-target error messages match upstream's `-i
      // test`-style module names) -- write the C output under that SAME
      // module-name-encoded stem so the self-#include actually resolves.
      val cBase = outBase.dirname.path / (modContext.module-name-to-path).path
      if fl.showAsmC then emit-line(cdoc.show)  // --showc
      write-text-file-atomic(cBase.change-ext("c"), cdoc.show)
      phase-verbose(2, "wrote", cBase.change-ext("c").string)
      write-text-file-atomic(cBase.change-ext("h"), hdoc.show)
      phase-verbose(2, "wrote", cBase.change-ext("h").string)
      // The .c is NOT compiled here. `compile-graph-rpc` dispatches it to a
      // dedicated clang pool the moment this module's compile returns, so the
      // front-end worker never blocks on `run-system-read` and can go straight
      // back for its next module. (Compiling inline here overlaps the phases
      // -- first .o at 0.2s instead of 259.7s -- but costs the front end its
      // worker: measured, the front-end span stretched 258s -> 491s, since on a
      // serial dependency chain a single worker alternates front-end/clang --
      // a module is not announced ready until its compile RETURNS.)
      // Link an executable when there's a `main`
      // to run (a library module with no entry has nothing to link)
      match mbMain
        Just(_) ->
          if fl.kklibIncludeDir != "" then
            // `outBase.noext` leaves a trailing "." (lib/std/os/path.kk
            // `change-ext(p,"")` always prepends a dot to the new -- empty --
            // extension); build the extension-less exe path directly instead.
            // `-o`/`--output` overrides the final executable path (upstream
            // outFinalPath, extension-less by convention).
            // use the module-name-encoded stem (like the .c/.h above, and like
            // upstream's `lib_dir` exe naming) -- the plain source stem can
            // collide with a DIRECTORY next to the source (test/lib/dir/)
            val exePath = if fl.outFinalPath != "" then fl.outFinalPath.path
                          else cBase
            // the linker does not create the directory of `-o out/sub/app`
            if fl.outFinalPath != "" then ensure-dir(exePath.dirname.path)
            phase("linking", exePath.string)
            match c-link(fl, C-unit(cBase.change-ext("c"), entryEimports), exePath, fl.kklibIncludeDir.path, cImports, clibs, csyslibs)
              Nothing ->
                phase("created", exePath.string)
                on-exe(exePath)
                // `-e`/evaluate runs the just-linked
                // executable and its stdout is the actual test/run output
                if fl.evaluate then
                  val (out, exitcode) = run-exe(exePath, fl.execOpts)
                  print(out)
                  // a failing program fails the compile, as upstream `runSystem`
                  // raises on a non-zero exit (so the driver exits non-zero)
                  if exitcode != 0 then throw("command failed:\n " ++ exePath.string)
              Just(diagnostics) ->
                // A link failure fails the compile, as upstream `runCommand`
                // raises: the driver reports it and exits non-zero, and the
                // language server's `try` turns it into a response. It must
                // not go straight to stdout, which in language-server mode is
                // the JSON-RPC stream -- see `claim-stdout`.
                throw("link failed for " ++ exePath.string ++ ":\n" ++ diagnostics)
        Nothing -> ()
      phase-verbose(3, "codegen done", modContext.show-plain)
    _ ->
      throw("code-gen: unsupported target " ++ fl.target.show)
