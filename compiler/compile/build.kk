// Port of the loading/build logic of src/Compile/Build.hs + Compile/Module.hs,
// SEQUENTIAL: upstream builds modules concurrently over IORef module-maps with
// wait-conditions; this port compiles in dependency (topological) order with a
// plain finished-module map, which is semantically equivalent for a correct
// dependency graph (upstream's build order is only a scheduling concern).
//
// Phases are collapsed accordingly: a module here is either loaded from an
// interface (.kki, inline section parsed lazily against the full gamma,
// upstream PhaseIfaceLoaded) or compiled from source through
// type-check -> optimize -> codegen (upstream PhaseTyped/Optimized/CodeGen).
// File-time-based revalidation (modulesReValidate): a dependency module whose
// cached interface (in the build output dir) is newer than its source and
// newer than every dependency's interface is LOADED rather than recompiled;
// the entry module named on the command line always rebuilds.
module compiler/compile/build
import std/os/path
import std/core/undiv
import std/core/unsafe
import std/os/file
import std/os/env
import std/os/dir
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/platform/config
import compiler/syntax/syntax
import compiler/syntax/colorize
import compiler/syntax/gen-doc
import compiler/syntax/parse
import compiler/common/parse
import compiler/lib/pprint
import compiler/type/assumption
import compiler/core/core
import compiler/core/parse
import compiler/core/inlines
import compiler/kind/synonyms
import compiler/compile/options
import compiler/compile/module
import compiler/compile/vfs
import compiler/compile/phase
import compiler/common/file
import std/data/rb-map
import compiler/lib/scc
import std/data/rb-set
import compiler/common/name-collections
import std/async
import std/async/thread
import compiler/common/name-prim
import compiler/common/color-scheme
import compiler/common/unique
import compiler/common/nice
import compiler/kind/kind
import compiler/kind/assumption
import compiler/kind/pretty
import compiler/kind/import-map
import compiler/kind/newtypes
import compiler/kind/unify
import compiler/syntax/range-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/pretty
import compiler/core/pretty
import compiler/compile/type-check
import compiler/compile/optimize
import compiler/compile/code-gen
import compiler/compile/link
import compiler/static/binding-groups
import compiler/lib/log
import compiler/compile/rpc

// Everything a check of ONE module makes available to an out-of-band consumer
// (today: the language server). A record rather than more callback parameters
// because each new feature wants one more field -- document symbols needed the
// parsed program, code actions need the newtypes -- and every added parameter
// churned four call sites.
pub type module-check
  ModuleCheck(
    modname: name,
    rmap: range-map,
    gam: gamma,
    prog: user-program,
    ntypes: newtypes,
    // for completion in a TYPE position: upstream offers synonyms there
    // alongside the data types (`synonymCompletions`)
    syns: synonyms,
    // for the REPL's `:k` listing
    kgam: kGamma)

// `@`-identifiers are permitted when lexing ANY module, not only primitive
// ones and the synthesized `@main` module.
//
// The layout pass rejects `@` in identifiers unless this is set -- with a narrow
// exemption for an id directly after `fun`/`val`/`extern`. That exemption is why
// `pub fun @expr()` parsed while `@open import` did NOT: upstream's REPL and
// language server both depend on `@open import` to reach a module's private
// definitions, and the synthetic `@main.kk` compile-expr writes is full of
// `@`-names. `.kki` interfaces and `std/core/types`/`hnd` are the other users.
pub val allow-at = True

// a build module: either an interface load or a from-source compile
// (collapsed from upstream's Module record; fields added as the port needs them)
pub type bmodule
  // loaded from a compiled interface; inlines parse lazily against the full gamma
  // `mgamma` caches `extract-gamma(is-value, False, mcore)` -- computed ONCE
  // per module instead of re-extracted on every `defs-of` (which every
  // compile-module calls, so re-extraction was O(modules^2) over a build;
  // the reference compiler leaves the same cache commented out because
  // laziness hides the cost there; this port is strict)
  // `inlineDefs` holds the interface's inline section ALREADY RESOLVED, not a
  // lazy closure. A module's inline bodies only reference ITS OWN imports
  // (upstream moduleWaitForInlineImports -- e.g. std/core's inlines mention
  // std/core/undiv, a private import), and those are all loaded by the time
  // this module is, so the section can be resolved here once. Keeping it lazy
  // meant re-parsing it once per DEPENDENT (inlines-of forces every loaded
  // module on every compile) and left a closure in the module map, which a
  // parallel build would then re-run in each worker's heap.
  //
  // `pending-inlines`: the inline section NOT yet resolved (upstream
  // `PhaseIfaceLoaded`: "interface is loaded, but the inline definitions are not
  // yet parsed"). Pre-loading defers it so interfaces load with no ordering at
  // all -- resolving it needs the gamma of the module's own closure, which is
  // the only thing that ever forced dependency order on loading. It is resolved
  // before anything is optimized (`resolve-pending-inlines`), and `inlines-of`
  // resolves any that are still pending rather than dropping them.
  ModIface(mcore: core, inlineDefs: list<inline-def>, mgamma: gamma, at: build-time = 0, cFile: maybe<path> = Nothing,
           pending-inlines: maybe<(gamma) -> <div,exn,ndet,parse-error> list<inline-def>> = Nothing)
  // compiled from source in this build (final core after optimize + its inline
  // defs); `cFile` is the generated C translation unit (when targeting C) so
  // the entry link can compile locally-built imported modules in too --
  // upstream links each module's own .o, this port's single-invocation c-link
  // (see link.kk) passes the .c files along instead
  ModCompiled(mcore: core, inlineDefs: list<inline-def>, mgamma: gamma, cFile: maybe<path> = Nothing, at: build-time = 0)
  // type checked in this build but not yet optimized or code generated
  // Enough for a DEPENDENT's type check, which only
  // needs gammas and types -- never for its optimize/codegen, which need
  // inline definitions and an interface. `typed` is what the finish stage
  // resumes from.
  ModTyped(mcore: core, mgamma: gamma, typed: typed-module)

// The state a module's compile carries from type checking into optimize and
// code generation, so the two can run as separate scheduled stages (upstream
// Build.hs `moduleTypeCheck` / `moduleOptimize` / `moduleCodeGen`).
// `unique` is the module's unique counter at the end of type checking: the
// finish stage continues from it, so generated names are the same as when
// both stages ran in one go.
pub struct typed-module
  prog: syntax/syntax/program<user-type, user-kind>
  tcore: core
  gamma0: gamma
  newtypes: newtypes
  kgamma: kGamma
  rmap: range-map
  unique: int

// Which part of a module's compile to run (see `typed-module`).
pub type compile-stage
  // parse, type check, optimize and generate code (entries always do this)
  StageAll
  // parse and type check only; the result is a `ModTyped`
  StageTypecheck
  // optimize and generate code for a module already type checked
  StageFinish(typed: typed-module)

pub fun bmod/gamma(m: bmodule): gamma
  match m
    ModIface(mgamma=g) -> g
    ModCompiled(mgamma=g) -> g
    ModTyped(mgamma=g) -> g

pub fun bmod/core(m: bmodule): core
  match m
    ModIface(c) -> c
    ModCompiled(c) -> c
    ModTyped(c) -> c

// when this module's interface was produced: the artifact's mtime for a
// loaded interface, the freshly written .kki's mtime for a compile.
// This is the whole incremental-rebuild mechanism (see compile/phase).
pub fun bmod/at(m: bmodule): build-time
  match m
    ModIface(at=t) -> t
    ModCompiled(at=t) -> t
    ModTyped -> 0

pub fun bmod/cfile(m: bmodule): maybe<path>
  match m
    ModIface(cFile=c) -> c
    ModCompiled(cFile=c) -> c
    ModTyped -> Nothing

// the (sequential) build state: modules finished so far, in build order
// Loaded/compiled modules by name. Upstream keeps `[Module]` lists in build
// order plus a `NameMap` for lookup; nothing here depends on the order this map
// iterates in beyond message order (gamma candidates, import-map ambiguity hints).
pub alias bmodules = name-map<bmodule>

// upstream `modulesResolveDependencies`/`moduleLoad` collapsed: resolve a
// module name to either a sibling source file (compile it via `compileSource`)
// or a compiled interface on the search path; recurses over imports first so
// the returned map is in dependency order.
//
// `in-progress` tracks the chain of modules currently being resolved (upstream
// detects cycles separately via `scc` over the fully-loaded module set in
// `toBuildOrder`, reporting "recursive imports" for any non-singleton SCC).
// This port instead finishes each module before returning from its call, so
// a module isn't in `mods0` until its own resolution is done -- without this
// explicit chain, a cyclic import (A imports B, B imports A) would recurse
// forever instead of producing upstream's clean build error.
// Where modules are looked for, and what names them. A module's file is looked
// for in its importer's own directory first (`relative-fallback-dir`), then in
// `search`. `roots` is the include path: a found file is named after its real
// path relative to the longest root containing it (upstream
// `searchPathsCanonical`). `search` is the directory of every file being built,
// then the include path; those directories are searched but are never roots,
// which upstream has no counterpart for: it finds a root file's siblings only
// through the root's own directory.
pub struct module-dirs
  search: list<path>
  roots: list<path>

// upstream `moduleNameResolve`/`resolveDep`, called once per import
// immediately after lexing: resolve a module name to its source file and its
// CANONICAL name, so nothing downstream sees the as-written name again.
// Also used to find the source of a name that is already canonical.
fun resolve-module-name(nm: name, dirs: module-dirs, fallback-dir: maybe<path>): _ (maybe<path>, name)
  val fname = (nm.show-plain ++ ".kk").path
  val candidates = match fallback-dir
    Just(fd) -> Cons(fd, dirs.search)
    Nothing -> dirs.search
  match candidates.map(fn(d) d / fname).find(vfs/is-file)
    Just(fp) -> (Just(fp), canonical-module-name(fp, dirs.roots).default(nm))
    Nothing -> (Nothing, nm)

// The name of the module in file `fp`: upstream `pathToModuleName` of its real
// path relative to the longest root containing it (roots nest: the current
// directory holds `lib` in a workspace). An in-memory overlay is named by its
// path as given, as upstream looks the VFS up before `realPath`.
//
// Nothing when no root contains the file, or when the name does not lead back
// to it (a `.` or `_` in the path: `.koka/x/m.kk` under the current directory
// is `koka/x/m`). Upstream uses such a name regardless and then fails to find
// the module by it; here the import keeps the name as written, which the
// importer's own directory resolves.
fun canonical-module-name(fp: path, roots: list<path>): _ maybe<name>
  val s = match vfs-find(fp)
    Just -> fp.string
    Nothing -> fp.string.realpath.string
  val fromRoot = roots.filter-map fn(d)
    match s.starts-with(d.string ++ "/")
      Just(rest) -> Just((d.string.count, rest.string))
      Nothing -> Nothing
  match fromRoot.foldl(Nothing) fn(best, (n, rel)) match best { Just((m, _)) | m >= n -> best; _ -> Just((n, rel)) }
    Just((_, rel)) ->
      val stem = if rel.ends-with(".kk").bool then rel.list.take(rel.count - 3).string else rel
      val canonical = stem.path-to-module-name
      if canonical.show-plain == stem then Just(canonical) else Nothing
    Nothing -> Nothing

// A module's
// relative imports resolve against a root computed from its OWN DECLARED
// name (the `module X` header), not a fixed number of directory levels.
// `declared`'s segment count minus one is how many levels `updirs` walks up
// from the importing file's own directory -- e.g. `std/async/async.kk`
// declaring `module async/async` (2 segments) walks up 1 level from its own
// directory (`.../std/async`) to `.../std`, so its relative import
// `async/internal` resolves to `.../std/async/internal.kk`. A 0-segment
// (nil) or unparsed declared name walks up 0 levels -- the importing file's
// own directory, same as before this existed.
fun updirs(p: path, n: int): path
  if n <= 0 then p else updirs(p.dirname.path, (n - 1).pretend-decreasing)

pub fun relative-fallback-dir(src: path, declared: name): path
  val segs = if declared.is-nil then 0 else declared.show-plain.split("/").length
  updirs(src.dirname.path, if segs <= 0 then 0 else segs - 1)

// Alias each of `src`'s imports AS WRITTEN to the entry of its canonical name,
// for a module about to be compiled from `src` whose deps were read from its
// interface (see `resolve-module`).
fun with-source-aliases(mods: bmodules, src: path, declared: name, source-dirs: module-dirs, tpl: target-platform): _ bmodules
  val fallback-dir = Just(relative-fallback-dir(src, declared))
  parse-dependencies-of(src, tpl).snd.foldl(mods) fn(acc, (asWritten, _))
    val dep = resolve-module-name(asWritten, source-dirs, fallback-dir).snd
    if asWritten == dep || acc.contains-key(asWritten) then acc
    else match acc.lookup(dep)
      Just(bm) -> acc.set(asWritten, bm)
      Nothing -> acc

// Canonicalize every dep name in one pass, upstream `resolveDep`-style (see
// `resolve-module-name`'s doc comment): called wherever a `(name, range)`
// dep list is about to feed `resolve-module`'s recursion or
// `restrict-to-closure`, so nothing downstream ever sees an as-written alias.
pub fun canonicalize-deps(deps: list<(name, range)>, src: path, declared: name, source-dirs: module-dirs): _ list<(name, range)>
  val fallback-dir = Just(relative-fallback-dir(src, declared))
  deps.map(fn((dep, drng)) (resolve-module-name(dep, source-dirs, fallback-dir).snd, drng))

pub fun resolve-module(mods0: bmodules, nm: name, out-dir: path, need-cfile: bool,
                       search-dirs: list<path>,
                       source-dirs: module-dirs,
                       // INFERRED, written out: the parameter's row is the SAME as
                       // this function's own row below, so `compile-source` is invoked
                       // with exactly the evidence in scope here -- no colors, no
                       // comp-flags, and ONE `exn` (from `io`). `vfs-lookup` is here
                       // because a module's SOURCE may come from the in-memory
                       // overlay rather than disk (compiler/compile/vfs.kk).
                       compile-source: (path, name, bmodules) -> <io,comp-error,parse-error,vfs-lookup,log|e> bmodule,
                       deps-cache: dep-cache = rb-map/empty(),
                       in-progress: list<name> = [], irange: range = range/null,
                       // see `resolve-module-name`'s doc comment: callers now
                       // canonicalize via `canonicalize-deps` before this is
                       // ever reached in the normal case, so this fallback is
                       // a safety net, not the primary mechanism.
                       fallback-dir: maybe<path> = Nothing,
                       // for host-conditional imports -- see `parse-dependencies-of`
                       tpl: target-platform = target-platform-default,
                       // `walk-rebuild`'s decisions: when given, they decide whether a
                       // module is compiled or loaded, instead of the check below
                       decisions: maybe<name-map<rebuild-decision>> = Nothing): <io,comp-error,parse-error,vfs-lookup,log|e> bmodules
  if mods0.contains-key(nm) then mods0
  elif in-progress.any(fn(n) n == nm) then
    parse-error("recursive imports: " ++ Cons(nm, in-progress).reverse.map(show-plain).join(" -> "), range/null)
  else
    val chain = Cons(nm, in-progress)
    // the AS-WRITTEN name (before any relative-import rename below):
    // consumers that still reference a module by the name as it appeared in
    // an import statement (e.g. `pub-import-closure`'s own `mods.lookup` on
    // `prog1.imports`'s raw text) need this to keep working -- see the
    // aliasing at the end of this function.
    val orig-nm = nm
    val (mbSrc, nm) = resolve-module-name(nm, source-dirs, fallback-dir)
    val result = match mbSrc
      Just(src) ->
        // compile its imports first; the parallel discovery pre-pass usually
        // already scanned this file (fall back to a direct parse if not).
        // `discover-deps`'s own scan is keyed by canonical name -- when a
        // relative import renamed `nm`, a `deps-cache` entry under that
        // canonical key could belong to a DIFFERENT same-named source file,
        // so always re-parse `src` directly in that case rather than trust
        // the cache.
        val (declared0, deps00, fromIface) = if orig-nm != nm then
                      { val (dn, ds) = parse-dependencies-of(src, tpl); (dn, ds, False) }
                    else match deps-cache.lookup(nm)
                      Just((_, dn, ds, fi)) -> (dn, ds, fi)
                      Nothing -> { val (dn, ds) = parse-dependencies-of(src, tpl); (dn, ds, False) }
        // Interface-derived deps are canonical: they carry no as-written form,
        // so they produce none of the relative-import aliases below. A module
        // loaded from its interface needs none, since it is never type-checked;
        // one that is compiled does, and gets them from its source in
        // `with-source-aliases` below. Reading every module's source instead
        // would cost a warm load most of what interface discovery saves (293ms
        // of a 1455ms load on a 27-module closure).
        val (declared, deps0) = (declared0, deps00)
        val deps = deps0.canonicalize-deps(src, declared, source-dirs)
        // `deps0.zip(deps)` pairs each dep's AS-WRITTEN name with its
        // canonical form: `prog1.imports` (what `pub-import-closure` and
        // friends key their `mods.lookup`s on) still holds the AS-WRITTEN
        // text, but `mods1` below only ever gets a canonical key from
        // `resolve-module` -- alias the as-written key to the same entry
        // here too, or an as-written relative import like `async/internal`
        // (canonical `std/async/internal`) is invisible to every later
        // lookup keyed by the raw import text.
        val mods1 = deps0.zip(deps).foldl(mods0) fn(acc, ((asWritten, _), (dep, drng)))
          val acc1 = resolve-module(acc.pretend-decreasing, dep, out-dir, need-cfile, search-dirs, source-dirs, compile-source, deps-cache, chain, drng,
                                     Just(relative-fallback-dir(src, declared)), tpl, decisions)
          if asWritten == dep then acc1
          else match acc1.lookup(dep)
            Just(bm) -> acc1.set(asWritten, bm)
            Nothing -> acc1
        // Incremental rebuild (upstream modulesReValidate, collapsed): reuse
        // the interface a previous build wrote to the OUTPUT cache when it is
        // newer than the source and newer than every dependency's interface.
        // Roots always recompile (the driver compiles the entry directly, not
        // through here), so diagnostics for the file the user asked about are
        // always fresh -- upstream behaves the same way, and its test suite
        // runs with reuse enabled (Spec.hs only adds -r when --rebuild is
        // explicitly requested).
        val kki = out-dir / (nm.module-name-to-path ++ ".kki").path
        val cfile = out-dir / (nm.module-name-to-path ++ ".c").path
        val src-t = vfs/file-mtime(src)
        val iface-t = file/file-mtime(kki)
        val dep-ts = deps.map(fn((dep, _)) mods1.lookup(dep).map(bmod/at).default(0))
        val can-link = if need-cfile then cfile.dir/is-file else True
        val load = match decisions.map(fn(ds) ds.lookup(nm))
          Just(Just(d)) -> !d.is-stale
          _ -> iface-t > 0 && can-link && !is-stale(src-t, iface-t, dep-ts)
        if load then
          // An unreadable cached interface must mean "recompile", never a
          // build error: the cache may hold output from an older compiler
          // whose printer disagreed with today's parser (two such round-trip
          // bugs fixed already), or a torn write from a crashed process.
          // Falling back keeps the cache self-healing -- the recompile
          // overwrites the bad artifact. The trace keeps regressions visible
          // on stderr without affecting -v0 output.
          match load-iface(kki, mods1, iface-t, if need-cfile then Just(cfile) else Nothing)
            Just(m) ->
              trace-orch("resolve load-kki   " ++ nm.show-plain)
              phase("load", nm.show-plain)
              mods1.set(nm, m)
            Nothing ->
              trace("incremental: unreadable cached interface, recompiling: " ++ kki.string)
              trace-orch("resolve compile-source(bad-cache) " ++ nm.show-plain)
              val mods2 = if fromIface then mods1.with-source-aliases(src, declared, source-dirs, tpl) else mods1
              mods2.set(nm, compile-source(src, nm, mods2))
        else
          val tdep0 = dep-tlog-start()
          // compile against the module's own transitive import closure, not
          // every module the walk happens to have resolved so far (upstream
          // moduleWaitForPubImports/moduleOptimize build per-module
          // environments the same way). This makes a module's compile a pure
          // function of its dependencies -- the precondition for running
          // module compiles as parallel tasks with identical output.
          trace-orch("resolve compile-source " ++ nm.show-plain)
          val mods2 = if fromIface then mods1.with-source-aliases(src, declared, source-dirs, tpl) else mods1
          val env = mods2.restrict-to-closure(deps.map(fst))
          trace-env("compile", nm, env)
          val m = compile-source(src, nm, env)
          dep-tlog(nm, tdep0)
          mods2.set(nm, m)
      Nothing -> match find-kki(search-dirs, nm)
        Nothing ->
          // upstream Build.hs `errorNotFound`: an ErrBuild message at the
          // IMPORT's range, naming the importing module and the search path
          val parent = in-progress.head.default(name/nil)
          val fromDoc = if parent.is-nil then pprint/empty
                        else pprint/empty |+| ("(imported from " ++ parent.show-plain ++ ")").text
          val spDoc = "search path:".text |+| (search-dirs ++ source-dirs.search).map(fn(d) d.string.text).list.align
          msg/add-error(error-message-kind(
            ("could not find module: " ++ nm.show-plain).text |.| fromDoc |-| spDoc,
            irange, ErrBuild))
        Just(kki) ->
          trace-orch("resolve load-kki   " ++ nm.show-plain)
          val (c, mkInlines) = parse-core(kki, syns0 = mods-synonyms(mods0))
          // interfaces import transitively; load those too (iface-only, no compile)
          val mods1 = c.imports.map(importName).foldl(mods0) fn(acc, dep)
            resolve-module(acc.pretend-decreasing, dep, out-dir, need-cfile, search-dirs, source-dirs, compile-source, deps-cache, chain, decisions = decisions)
          val own = extract-gamma(data/is-value, False, c)
          mods1.set(nm, ModIface(c, with-inline-fp("iface", c.coreName, force-inlines(mkInlines, mods1, own)), own,
                                 at = file/file-mtime(kki)))
    // alias the AS-WRITTEN name to the same entry (see `orig-nm`'s doc
    // comment): a relative import (`import async/async`, resolved above to
    // `std/async/async`) still gets looked up by its AS-WRITTEN text
    // elsewhere (e.g. `pub-import-closure` walking `prog1.imports`, which
    // holds the raw parsed name, not the resolved one -- upstream instead
    // rewrites the import record itself right after resolution; the port
    // aliases both keys in the map instead, which is simpler and gives the
    // same lookup result everywhere a name from `prog1.imports` is used).
    if orig-nm == nm then result
    else match result.lookup(nm)
      Just(bm) -> result.set(orig-nm, bm)
      Nothing -> result

// KOKA_TRACE_ORCH=1: emit one line per module-resolution decision, so the
// parallel and sequential paths can be diffed. A module that appears BOTH as
// an orchestrator `compiled` event and as a `resolve compile-source` event
// here was built twice -- the exact defect the wave path used to hide.
// DIAGNOSTIC (KOKA_INLINE_FP=1): the inline-definition set a module contributes,
// and where it came from. An interface round-trip must preserve this set
// exactly: the optimizer's inlining decisions depend on it, so a set that
// differs between a dependency COMPILED in this run and the same dependency
// LOADED from its interface makes the two paths draw a different number of
// uniques and emit different generated names -- which is what makes a cold and
// an incremental build produce different artifacts for identical sources.
pub fun inline-fp(prov: string, nm: name, idefs: list<inline-def>): _ ()
  if get-env-value("KOKA_INLINE_FP").is-just then
    val parts = idefs.map fn(d)
      d.def-name.show-plain ++ ":" ++ d.cost.show ++ ":" ++ d.kind.show ++ ":" ++
        d.is-rec.show ++ ":" ++ d.paramSpecialize.show-list(show)
    val h = parts.join("|").list.foldl(7, fn(a, c) (a * 31 + c.int) % 1000000007)
    println("INLINE-FP " ++ prov.pad-right(9) ++ " " ++ nm.show-plain ++
            " n=" ++ idefs.length.show ++ " fp=" ++ h.show)
    // KOKA_INLINE_FP_MOD=<module>: dump the fields per definition, to say WHICH
    // of them the round-trip fails to preserve.
    match get-env-value("KOKA_INLINE_FP_MOD")
      Just(want) ->
        if want == nm.show-plain then
          parts.foreach fn(line) println("INLINE-DEF " ++ prov.pad-right(9) ++ " " ++ line)
      Nothing -> ()

// Pass-through form for the interface sites, which build the set inline.
pub fun with-inline-fp(prov: string, nm: name, idefs: list<inline-def>): _ list<inline-def>
  inline-fp(prov, nm, idefs)
  idefs

pub fun trace-orch(msg: string): _ ()
  if get-env-value("KOKA_TRACE_ORCH").is-just then println("ORCH " ++ msg)

// Per-dependency compile timing (KOKA_TIMING=1), so a cold build attributes
// its wall time to modules rather than one opaque `load-modules` bucket.
fun dep-tlog-start(): _ int
  if get-env-value("KOKA_TIMING").is-just then now-ms() else 0

fun dep-tlog(nm: name, t0: int): _ ()
  if get-env-value("KOKA_TIMING").is-just then
    println("TIMING dep " ++ nm.show-plain.pad-right(40) ++ ": " ++ (now-ms() - t0).show ++ "ms")

// ---------------------------------------------------------------------------
// Dependency discovery pre-pass (Stage 3, increment 1).
//
// Before the build walk, discover the import graph of all SOURCE modules
// breadth-first. The walk then reuses these scans instead of re-parsing every
// source for its imports, which removes the historical double-parse of each
// module (once for deps, once to compile). That double-parse removal is the
// entire point of this pass.
//
// The scan is deliberately SEQUENTIAL. It was written to fan out over
// std/os/task, which segfaulted on any graph with real source dependencies
// (the 440-test sweep never caught it: those tests import only interface-only
// std modules, so the fan-out had nothing to do and never ran). Measured on
// the compiler's own 97-module graph, discovery is 312ms against 18.6s of
// load-modules -- 1.6% of the build -- so concurrency here buys nothing even
// when it works. The parallelism worth having is per-module compilation
// (increment 2b).
//
// A file that fails to parse contributes no edges here -- the build walk will
// compile it and report the error with full diagnostics.
// declared name (the file's own `module X` header, see `relative-fallback-
// dir`'s doc comment) alongside the path and deps, so a `resolve-module`
// hit that reuses this cache instead of reparsing still has what it needs
// to compute the fallback dir for THIS module's own relative imports.
// The `bool` is FROM-INTERFACE: True when the import list came from the .kki
// rather than the source. It matters for RELATIVE imports: a source writes
// `import async/internal`, an interface records `std/async/internal`, and
// `resolve-module` builds its as-written -> canonical aliases by zipping the
// two forms. From an interface both sides are canonical, so no alias is made
// and a later lookup keyed on the source's text misses -- which shows up as
// `Type async-cancel is not defined` when the module is compiled.
pub alias dep-cache = name-map<(path, name, list<(name, range)>, bool)>

// `tpl`: the SAME target platform the real compile uses (`fl.tpl`), not
// `parse-program-from-string`'s wildcard default. A conditional import
// (`[host=libc|jsnode] ...`) is resolved AT PARSE TIME against whatever
// `ptarget-platform` is in scope -- parsing with the wrong platform makes
// every guard fail, silently dropping the WHOLE conditional import from
// `prog.imports` (not an error, just gone). `resolve-module` trusts this
// scan's `deps` on a cache hit instead of reparsing, so a module compiled
// with the RIGHT platform (and so seeing the import) still gets handed an
// environment missing that dependency's exports -- and, since a dependency
// missed here is invisible to `discover-deps`'s wave/dispatch scheduling
// entirely, it only ever gets resolved later via `resolve-module`'s own
// fallback, INLINE, on whatever thread happens to need it -- outside the
// normal dispatch path (see the compile-graph-rpc segfault this also fixes).
fun scan-deps(content: string, fname: string, tpl: target-platform): pure (name, list<(name, range)>)
  val r = unsafe-total fn()
    try fn()
      val prog = parse-program-from-string(content, fname.path, allow-at, tpl = tpl)
      (prog.name, prog.imports.map(fn(i) (i.fullName, i.nameRange)))
  match r
    Ok(r2) -> r2
    Error(_) -> (name/nil, [])

// `next`'s frontier names are canonicalized (via each work item's own
// `(src, declared)`, `relative-fallback-dir`-style) BEFORE `locate` ever
// sees them: a bare relative import like `async/internal` doesn't exist as
// a literal path under any `source-dirs` root, only under its declared
// module's own fallback dir, so leaving it as-written here means `locate`
// silently fails to find it (treated as "interface-only", never scheduled
// for compilation) and it only ever gets compiled later via
// `resolve-module`'s own fallback -- INLINE, synchronously, on whichever
// thread happens to be resolving it at the time, instead of through the
// normal wave/dispatch path. Not just a completeness gap: the reference-
// compiler's orchestrator drove exactly this way once, and it corrupted
// memory (see the compile-graph-rpc segfault this fixes).
// `out-dir` has NO default on purpose. A defaulted `".".path` here segfaults:
// `path` runs a `std/text/parse` handler, and evaluating that inside a
// default-argument thunk in this module makes the handler frame resume into a
// wild address (reproducible at -O1 and -O2; hoisting the same expression to a
// top-level `val` avoids it). That is a reference-compiler codegen bug, not a
// bug here -- but every caller already has the out dir, so requiring it costs
// nothing and keeps the crash out of the port.
pub fun discover-deps(roots: list<name>, source-dirs: module-dirs, tpl: target-platform,
                      out-dir: path,
                      // a previous run's cache to start from: a language server
                      // re-checks the same graph on every keystroke, and rescanning
                      // it dominates the cost of the edit itself
                      cache0: dep-cache = rb-map/empty()): _ dep-cache
  fun locate(nm: name): _ maybe<path>
    source-dirs.search.map(fn(d) d / (nm.show-plain ++ ".kk")).find(vfs/is-file)
  fun waves(cache: dep-cache, frontier: list<name>): _ dep-cache
    val work = frontier.filter-map fn(nm)
      if cache.contains-key(nm) then Nothing
      else match locate(nm)
        Just(src) ->
          if !iface-discovery() then Just((nm, src, Right(vfs/read-text-file(src))))
          else
            val kki = out-dir / (nm.module-name-to-path ++ ".kki").path
            val it = file/file-mtime(kki)
            if it > 0 && vfs/file-mtime(src) <= it then
              match imports-of-kki(kki)
                Just((dn, ds)) -> Just((nm, src, Left((dn, ds))))
                Nothing        -> Just((nm, src, Right(vfs/read-text-file(src))))
            else Just((nm, src, Right(vfs/read-text-file(src))))
        Nothing -> Nothing   // interface-only module; the walk loads its kki
    if work.is-nil then cache
    else
      val scanned = work.map fn((_, src, e))
        match e
          Left(pre)      -> pre
          Right(content) -> scan-deps(content, src.string, tpl)
      val cache1 = work.zip(scanned).foldl(cache) fn(acc, ((nm, src, e), (declared, deps)))
        phase-verbose(3, "discover", nm.show-plain ++ (if e.is-left then " (interface)" else " (source)"))
        acc.set(nm, (src, declared, deps, e.is-left))
      val next = work.zip(scanned).flatmap fn(((_, src, _), (declared, deps)))
        deps.canonicalize-deps(src, declared, source-dirs).map(fst)
                     .filter(fn(nm) !cache1.contains-key(nm))
      waves(cache1, next.pretend-decreasing)
  waves(cache0, roots)

// Whether a module of this build is compiled or loaded: see `walk-rebuild`.
pub type rebuild-decision
  // load the interface; not compiled this round
  Fresh(iface-time: build-time)
  // compile from source this round, with the imports as written in that source
  Stale(src: path, declared: name, deps: list<(name, range)>)

// The walk's only state. A decision is final once made, and a module is
// decided from its dependencies' decisions alone, so a handler may keep the
// decisions locally (one walker) or share them with other walkers through an
// owner that keeps the first decision made for each module.
pub effect rebuild-plan
  // the decision already made for `nm`, if any
  fun decided(nm: name): maybe<rebuild-decision>
  // record the decision for `nm`; every dependency of `nm` is decided before it
  fun decide(nm: name, d: rebuild-decision): ()

// Decide, dependencies first, which modules reachable from `roots` are compiled
// this round. A module with source is Stale when
//   - it has no interface, or (C target) no generated C to link, or
//   - its source is newer than its interface, or
//   - a dependency is Stale, or
//   - a Fresh dependency's interface is newer than its own (rebuilt by an
//     earlier build that did not rebuild this module).
// Its compiled output depends on every interface its compile read, all of which
// lie in its transitive import closure, so this is exactly "something it was
// compiled against changed" -- by induction over the dependency order.
//
// Dependencies are BUILD-ORDER imports. An interface also records `inline`
// imports the optimizer introduced (`std/core/order` records
// `std/core/hnd inline`, and `hnd` is compiled after `order`); comparing
// interface times across such an edge made `order` stale against an artifact of
// the very same build, cascading into 98 of 113 modules. `imports-of-kki`
// leaves them out: whatever they refer to was reached through the build-order
// closure, which the rule above already covers.
//
// A Stale module whose imports were read from its interface gets them from its
// source instead: it is compiled from source, which looks its imports up by the
// name as written, relative ones included. (Upstream `validateDependency`
// reloads such a module from source.) Modules without source here are loaded
// from an interface on the search path and are never compiled.
pub fun walk-rebuild(roots: list<name>, dcache: dep-cache, out-dir: path, search-dirs: list<path>,
                     source-dirs: module-dirs, need-cfile: bool, tpl: target-platform): _ ()
  fun iface-time(p: path): _ build-time
    file/file-mtime(p)
  fun visit(nm: name, chain: list<name>): _ rebuild-decision
    match decided(nm)
      Just(d) -> d
      Nothing ->
        // a cycle is reported by the build itself; decide nothing through it
        if chain.any(fn(c) c == nm) then Fresh(0)
        else
          val chain1 = Cons(nm, chain)
          val d = match dcache.lookup(nm)
            Nothing ->
              Fresh(find-kki(search-dirs, nm).map(iface-time).default(0))
            Just((src, declared, deps0, fromIface)) ->
              val ds = deps0.canonicalize-deps(src, declared, source-dirs).map(fn((dep, _)) visit(dep, chain1))
              val kki = out-dir / (nm.module-name-to-path ++ ".kki").path
              val kki-t = iface-time(kki)
              val can-link = if need-cfile then (out-dir / (nm.module-name-to-path ++ ".c").path).dir/is-file else True
              val stale = kki-t <= 0 || !can-link || vfs/file-mtime(src) > kki-t
                          || ds.any(fn(d) match d { Stale -> True; Fresh(t) -> t > kki-t })
              if !stale then Fresh(kki-t)
              elif !fromIface then Stale(src, declared, deps0)
              else
                val (declared1, deps1) = parse-dependencies-of(src, tpl)
                deps1.canonicalize-deps(src, declared1, source-dirs).foreach fn((dep, _))
                  val _ = visit(dep, chain1)
                  ()
                Stale(src, declared1, deps1)
          phase-verbose(3, "validate", nm.show-plain ++ (if d.is-stale then " (stale)" else " (fresh)"))
          decide(nm, d)
          d
  roots.foreach fn(r)
    val _ = visit(r, [])
    ()

// The transitive import closure of `direct` within the resolved map, keeping
// the map's own (build) order for the surviving entries -- gamma/newtype
// union order is observable in ambiguity hints, so the order must not depend
// on how the closure was grown. A resolved module's core imports already list
// its own closure (see core-imports-from-modules), so growth converges fast.
//
// `direct` can hold AS-WRITTEN relative-import aliases (e.g. "async/internal")
// rather than a module's CANONICAL identity (e.g. "std/async/internal") --
// every caller passes `deps.map(fst)`, a module's raw parsed import list,
// which `resolve-module`'s fallback mechanism only canonicalizes for its OWN
// `mods` key, not at the call site (see `pub-import-closure`'s doc comment
// for the general shape of this class of bug: an un-canonicalized name here
// means `keep` ends up containing the alias key instead of (or in addition
// to) the canonical one some OTHER module's `core.imports` already
// references, so the restricted env handed to a worker is missing that
// module under the key everything else expects it under). Canonicalize each
// `direct` name via the module's own `core.coreName` up front, same as
// `pub-import-closure` does for its own output.
pub fun restrict-to-closure(mods: bmodules, direct: list<name>): div bmodules
  fun canonical(nm: name): name
    match mods.lookup(nm)
      Just(m) -> m.bmod/core.coreName
      Nothing -> nm
  fun grow(done: list<name>, frontier: list<name>): div list<name>
    val fresh = frontier.filter(fn(n) !done.any(fn(d) d == n))
    if fresh.is-nil then done
    else
      val next = fresh.flatmap fn(n)
        match mods.lookup(n)
          Just(m) -> m.bmod/core.imports.map(importName)
          Nothing -> []
      grow(done ++ fresh, next.pretend-decreasing)
  val keep = grow([], direct.map(canonical))
  // Keep a KEPT module's ALIAS key(s) too (any name that resolves, via
  // `mods`'s own aliasing, to a bmodule whose CANONICAL identity is in
  // `keep`) -- not just the canonical key itself. `compile-module` calls
  // `pub-import-closure` a SECOND time on THIS restricted map (to build
  // `tcMods`), and that call's own canonicalization does `mods.lookup(nm)`
  // on the AS-WRITTEN name from `prog1.imports` (e.g. "async/internal");
  // dropping the alias key here -- keeping only "std/async/internal" -- means
  // that second lookup misses, silently omitting the module from `tcMods`
  // even though it's genuinely in the closure.
  rb-map/empty().add-all(mods.list.filter(fn((n, m)) keep.any(fn(k) k == n) || keep.any(fn(k) k == m.bmod/core.coreName)))

// Synonyms of every module loaded so far. Seeds the interface parser so a
// synonym the emitter did not re-declare in the `local alias` section (e.g.
// std/core/types/ctx in trmc-lifted signatures) still parses as TSyn rather
// than degrading to a bare TCon. Dependencies load before dependents, so at
// each parse the relevant synonyms are present.
fun mods-synonyms(mods: bmodules): _ synonyms
  mods.values.map(fn(m) m.bmod/core.core/extract-synonyms).foldl(synonyms/empty, synonyms/compose)

// Parse a cached interface, absorbing parse failures into Nothing so the
// caller can fall back to recompiling (see the reuse branch above).
// Read one module from its cached `.kki`: the interface parse, its gamma, and
// its inline section. Factored out of `resolve-module` so the SAME load can run
// on a worker thread (see `compile-graph-rpc`): upstream loads interfaces
// concurrently -- `modulesResolveDeps` maps `moduleLoad` with
// `mapConcurrentModules`, "we can concurrently load (and lex) modules" -- and
// on a warm build that is the whole of the work.
//
// `deps` must already hold everything this module imports: `force-inlines`
// needs the accumulated gamma to resolve the inline bodies. A wave/readiness scheduler satisfies
// exactly that precondition, which is why loads can be dispatched at all.
//
// `Nothing` means "unreadable, recompile it" -- never a build error. The cache
// may hold output from an older compiler whose printer disagreed with today's
// parser (two such round-trip bugs fixed already), or a torn write from a
// crashed process. Falling back keeps the cache self-healing: the recompile
// overwrites the bad artifact.
pub fun load-iface(kki: path, deps: bmodules, at: int, cFile: maybe<path>,
                   // leave the inline section unresolved (see `pending-inlines`);
                   // `deps` is then not consulted at all
                   defer-inlines: bool = False): _ maybe<bmodule>
  // No synonyms are seeded from `deps`: an interface carries everything needed
  // to read it back, and the reader builds its synonym environment from the
  // file's own `local alias` section and type declarations. That holds only
  // while the emitter declares every synonym it prints -- including a `TSyn`
  // with no `syn-info` (`pp-synonym`) and synonyms used only in the inline
  // section (`extract-imported-synonyms`). Seeding would cost an O(closure)
  // `mods-synonyms` fold per module, measured at ~9% of a warm build of
  // compiler/main/driver.kk.
  match parse-core-cached(kki, synonyms/empty)
    Nothing -> Nothing
    Just((c, mkInlines)) ->
      val own = extract-gamma(data/is-value, False, c)
      if defer-inlines then Just(ModIface(c, [], own, at = at, cFile = cFile, pending-inlines = Just(mkInlines)))
      else Just(ModIface(c, with-inline-fp("iface", c.coreName, force-inlines(mkInlines, deps, own)), own, at = at, cFile = cFile))

// One module's pre-load request, resolved on the OWNER strand so a worker
// never needs `vfs-lookup` evidence established on another thread (mtimes and
// the C-file check are the owner's job; the worker only parses).
struct load-req
  nm    : name
  kki   : path
  at    : int
  cFile : maybe<path>
  env   : bmodules

// PARALLEL INTERFACE PRE-LOAD -- the warm build's entire cost, and the one
// phase no scheduler ever saw.
//
// `compile-graph-rpc` schedules only STALE modules, so on a warm rebuild
// (`stale-set` empty) it returns immediately and every interface is then loaded
// one at a time on the walk's own strand. Measured on `scripts/probe-tiny.kk`:
// 1.24s wall against 1.25s CPU -- fully serial -- while upstream's warm run of
// the SAME target is 1.6x parallel at 0.43s. Upstream needs no separate pass
// for this because its resolve phase is concurrent by construction:
// `modulesResolveDeps` maps `moduleLoad` with `mapConcurrentModules`, commented
// "we can concurrently load (and lex) modules". This is that phase, as a
// pre-pass, feeding the `preloaded` map the rest of the build already accepts.
//
// WHY THIS IS SAFE WHERE PARALLEL SCANNING WAS NOT. Scanning a wave on workers
// (see the note above `imports-of-kki`) regressed on speed AND on
// reproducibility -- ids shifted, `@unroll-foldl@435` vs `@436`. The reason is
// specific: a source scan runs `parse-program-from-string`, which draws from the
// SHARED `unique` effect, so interleaving two scans interleaves their id
// allocation. An interface parse does not -- `core/parse`'s `eenv` handler
// carries its own `var unique := 1000`, private to that one parse. Loads are
// therefore order-independent. The only ordering that remains is the real one:
// a module's imports must be loaded before it, which is what the waves are for.
//
// Results are merged in WAVE order, never completion order: a bmodules map's
// order is observable (gamma/newtype union order reaches ambiguity hints, e.g.
// static/wrong/alias1), so dispatch nondeterminism must not reach it.
//
// Only a module whose WHOLE transitive closure is fresh may be preloaded. A
// module can look fresh against the `.kki` its dependency wrote LAST build while
// that dependency is itself stale. The sequential walk catches this -- it
// re-checks staleness against the dep's IN-MEMORY timestamp after resolving it,
// so the dependent recompiles -- but a preloaded entry is handed to the build as
// authoritative and would never be rebuilt. `prune` below drops them.
pub fun preload-ifaces(fl: flags, out-dir: path, source-dirs: module-dirs,
                       dcache: dep-cache, stale-set: list<name>,
                       have0: bmodules): _ bmodules
  // canonicalize each entry's deps ONCE, upstream-`resolveDep`-style, before any
  // of it is treated as authoritative (see `canonicalize-deps`)
  val entries = dcache.list.map fn((nm, (src, declared, deps0, _)))
    (nm, src, deps0.canonicalize-deps(src, declared, source-dirs).map(fst))
  fun in-graph(n: name): bool
    entries.any(fn((k, _, _)) k == n)
  val cand0 = entries.filter-map fn((nm, _, _))
    if stale-set.any(fn(s) s == nm) then Nothing
    elif have0.contains-key(nm) then Nothing
    else Just(nm)
  // fixpoint: drop any candidate that depends on a module which is itself not
  // preloadable (stale, or dropped by an earlier round)
  fun prune(cands: list<name>): div list<name>
    val keep = cands.filter fn(nm)
      match entries.find(fn((k, _, _)) k == nm)
        Nothing -> False
        Just((_, _, ds)) -> ds.all fn(d)
          // not in the source graph => interface-only, imposes no ordering;
          // already in `have0` => loaded and valid
          !in-graph(d) || have0.contains-key(d) || cands.any(fn(c) c == d)
    if keep.length == cands.length then keep
    else prune(keep.pretend-decreasing)
  val cands = prune(cand0)
  // DIAGNOSTIC (KOKA_NO_PRELOAD=1): load every interface on the walk's own
  // strand, as before this pass existed. The point is a same-binary A/B: the
  // build dir, the flags hash and the driver are then identical on both sides,
  // so a diff in the artifacts is attributable to the loading path and nothing
  // else. (Comparing two DIFFERENT drivers cannot show that -- the port's cold
  // parallel compile is independently nondeterministic on `std/core/list`,
  // `bytes` and `show`, which an old-vs-new comparison picks up as well.)
  if get-env-value("KOKA_NO_PRELOAD").is-just then have0
  elif cands.length < 2 then have0
  else
    // a cycle is the walk's to report (`resolve-module` prints the full chain);
    // pre-loading nothing keeps this pass out of that path entirely
    val adj = entries.filter-map fn((nm, _, ds))
      if cands.any(fn(c) c == nm) then Just((nm, ds.filter(fn(d) cands.any(fn(c) c == d)))) else Nothing
    if !import-cycles(adj).is-nil then have0
    else load-unordered(fl, out-dir, cands, have0)

// Load every candidate interface concurrently, in no particular order. An
// interface parse needs nothing but its own file: synonyms are self-contained
// (see `load-iface`) and the inline section is deferred (see
// `pending-inlines`), so there is no dependency to wait for. Results merge by
// NAME in `cands` order, so which worker took which module cannot reach the
// output.
fun load-unordered(fl: flags, out-dir: path, cands: list<name>, have0: bmodules): _ bmodules
  // mtimes and the C-file check stay on THIS strand (see `load-req`)
  val reqs = cands.filter-map fn(nm)
    val kki = out-dir / (nm.module-name-to-path ++ ".kki").path
    val at = file/file-mtime(kki)
    if at <= 0 then Nothing else
      val cfile = out-dir / (nm.module-name-to-path ++ ".c").path
      val need-cfile = fl.target.is-c
      if need-cfile && !cfile.dir/is-file then Nothing
      else Just(Load-req(nm, kki, at, if need-cfile then Just(cfile) else Nothing, rb-map/empty()))
  if reqs.is-nil then have0
  else
    val results = xchannel()
    val n-workers = match get-env-value("KOKA_MAX_WORKERS")
      Just(v) -> max(1, min(v.parse-int.default(get-cpu-count()), reqs.length))
      Nothing -> max(1, min(get-cpu-count(), reqs.length))
    val numbered = reqs.map-indexed(fn(i, r) (i, r))
    list(0, n-workers - 1).foreach fn(w)
      val mine = numbered.filter-map(fn((i, r)) if i % n-workers == w then Just(r) else Nothing)
      spawn-thread fn()
        mine.foreach fn(r)
          results.xemit((r.nm, load-one-isolated(r)))
    val got = list(1, reqs.length).map(fn(_) results.xreceive)
    results.close
    if timing-on() then
      println("PRELOAD unordered: loaded " ++ got.filter(fn((_, mb)) mb.is-just).length.show ++ " of "
              ++ reqs.length.show ++ ", workers " ++ n-workers.show)
    cands.foldl(have0) fn(acc, nm)
      match got.find(fn((n2, _)) n2 == nm)
        Just((_, Just(m))) ->
          phase("load", nm.show-plain)
          acc.merge-loaded(nm, m)
        _ -> acc

// Resolve a module's deferred inline section against its OWN closure (upstream
// `moduleOptimize`'s `defsFromModules (mod:imports)`), exactly as `load-iface`
// does when it resolves eagerly.
pub fun bmod/resolve-inlines(m: bmodule, mods: bmodules): _ bmodule
  match m
    ModIface(c, _, own, at, cFile, Just(mk)) ->
      val deps = mods.restrict-to-closure(c.imports.map(fn(i) i.importName))
      ModIface(c, with-inline-fp("iface", c.coreName, force-inlines(mk, deps, own)), own, at = at, cFile = cFile)
    _ -> m

fun has-pending-inlines(m: bmodule): bool
  match m
    ModIface(pending-inlines = Just(_)) -> True
    _ -> False

// Resolve every deferred inline section, IN PARALLEL. Each needs only the CORES
// of its own closure, never another module's inline definitions, so there is
// no ordering between them. (A serial pass here was measured SLOWER than
// resolving during a dependency-ordered load: 58.6s -> 62.1s warm.)
pub fun resolve-pending-inlines(mods: bmodules): _ bmodules
  // one resolution per MODULE, even when it is present under an alias key too
  val pending = mods.list.filter(fn((_, m)) m.has-pending-inlines).foldl([]) fn(acc, km)
    val (_, m) = km
    if acc.any(fn((_, m2)) m2.bmod/core.coreName == m.bmod/core.coreName) then acc else acc ++ [km]
  if pending.is-nil then mods
  else
    val results = xchannel()
    val n-workers = match get-env-value("KOKA_MAX_WORKERS")
      Just(v) -> max(1, min(v.parse-int.default(get-cpu-count()), pending.length))
      Nothing -> max(1, min(get-cpu-count(), pending.length))
    val numbered = pending.map-indexed(fn(i, km) (i, km))
    list(0, n-workers - 1).foreach fn(w)
      val mine = numbered.filter-map(fn((i, km)) if i % n-workers == w then Just(km) else Nothing)
      spawn-thread fn()
        mine.foreach fn((_, m))
          results.xemit((m.bmod/core.coreName, resolve-inlines-isolated(m, mods)))
    val got = list(1, pending.length).map(fn(_) results.xreceive)
    results.close
    mods.list.foldl(mods) fn(acc, km)
      val (k, m) = km
      if !m.has-pending-inlines then acc
      else match got.find(fn((cn, _)) cn == m.bmod/core.coreName)
        Just((_, r)) -> acc.set(k, r)
        Nothing -> acc

// as `load-one-isolated`: nothing escapes into the worker's `<async,ioc>` row;
// a failure keeps the module with no inline definitions, which costs inlining,
// never correctness (the same absorption as `force-inlines`)
fun resolve-inlines-isolated(m: bmodule, mods: bmodules): <async,ioc> bmodule
  match try({ m.resolve-inlines(mods) })
    Ok(r) -> r
    Error(_) -> match m
      ModIface(c, _, own, at, cFile) -> ModIface(c, [], own, at = at, cFile = cFile)
      _ -> m

// A load that cannot escape into the worker's caller: `spawn-thread` runs its
// body in a closed `<async,ioc>` row, which has no `exn`, and an exception
// raised here could not be handled there anyway. An unreadable interface is
// already `Nothing` (see `load-iface`); this covers the rest, and a `Nothing`
// simply leaves the module to the walk, which recompiles it.
fun load-one-isolated(r: load-req): <async,ioc> maybe<bmodule>
  match try({ load-one(r) })
    Ok(m)     -> m
    Error(_)  -> Nothing

fun load-one(r: load-req): _ maybe<bmodule>
  load-iface(r.kki, r.env, r.at, r.cFile, defer-inlines = True)

// `resolve-module` aliases an as-written (relative) import name onto the
// canonical entry; a preloaded module is only ever keyed canonically, and the
// walk adds the alias itself when it resolves the importer.
fun merge-loaded(mods: bmodules, nm: name, m: bmodule): _ bmodules
  mods.set(nm, m)

fun parse-core-cached(kki: path, syns0: synonyms): _ maybe<(core, (gamma) -> <div,exn,ndet,parse-error> list<inline-def>)>
  with final ctl parse-error(_, _) Nothing
  Just(parse-core(kki, syns0 = syns0))

// A module's DECLARED name and imports read straight out of its INTERFACE,
// without parsing it. ON by default; see `iface-discovery` for the off switch.
//
// Upstream never touches the source when the interface is newer
// (`Build.hs`: `if modSourceTime < modIfaceTime then moduleLoadIface`), and
// takes a module's deps from the interface's CORE import list --
// `modFromIface`: `modDeps = [LexImport (Core.importName imp) nameNil ... |
// imp <- Core.coreProgImports core, not (Core.isCompilerImport imp)]`.
//
// Those core imports are a SUPERSET of the lexical ones (compiler/type/type:
// 10 lexical, 35 in its interface) because they are flattened and carry the
// interface's own dependencies. A superset is safe for discovery -- it can
// schedule a module that was not strictly needed, never miss one.
//
// It has to be a SCAN, not a `parse-core`: a core parsed during discovery
// would have an empty `syns0` (its dependencies are not loaded yet), which
// degrades synonyms to bare TCons that backend passes then fail on -- see
// `core/parse.kk`. So the real parse still happens once, in `resolve-module`,
// in dependency order where the synonyms are available.
//
// The shape is fixed and line-oriented, at the very top of the file:
//   module interface compiler/type/type
//   import std/core/types = std/core/types pub = "";
//
// The prize: discovery of `compiler/main/driver.kk` against a warm build dir
// costs 0.26s of user time this way against 5.39s of source parsing, and
// yields the IDENTICAL graph (127 modules, 27 waves, same wave sizes).
fun imports-of-kki(kki: path): _ maybe<(name, list<(name, range)>)>
  if !kki.dir/is-file then Nothing
  else
    // only the head: the import block is at the top, and an interface can be
    // megabytes (compiler/compile/build's is 5.77MB against 83KB of source).
    // If the block did not terminate inside the head, fall back to the whole
    // file rather than silently truncating the import list.
    val head-text = file/read-head(kki)
    val lines = if head-text.lines.any(fn(l) terminates-import-block(l)) then head-text.lines
                else file/read-text-file(kki).lines
    val declared = match lines.find(fn(l) l.starts-with("module interface ").bool)
      Just(l) -> l.replace-all("module interface ", "").trim.new-module-name
      Nothing -> return Nothing
    // imports are contiguous at the head; stop at the first declaration line
    // after them so a 400KB interface is not scanned end to end
    fun collect(ls: list<string>, acc: list<(name, range)>, seen: bool): _ list<(name, range)>
      match ls
        Nil -> acc
        Cons(l, rest) ->
          val t = l.trim
          // BOTH forms, and missing the second one is what made this look like
          // a dead end: a `pub import` is a publicly re-exported dependency and
          // is written with the keyword LEADING. `std/core` is 23 of them out
          // of 25, so matching only "import " saw 2 imports instead of 25, the
          // walk never reached `std/core/list`, and a warm compile failed with
          // `(++) cannot be resolved`.
          if t.starts-with("import ").bool || t.starts-with("pub import ").bool then
            // `[pub ]import <as-written> = <canonical> [pub] = "";`
            val rhs = t.replace-all("pub import ", "").replace-all("import ", "")
            val nm  = match rhs.split(" =").head
              Just(x) -> x.trim
              Nothing -> ""
            // `= <canonical> inline`: introduced by the optimizer, not a build-order
            // dependency (see `walk-rebuild`)
            if nm.is-empty || rhs.contains(" inline =") then collect(rest.pretend-decreasing, acc, True)
            else collect(rest.pretend-decreasing, acc ++ [(nm.new-module-name, range/null)], True)
          elif seen && !t.is-empty && !t.starts-with("//").bool then acc
          else collect(rest.pretend-decreasing, acc, seen)
    Just((declared, collect(lines, [], False)))

// PARALLEL DISCOVERY -- MEASURED, AND NOT WORTH IT AS TRIED.
//
// A wave's files ARE mutually independent (`scan-deps` is a pure function of
// one file's text; the cache is folded only after the whole wave; new names go
// to the next wave), and discovery's waves are WIDE -- scanning
// `compiler/compile/build.kk` takes three waves of 46, 75 and 29 modules, so
// spawn cost per wave is negligible.
//
// Scanning a wave on `spawn-thread` workers (workers xemit, owner xreceives --
// the correct channel direction) runs to completion, but it is a REGRESSION on
// both axes: discovery went 7724ms -> 9176ms, and module output stopped being
// reproducible (ids shift, e.g. `@unroll-foldl@435` vs `@436`; std modules
// differed in 38 of 186 files against 2 sequentially). The remaining suspects
// are the static round-robin slicing and the cross-thread transfer of results
// -- not wave width, and not thread-safety of the parse path (a probe ladder
// passes 20/20 at 14 workers).
//
// The far larger win is not to scan the sources at all: see `imports-of-kki`.

// Take a module's imports from its .kki when that interface is newer than the
// source, instead of parsing the source -- what upstream always does. ON by
// default; `KOKA_NO_IFACE_DISC=1` forces the source scan, which is the
// fallback to reach for when a graph looks wrong. See `imports-of-kki` for
// the shape and the measurement.
//
// The scan must match BOTH `import` and `pub import`. A publicly re-exported
// dependency is written with the keyword LEADING, and 23 of `std/core`'s 25
// interface imports are `pub import` -- matching only "import " saw 2, the
// walk never reached `std/core/list`, and a warm compile failed with
// `(++) cannot be resolved`. That looked like proof that the information was
// absent from the interface; it was a hole in the scanner.
fun iface-discovery(): ndet bool
  get-env-value("KOKA_NO_IFACE_DISC").is-nothing

// DIAGNOSTIC (KOKA_TRACE_ENV=1): what a module is actually compiled against.
// The ambiguity says extra names are in scope; this says WHICH.
// A line that ends the import block: the first non-blank, non-comment,
// non-import line.
fun terminates-import-block(l: string): bool
  val t = l.trim
  !t.is-empty && !t.starts-with("//").bool
    && !t.starts-with("import ").bool && !t.starts-with("pub import ").bool

pub fun trace-env(label: string, nm: name, mods: bmodules): _ ()
  if !get-env-value("KOKA_TRACE_ENV").is-just then () else
    val keys = mods.list.map(fn((k, _)) k.show-plain)
    println("ENV " ++ label ++ " " ++ nm.show-plain ++ " [" ++ keys.length.show ++ "] " ++ keys.join(" "))

// dependency scan: parse the program and take its DECLARED name (the
// `module X` header, before any path-derived rewriting -- see
// `relative-fallback-dir`'s doc comment) and its import list (upstream
// moduleLex scans just the header lexemes; parsing the whole file is
// equivalent for a valid program and reuses the existing parser)
// `tpl` is NOT optional in practice: a module can select its imports by host
//   import async/api/evloop
//     [host=libc|jsnode]   async/api/uv/evloop
//     [host=jsweb|wasmweb] async/api/web/evloop
// and resolving that against `target-platform-default` instead of `fl.tpl`
// silently picks the wrong branch -- `timer-setup` then "cannot be found"
// because it lives in the uv backend. `scan-deps` already threads `tpl`; this
// path did not, which was latent while it was only a cache-miss fallback.
pub fun parse-dependencies-of(src: path, tpl: target-platform = target-platform-default): _ (name, list<(name, range)>)
  val prog = parse-program-from-string(vfs/read-text-file(src), src, allow-at, tpl = tpl)
  (prog.name, prog.imports.map(fn(i) (i.fullName, i.nameRange)))

// EVERY resolved module (transitive, not
// just direct imports) becomes a core import; a module that was a direct
// lexical import keeps its declared visibility, everything pulled in only
// transitively (a public re-export) is Private in this module's own interface.
// The modules visible to a compile are the
// declared imports plus the closure of their PUBLIC core imports (and, for
// `@open` imports -- the generated-main case -- also their plain user
// imports), level by level, with DEEPER levels PREPENDED and first-occurrence
// order (`nub`) within a level. This exact order is what gets emitted as the
// module's own core import list (the parc suite inspects it byte-for-byte).
// A module's own identity, independent of which name a particular importer wrote.
// `resolve-module` keys `mods` under BOTH an as-written (relative) import alias and
// the canonical name, so a lookup succeeds either way; `core.coreName` is the truth.
pub fun canonical-modname(mods: bmodules, nm: name): name
  match mods.lookup(nm)
    Just(m) -> m.bmod/core.coreName
    Nothing -> nm

pub fun pub-import-closure(mods: bmodules, progImports: list<syntax/syntax/kimport>): div list<name>
  // A name reaching this closure can be an AS-WRITTEN relative-import alias
  // (e.g. "async/internal") rather than the module's own CANONICAL identity
  // (e.g. "std/async/internal") -- `resolve-module`'s fallback mechanism
  // aliases BOTH keys to the same `bmodule` in `mods` (see its own doc
  // comment), so `mods.lookup` succeeds either way, but the raw alias must
  // never leak into this function's OUTPUT: it becomes `core.imports`,
  // which every OTHER importer's own `pub-import-closure` walk (and
  // `import-map-from-core-imports`) treats as authoritative. An un-canonicalized
  // alias here produces a DIFFERENT import-map entry (2 segments, "as-written")
  // than the alias's own canonical 3-segment form, so a later reference
  // qualified with the canonical form ("std/async/internal/async-await")
  // never matches this entry and falls through to `resolve-path`'s
  // strip-and-locally-qualify fallback -- which reassembles the segments in
  // the WRONG (reversed) order ("internal/async/std/async-await"), not
  // just failing to resolve. Always resolving to the module's own
  // `core.coreName` here (its true identity, independent of which alias a
  // particular importer happened to write) fixes this at the source.
  fun canonical(nm: name): name
    canonical-modname(mods, nm)
  fun closure(alreadyDone0: list<name>, level: list<(bool, name)>): div list<name>
    val alreadyDone = alreadyDone0 ++ level.map(snd)
    val extras0 = level.flatmap fn((isOpen, mn))
      match mods.lookup(mn)
        Just(m) -> m.core.imports
          .filter(fn(imp) (imp.visibility.is-public || (isOpen && imp.provenance.is-importUser)) &&
                          !imp.provenance.is-importCompiler)
          .map(fn(imp) (isOpen, imp.importName))
        Nothing -> []
    val extras = extras0.foldl([]) fn(acc: list<(bool, name)>, x)
      val (_, nm) = x
      if alreadyDone.any(fn(d) d == nm) || acc.any(fn((_, a)) a == nm) then acc else acc ++ [x]
    if extras.is-nil then level.map(fn((_, nm)) nm.canonical)
    else closure(alreadyDone, extras) ++ level.map(fn((_, nm)) nm.canonical)
  // the program's own import list can name the same module twice (a redundant
  // `import m` is legal and upstream tolerates it); dedupe it on first
  // occurrence exactly as `extras` above, otherwise the module contributes its
  // typedefs twice and every type it exports looks ambiguous with itself
  val level0 = progImports.map(fn(imp) (imp.open, imp.fullName)).foldl([]) fn(acc: list<(bool, name)>, x)
    val (_, nm) = x
    if acc.any(fn((_, a)) a == nm) then acc else acc ++ [x]
  closure([], level0)

pub fun core-imports-from-modules(progImports: list<syntax/syntax/kimport>, mods: bmodules): div list<core/core/kimport>
  pub-import-closure(mods, progImports).map fn(nm)
    // upstream getVisibility/getProvenance: a direct lexical import keeps
    // its declared visibility and is ImportUser; anything pulled in only
    // transitively (a public re-export) is Private + ImportPub
    // `pub-import-closure` yields CANONICAL names, but a program's own import can
    // be written relatively -- `pub import async/api/thread [host=libc]
    // async/api/uv/thread` inside `std/async/thread` gives `fullName =
    // async/api/uv/thread`. Upstream compares against `lexImportName`, which is
    // already the RESOLVED module name, so canonicalize before matching here too.
    // Otherwise every relatively-written import is demoted to Private/ImportPub,
    // an importer's `pub-import-closure` refuses to follow the re-export (it
    // filters on `is-public`), and the re-exported module's types never reach the
    // importer -- e.g. `xsender` from `std/async/api/uv/thread`.
    val (vis, prov) = match progImports.find(fn(imp) canonical-modname(mods, imp.fullName) == nm)
      Just(imp) -> (imp.vis, ImportUser)
      Nothing -> (Private, ImportPub)
    core/core/Kimport(nm, "", vis, "", provenance = prov)

// `roots` and everything they import, in the order
// `scc` gives over each module's imports (dependencies before dependents)
pub fun build-order(mods: bmodules, roots: list<name>): _ list<(name, bmodule)>
  // the closure: `roots` and everything they import
  fun visit(acc: (name-set, list<(name, bmodule)>), nm: name): div (name-set, list<(name, bmodule)>)
    val (seen, out) = acc
    if rb-set/member(seen, nm) then acc
    else match mods.lookup(nm)
      Nothing -> (seen + nm, out)
      Just(m) ->
        val (seen1, out1) = m.bmod/core.imports.foldl((seen + nm, out)) fn(a, i) visit(a, i.importName)
        (seen1, Cons((nm, m), out1))
  val (inClosure, closure) = roots.foldl((names/empty, []), visit)
  val deps = closure.map fn((nm, m))
    (nm, m.bmod/core.imports.map(fn(i) i.importName).filter(fn(d) rb-set/member(inClosure, d) && mods.contains-key(d)))
  scc(deps).concat.filter-map(fn(nm) mods.lookup(nm).map(fn(m) (nm, m)))

// The import cycles in `deps` (module, its direct imports), one list of
// modules per cycle: upstream `toBuildOrder` reports every strongly connected
// component with more than one module as "recursive imports". A module that
// imports itself is a cycle as well, which upstream does not catch. Imports of
// modules outside `deps` (interface-only) cannot close a cycle and are ignored.
pub fun import-cycles(deps: list<(name, list<name>)>): div list<list<name>>
  val keys = deps.foldl(names/empty) fn(s, (nm, _)) s + nm
  val adj = deps.map(fn((nm, ds)) (nm, ds.filter(fn(d) rb-set/member(keys, d))))
  scc(adj).filter fn(grp)
    match grp
      [nm] -> adj.any(fn((k, ds)) k == nm && ds.any(fn(d) d == nm))
      _ -> True

// upstream `codeGen`'s `eimports`: the `library` declarations of a module and
// of its direct imports (`bcore : importcores`)
pub fun c-unit-eimports(mods: bmodules, c: core, bt: buildType): _ list<(string, maybe<string>, maybe<string>)>
  val cores = Cons(c, c.imports.filter-map(fn(i) mods.lookup(i.importName).map(fn(m) m.bmod/core)))
  nub-decls(cores.flatmap(fn(c2) clibs-of-core(c2, bt)))

// A LIST, so the caller's order
// (e.g. pub-import closure order) is the fold order
pub fun defs-of(mods: list<(name, bmodule)>): _ definitions
  // pass the CACHED per-module gammas alongside the cores: `defs-from-modules-g`
  // performs the exact same `unions`/folds in the same order as before, only
  // the per-module `extract-gamma` is memoized (ordering here is observable in
  // ambiguity hints, e.g. static/wrong/alias1, so it is deliberately untouched)
  // `mods` can hold the SAME module under two keys: `resolve-module` aliases an
  // as-written (relative) import name onto the canonical entry, so both keys map
  // to one bmodule. Folding both copies puts every one of that module's names
  // into gamma TWICE, and any lookup that requires a unique match then fails --
  // e.g. `core/open-resolve`'s effect `@tag` lookup, which needs exactly one
  // match for `std/async/internal/#async-ioc/@tag`. Deduplicate on the module's
  // own name, keeping first occurrence so the fold order stays as before
  // (ordering is observable in ambiguity hints, e.g. static/wrong/alias1).
  val deduped = mods.map(snd).foldl(([], [])) fn(acc: (list<name>, list<(core, gamma)>), m)
                  val (seen, out) = acc
                  val nm = m.bmod/core.coreName
                  if seen.any(fn(s) s == nm) then acc
                  else (Cons(nm, seen), Cons((m.bmod/core, m.bmod/gamma), out))
  defs-from-modules-g(deduped.snd.reverse)

// parse all interface inline sections against the full gamma
// (upstream moduleWaitForInlineImports + modInlines resolution)
// Resolve one interface's inline section against the module's OWN closure --
// its already-loaded dependencies PLUS its own defs, mirroring upstream
// `moduleOptimize`'s `defsFromModules (mod:imports)`. Upstream forces this
// once per module and memoises it in `modInlines`; the port kept a closure and
// re-ran it per DEPENDENT (inlines-of forced every loaded module on every
// compile), which is both redundant work and a closure in the module map. Failure is absorbed:
// an unreadable inline section costs inlining opportunities, never the build.
fun force-inlines(mk: (gamma) -> <div,exn,ndet,parse-error> list<inline-def>,
                  deps: bmodules, own: gamma): _ list<inline-def>
  val g = type/assumption/union(defs-of(deps.list).defs-gamma, own)
  with final ctl parse-error(_, _) []
  match try({ mk(g) })
    Ok(ds) -> ds
    Error(_) -> []

// Inline definitions are resolved when each module is loaded, so this is now a
// concatenation rather than N re-parses.
pub fun inlines-of(mods: bmodules): _ inlines
  val defss = mods.values.map fn(m)
    match m
      // normally resolved already (`resolve-pending-inlines`); resolving here
      // keeps a caller that skipped that pass correct rather than inline-less
      ModIface(pending-inlines = Just(_)) -> match m.resolve-inlines(mods)
        ModIface(_, idefs) -> idefs
        _ -> []
      ModIface(_, idefs) -> idefs
      ModCompiled(_, idefs) -> idefs
      ModTyped -> []
  inlines(defss.concat)


//----------------------------------------------------------------------
// Per-module compilation (upstream Build.hs `moduleCompile` and the
// `moduleParse`/`moduleTypeCheck`/`moduleOptimize`/`moduleCodeGen` chain it
// drives). `make-expr-def`/`prog-end-rng`/`add-default-handlers` are upstream
// BuildContext.hs's `buildcCompileExpr` source synthesis and `completeMain`;
// they live here because this port calls them from inside `compile-module`
// rather than from the build-context layer.
//----------------------------------------------------------------------

// --- profiling: coarse per-phase CPU timing (KOKA_TIMING=1 to enable) ---
// <time.h> must be included explicitly: it only arrived transitively via
// mimalloc's headers, so any build with `--fstdalloc` (needed for asan /
// valgrind / the macOS heap tools) failed with an implicit `clock()` decl
extern import
  c include-inline "#include <time.h>"

pub extern cpu-ms(): ndet int
  c inline "kk_integer_from_int((kk_intx_t)(clock()/(CLOCKS_PER_SEC/1000)), kk_context())"
  js inline "Date.now()"

// WALL time, not process CPU. `clock()` sums across threads (see
// [[timing-clock-is-cpu-not-wall]] in project memory), which understates
// parallel work's real cost and made the parallel path look slower than it
// is. Use this for any measurement that spans concurrent work.
pub extern wall-ms(): ndet int
  c inline "kk_integer_from_int((kk_intx_t)(({struct timespec _ts; clock_gettime(CLOCK_MONOTONIC,&_ts); (int64_t)_ts.tv_sec*1000 + _ts.tv_nsec/1000000;})), kk_context())"
  js inline "Date.now()"

pub fun timing-on(): ndet bool
  get-env-value("KOKA_TIMING").is-just

pub fun tlog(msg: string, t0: int): <ndet,console> int
  val now = cpu-ms()
  if timing-on() then println("TIMING " ++ msg.pad-right(16) ++ ": " ++ (now - t0).show ++ "ms")
  now

// Synthesize `pub fun @expr() (main()).println` at the SYNTAX level (upstream
// buildcCompileExpr/completeMain writes the same wrapper as virtual source) so
// the ordinary type checker resolves `println`'s `?show` implicit chain; for a
// function-typed result upstream prints "<function>" without calling main
// a point range one line past the program's last definition (see make-expr-def)
pub fun prog-end-rng(prog: syntax/syntax/program<user-type, user-kind>): range
  val endLine = prog.defs.flatmap(fn(dg) match dg
      syntax/syntax/DefNonRec(d) -> [d.def/range.end.line]
      syntax/syntax/DefRec(ds) -> ds.map(fn(d) d.def/range.end.line)
    ).foldl(1, max)
  val p = Pos(prog.source, -1, endLine + 1, 1)
  Range(p, p, False)

pub fun make-expr-def(isFun: bool, modName: name, mainName: string, endRng: range): syntax/syntax/def<user-type>
  val rng = range/null
  // reference the entry fully qualified: an imported module may export one
  // with the same name too (upstream callExpr uses the qualified exprName)
  val mainVar = Var(qualify(modName, mainName.new-name), False, rng)
  val body = if isFun
    then App(Var("println".new-name, False, rng), [(Nothing, syntax/syntax/Literal(LitString("<function>", rng)))], rng)
    else App(Var("println".new-name, False, rng), [(Nothing, App(mainVar, [], rng))], rng)
  val lam = syntax/syntax/Lam([], body, True, rng)
  // the DEF range must sit at the END of the program (not range/null): binding
  // groups order top-level groups by source line, and a line-0 group is an
  // impassable barrier in `insert` (`n < line-of(x)` never holds) -- the
  // effect-generated @tag/@handle groups could no longer bubble past @expr in
  // the wrapper pass and ended up AFTER main (algeff/exn3 with -e under the
  // name-ordered scc input). Diagnostics keep the null binder ranges.
  // PRIVATE. Upstream puts this synthesized def in its own `<entry>/@main`
  // module, where nothing imports it; this port appends it to the ENTRY module
  // instead, so `Public` exported it in the entry's own `.kki` -- `pub fun
  // @expr : () -> <console> ()` plus its inline body, in the public interface of
  // a module a user may well import. Upstream's entry interface has no trace of
  // it. Private restores that: the C entry glue references `@expr` from within
  // this same module, and the REPL's `:type` reads it out of the gamma of the
  // module being checked (build-context.kk `capture`), neither of which needs
  // it exported.
  syntax/syntax/Def(ValueBinder(nameExpr, (), lam, rng, rng), endRng, Private, DefFun([]), InlineAuto, "")

// `--showkindsigs` prints each top-level type's kind and then, if any, its
// synonyms' full definitions; `--showtypesigs`/`--showhiddentypesigs` print
// each top-level definition's `name: type`.
//
// The caller prints this AFTER a program's entry module has been built and
// run, so the program's own output comes first.
//
// The gamma comes from the POST-optimize core, which is what the module
// finally compiled to, and therefore includes optimize-generated hidden
// definitions (`@lift-...`) that --showhiddentypesigs must list. It is
// extracted here rather than reusing the type checker's: `extract-gamma` also
// covers the typedefs' constructors.
pub fun show-module-info(fl: flags, modName: name, mods: bmodules, core: core): _ ()
  if !(fl.showKindSigs || fl.show-type-sigs) then () else
    val importsMap = import-map-from-modules(Cons(modName, mods.keys))
    with nice-env
    with type/pretty/default-doc-env
    with with-pp-env-from-flags(fl)
    with type/pretty/default-indent
    with handler
      val ranked = rankedDefault
      val moduleContext = modName
      val importsMap = importsMap
    with val type/pretty/pp-prec = type/pretty/precTopTop
    if fl.showKindSigs then
      val ownKGamma = core.core/extract-typedefs
      emit-line(" ")
      emit-line(pp-kgamma(ownKGamma, modName).show)
      val ownSynonyms = core.core/extract-synonyms
      if !ownSynonyms.list.is-nil then
        emit-line(" ")
        emit-line(pp-synonyms(ownSynonyms).show)
    if fl.show-type-sigs then
      // NOTE: deliberately NOT `gamma0` (type-check.kk's local var of
      // that name) -- that's the PRE-inference resolution environment
      // (upstream gammaUnions[defsGamma,...,extractGammaImports]),
      // returned as-is BEFORE infer-types runs, so it never even
      // contains this module's own freshly-inferred definitions. Also
      // deliberately NOT the existing `ownCoreGamma` local (built just
      // above, for a different purpose -- open-resolve name lookups
      // during optimize -- from only `core1.defs`, which omits
      // constructors): `extract-gamma` also covers the typedefs'
      // constructors, which the signature listing must include.
      // Extracted from the POST-optimize core, so --showhiddentypesigs lists
      // optimize-generated hidden defs like specialize/fun-lift's
      // `@lift-...` (the cgen/specialize suite inspects these).
      val ownGamma = extract-gamma(data/is-value, True, core)
      emit-line(" ")
      emit-line((if fl.showHiddenTypeSigs then pp-gamma-hidden(ownGamma) else pp-gamma(ownGamma)).show)

// The source of a program's entry module, `<root>/@main`:
//
//     @open import prog
//     pub fun @expr() : _ ()
//       (prog/main()).println
//
// Keeping the entry in a module of its own leaves the program's own `.c` and
// `.kki` free of entry glue, and names the executable after this module
// (`prog__main`). `@open import` brings the program's PRIVATE definitions into
// scope as well, so an entry function need not be public.
//
// A non-unit result is printed; a function-typed one prints `<function>`
// rather than being called.
pub fun entry-module-source(rootName: name, mainName: string, resTp: maybe<ktype>): _ (name, string)
  val call = rootName.show-plain ++ "/" ++ mainName ++ "()"
  val shown = match resTp
    Nothing -> call
    Just(tp) -> if tp.is-type-unit then call
                elif (match tp.expand-syn { TFun -> True; _ -> False }) then "println(\"<function>\")"
                else "(" ++ call ++ ").println"
  val lines = ["@open import " ++ rootName.show-plain,
               "pub fun @expr() : _ ()",
               "  " ++ shown]
  ((rootName.show-plain ++ "/@main").new-module-name, lines.unlines ++ "\n")

// Complete the entry for execution: install `@default-<eff>` handlers (e.g.
// `@default-exn`) around it, so a raised effect runs under the top-level
// handler instead of crashing on missing evidence. The entry is `@expr` when
// present, else the entry function itself. Returns the synthesized `@main`
// definition wrapping it.
//
// Label selection:
//   * the row is walked SHALLOW, so an effect ALIAS stays a `TSyn` and its own
//     name is tried first. `@default-<eff>` is often declared only for the
//     alias -- `pub alias async = <async-await,async-ioc,async-cancel,
//     discontinue>` has `@default-async` and no per-label default -- so
//     expanding the alias up front loses the handler and leaves `main` running
//     with fewer evidence entries than its type promises (a constant-folded
//     `@evv-index` then reads past the end of the evidence vector).
//     Only when the alias has no default is it expanded and its labels retried.
//   * unhandled (non-evidence) labels are skipped; a HANDLED label with no
//     default handler is an error, not something to skip silently.
//   * `async` is always installed as the OUTERMOST handler.
pub fun add-default-handlers(core1: core, modName: name, gamma: gamma, mainName: string): _ (core, maybe<(name, bool)>)
  val mbEntry = match core1.defs.flatten.find(fn(d) d.def-name.unqualify.show-plain == "@expr")
    Just(d) -> Just(d)
    Nothing -> core1.defs.flatten.find(fn(d) d.def-name.unqualify.show-plain == mainName)
  match mbEntry
    Nothing -> (core1, Nothing)
    Just(mainDef) ->
      val mainEntry = Just((mainDef.def-name, False))
      match mainDef.ktype.split-fun-scheme
        Nothing -> (core1, mainEntry)
        Just((_, _, eff, resTp)) ->
          val mainVar = Var(TName(mainDef.def-name, mainDef.ktype), InfoArity(0, 0))
          // std/core/* effects have their default
          // in std/core, all others in the same module as the effect; the name
          // must resolve to exactly one function
          fun lookup-default-handler(ename: name): _ maybe<(name, compiler/type/assumption/name-info)>
            val dname = make-hidden-name("default", if ename.is-system-core-name then nameSystemCore.qualify(ename.unqualify) else ename)
            match gamma.gamma-lookup(dname)
              [(qname, info as InfoFun)] -> Just((qname, info))
              _ -> Nothing
          // `@default-<eff>(fn() body)`. Upstream wraps at the SOURCE level and
          // re-typechecks, so the handler scheme is instantiated by inference;
          // here we build core directly and instantiate by KIND: effect vars ->
          // total, star vars -> the entry's result type. (A blanket
          // `[typeTotal]` previously set e.g. `@default-utc : forall<a> ...`'s
          // RESULT type to `total`, generating C returning the total struct.)
          fun wrap(qname: name, info: compiler/type/assumption/name-info, b: compiler/core/core/expr): _ compiler/core/core/expr
            val (hvars, _) = info.typ.split-type-scheme
            val targs = hvars.map(fn(v) if v.kind == kindEffect then typeTotal else resTp)
            val h = info.core-expr(qname)
            App(if targs.is-nil then h else TypeApp(h, targs), [Lam([], eff, b)])
          fun add-defaults(ls: list<ktype>, b: compiler/core/core/expr): _ compiler/core/core/expr
            match ls
              Nil -> b
              Cons(l, ls') ->
                // Left = keep walking that list; Right = install this handler
                val step: either<list<ktype>, (name, name, compiler/type/assumption/name-info)> = match l
                  // an alias: try its own name before expanding it
                  TSyn(syn, _, _) ->
                    match lookup-default-handler(syn.name)
                      Just((qname, info)) -> Right((syn.name, qname, info))
                      Nothing -> Left(l.extract-ordered-effect.fst ++ ls')
                  _ | !l.is-handled-effect -> Left(ls')
                  _ ->
                    match l.get-operation-effectx([nameTpNamed])
                      Just((_, ename)) ->
                        match lookup-default-handler(ename)
                          Just((qname, info)) -> Right((ename, qname, info))
                          Nothing -> msg/add-error(error-message-kind(
                            "there are unhandled effects for the main expression".text |-|
                            " inferred effect :".text |+| eff.ktp/pretty |-|
                            " unhandled effect:".text |+| l.ktp/pretty |-|
                            " hint            : wrap the main function in a handler".text,
                            range/null, ErrBuild))
                      Nothing -> Left(ls')
                match step
                  Left(rest) -> add-defaults(rest, b)
                  // async is always the most outer handler
                  Right((effName, qname, info)) ->
                    if effName == nameTpAsync
                      then wrap(qname, info, add-defaults(ls', b))
                      else add-defaults(ls', wrap(qname, info, b))
          val body0 = App(mainVar, [])
          val body = add-defaults(eff.shallow-extract-effect-extend.fst, body0)
          match body
            // no default handler applied: the entry stays the entry
            App(Var(tn), []) | tn.get-name == mainDef.def-name -> (core1, mainEntry)
            _ ->
              val atName = qualify(modName, "@main".new-name)
              val atDef = Def(atName, TFun([], typeTotal, typeUnit), Lam([], typeTotal, body),
                              Private, DefFun([]), InlineNever, range/null, "")
              (core1(defs = core1.defs ++ [DefNonRec(atDef)]), Just((atName, False)))

// Build outputs (interfaces, generated C/JS, objects, executables) go under
// the build cache directory, NOT next to the sources: littering the source
// tree with .kki/.c/.mjs made every git operation a minefield. Respects
// --builddir and --buildtag like the reference compiler.
pub fun build-out-dir(fl: flags): _ path
  val tag = if fl.buildTag == "" then "" else "-" ++ fl.buildTag
  // the interface CONTENT depends on the optimization level (specialization
  // and inlining differ), so each build type gets its own cache -- an -O0
  // interface reused by an -O2 build would be wrong code, silently. Mirrors
  // the reference compiler's clang-debug / clang-drelease naming.
  val d = fl.buildDir.path / ("v" ++ comp-flags.version ++ tag) / fl.build-variant
  ensure-dir(d)
  d

// a minimal stand-in until real .kki import loading exists for a program with
// NO imports at all (not even std/core): seed bool/@optional so the core
// passes and codegen have something to resolve (upstream loads these from
// std/core's .kki; every file in the real test suite imports std/core
// transitively, so this path is for standalone smoke tests only)
pub fun builtin-extend(g: gamma): _ gamma
  fun bool-con(n: name, tag: int): (name, compiler/type/assumption/name-info)
    val vrepr = ValueRepr(0, 0, 0)
    val crepr = ConEnum(nameTpBool, DataEnum, vrepr, tag)
    val cinfo = ConInfo(n, nameTpBool, [], [], [], TFun([], typeTotal, typeBool), Inductive, range/null, [], [], False, [], vrepr, Nothing, tag, Public, "")
    (n, InfoCon(Public, typeBool, crepr, cinfo, range/null, ""))
  val (tname, tinfo) = bool-con(nameTrue, 1)
  val (fname, finfo) = bool-con(nameFalse, 0)
  val (conOptional, conNone) = optional-con-infos()
  val vrepr = ValueRepr(0, 0, 0)
  val optInfo = InfoCon(Public, conOptional.typeScheme, ConNormal(nameTpOptional, DataNormal(True), vrepr, CtxNone, 1), conOptional, range/null, "")
  val noneInfo = InfoCon(Public, conNone.typeScheme, ConSingleton(nameTpOptional, DataNormal(True), vrepr, 2), conNone, range/null, "")
  g.extend(tname, tinfo).extend(fname, finfo)
    .extend(nameOptional, optInfo).extend(nameOptionalNone, noneInfo)

// the two constructors of the builtin `@optional` type
pub fun optional-con-infos(): (con-info, con-info)
  val a = TypeVar(1000000, kindStar, Bound)
  val vrepr = ValueRepr(0, 0, 0)
  val optTp = TApp(typeOptional, [TVar(a)])
  val conOptional = ConInfo(nameOptional, nameTpOptional, [a], [], [("value".new-name, TVar(a))],
    TForAll([a], TFun([("value".new-name, TVar(a))], typeTotal, optTp)), Inductive, range/null,
    [range/null], [Public], False, [("value".new-name, TVar(a))], vrepr, Nothing, 1, Public, "")
  val conNone = ConInfo(nameOptionalNone, nameTpOptional, [a], [], [],
    TForAll([a], optTp), Inductive, range/null, [], [], False, [], vrepr, Nothing, 2, Public, "")
  (conOptional, conNone)

pub fun builtin-newtypes(nt: newtypes): _ newtypes
  val (conOptional, conNone) = optional-con-infos()
  val a = TypeVar(1000000, kindStar, Bound)
  val di = DataInfo(Inductive, nameTpOptional, kind-fun(kindStar, kindStar), [a], [conOptional, conNone],
    range/null, DataDefNormal, DataNoEffect, False, Public, "")
  nt.extend(nameTpOptional, di)

// The path-derived name of a source file, as upstream `moduleFromSource`: the
// file's real path relative to the longest include root containing it (the
// current directory is always one), or its bare name when it is under none or
// a path segment is not a valid module identifier. An in-memory overlay is
// named by its path as given, as upstream looks the VFS up before `realPath`.
pub fun module-path-name(fl: flags, srcPath: path, isEntry: bool): _ string
  val stem = srcPath.stemname
  if !isEntry then stem
  else
    val s = match vfs-find(srcPath)
      Just -> srcPath.string
      Nothing -> srcPath.string.realpath.string
    val fromInclude = fl.includePath.filter-map fn(inc)
      match s.starts-with(inc ++ "/")
        Just(rest) -> Just((inc.count, rest.string))
        Nothing -> Nothing
    match fromInclude.foldl(Nothing) fn(best, (n, rel)) match best { Just((m, _)) | m >= n -> best; _ -> Just((n, rel)) }
      Just((_, rel)) ->
        val relStem = if rel.ends-with(".kk").bool then rel.list.take(rel.count - 3).string else rel
        if relStem.split("/").all(is-valid-module-id) then relStem else stem
      Nothing -> stem

// upstream `moduleFromSource`'s `isValidId`
fun is-valid-module-id(s: string): bool
  match s.list
    Cons(c, cs) -> (c.is-lower || c == '@') && cs.all(fn(x) x.is-alpha-num || x == '_' || x == '-' || x == '@')
    Nil -> False

// The module name a source file will be given, WITHOUT compiling it: a lenient
// parse of the header plus the same path-derived naming the real build applies.
// The language server needs this to know what a file's entry should `@open
// import`; going through a full check just to learn the name cost an entire
// extra build pass on every click of the run lens.
pub fun module-name-of(fl: flags, srcPath: path, isEntry: bool = True): _ name
  val prog0 = parse-program-from-string(vfs/read-text-file(srcPath), srcPath, allow-at, fl.semiInsert, fl.tpl)
  name-program(fl, prog0, srcPath, isEntry).name

pub fun name-program(fl: flags, prog0: syntax/syntax/program<user-type, user-kind>, srcPath: path, isEntry: bool): _ syntax/syntax/program<user-type, user-kind>
  val pathName = module-path-name(fl, srcPath, isEntry)
  // no `module` header: its name is the file's, with no range
  if prog0.name.is-nil || prog0.name-range.is-null
    then prog0(name = pathName.new-module-name)
    else
      // declared module name: replace with the path-derived name when the
      // declaration is a (proper or full) suffix of it; otherwise keep the
      // declaration -- upstream errors here, this port is deliberately lenient
      val declared = prog0.name.show-plain
      if declared == pathName || pathName.ends-with("/" ++ declared).bool
        then prog0(name = pathName.new-module-name)
        else prog0

// Compile one module (source file) through type-check -> [two-pass @expr
// wrapper] -> optimize -> code-gen, given its already-resolved dependencies.
// `outBase` is the path stem outputs are written next to (== srcPath, except
// the top-level entry writes next to the originally-requested file name).
// INFERRED, written out (see `compile-once` below on why `pure` cannot be dropped).
pub fun compile-module(fl: flags, srcPath: path, outBase: path, isEntry: bool, mods: bmodules, mbModName: maybe<name> = Nothing,
                       // Hand the type checker's range map AND gamma to the
                       // caller. A language server needs the map for hover and
                       // the gamma to resolve a name to its definition site;
                       // both are discarded otherwise -- so this is a callback
                       // rather than fields on `bmodule`, which every other
                       // consumer would then carry for nothing.
                       // row matches `compile-once`'s, which is where it is called
                       on-range-map: (module-check) -> <io,pure,colors,comp-error,comp-flags,log,emit> () = fn(_mc) (),
                       // Polled BETWEEN phases. Without this a module's own
                       // compile is atomic: for a language server editing one
                       // file whose dependencies are all cached, the entry
                       // compile is the ONLY work there is, and the
                       // orchestrator's between-module checks never run at all.
                       // Type inference dominates that time, so the checks that
                       // matter are the ones around it.
                       cancelled: () -> _ bool = fn() False,
                       // see `code-gen`'s parameter of the same name
                       on-exe: (path) -> _ () = fn(_p) (),
                       // which part of the compile to run; see `compile-stage`.
                       // The type check stage's `mods` may hold `ModTyped`
                       // dependencies, the finish stage's must be compiled.
                       stage: compile-stage = StageAll): _ bmodule
  val resume = match stage
    StageFinish(t) -> Just(t)
    _ -> Nothing
  val prog1 = match resume
    Just(t) -> t.prog
    Nothing ->
      // upstream `phase "parse"` (Build.hs:522). At verbose 1 it shows the module's
      // relative path, at 2 the full one.
      phase("parse", if fl.verbose > 1 then srcPath.string else srcPath.basename)
      val prog0 = parse-program-from-string(vfs/read-text-file(srcPath), srcPath, allow-at, fl.semiInsert, fl.tpl)
      // a module resolved through the import search path is named by its
      // REQUESTED import name (e.g. `import static/modA` found at
      // <include>/static/modA.kk is `static/modA`): a module name is always
      // the include-root-relative path
      match mbModName
        Just(nm) -> prog0(name = nm)
        Nothing -> name-program(fl, prog0, srcPath, isEntry)
  // The defs visible during TYPE CHECK come from the
  // pub-import closure only (declared imports + their public re-exports, in
  // closure order) -- NOT every transitively loaded module; a private import of
  // an imported module must not resolve here, and the closure ORDER determines
  // gamma/kgamma candidate order in error messages (ambiguity hints etc.)
  val tcMods = (pub-import-closure(mods, prog1.imports)
    .flatmap(fn(nm) match mods.lookup(nm) { Just(m) -> [(nm, m)]; Nothing -> [] }))
  val modDefs0 = defs-of(tcMods)
  // bootstrap fallback for a module with literally zero (transitive) imports
  // (named `modDefs`, not `defs` -- that would shadow core.kk's `defs` field
  // accessor, e.g. in `core1.defs` below). `mods` is empty not only for a
  // standalone smoke test but ALSO for std/core/types itself when it is the
  // very first module compiled from source in a fresh build (nothing else is
  // loaded yet) -- but that module defines bool/True/False/@optional itself,
  // so injecting the stand-in there duplicates its own source-level defs
  // (ambiguous `False` candidates). Exclude it explicitly.
  val modDefs = if mods.list.is-empty && prog1.name != nameCoreTypes
    then modDefs0(defs-gamma = modDefs0.defs-gamma.builtin-extend, defs-newtypes = modDefs0.defs-newtypes.builtin-newtypes)
    else modDefs0
  // Parsing .kki INLINE bodies needs the
  // imports of every inline-carrying module too (e.g. std/core's inlines
  // reference std/core/undiv which is NOT publicly re-exported) -- use the
  // gamma over ALL loaded modules for the inline/optimize phase
  val fullDefs = defs-of(mods.list)
  val fullDefsGamma = fullDefs.defs-gamma
  // parc analyzes types INSIDE inlined code from other modules (upstream
  // moduleOptimize: `defsNewtypes (defsFromModules (mod:imports))` over the
  // inline-import closure) -- the type-check newtypes cover only the
  // pub-import closure, so e.g. `std/time/timestamp/timestamp` referenced by
  // std/time's inline bodies was missing (Parc getDataDefInfo failure)
  val fullDefsNewtypes = fullDefs.defs-newtypes
  val coreImports = core-imports-from-modules(prog1.imports, mods)
  val importsMap = import-map-from-modules(Cons(prog1.name, mods.keys))

  // the wrapper pass extends the import list (see below), so the type-check
  // environment (pub-import closure defs + core imports) must be recomputable
  // for the EXTENDED program rather than fixed to prog1's imports
  fun defs-for(progX: syntax/syntax/program<user-type, user-kind>)
    val tcModsX = (pub-import-closure(mods, progX.imports)
      .flatmap(fn(nm) match mods.lookup(nm) { Just(m) -> [(nm, m)]; Nothing -> [] }))
    val modDefsX0 = defs-of(tcModsX)
    if mods.list.is-empty && prog1.name != nameCoreTypes
      then modDefsX0(defs-gamma = modDefsX0.defs-gamma.builtin-extend, defs-newtypes = modDefsX0.defs-newtypes.builtin-newtypes)
      else modDefsX0
  // INFERRED, written out. `pure` is REDUNDANT with `io` (`io = <exn,ioc>`,
  // `pure = <exn,div>`, `ioc = <div,ioc-total>`) -- but it cannot be dropped:
  // annotating this `<io,colors,comp-error,comp-flags>` is REJECTED with
  //   inferred effect: <alloc<global>,colors,comp-error,comp-flags,console,div,div,
  //                     exn,exn,fsys,ndet,net,read<global>,ui,write<global>|_e>
  // i.e. the checker's own solution really does carry `div` and `exn` twice.
  // The duplication enters at `compile/type-check.kk:56`, whose inferred row is
  // `<pure,...,div,...,exn,...>` -- the `pure` alias left unexpanded beside the
  // very labels it expands to.  See docs/async-segfault-root-cause-brief.md.
  fun compile-once(progX: syntax/syntax/program<user-type, user-kind>, emit: bool, modDefsP: definitions = modDefs, coreImportsP: list<core/core/kimport> = coreImports): _ (maybe<ktype>, maybe<bmodule>)
    // a resumed (finish-stage) compile continues the type check stage's
    // counter, so generated names match a compile that ran both in one go
    with common/unique/run-unique(match resume { Just(t) -> t.unique; Nothing -> 0 })
    with with-modname(progX.name)
    with val uctx = kind/unify/Infer(range/null)
    with build-range-map
    val tc0 = cpu-ms()
    // DIAGNOSTIC (KOKA_UNIQ_TRACE=1): the unique counter at phase boundaries.
    // A generated name's id differing by one between two runs of the same build
    // means some earlier phase drew a different number of uniques; this says which.
    fun uniq-trace(label: string): _ ()
      if get-env-value("KOKA_UNIQ_TRACE").is-just then
        println("UNIQ " ++ label ++ " " ++ progX.name.show-plain ++ " = " ++ get-unique().show)
    // Before type inference -- the expensive phase. A cancelled compile returns
    // "nothing produced" rather than raising: every caller already handles that
    // (it is what a `-l` library check with no entry returns), so cancellation
    // needs no new failure path.
    // Checked HERE, not inside the `match` below: a `return` inside a match
    // bound by `val` is miscompiled by the reference compiler (the match is
    // lifted into a function and the `return` exits that instead).
    if resume.is-nothing && cancelled() then return (Nothing, Nothing)
    val (core1, gamma0, nt, kg, rmap) = match resume
      Just(t) -> (t.tcore, t.gamma0, t.newtypes, t.kgamma, t.rmap)
      Nothing ->
        phase("check", progX.name.show-plain)
        uniq-trace("before-typecheck")
        val (c1, g0, nt0, kg0) = type-check(fl, modDefsP, coreImportsP, progX)
        uniq-trace("after-typecheck")
        phase-verbose(3, "check done", progX.name.show-plain)
        // sorted ONCE, here, right after type checking: every consumer --
        // hover, definition, inlay hints, colorize -- relies on the sorted
        // order and must not re-sort
        val rm = get-range-map().rm/sort
        // `type-check` returns the IMPORTS gamma; the module's own definitions are
        // only in its core. Definition lookup needs both, and `core-def-info`
        // carries each def's `nameRange`, which is exactly the range to jump to.
        val ownGamma = gamma/new(c1.defs.flatten.map(fn(d) core-def-info(d, 0)))
        // The PARSED program goes out with the range map: document symbols and
        // folding are pure syntax tree walks (upstream reads it back with
        // `lookupProgram`), and `bmodule` retains only core, so this callback is
        // the one point where the tree is still in hand.
        on-range-map(ModuleCheck(progX.name, rm, type/assumption/union(g0, ownGamma), progX, nt0,
                                 modDefsP.defs-synonyms, kg0))
        (c1, g0, nt0, kg0, rm)
    val tc1 = tlog("  typecheck", tc0)
    // End of the TYPE CHECK stage. A language server's
    // analysis stops here too: `on-range-map` above
    // has handed over everything diagnostics, hover and definition need.
    val stop-typed = match stage
      StageTypecheck -> True
      _ -> fl.typeCheckOnly && isEntry
    if stop-typed then
      return (Nothing, Just(ModTyped(core1, extract-gamma(data/is-value, False, core1),
                                     Typed-module(progX, core1, gamma0, nt, kg, rmap, get-unique()))))
    // `-l`/`--library`: compile only -- no entry point is created, linked, or
    // run (upstream: `mainEntries = if library flags then [] else ...`).
    // NOTE: `isEntry` still controls module NAMING and the show-info prints;
    // only the entry-point machinery is suppressed.
    // ONLY the synthesized entry module carries the entry point: the `@expr`
    // wrapper, the default effect handlers and the link. A program is a plain
    // module; `build-entry-module` (build-context.kk) builds its `<root>/@main`.
    val at-main = progX.name.show-plain.ends-with("@main").bool
    val wantEntry = at-main && !fl.library
    // `--main-entry=<name>` selects the entry function
    val mainName = if fl.mainEntryName == "" then "main" else fl.mainEntryName
    val mbMainRes = match core1.defs.flatten.find(fn(d) d.def-name.unqualify.show-plain == mainName)
      Just(d) -> match d.ktype.split-fun-scheme
        Just((_, _, _, resTp)) -> Just(resTp)
        Nothing -> Nothing
      Nothing -> Nothing
    val needsWrapper0 =
      if !wantEntry then False
      else match mbMainRes
        Just(resTp) -> !resTp.is-type-unit
        Nothing -> False
    if emit || !needsWrapper0 then
      // imported modules' inline bodies parse against the FULL loaded-module
      // gamma (they may reference modules outside the pub closure); gamma0
      // is a subset of it and unioning would duplicate entries, breaking
      // single-match constructor lookups
      // inline sections are resolved once, when each module is loaded, against
      // that module's OWN closure -- see build.kk force-inlines
      val inls = inlines-of(mods)
      // core passes (e.g. open-resolve) look up the module's own generated
      // names (effect `@tag`s, handler cons) by their fully-qualified name;
      // make them visible to THIS module's own optimize pass regardless of
      // Private/Public (upstream Build.hs moduleOptimize: `defsFromModules
      // (mod:imports)` includes the module being optimized in its own gamma)
      val ownCoreGamma = gamma/new(core1.defs.flatten.map(fn(d) core-def-info(d, 0))).gamma/private-as-public
      // optimize sees the FULL gamma (upstream moduleOptimize's defs come from
      // the inline-import closure, a superset of the type-check closure);
      // NOTE: fullDefsGamma replaces (not unions) gamma0 here -- gamma0 is its
      // subset plus the module's own defs, which ownCoreGamma re-adds
      // newtypes: the module's own (from type check, first -- wins conflicts)
      // over ALL loaded modules' types (for types referenced only by inlined
      // imported code)
      val ntFull = unions([nt, fullDefsNewtypes])
      val topt0 = cpu-ms()
      // after type inference, before optimize+codegen: the diagnostics a
      // language server wants already exist by here, so a superseded request
      // should not pay for the rest
      if cancelled() then return (Nothing, Nothing)
      phase-verbose(2, "optimize", progX.name.show-plain)
      uniq-trace("before-optimize")
      val (coreOpt, inlineDefs) = core-optimize(fl, ntFull, type/assumption/union(fullDefsGamma, ownCoreGamma), inls, core1)
      uniq-trace("after-optimize")
      phase-verbose(3, "optimize done", progX.name.show-plain)
      val topt1 = tlog("  optimize", topt0)
      // install the top-level default effect handlers around the entry
      val (coreForGen, mbMain) = if wantEntry then add-default-handlers(coreOpt, progX.name, gamma0, mainName) else (coreOpt, Nothing)
      // KOKA_SHOW_CORE=1: dump the full core (with definition bodies) for debugging
      // `.kkc`, not `.kki`: this is the debug core dump. The INTERFACE is
      // `.kki` and is written by code-gen.kk.
      if get-env-value("KOKA_SHOW_CORE").is-just then
        with nice-env
        with default-doc-env
        with val pp-env = PrettyEnv(coreIface=False, coreShowDef=True)
        with val pp-prec = precTopTop
        with val indent = 0
        with handler
          val ranked = rankedDefault
          val moduleContext = progX.name
          val importsMap = importsMap
        write-text-file(outBase.change-ext("kkc"), pretty-core(fl.target, inlineDefs, coreForGen).show)
      // The imported modules in BUILD ORDER
      // (dependencies first), each compiled against its own and its direct
      // imports' `extern import` libraries. `build-order` walks canonical
      // import names, so a module aliased under a second key appears once.
      val ordered = build-order(mods, coreForGen.imports.map(fn(i) i.importName))
      val cImports = ordered.filter-map fn((_, m))
        m.bmod/cfile.map(fn(cf) C-unit(cf, c-unit-eimports(mods, m.bmod/core, fl.build-type)))
      // ntFull, not nt: parc runs in the C backend and "analyzes types inside
      // abstract types" (upstream CodeGen comment) from INLINED imported code
      val tcg0 = cpu-ms()
      // Documentation output, upstream `CodeGen.hs:101`. Written before the
      // backend runs, so a code-generation failure still leaves the HTML
      // behind. `--html` implies `genRangeMap` (options.kk:833), which is what
      // the LINKED version will need; this is the plain highlighted source.
      if fl.outHtml > 0 then
        phase-verbose(3, "trace", "write html source")
        // the range map is what turns identifiers into links and adds the type
        // popups; `--html` forces `genRangeMap` on precisely for this
        val html = with-pretty-env fn()
          colorize(srcPath, 1, vfs/read-text-file(srcPath),
                   rmap = Just(rmap),
                   env = Html-env(progX.name, fl.htmlBases),
                   full-html = fl.outHtml > 1,
                   css = fl.htmlCss.undelim-paths, js = fl.htmlJs)
        write-text-file-atomic((outBase.string ++ "-source.html").path, html)
        // The API documentation, generated from the
        // CORE program rather than the source, so it lists exactly what the
        // module exports and with resolved types.
        phase-verbose(3, "trace", "write html documentation")
        // The environments the links resolve against. Upstream passes
        // `defsKGamma defs` / `defsGamma defs` over `mod:imports` -- ONE set
        // covering this module and everything it imports.
        //
        // `kg` (kind inference's result) is already exactly that: it holds the
        // module's OWN types as well as its imports. Unioning the core's
        // typedefs on top duplicates every local type, and a duplicated entry
        // makes the qname lookup AMBIGUOUS -- which silently degrades to an
        // unlinked name, so every type defined in this module lost its popup
        // while imported ones kept theirs.
        val docKGamma = kg
        val docGamma = type/assumption/union(fullDefsGamma,
                                             extract-gamma(data/is-value, True, coreForGen))
        val xmp = with-pretty-env fn()
          gen-doc(coreForGen, docKGamma, docGamma, env = Html-env(progX.name, fl.htmlBases),
                  // upstream writes each line with `writeLn`, so the document
                  // ends with a newline after `</html>`; Koka's `unlines` does not
                  css = fl.htmlCss.undelim-paths, js = fl.htmlJs).unlines ++ "\n"
        write-text-file-atomic((outBase.string ++ ".xmp.html").path, xmp)
      // upstream `codeGenLinkC`'s `libs` (every `library` of the closure) and
      // `syslibs` (the imported modules' `syslib`s), from the cores already in
      // memory rather than re-read from their interfaces
      // (upstream order: the entry and its DIRECT imports first -- `codeGen`'s
      // own `clibs` over `bcore : importcores` -- then every imported module in
      // build order)
      val directCores = Cons(coreForGen, coreForGen.imports.filter-map(fn(i) mods.lookup(i.importName).map(fn(m) m.bmod/core)))
      val clibs = nub-decls((directCores ++ ordered.map(fn((_, m)) m.bmod/core)).flatmap(fn(c) clibs-of-core(c, fl.build-type)))
      val csyslibs = ordered.flatmap(fn((_, m)) csyslibs-of-core(m.bmod/core, fl.build-type))
      code-gen(fl, ntFull, modDefs.borrowed, mbMain, outBase, importsMap, inlineDefs, progX.name, coreForGen,
               cImports, c-unit-eimports(mods, coreForGen, fl.build-type), clibs, csyslibs, on-exe)
      val _tcg = tlog("  codegen", tcg0)
      // record the generated C file (same path code-gen writes, see cBase
      // there) so a later entry link can compile this module in
      val mbCFile = match fl.target
        C -> Just((outBase.dirname.path / (progX.name.module-name-to-path).path).change-ext("c"))
        _ -> Nothing
      inline-fp("compiled", progX.name, inlineDefs)
      (mbMainRes, Just(ModCompiled(coreForGen, inlineDefs, extract-gamma(data/is-value, False, coreForGen), mbCFile,
                                   at = file/file-mtime(outBase.change-ext("kki")))))
    else
      (mbMainRes, Nothing)

  // pass 1: type-check (and emit when the result needs no show-wrapper); a
  // non-unit `main` result gets the `@expr` show-wrapper
  // compiled and emitted by pass 2
  val (mbRes, mbMod0) = compile-once(prog1, False)
  val needsWrapper =
    if !isEntry || fl.library || !prog1.name.show-plain.ends-with("@main").bool then False
    else match mbRes
      Just(resTp) -> !resTp.is-type-unit
      Nothing -> False
  val finalMod =
    if needsWrapper then
      val isFun = match mbRes.unjust.expand-syn
        TFun -> True
        _ -> False
      // upstream's generated main module also imports the USER imports of the
      // entry module's imports (Build.hs:474 "with @open import <mod>, also
      // import its imports (for `println` for example)") -- the wrapper's
      // `?show` implicit must see e.g. std/num/float64 when the entry only
      // imports a module that imports it privately (test cgen/tail2)
      val extraImps = prog1.imports.flatmap fn(imp)
        match mods.lookup(imp.fullName)
          Just(m) -> m.core.imports
            .filter(fn(ci) ci.provenance.is-importUser && !ci.provenance.is-importCompiler &&
                           !prog1.imports.any(fn(pi) pi.fullName == ci.importName))
            .map(fn(ci) syntax/syntax/Kimport(ci.importName, ci.importName, range/null, range/null, range/null, Private, False))
          Nothing -> []
      val extraImps1 = extraImps.foldl([]) fn(acc: list<syntax/syntax/kimport>, x)
        if acc.any(fn(a) a.fullName == x.fullName) then acc else acc ++ [x]
      val prog2 = prog1(imports = prog1.imports ++ extraImps1,
                        defs = prog1.defs ++ [syntax/syntax/DefNonRec(make-expr-def(isFun, prog1.name, if fl.mainEntryName == "" then "main" else fl.mainEntryName, prog-end-rng(prog1)))])
      val (_, mbMod2) = compile-once(prog2, True, defs-for(prog2), core-imports-from-modules(prog2.imports, mods))
      mbMod2.unjust
    else mbMod0.unjust
  // mirror a sibling library's output under its ascii-encoded module name too
  // (e.g. `mpat-lib` -> `mpat_dash_lib`): the importer's generated JS import
  // path always uses the ascii-encoded name, so both must exist on disk.
  val typed-only = match finalMod
    ModTyped -> True
    _ -> False
  if !isEntry && !typed-only then
    val enc = prog1.name.module-name-to-path
    if enc != prog1.name.show-plain then
      val encBase = outBase.dirname.path / (enc ++ ".dummy").path
      write-text-file(encBase.change-ext("kki"), file/read-text-file(outBase.change-ext("kki")))
      match fl.target
        JS -> write-text-file(encBase.change-ext("mjs"), file/read-text-file(outBase.change-ext("mjs")))
        _ -> ()
  finalMod