// Build-context entry points: upstream Compile/BuildContext.hs.
//
// Upstream threads an explicit `BuildContext` record through `buildcTypeCheck`
// / `buildcBuild` / `buildcBuildEx`; this port keeps the equivalent state in
// the ambient `bmodules` map that `check-file-ex` builds and hands on, so the
// `buildc*` accessors have no counterpart here. What does correspond is the
// entry surface: resolve the roots, run the (parallel) build, then walk the
// remainder sequentially.
module compiler/compile/build-context

import std/os/path
import std/os/file
import std/os/env
import std/core/undiv
import std/async
import std/async/thread
import compiler/compile/phase
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/error
import compiler/common/color-scheme
import compiler/common/unique
import compiler/common/nice
import compiler/common/parse
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/assumption
import compiler/kind/pretty
import compiler/kind/synonyms
import compiler/kind/import-map
import compiler/kind/newtypes
import compiler/kind/unify
import compiler/syntax/range-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/assumption
import compiler/type/pretty
import compiler/syntax/syntax
import compiler/syntax/parse
import compiler/core/core
import compiler/core/pretty
import compiler/compile/module
import compiler/compile/options
import compiler/compile/type-check
import compiler/compile/optimize
import compiler/compile/code-gen
import compiler/compile/link
import std/os/dir
import compiler/common/file
import compiler/static/binding-groups
import compiler/lib/pprint
import std/data/rb-map
import compiler/common/name-collections
import compiler/compile/rpc
import compiler/lib/log
import compiler/compile/build
import compiler/compile/vfs
import compiler/compile/orchestrate


// Type-check and compile `fname` (and its sibling-source imports) to `i` +
// the target backend output, next to `fname`.
pub fun check-file(fl: flags, fname: string, on-progress: (int, int, name) -> _ () = fn(_c, _t, _n) ()): _ ()
  check-file-ex(fl, [fname], True, on-progress)
  ()

// What compiling ONE root produced. Diagnostics come back as DATA rather than
// being printed, so a caller driving the compiler as a library (the test
// runner) can attribute every message to the test that produced it -- inside a
// SHARED build. Upstream can only attribute output by running one test per
// process.
pub struct root-result
  // the source this result is FOR. Callers must match on this, never on
  // position: results are emitted as roots finish, and an unparseable root is
  // reported before any compiled one, so ordering does not track the input.
  rsrc     : path
  rname    : name
  routcome : either<string, bmodule>
  messages : list<string>          // this root's errors, in emission order
  warns    : list<string>          // ... and its warnings
  emitted  : list<string>          // `--showtypesigs`/`--showcore` output
  exe      : maybe<path>           // the executable it linked, if any

// Build SEVERAL roots in one graph. Every root's dependency closure is
// discovered and built ONCE (upstream `buildcBuildEx`'s `[ModuleName]` roots +
// `[Name]` main entries), then each root compiles as its own entry -- so each
// gets its own `main` and its own executable.
//
// This is what a test runner wants: N test files sharing one std-library build
// instead of N cold builds, which is the difference the sweep currently pays
// (a cold `lib/time7` costs ~25s serially, ~8.6s warm).
//
// `on-exe` fires once per root that links one; the roots are compiled in the
// order given, so a caller can pair them up positionally.
pub fun build-roots(fl: flags, fnames: list<string>, sess: session = Session(),
                    on-progress: (int, int, name) -> <io,async,comp-error,parse-error,vfs-lookup,log,emit> () = fn(_c, _t, _n) (),
                    cancelled: () -> <io,async,comp-error,parse-error,vfs-lookup,log,emit> bool = fn() False,
                    on-exe: (path) -> <io,pure,colors,comp-error,comp-flags,log,emit> () = fn(_p) ())
      : <io,pure,async,colors,comp-error,comp-flags,parse-error,vfs-lookup,log,emit> session
  check-file-ex(fl, fnames, True, on-progress, sess, cancelled, fn(_mc) (), on-exe)

// `build-roots`, but each root's entry compile is ISOLATED: its diagnostics are
// captured as data instead of printed, and a failing root does not abort the
// others. Reuses `isolate-diagnostics`, the same handler stack the parallel
// worker path installs -- so a root compiled here and a module compiled on a
// worker turn diagnostics into data by exactly the same route.
pub fun build-roots-isolated(fl: flags, fnames: list<string>, sess: session = Session(),
                    on-progress: (int, int, name) -> <io,async,comp-error,parse-error,vfs-lookup,log,emit> () = fn(_c, _t, _n) (),
                    cancelled: () -> <io,async,comp-error,parse-error,vfs-lookup,log,emit> bool = fn() False)
      : <io,pure,async,colors,comp-error,comp-flags,parse-error,vfs-lookup,log,emit> (session, list<root-result>)
  // a heap `ref` rather than a `var` for the same reason as inside the fold:
  // the sink is called from a row that has no `local<h>`
  val results : ref<global,list<root-result>> = ref([])
  val sess' = check-file-ex(fl, fnames, True, on-progress, sess, cancelled, fn(_mc) (),
                            fn(_p) (), Just(fn(r) results := (!results) ++ [r]))
  (sess', !results)

// A build session: the resolved module map and dependency scan from a previous
// check of the SAME graph. Re-checking one edited file otherwise spends all its
// time rebuilding state that did not change -- measured on a 2-line file with a
// warm cache: 348ms rescanning dependencies and 1126ms reloading interfaces, to
// type-check the edit itself in 5ms. Handing the previous result back collapses
// both. Entries are revalidated by timestamp (`session-revalidate`) so an
// interface that changed underneath us is dropped rather than trusted.
pub struct session
  mods: bmodules = rb-map/empty()
  deps: dep-cache = rb-map/empty()
  // The module names this context was built FOR. A
  // context can hold many (a language server tracks every open document; a
  // test runner one per test file), and each may carry its own `main`.
  roots: list<name> = []

// Drop any cached module whose interface on disk is newer than the copy we
// loaded -- i.e. something outside this session rebuilt it (a git checkout, a
// concurrent `koka -c`).
//
// NOT cheap: `file-mtime` shells out per query, so this is one subprocess per
// cached module. Call it when an external change is plausible (opening a
// document), not on every keystroke -- a keystroke changes the buffer, which
// the overlay already reflects, and nothing on disk moved.
pub fun session-revalidate(s: session, fl: flags): _ session
  val odir = build-out-dir(fl)
  val kept = s.mods.list.filter fn((nm, m))
    val kki = odir / (nm.module-name-to-path ++ ".kki").path
    val t = file/file-mtime(kki)
    t <= 0 || t <= m.bmod/at
  s(mods = rb-map/empty().add-all(kept))

// Drop the cached module(s) whose SOURCE is `p`, so the next check reloads them
// from the overlay. This is what a buffer edit needs: the file on disk has not
// moved, so a timestamp sweep would keep the stale copy, and dropping the whole
// session would throw away every unrelated module for nothing.
pub fun session-invalidate(s: session, p: path): _ session
  s.paths/session-invalidate([p])

// Invalidate SEVERAL sources at once. One pass over the caches instead of one
// per path: a test runner re-running a changed batch, or an editor applying a
// multi-file refactor, invalidates a set, and folding `session-invalidate` over
// it would rescan `deps` once per member.
pub fun paths/session-invalidate(s: session, ps: list<path>): _ session
  val names = s.deps.list.filter-map fn((nm, (src, _, _, _)))
    if ps.any(fn(p) src.string == p.string) then Just(nm) else Nothing
  if names.is-nil then s
  else s(mods = rb-map/empty().add-all(s.mods.list.filter(fn((k, _)) !names.any(fn(n) n == k))))

// upstream `buildcClearRoots` / `buildcRemoveRootModule`
pub fun session-clear-roots(s: session): session
  s(roots = [])

pub fun session-remove-root(s: session, nm: name): _ session
  s(roots = s.roots.filter(fn(r) !(r == nm)))

pub fun check-file-session(fl: flags, fname: string, s: session,
                           on-progress: (int, int, name) -> _ () = fn(_c, _t, _n) (),
                           cancelled: () -> _ bool = fn() False,
                           on-range-map: (module-check) -> _ () = fn(_mc) (),
                           on-exe: (path) -> _ () = fn(_p) ()): _ session
  check-file-ex(fl, [fname], True, on-progress, s, cancelled, on-range-map, on-exe)

// What compiling an expression produced.
pub struct expr-result
  sess: session
  // the expression's own type, once it type-checked
  typ: maybe<ktype>
  // the linked executable, when this was a full compile rather than a check
  exe: maybe<path>

// Compile an EXPRESSION, upstream `buildcCompileExpr` (BuildContext.hs:339).
//
// The expression cannot be compiled on its own, so a synthetic module is
// written into the VFS next to one of the roots:
//
//     @open import <root>          -- everything the root can see, privates too
//     pub fun @expr()
//       <expr>
//
// and compiled like any other file. `@open import` is what makes the REPL able
// to call a module's private definitions.
//
// Two passes when actually running it: type-check first to
// learn the expression's type, then decide from that type whether to wrap the
// result in `println` before building for real. `compile-module`'s
// `add-default-handlers` already looks for `@expr` before the ordinary entry
// name, so the effect handlers a `main` would get are applied here too.
//
// This is the primitive the REPL's `Eval`/`:type`/`:kind` need, and the one
// upstream's `koka/compileFunction` is built on -- `buildcCompileEntry` is just
// `buildcCompileExpr` with the expression `"<name>()"`.
pub fun compile-expr(fl: flags, sess: session, expr: string, roots: list<name>,
                     rel-dir: string,
                     type-check-only: bool = False, add-show: bool = True,
                     on-progress: (int, int, name) -> _ () = fn(_c, _t, _n) ())
      // INFERRED, not written out: spelling `io` and `pure` together puts `exn`
      // and `div` in the row TWICE (see `check-file-ex`'s note), which then fails
      // to unify at the language-server call site.
      : _ expr-result
  val src = virtual-path(rel-dir ++ "/@main.kk")
  // `@open import` also exposes the module's PRIVATE definitions, which is what
  // lets a REPL expression call them.
  val imports = roots.map(fn(nm) "@open import " ++ nm.show-plain)
  val tpref : ref<global,maybe<ktype>> = ref(Nothing)
  val modref : ref<global,name> = ref(name/nil)
  fun capture(ModuleCheck(nm, _rm, g, _pr, _nt, _sy): module-check)
    modref.set(nm)
    match g.gamma-lookup(qualify(nm, "@expr".new-name))
      Cons((_, ninfo), _) -> tpref.set(Just(ninfo.scheme))
      Nil -> ()

  fun check(content: string, fl': flags, on-exe: (path) -> _ ()): _ session
    with with-vfs([(src, Vfile(content, epoch-nanos()))])
    check-file-session(fl', src.string, sess, on-progress = on-progress,
                       on-range-map = capture, on-exe = on-exe)
  // Pass 1 exists to learn the expression's TYPE, which is needed to decide
  // whether to wrap the result in `println` -- and to answer `:type` at all.
  // An entry point (`add-show = False`) needs neither, so it goes straight to
  // the build: running both passes there doubled the cost of the run lens.
  val want-type = type-check-only || add-show
  val sess1 = if !want-type then sess
              else
                val body1 = imports ++ ["pub fun @expr()", "  " ++ expr]
                check(body1.unlines, fl(library = True, evaluate = False), fn(_p) ())
  match (if want-type then !tpref else Just(typeUnit))
    Nothing -> Expr-result(sess1, Nothing, Nothing)
    Just(tp) ->
      // `@expr` is a nullary function wrapping the expression; the type the user
      // asked about is its RESULT.
      val user-tp = match tp.split-fun-scheme
        Just((_, _, _, r)) -> r
        Nothing -> tp
      if type-check-only then Expr-result(sess1, Just(user-tp), Nothing)
      else
        // pass 2: wrap the result for display and build an entry point
        val res-tp = match tp.split-fun-scheme
          Just((_, _, _, r)) -> r
          Nothing -> tp
        val shown = if !add-show || res-tp.is-unit-tp then expr
                    elif res-tp.is-fun-tp then "println(\"<function>\")"
                    else "(" ++ expr ++ ").println"
        val body2 = imports ++ ["pub fun @expr() : _ ()", "  " ++ shown]
        val exe : ref<global,maybe<path>> = ref(Nothing)
        // `evaluate = False`: the CALLER runs the executable (upstream hands back
        // an IO action and the REPL invokes it). Leaving the interpreter's
        // `evaluate = True` in place made `code-gen` run it too, printing every
        // result twice.
        val sess2 = check(body2.unlines, fl(library = False, evaluate = False), fn(p) exe.set(Just(p)))
        Expr-result(sess2, Just(user-tp), !exe)

// Build a program's entry module, `<root>/@main` (see `entry-module-source`),
// and run it under `-e`. A library, a type check, and the entry module itself
// build nothing; nor does a module that does not define the entry function.
fun build-entry-module(fl: flags, mods: bmodules, odir: path, rootName: name, bm: bmodule, isEntry: bool,
                       cancelled: () -> _ bool, on-exe: (path) -> _ ()): _ bmodules
  val mainName = if fl.mainEntryName == "" then "main" else fl.mainEntryName
  val resTp = match bm
    ModCompiled(c) -> match c.defs.flatten.find(fn(d) d.def-name.unqualify.show-plain == mainName)
      Just(d) -> match d.ktype.split-fun-scheme
        Just((_, _, _, r)) -> Just(r)
        Nothing -> Nothing
      Nothing -> Nothing
    _ -> Nothing
  if !isEntry || fl.library || fl.typeCheckOnly || resTp.is-nothing then mods
  else
    val (atName, content) = entry-module-source(rootName, mainName, resTp)
    val atSrc = virtual-path(atName.show-plain ++ ".kk")
    with with-vfs([(atSrc, Vfile(content, epoch-nanos()))])
    // `@open import` sees the program's PRIVATE definitions -- an entry
    // function is rarely `pub` -- so the program is handed to this one compile
    // with its private bindings promoted. No other module gets that view.
    val openMods = match bm
      ModCompiled(c, inls, _g, cf, at) ->
        mods.set(rootName, ModCompiled(c, inls, extract-gamma(data/is-value, True, c), cf, at))
      _ -> mods
    val atMod = compile-module(fl, atSrc, odir / atName.module-name-to-path.path, True, openMods,
                               Just(atName), fn(_mc) (), cancelled, on-exe)
    mods.set(atName, atMod)

fun is-unit-tp(tp: ktype): div bool
  match tp.expand-syn
    TCon(TypeCon(nm)) -> nm == nameTpUnit
    _ -> False

fun is-fun-tp(tp: ktype): div bool
  match tp.expand-syn
    TFun -> True
    _ -> False

// `isEntry` is False for imported sibling modules compiled as libraries: their
// output must not run `main` at import time nor get the `@expr` show-wrapper
// (the reference build attaches the entry only to the target module)
// Compile ONE module with every handler installed INSIDE, returning
// diagnostics as DATA rather than printing them.
//
// This is what makes a module compile offloadable to a worker thread
// (Stage 3 increment 2b). `std/async/thread`'s `compute` restricts its closure
// to `ioc` -- primitives only, no `exn` and no user-handled effects -- because
// a worker performing a handled operation would look up evidence belonging to
// the spawning thread's context and crash in `kk_evv_at` (see
// scripts/... task-evv repro). `compile-files` installs `parse-error`,
// `add-errors`, `add-warnings` and `add-infos` around the WHOLE build, so a
// module compile performs operations whose handlers live on the main thread.
// Installing them per-module here removes that coupling.
//
// Returning messages instead of printing them also gives deterministic

// INFERRED, written out.
fun check-file-ex(fl: flags, fnames: list<string>, isEntry: bool,
                  // reports (completed, total, module) as the build proceeds; see
                  // `compile-graph-rpc`'s own parameter for why this is safe here
                  on-progress: (int, int, name) -> <io,async,comp-error,parse-error,vfs-lookup,log,emit> () = fn(_c, _t, _n) (),
                  // a previous check of the same graph to reuse; empty for a
                  // one-shot batch compile
                  sess: session = Session(),
                  // cooperative cancellation, checked between build phases and
                  // by the orchestrator between dispatches
                  cancelled: () -> <io,async,comp-error,parse-error,vfs-lookup,log,emit> bool = fn() False,
                  // the entry's range map and gamma, for hover/definition
                  on-range-map: (module-check) -> <io,pure,colors,comp-error,comp-flags,log,emit> () = fn(_mc) (),
                  // see `code-gen`'s parameter of the same name; only the ENTRY
                  // module links an executable, so only its compile passes this on
                  on-exe: (path) -> <io,pure,colors,comp-error,comp-flags,log,emit> () = fn(_p) (),
                  // when present, each root's entry compile runs ISOLATED and its
                  // result is handed here instead of its diagnostics being printed
                  on-root: maybe<(root-result) -> <io,pure,async,colors,comp-error,comp-flags,parse-error,vfs-lookup,log,emit> ()> = Nothing)
      : <io,pure,async,colors,comp-error,comp-flags,parse-error,vfs-lookup,log,emit> session
  val tstart = cpu-ms()
  val twall0 = wall-ms()
  if timing-on() then println("SESSION in: " ++ sess.mods.list.length.show ++ " modules, deps " ++ sess.deps.list.length.show)
  val odir = build-out-dir(fl)
  // Every root's own directory is a source root: sibling imports resolve
  // relative to the importing file, so a batch spanning directories needs all
  // of them (a single root reduces to exactly the previous behaviour).
  val rootPaths = fnames.map(path)
  fun add-dir(acc: list<path>, d: path): _ list<path>
    if acc.any(fn(x) x.string == d.string) then acc else acc ++ [d]
  val maindirs = rootPaths.map(fn(p) p.dirname.path).foldl([], add-dir)
  val sdirs = Cons(odir, maindirs)
  val srcdirs = Module-dirs(maindirs ++ fl.includePath.map(path), fl.includePath.map(path))
  // scan each root's direct imports so the dependency closure can be resolved
  // (siblings preferred over the search path, recursing transitively)
  // A root's PARSE is isolated too, not just its compile. Parse errors are
  // raised as exceptions carrying an already-formatted message, and roots are
  // parsed here on the main strand -- so without this ONE malformed root aborts
  // the whole build, taking every other root with it. That is fatal for
  // batching: a suite deliberately contains malformed inputs (`syntax/wrong/*`,
  // `type/wrong/*`), and a group of 50 tests must not be lost because one of
  // them is meant not to parse.
  val parsed = rootPaths.map fn(srcPath)
    phase("parse", srcPath.string)
    match try({ val p0 = parse-program-from-string(vfs/read-text-file(srcPath), srcPath, allow-at, fl.semiInsert, fl.tpl)
                (srcPath, p0, name-program(fl, p0, srcPath, isEntry)) })
      Ok(t)      -> Right(t)
      Error(exn) -> Left((srcPath, exn.message))
  val roots = parsed.filter-map fn(e)
    match e
      Right(t) -> Just(t)
      Left(_)  -> Nothing
  // report the unparseable ones through the same sink the compiled roots use,
  // so a caller sees one result per root either way. With NO sink (the CLI
  // path) there is nowhere to report them, so re-raise the first one: the
  // point of catching here is only to stop one bad root taking a BATCH down,
  // never to make a single-root compile of a malformed file succeed silently.
  match on-root
    Nothing ->
      match parsed.filter-map(fn(e) match e { Left((_, msg)) -> Just(msg); Right(_) -> Nothing })
        Cons(msg, _) -> throw(msg)
        Nil          -> ()
    Just(sink) ->
      parsed.foreach fn(e)
        match e
          Right(_) -> ()
          Left((srcPath, msg)) ->
            sink(Root-result(srcPath, srcPath.stemname.new-name, Left(msg), [msg], [], [], Nothing))
  val tparse = tlog("parse", tstart)
  // INFERRED, written out (inference gave `<io,pure,...>`; `pure` is redundant with
  // `io` -- `io = <exn,ioc>`, `pure = <exn,div>`, `ioc = <div,ioc-total>` -- and writing
  // both puts `exn` and `div` in the row TWICE, which is what makes `open` ask for a
  // second `exn` handler via `@evv-index-mask`).
  // INFERRED, written out. THIS is the closure that ends up mis-opened: it is
  // passed as `compile-graph-rpc`'s `compile-src`, whose effect is the bare row
  // variable `e` (see that signature), and is then invoked by `resolve-module`
  // with only `<io,comp-error,parse-error|e>` evidence in scope -- no `colors`,
  // no `comp-flags`, and one `exn` where this row wants two.
  fun compile-source(src: path, nm: name, mods: bmodules): <io,pure,colors,comp-error,comp-flags,vfs-lookup,log,emit> bmodule
    compile-module(fl, src, odir / nm.module-name-to-path.path, False, mods, Just(nm))
  // Stage 3, increment 1: discover the source import graph up front, each
  // wave's files parsed in PARALLEL (std/os/task). The entry was parsed
  // above, so shared lazy state is already warmed on the main thread (see
  // scripts/partask-probe.kk rule 3). The sequential walk below then reuses
  // these scans instead of re-parsing every source for its imports.
  // ONE discovery over the union of every root's imports, so a shared
  // dependency (std, or a helper both tests import) is scanned once.
  // Canonical names, as every other module's imports are: a relative import
  // left as written would be a second name for the same module.
  val allImports = roots.flatmap fn((srcPath, p0, p1))
    p1.imports.map(fn(i) (i.fullName, i.nameRange)).canonicalize-deps(srcPath, p0.name, srcdirs).map(fst)
  val dcache0 = discover-deps(allImports, srcdirs, fl.tpl, odir, sess.deps)
  val tdiscover = tlog("discover", tparse)
  // Decide what this round compiles (see `walk-rebuild`). The walk records each
  // decision here, dependencies first, so `stale-set` is already a valid
  // compile order.
  var decisions : name-map<rebuild-decision> := rb-map/empty()
  var stale-rev : list<name> := []
  with handler
    fun decided(nm) decisions.lookup(nm)
    fun decide(nm, d)
      decisions := decisions.set(nm, d)
      if d.is-stale then stale-rev := Cons(nm, stale-rev)
  walk-rebuild(allImports, dcache0, odir, sdirs, srcdirs, fl.target.is-c, fl.tpl)
  val stale-set = stale-rev.reverse
  val plan = decisions
  // a Stale module is compiled with the imports its source declares
  val dcache = plan.list.foldl(dcache0) fn(acc, (nm, d))
    match d
      Stale(src, declared, deps) -> acc.set(nm, (src, declared, deps, False))
      Fresh -> acc
  val twalk = tlog("walk", tdiscover)
  // `compile-graph-rpc`, the dynamic per-module-readiness orchestrator, is the
  // only scheduler. On `compiler/compile/build.kk`, cold, wall-clock,
  // hash-verified, it beat both alternatives it replaced:
  //   sequential   81.25s (0.94x)
  //   wave barrier 72.24s (1.15x)
  //   RPC          37.50s (2.26x)
  // The static wave-barrier path and the KOKA_NO_PARALLEL sequential bypass are
  // gone: neither was ever faster, and keeping three schedulers agreeing on
  // artifacts was pure maintenance cost. The walk below still runs -- it
  // resolves interface-only modules and is seeded by the orchestrator's map --
  // but it is a resolve pass, not a fallback scheduler.
  // Reuse what this process already has in memory. An entry survives only if
  //   - its source is not stale (`stale-set` already decided that), and
  //   - the `.kki` on disk is no NEWER than the interface we hold, so nothing
  //     outside this process has rebuilt it behind our back.
  // A missing `.kki` (mtime 0) is not a reason to drop it: a module compiled
  // earlier in this session is valid whether or not it was written out.
  fun still-valid((nm, m): (name, bmodule)): _ bool
    if stale-set.any(fn(s) s == nm) then False
    else
      val kki-t = file/file-mtime(odir / (nm.module-name-to-path ++ ".kki").path)
      kki-t <= 0 || kki-t <= m.bmod/at
  val preloaded0 = rb-map/empty().add-all(sess.mods.list.filter(still-valid))
  if timing-on() then println("PRELOAD reused: " ++ preloaded0.list.length.show ++ " of " ++ sess.mods.list.length.show)
  // Load every FRESH interface concurrently before the build proper. The
  // orchestrator below only schedules stale modules, so on a warm rebuild it has
  // nothing to do and the walk would otherwise load all of these one at a time
  // on this strand -- the whole of a warm build's cost. Upstream's resolve phase
  // is concurrent by construction; see `preload-ifaces` (build.kk).
  val wall-before-preload = wall-ms()
  val preloaded1 = preload-ifaces(fl, odir, srcdirs, dcache, stale-set, preloaded0)
  val tpreload = tlog("preload-ifaces", twalk)
  // WALL as well as CPU: `tlog` reports CPU, which sums across the pre-load's
  // worker threads, so it cannot show how well this phase actually overlaps.
  if timing-on() then println("WALL preload: " ++ (wall-ms() - wall-before-preload).show ++ "ms")
  // Inline sections are needed only before something is OPTIMIZED: a stale
  // module's compile, or the root's unless this is a type-check-only analysis.
  val wall-before-inlines = wall-ms()
  val preloaded = if fl.typeCheckOnly && stale-set.is-nil then preloaded1
                  else resolve-pending-inlines(preloaded1)
  if timing-on() then println("WALL inlines: " ++ (wall-ms() - wall-before-inlines).show ++ "ms")
  phase-verbose(2, "scan", dcache.list.length.show ++ " modules in the import graph")
  phase-verbose(3, "build order", stale-set.map(show-plain).join(" "))
  phase("build", roots.map(fn((_, _, p1)) p1.name.show-plain).join(" ") ++
                 " (" ++ stale-set.length.show ++ " of " ++ dcache.list.length.show ++ " modules to compile)")
  val wall-before-waves = wall-ms()
  val (graph-mods, outcomes) = compile-graph-rpc(fl, odir, sdirs, srcdirs, dcache, stale-set, compile-source, on-progress, cancelled, preloaded,
                                                 decisions = Just(plan))
  if timing-on() then println("WALL waves: " ++ (wall-ms() - wall-before-waves).show ++ "ms")
  // flush diagnostics in BUILD order, not completion order
  outcomes.foreach fn((_, o)) o.messages.foreach(println)
  // `--showtypesigs` / `--showcore` output. It goes AFTER the program's own
  // output, not before: `compileShowInfo` runs after `code-gen`, and `code-gen`
  // is what runs the program under `-e`. `algeff/cps1.kk.out` pins this down --
  // `[1,3]` from the program, then the signature listing.
  outcomes.foreach fn((_, o)) o.emitted.foreach(println)
  // Warnings wait. Upstream prints them at the very END of a compile, after
  // errors AND after the program's own output -- and under `-e` the program
  // runs inside the ENTRY module's code-gen, below. Printing them here put
  // every module's warnings ahead of everything the program printed.
  val deferredWarnings = outcomes.flatmap(fn((_, o)) o.warn-messages)
  // REPORT worker failures instead of absorbing them. Previously a failed
  // compile became a `Left` that was counted as "handled" and the walk below
  // silently redid the work, so a parallel path that failed on EVERY module
  // still exited 0.
  outcomes.foreach fn((nm, o))
    match o.outcome
      Left(msg) -> log-phase(0, "error", "parallel compile of " ++ nm.show-plain ++ " failed: " ++ msg)
      Right(_)  -> ()
  val tpar = tlog("parallel-compile", tpreload)
  // SEED THE WALK WITH THE ORCHESTRATOR'S MAP. Discarding it made the walk
  // re-load every interface the orchestrator had already loaded -- the ORCH
  // trace showed all 31 `.kki` files plus 11 `.kki` read a second time, which
  // is the entire `load-modules` phase (2.5s on schedule.kk, 64s on build.kk).
  // `resolve-module` short-circuits on `mods0.contains-key(nm)`, so seeding
  // simply skips that repeat work.
  //
  // An earlier attempt at this failed with `Type std/core/#types/int is not
  // defined` because the map held only SOURCE modules -- the same root cause as
  // the 152 kind errors. The orchestrator resolves interface-only modules into
  // its map too, so the precondition that was missing then holds.
  // seed with the session's already-resolved modules as well as this run's
  val seeded = sess.mods.list.foldl(graph-mods) fn(acc, (k, v)) if acc.contains-key(k) then acc else acc.set(k, v)
  // Each root: canonicalize its own direct imports (upstream `resolveDep`-style,
  // see `canonicalize-deps` in build.kk), resolve them, then compile the root
  // itself as an ENTRY so it gets its own `main` and its own executable.
  //
  // `mods` threads through the fold, so a module resolved for one root is
  // already present for the next -- N roots share one dependency graph and one
  // orchestrated build, and only their own entry compiles are per-root.
  //
  // NOTE: roots are deliberately NOT nodes in the orchestrator's graph. Putting
  // them there schedules each the moment its own deps land (better in
  // principle -- no waiting on unrelated modules) but three things broke, see
  // `next.md`: a root that legitimately FAILS is reported a second time by the
  // orchestrator's own "parallel compile of X failed" line, which no `wrong/*`
  // fixture has; plus unexplained timeouts and a 2x slowdown. Revisit with the
  // runner switch, where the caller captures program output too.
  val wall-before-entry = wall-ms()
  val modsFinal = roots.foldl(seeded) fn(acc0, (srcPath, prog0, prog1))
    val entryDeps0 = prog1.imports.map(fn(imp) (imp.fullName, imp.nameRange))
    // `prog0.name`, not `prog1.name`: the fallback dir comes from the file's
    // OWN declared header name (see `relative-fallback-dir`'s doc comment).
    val entryDeps = entryDeps0.canonicalize-deps(srcPath, prog0.name, srcdirs)
    fun resolve-deps(start: bmodules)
      entryDeps0.zip(entryDeps).foldl(start) fn(acc, dr)
        val ((asWritten, _), (nm, rng)) = dr
        val acc1 = resolve-module(acc, nm, odir, fl.target.is-c, sdirs, srcdirs, compile-source, dcache, [prog1.name], rng,
                                  Just(relative-fallback-dir(srcPath, prog0.name)), fl.tpl, Just(plan))
        if asWritten == nm then acc1
        else match acc1.lookup(nm)
          Just(bm) -> acc1.set(asWritten, bm)
          Nothing -> acc1
    val outBase = odir / prog1.name.module-name-to-path.path
    match on-root
      Nothing ->
        val mods = resolve-deps(acc0)
        if cancelled() then mods
        else
          trace-env("root", prog1.name, mods)
          // DIAGNOSTIC (KOKA_ENTRY_FP=1): a fingerprint of the environment the
          // ENTRY compile is actually handed, in map order. If this matches across
          // runs while the produced artifact does not, the nondeterminism is
          // INSIDE compile-module rather than in what loading produced.
          if get-env-value("KOKA_ENTRY_FP").is-just then
            val parts = mods.list.map fn((k, m))
              k.show-plain ++ ":" ++ m.bmod/core.coreName.show-plain ++ ":"
                ++ (match m { ModIface(_, i) -> i.length; ModCompiled(_, i) -> i.length; ModTyped -> 0 }).show
            val fp = parts.join("|").list.foldl(7, fn(h, c) (h * 31 + c.int) % 1000000007)
            println("ENTRY-FP " ++ mods.list.length.show ++ " modules fp=" ++ fp.show)
          val bm = compile-module(fl, srcPath, outBase, isEntry, mods, Nothing, on-range-map, cancelled, on-exe)
          // a type-check-only entry has no interface or C file; keeping it in the
          // session would let a later FULL build reuse it as if compiled
          val mods1 = if fl.typeCheckOnly then mods else mods.set(prog1.name, bm)
          val modsE = build-entry-module(fl, mods1, odir, prog1.name, bm, isEntry, cancelled, on-exe)
          // the signature listing comes last, after the program has run
          match bm
            ModCompiled(c) -> if isEntry then show-module-info(fl, prog1.name, mods1, c)
            _ -> ()
          modsE
      Just(sink) ->
        if cancelled() then acc0
        else
          val rexe : ref<global,maybe<path>> = ref(Nothing)
          // Resolve this root's imports INSIDE the isolation, not outside it.
          // `resolve-module` reports an unresolvable import with `add-error`
          // (build.kk `errorNotFound`) -- an EFFECT, not an exception. Raised
          // outside the isolation it walks straight past this root to whatever
          // handler the CALLER installed, and for a batch that is a `final ctl`
          // which discards EVERY root's result. One test importing a module that
          // does not exist took its entire flag group down with it.
          //
          // The modules resolved along the way are stashed in a `ref` so they
          // survive that abort: a `final ctl` discards the continuation, so a
          // value merely RETURNED from the action would be lost. Whatever was
          // resolved before the failure is still valid and worth keeping for the
          // next root.
          val rmods : ref<global,bmodules> = ref(acc0)
          // `isolate-diagnostics` turns DIAGNOSTICS into data but still lets an
          // exception escape (see `compile-module-isolated`, which wraps it for
          // exactly this reason). Escaping here would abort the fold and leave
          // every remaining root in the group with no result at all, so contain
          // it and report it as this root's own failure.
          fun compile-root()
            isolate-diagnostics(fl, []) fn()
              val mods = resolve-deps(acc0)
              rmods := mods
              val bm = compile-module(fl, srcPath, outBase, isEntry, mods, Nothing,
                                      fn(_mc) (), fn() False, fn(p) rexe := Just(p))
              val mods1 = if fl.typeCheckOnly then mods else mods.set(prog1.name, bm)
              rmods := build-entry-module(fl, mods1, odir, prog1.name, bm, isEntry,
                                          fn() False, fn(p) rexe := Just(p))
              match bm
                ModCompiled(c) -> if isEntry then show-module-info(fl, prog1.name, mods1, c)
                _ -> ()
              bm
          val o = match try(compile-root)
            Ok(o0)     -> o0
            Error(exn) -> Mod-outcome(Left(exn.message), [])
          sink(Root-result(srcPath, prog1.name, o.outcome, o.messages, o.warn-messages, o.emitted, !rexe))
          match o.outcome
            Right(bm) -> (!rmods).set(prog1.name, bm)
            Left(_)   -> !rmods
  val tload = tlog("load-modules", tpar)
  // the entry (and, under `-e`, the program itself) has now run
  deferredWarnings.foreach(println)
  val tend = tlog("compile", tload)
  if timing-on() then println("WALL entry-compile: " ++ (wall-ms() - wall-before-entry).show ++ "ms")
  // Compile the closure's C to objects. `code-gen` -> `c-link` already does
  // this for an ENTRY build (batched, see `compile-objs`), and `c-compile-objects`
  // returns immediately when nothing is stale -- so for an entry this is a stat
  // loop. It exists for the LIBRARY case, which never links and so never
  // compiled its C at all; upstream compiles every module's C regardless of
  // whether it links (`CodeGen.hs:318`).
  //
  // An earlier attempt put an UNCONDITIONAL second batch pass here that did not
  // skip what `c-link` had already built; it spawned a redundant xargs tree per
  // build and pushed already-slow tests (algeff/cps*, effs*) over the sweep
  // timeout -- 16 new TIMEOUTs. The staleness filter in `compile-objs` is what
  // makes this version safe.
  val wall-before-objs = wall-ms()
  if fl.target.is-c && fl.kklibIncludeDir != "" && !fl.typeCheckOnly then
    val closureC = modsFinal.list.flatmap fn((_, m))
      match m.bmod/cfile
        Just(cf) -> [C-unit(cf, c-unit-eimports(modsFinal, m.bmod/core, fl.build-type))]
        Nothing  -> []
    c-compile-objects(fl, closureC, fl.kklibIncludeDir.path)
  if timing-on() then println("WALL c-objects: " ++ (wall-ms() - wall-before-objs).show ++ "ms")
  if timing-on() then println("WALL total-since-parse: " ++ (wall-ms() - twall0).show ++ "ms")
  if timing-on() then { val _ = tlog("TOTAL", tstart); () }
  // hand the resolved state back so the next check of this graph can skip
  // discovery and interface loading entirely
  if timing-on() then println("SESSION out: " ++ modsFinal.list.length.show ++ " modules, deps " ++ dcache.list.length.show)
  // remember what this context was built FOR
  Session(modsFinal, dcache, roots.map(fn((_, _, p1)) p1.name))