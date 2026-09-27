// Parallel module-build orchestration.
//
// PORT-SPECIFIC: upstream has no counterpart file. Upstream Build.hs runs the
// whole build inside one process on green threads and serialises access to a
// shared module map with `moduleGuard`/`modmapPut`/`modmapRead`; this port
// drives per-module compiles through an RPC orchestrator over `std/async`
// worker threads (`compile-graph-rpc`). It is the only scheduler: a static
// wave-barrier variant and a sequential bypass both existed and both lost on
// wall-clock (72.2s and 81.3s against 37.5s on compiler/compile/build.kk), so
// they were removed rather than maintained alongside it.
// The isolation wrappers below (`compile-module-isolated`, `isolate-diagnostics`)
// exist for the same reason: a worker must not let its diagnostics or its
// failures escape into another worker's compile.
//
// Everything here is a deliberate divergence from upstream's concurrency model,
// not a porting gap -- keep upstream-faithful per-module work in build.kk.
module compiler/compile/orchestrate

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

// diagnostics: the caller flushes them in BUILD order regardless of the order
// workers happen to finish.
pub struct mod-outcome
  outcome  : either<string, bmodule>   // Left = fatal message for this module
  messages : list<string>              // formatted ERRORS, in emission order
  // `--showtypesigs` / `--showcore` output: the program's observable RESULT,
  // kept apart from diagnostics because a caller comparing against a fixture
  // needs it verbatim and in order.
  emitted  : list<string> = []
  // Warnings are kept apart from `messages` because they are printed at a
  // different TIME, not merely in a different style: upstream carries them in
  // its `Error` monad (`Err err warnings`) and prints them at the very end of
  // the compile -- after errors, and after the program's own output under
  // `-e`. Flushing them with the errors as each module finishes puts them
  // ahead of everything the program prints.
  warn-messages : list<string> = []
  // Phase reports from inside this module's compile, as (level, phase, message)
  // -- NOT pre-formatted, and deliberately kept apart from `messages`. A worker
  // has no front end: it cannot know the verbosity, and it must not write to
  // the console or the client's connection while other workers are running. The
  // orchestrator replays these through the real `log` handler on its own
  // strand, so they are gated and routed exactly like a main-strand phase call.
  phases   : list<(int, string, string)> = []
  // The executable this module linked, when compiled as a ROOT (an entry).
  // Dependencies never link one. LAST so the positional constructors above
  // stay aligned.
  exe      : maybe<path> = Nothing

// A module compiled in two stages reports ONE outcome: the type check stage's
// diagnostics first, then the finish stage's. Phase reports were already
// replayed as each stage came back.
fun merge-stage-outcomes(tc: mod-outcome, fin: mod-outcome): mod-outcome
  fin(messages = tc.messages ++ fin.messages, emitted = tc.emitted ++ fin.emitted,
      warn-messages = tc.warn-messages ++ fin.warn-messages, phases = [])

pub fun compile-module-isolated(fl: flags, srcPath: path, outBase: path, isEntry: bool,
                            mods: bmodules, mbModName: maybe<name> = Nothing,
                            stage: compile-stage = StageAll): ioc mod-outcome
  // consume `exn` at the OUTERMOST point: `ioc` has no `exn`, and an exception
  // escaping to a worker's caller could not be handled there anyway
  match try({ compile-module-body(fl, srcPath, outBase, isEntry, mods, mbModName, stage = stage) })
    Ok(o)      -> o
    Error(exn) -> Mod-outcome(Left(exn.message), [])

pub fun compile-module-body(fl: flags, srcPath: path, outBase: path, isEntry: bool,
                        mods: bmodules, mbModName: maybe<name> = Nothing,
                        // in-memory sources for THIS worker. Passed as data and
                        // installed locally rather than inherited: a worker must
                        // never reach for evidence established on the spawning
                        // thread (same reason `isolate-diagnostics` installs
                        // `colors`/`comp-flags` itself). Empty for a batch build;
                        // a language server compiling an edited-but-unsaved
                        // import would populate it.
                        overlay: list<(path, vfile)> = [],
                        stage: compile-stage = StageAll): <exn,ioc> mod-outcome
  // A ROOT links an executable; record its path so the caller gets it back in
  // the outcome rather than having to guess where it landed. A heap `ref`, not
  // a `var`: `isolate-diagnostics` fixes its action to the row a worker can
  // run, which has no `local<h>`.
  val rexe : ref<global,maybe<path>> = ref(Nothing)
  val o = isolate-diagnostics(fl, overlay) fn()
    compile-module(fl, srcPath, outBase, isEntry, mods, mbModName, fn(_mc) (), fn() False,
                   fn(p) rexe := Just(p), stage = stage)
  o(exe = !rexe)

// Install the per-module handler stack and run `action`, turning every
// diagnostic into DATA. Shared by the in-process path and the worker path so
// both isolate exactly the same effects.
pub fun isolate-diagnostics(fl: flags, overlay: list<(path, vfile)>, action: () -> _ bmodule): <exn,ioc> mod-outcome
  // `colors` and `comp-flags` are ordinary user-handled effects, installed
  // locally (not inherited from main's handlers) so this closure -- which
  // may run on a spawned worker thread -- never reaches for evidence
  // established on the spawning thread. The source overlay is installed the
  // same way, from data passed in rather than inherited.
  with val colors = ColorScheme()
  with @default-comp-flags
  with no-vfs
  with with-vfs(overlay)
  var msgs : list<string> := []
  var warns : warnings := []
  // same shortening the driver applies (upstream threads `getCwd` into its
  // error printer); a worker formats its own diagnostics, so it needs it too
  val cwd = cwd()
  // Worker-side phase logging: a worker must not write to the console or the
  // client's connection (several run at once), so it collects as data and the
  // orchestrator replays -- see `mod-outcome/phases`.
  var phs : list<(int, string, string)> := []
  with fun log-phase(level, p, msg) phs := phs ++ [(level, p, msg)]
  // `--showcore` and friends are the program's OBSERVABLE OUTPUT, not
  // commentary, so they are captured in emission order alongside diagnostics
  // rather than written to a console this worker must not touch.
  var emits : list<string> := []
  with fun emit-line(s: string) emits := emits ++ [s]
  var wmsgs : list<string> := []
  fun take-warnings()
    warns.foreach fn(e) wmsgs := wmsgs ++ [e.err/show(cwd)]
    warns := []
  with handler
    final ctl parse-error(e: string, r: range)
      msgs := msgs ++ [r.show-range(cwd, False) ++ ": parse error: " ++ e]
      take-warnings()
      Mod-outcome(Left("parse error"), msgs, emits, wmsgs, phs)
  with collapse-div
  with handler
    final ctl add-errors(errs: errors)
      errs.take(fl.maxErrors).foreach fn(e) msgs := msgs ++ [e.err/show(cwd)]
      take-warnings()
      Mod-outcome(Left("type error"), msgs, emits, wmsgs, phs)
    fun add-warnings(ws: warnings)
      warns := warns ++ ws
    fun add-infos(is: warnings)
      warns := warns ++ is
  // every raise is consumed HERE: `ioc` has no `exn`, so an escaping exception
  // could not be caught by a handler on the spawning thread anyway
  val r = try
    val m = action()
    take-warnings()
    Right(m)
  match r
    Ok(res) -> Mod-outcome(res, msgs, emits, wmsgs, phs)
    Error(exn) -> Mod-outcome(Left(exn.message), msgs, emits, wmsgs, phs)

// Run one wave's compiles on worker threads.
//
// This is a SEPARATE function because `compute` fixes each thunk's row to a
// CLOSED `<async,ioc>`, and `interleaved` then unifies the ENCLOSING row with
// it. Inlined into the wave body, that pinned it closed and
// left no room for `resolve-module`'s `comp-error`/`exn`/`parse-error` --
// the async dispatch row and the module-resolution row cannot be one row.
// Confining the closed row to its own signature lets the call site open it,
// which is how the old `compile-waves` was callable from `check-file-ex`.
// One clang run on a C-compile pool worker. A pool worker is a worker like any
// other: it must not write to the console while the front end is running, so
// its phase reports are dropped rather than logged (the batch catch-up in
// `c-compile-objects` echoes the same commands at verbose 3). A failure is
// left for `c-link`, which re-runs any missing `.o` singly to capture its
// diagnostic.
fun cc-compile-one(fl: flags, unit: c-unit): <async,ioc> ()
  with fun log-phase(_level, _p, _msg) ()
  match try({ c-compile-module(fl, unit, fl.kklibIncludeDir.path) })
    _ -> ()

// A worker's request: report the previous module's result (Nothing on the
// very first call), and ask for the next one.
pub struct orch-request
  prev: maybe<(name, mod-outcome)>
  // A request from the C-COMPILE pool rather than a front-end worker (see the
  // pool's own note in `compile-graph-rpc`). `cc-finished` reports that the
  // job handed out by the previous reply is done, so the orchestrator knows
  // when no clang is running any more.
  cc: bool = False
  cc-finished: bool = False

pub type orch-reply
  // `stage`: which part of `nm`'s compile to run (see `compile-stage`)
  Work(nm: name, src: path, env: bmodules, stage: compile-stage)
  // one module's generated C, to compile to its sibling `.o`
  CcWork(unit: c-unit)
  AllDone

// Whether `nm`'s FULL transitive dependency closure is safe to resolve
// without ever falling into a fresh `compile-source` call: `resolve-module`
// (build.kk) recurses through EVERY reachable dependency BEFORE it decides
// whether `nm` ITSELF needs compiling or can just be loaded, so a one-level
// check of `nm`'s own direct deps (the old `find-ready`) missed a
// GRANDCHILD dependency that was still stale and unresolved -- `drain`
// (below) would then call `resolve-module`, its recursion would reach that
// grandchild, and it would compile it INLINE on the orchestrator thread
// from inside the xchannel delivery callback (confirmed via a native
// backtrace: `kk_os_read_text_file` <- `compile_module` <-
// `kk_xchan_async_cb` <- `uv__async_io`, all on one thread -- reentrancy,
// not cross-thread corruption). `visited` breaks cycles (already reported
// by the `import-cycles` check above `todo0`; treat as ready here so a
// cyclic pending item doesn't get re-derived forever).
pub fun transitively-ready(nm: name, dcache: dep-cache, have: bmodules, stale: list<name>, failed: list<name>, source-dirs: module-dirs, visited: list<name>): _ bool
  if have.contains-key(nm) then True
  elif visited.any(fn(v) v == nm) then True
  elif stale.any(fn(s) s == nm) then failed.any(fn(f) f == nm)
  else match dcache.lookup(nm)
    Nothing -> True  // interface-only: resolve-module's `.kki` branch only loads, never compiles
    Just((src, declared, deps0, _)) ->
      val deps = deps0.canonicalize-deps(src, declared, source-dirs)
      val visited1 = Cons(nm, visited)
      deps.all(fn((d, _)) transitively-ready(d, dcache, have, stale, failed, source-dirs, visited1))

// The first pending item whose FULL transitive dependency closure is
// satisfied (not stale, or already compiled), plus the remaining pending
// list with that item removed. O(n) per call; fine at this scale (dozens of
// modules, not thousands).
// `failed`: a dep that already FAILED to compile also counts as "resolved"
// for readiness purposes -- not because its dependent can succeed (it can't:
// `restrict-to-closure`/`resolve-module` will find no compiled module for it
// and report their own "not found"-style error), but because treating a
// failure as permanently un-ready deadlocks the whole build. A pending
// module blocked on a failed dependency must still get its turn, exactly as
// the wave-barrier orchestrator's static schedule always gave every module a
// turn regardless of earlier failures (cascading into secondary errors
// rather than hanging). Caught via a real reproduction, not assumed: with a
// dependency compile failing, the orchestrator sat blocked at ~0% CPU for
// the full timeout instead of finishing (`user` time far below `real` time
// is the signature of a wait, not of slow work).
pub fun find-ready(ps: list<(name, path, name, list<(name, range)>)>, have: bmodules, stale: list<name>, failed: list<name>, dcache: dep-cache, source-dirs: module-dirs)
                : _ (maybe<(name, path, name, list<(name, range)>)>, list<(name, path, name, list<(name, range)>)>)
  match ps
    Nil -> (Nothing, Nil)
    Cons(p, rest) ->
      val (_, src, declared, deps0) = p
      val deps = deps0.canonicalize-deps(src, declared, source-dirs)
      if deps.all(fn((d, _)) transitively-ready(d, dcache, have, stale, failed, source-dirs, []))
        then (Just(p), rest)
        else
          val (r, rest2) = find-ready(rest, have, stale, failed, dcache, source-dirs)
          (r, Cons(p, rest2))

// Dynamic per-module-readiness orchestrator: a worker asks for the next READY
// module the moment it finishes its last one, instead of every worker in a
// wave waiting for the wave's SLOWEST member before the next wave can start.
//
// Measured on `compiler/compile/build.kk`: the wave barrier's own ceiling
// (sum of per-module CPU / critical path, i.e. the best any DAG-respecting
// scheduler with unlimited workers could do) is 1.74x, but ACTUAL wave-barrier
// throughput was only 1.16x wall-clock -- the gap is entirely wave-boundary
// stalls between modules that share no dependency.
//
// This needs genuine SPAWN-THREAD workers, not `compute()`: a worker must be
// able to `xreceive` a reply that may arrive from ANOTHER thread at an
// unpredictable time (whenever the dependency it is waiting on finishes), and
// `compute`'s body has no `async` to do that with -- see compiler/compile/rpc.kk.
//
// The orchestrator DEFERS a request instead of replying "not ready yet": the
// requester's reply-sender is held in `waiting` until work appears. Polling
// would busy-spin every idle worker during a narrow wave (build.kk's own
// tail is four waves of width 1) while the single active compile is still
// running -- wasted cores competing with the module that IS making progress.
pub fun compile-graph-rpc(fl: flags, out-dir: path, search-dirs: list<path>,
                      source-dirs: module-dirs, dcache: dep-cache,
                      // every module compiled this round, dependencies first
                      // (`walk-rebuild`); anything else is loaded from its interface
                      stale-set: list<name>,
                      // INFERRED, written out: `e` here is a bare row variable that
                      // does NOT occur in this function's own effect row below. So any
                      // `compile-src` whatsoever is accepted, and it is then invoked
                      // inside the closed row `<io,async,comp-error,parse-error>`.
                      compile-src: (path, name, bmodules) -> <io,async,comp-error,parse-error,vfs-lookup,log|e> bmodule,
                      // Called as modules finish, with (completed, total). Runs on
                      // the ORCHESTRATOR strand -- the only strand that touches this
                      // state -- so a reporter can render from it without reaching
                      // across threads. The batch driver passes a no-op; the REPL
                      // draws a progress line.
                      on-progress: (int, int, name) -> <io,async,comp-error,parse-error,vfs-lookup,log|e> () = fn(_c, _t, _n) (),
                      // Cooperative cancellation. Checked on the orchestrator
                      // strand each time a worker asks for its next module --
                      // the one place that already owns the schedule, so
                      // stopping there needs no cross-thread state. Modules
                      // already in flight finish (a half-written `.kki` would
                      // poison the cache); nothing new is dispatched, workers
                      // are told `AllDone`, and the build unwinds normally.
                      cancelled: () -> <io,async,comp-error,parse-error,vfs-lookup,log|e> bool = fn() False,
                      // Interfaces already held IN MEMORY from an earlier build in
                      // this process (the language server's session). Starting from
                      // an empty map made `resolve-module` re-read every `.kki`
                      // from disk on a warm rebuild -- 26 interface loads and ~1.1s
                      // for a file whose modules had not changed. The caller is
                      // responsible for only passing entries that are still valid
                      // (see `check-file-ex`).
                      preloaded: bmodules = rb-map/empty(),
                      // Modules that are ROOTS of this build rather than
                      // dependencies: compiled as ENTRIES (their own `main`,
                      // their own executable).
                      //
                      // They are scheduled by the SAME readiness rule as
                      // everything else, which is the point: a root is queued
                      // the moment ITS OWN dependencies land, instead of
                      // waiting behind unrelated modules. Compiling roots in a
                      // phase after the graph would reintroduce exactly the
                      // wave-boundary stall this orchestrator exists to remove.
                      roots: list<name> = [],
                      // `walk-rebuild`'s decisions, for resolving dependencies
                      decisions: maybe<name-map<rebuild-decision>> = Nothing
                     ): <io,async,comp-error,parse-error,vfs-lookup,log|e> (bmodules, list<(name, mod-outcome)>)
  val adj = dcache.list.map(fn((nm, (_, _, ds, _))) (nm, ds.map(fst)))
  val cycle = import-cycles(adj).head.default([])
  if !cycle.is-nil then
    (rb-map/empty(),
     [(cycle.head.default(name/nil),
       Mod-outcome(Left("recursive imports: " ++ cycle.map(show-plain).join(" -> ")), []))])
  else
    val todo0 = stale-set.filter-map fn(nm)
      match dcache.lookup(nm)
        Just((src, declared, deps, _)) -> Just((nm, src, declared, deps))
        Nothing -> Nothing
    // Nothing to compile: hand BACK the interfaces the caller already has
    // (its session's, plus whatever `preload-ifaces` just read concurrently)
    // instead of an empty map. Returning empty made the caller's walk re-load
    // every one of them sequentially, which on a warm build is the entire cost.
    if todo0.is-nil then (preloaded, [])
    else
      val requests = xchannel()
      val done-ch = xchannel()   // detached spawn-threads: await an explicit exit signal each
      // C compilation is dispatched PER MODULE, to a bounded pool of clang
      // workers that request jobs through this same channel. Upstream overlaps
      // the same way (CodeGen.hs returns the C compile and final link "as a
      // separate IO action to increase concurrency"); batched, the front end
      // and clang ran strictly one after the other -- on a cold small build,
      // no clang at all for the first 1.25s, then a burst of 26.
      //
      // Two earlier attempts failed for reasons this design avoids:
      //
      //  1. A shared `xchannel` work queue drained by clang workers: an
      //     xchannel's receive side must run on the loop that CREATED it, so N
      //     workers calling `xreceive` on the orchestrator's channel is a
      //     cross-thread data race. 145 .c in 15m32s against 206 in 4m18s.
      //     Here the clang workers are RPC CLIENTS -- they only `xemit` -- so
      //     the orchestrator strand stays the only receiver.
      //  2. Each front-end worker compiling its own .c after reporting the
      //     module: correct, but all 14 workers then block in clang, saturating
      //     every core and starving the front end (front-end span 258s -> 640s).
      //     Here the pool is separate and capped well below the core count, so
      //     a clang run never consumes a front-end worker.
      //
      // ROOTS wait for the pool to drain (`next-work`). A root LINKS, and
      // `c-link` batch-compiles anything still stale -- if a pool worker were
      // mid-compile on the same file, two clangs would write one `.o`.
      // DIAGNOSTIC: KOKA_MAX_WORKERS caps worker count (e.g. =1 forces every dispatched
      // module through the SAME single worker thread, one at a time) -- keeps the real
      // async/RPC machinery active (unlike KOKA_NO_PARALLEL, which bypasses the orchestrator
      // entirely and hits an unrelated pre-existing gap in the sequential fallback) while
      // testing whether >=2 CONCURRENT workers are required to reproduce a given bug.
      val n-workers = match get-env-value("KOKA_MAX_WORKERS")
        Just(s) -> match s.parse-int
          Just(m) -> max(1, min(m, todo0.length))
          Nothing -> max(1, min(get-cpu-count(), todo0.length))
        Nothing -> max(1, min(get-cpu-count(), todo0.length))
      list(1, n-workers).foreach fn(_)
        spawn-thread fn()
          val client = rpc-client(requests.sender)
          fun work-loop(prev: maybe<(name, mod-outcome)>): <async,ioc> ()
            match call(client, Orch-request(prev))
              Work(nm, src, env, stage) ->
                trace-orch("dispatch  " ++ nm.show-plain ++ " env=" ++ env.list.length.show)
                val t0 = cpu-ms()
                val outcome = compile-module-isolated(fl, src, out-dir / nm.module-name-to-path.path,
                                                      roots.any(fn(r) r == nm), env, Just(nm), stage)
                trace-orch("compiled  " ++ nm.show-plain ++ " " ++ (cpu-ms() - t0).show ++ "ms")
                work-loop(Just((nm, outcome)))
              // AllDone, or (never, it does not ask for one) a C-compile job
              _ -> ()
          work-loop(Nothing)
          client.close
          done-ch.xemit(())
      // HALF the cores by default (`KOKA_CC_WORKERS` overrides, 0 disables).
      // Measured on a cold small build, 5 runs each: batched 4.50s, 4 workers
      // 4.36s, 7-8 workers 4.09s, all 14 no better (4.11s) -- past half the
      // cores the pool only takes cores the front end still needs, and
      // whatever is stale at the end is batched at full width anyway
      // (`c-compile-objects`).
      val cc-enabled = fl.target.is-c && fl.kklibIncludeDir != "" && !fl.typeCheckOnly
      // The pool's width has to key off the build type, because a worker's
      // FOOTPRINT does: clang on the largest generated unit
      // (compiler/syntax/parse, ~21MB of C) peaks at ~1.8GB without debug info
      // and ~9.9GB with it. Half the cores is right at 1.8GB a worker; at
      // 9.9GB it would be 70GB of resident memory, and a build that starves
      // the machine is not a fast build -- one such run took the whole system
      // down. Debug-info builds therefore get 2 workers, and are expected to
      // be slower.
      val cc-wide = max(1, get-cpu-count() / 2)
      val cc-default = match fl.build-type
        DebugFull       -> min(2, cc-wide)
        RelWithDebInfo  -> min(2, cc-wide)
        _               -> cc-wide
      val n-cc = if !cc-enabled then 0
                 else match get-env-value("KOKA_CC_WORKERS")
                   Just(s) -> match s.parse-int
                     Just(m) -> max(0, m)
                     Nothing -> cc-default
                   Nothing -> cc-default
      val cc-done-ch = xchannel()
      // Orchestrator state -- all of it lives on THIS strand only, never
      // touched by a worker directly (workers only ever see it via replies).
      //
      // Modules move through two scheduled STAGES, the way upstream's Build.hs
      // moves them through phases: a module may TYPE CHECK as soon as its
      // dependency closure is type checked (`moduleTypeCheck` waits on
      // `tcheckedMap`), and FINISH -- optimize and generate code -- once its
      // closure is compiled (`moduleCodeGen` waits on `optimizedMap`). Waiting
      // for whole compiles instead serialised every dependency chain end to end.
      // Roots (entries) still compile in one stage: they come last anyway, and
      // their `@expr` wrapper pass re-type-checks.
      var ready-mods : bmodules := preloaded           // interface or COMPILED
      var typed : bmodules := rb-map/empty()          // `ModTyped`: checked, not yet finished
      var pending-tc := todo0.filter(fn((nm, _, _, _)) !roots.any(fn(r) r == nm))
      var pending-roots := todo0.filter(fn((nm, _, _, _)) roots.any(fn(r) r == nm))
      var pending-finish := []                         // type checked, waiting for a compiled closure
      var tc-outcomes : name-map<mod-outcome> := rb-map/empty()
      var in-flight := 0
      var waiting : list<xsender<orch-reply>> := []
      var collected : list<(name, mod-outcome)> := []
      var failed : list<name> := []
      // How many workers have been told `AllDone`. Every spawned worker blocks
      // on a reply until it is released, and the run then waits for each to
      // confirm it exited -- so the serve loop MUST NOT stop before all of them
      // have been released, however the build ended. Stopping early (the
      // condition used to be "nothing pending and nothing waiting", which is
      // trivially true before any worker has registered) leaves the workers
      // blocked on a request nobody will ever receive, and the run then hangs
      // on `done-ch`.
      var released := 0
      // C-compile pool state, on this strand only, like everything else here
      var pending-cc : list<c-unit> := []
      var cc-waiting : list<xsender<orch-reply>> := []
      var cc-in-flight := 0
      var cc-released := 0
      list(1, n-cc).foreach fn(_)
        spawn-thread fn()
          val client = rpc-client(requests.sender)
          fun cc-loop(finished: bool): <async,ioc> ()
            match call(client, Orch-request(Nothing, True, finished))
              CcWork(u) ->
                cc-compile-one(fl, u)
                cc-loop(True)
              _ -> ()
          cc-loop(False)
          client.close
          cc-done-ch.xemit(())

      // what a TYPE CHECK may see: compiled modules plus type-checked ones
      fun check-view(): _ bmodules
        val t0 = typed
        t0.list.foldl(ready-mods) fn(acc, kv)
          val (k, v) = kv
          if acc.contains-key(k) then acc else acc.set(k, v)
      // finish first -- it is what unblocks dependents' own finishes -- then
      // type checks, then roots
      fun next-work(): _ maybe<((name, path, name, list<(name, range)>), compile-stage)>
        val (fin, fin-rest) = find-ready(pending-finish, ready-mods, stale-set, failed, dcache, source-dirs)
        match fin
          Just(it) ->
            pending-finish := fin-rest
            val (nm, _, _, _) = it
            match typed.lookup(nm)
              Just(ModTyped(_, _, t)) -> Just((it, StageFinish(t)))
              _ -> Just((it, StageAll))   // not reachable; a whole compile is still correct
          Nothing ->
            val (tc, tc-rest) = find-ready(pending-tc, check-view(), stale-set, failed, dcache, source-dirs)
            match tc
              Just(it) ->
                pending-tc := tc-rest
                Just((it, StageTypecheck))
              Nothing ->
                // a root LINKS: no clang of ours may be running on a file
                // `c-link`'s batch could pick up as well
                val (rt, rt-rest) = if !pending-cc.is-nil || cc-in-flight > 0 then (Nothing, pending-roots)
                                    else find-ready(pending-roots, ready-mods, stale-set, failed, dcache, source-dirs)
                match rt
                  Just(it) ->
                    pending-roots := rt-rest
                    Just((it, StageAll))
                  Nothing -> Nothing
      fun dispatch(w: xsender<orch-reply>, it: (name, path, name, list<(name, range)>), stage: compile-stage): _ ()
        val (nm, src, declared, deps0) = it
        // canonicalize upstream-`resolveDep`-style before anything
        // downstream treats a name as authoritative -- see
        // `canonicalize-deps`'s doc comment (build.kk)
        val deps = deps0.canonicalize-deps(src, declared, source-dirs)
        val is-check = match stage
          StageTypecheck -> True
          _ -> False
        // Tripwire: re-run the readiness check `next-work` just ran, over the
        // same state, right before the only call that can trigger an inline
        // compile (`resolve-module`, below). Nothing mutates in between, so this
        // cannot fire today; it guards against the two drifting apart.
        val have = if is-check then check-view() else ready-mods
        if !deps.all(fn((d, _)) transitively-ready(d, dcache, have, stale-set, failed, source-dirs, [])) then
          parse-error("compile-graph-rpc: next-work approved " ++ nm.show-plain ++
                      " but its own re-check disagrees -- readiness check is out of sync with resolve-module's recursion", range/null)
        // resolve THIS module's own deps into the map (interface-only ones
        // enter here, exactly as the sequential walk resolves them; idempotent),
        // aliasing the AS-WRITTEN name to the same entry too -- see
        // `resolve-module`'s own aliasing (build.kk). A dep that is only TYPE
        // CHECKED is skipped: it is stale, so `resolve-module` would compile it
        // inline. The type check view serves it from `typed` instead.
        val typed0 = typed
        // Resolve against a map that ALREADY CONTAINS the type-checked modules.
        // Skipping them one dep at a time is not enough: `resolve-module`
        // RECURSES into a dep's own deps, and that recursion has no such guard,
        // so a GRANDCHILD sitting in `typed` (checked, not yet finished) was
        // absent from the map and got compiled from source inline -- work the
        // finish stage then did again. Measured on an incremental build of the
        // compiler: 12 modules compiled twice, the second compile of
        // compiler/lsp/state alone costing 29s, which is most of why an
        // incremental build cost MORE than a cold one.
        val resolve-base = if is-check then check-view() else ready-mods
        val resolved = deps0.zip(deps).foldl(resolve-base) fn(acc, dr)
          val ((asWritten, _), (dep, drng)) = dr
          if !acc.contains-key(dep) && typed0.contains-key(dep) then acc
          else
            val acc1 = resolve-module(acc, dep, out-dir, fl.target.is-c, search-dirs, source-dirs, compile-src, dcache, [], drng,
                                      Just(relative-fallback-dir(src, declared)), fl.tpl, decisions)
            if asWritten == dep then acc1
            else match acc1.lookup(dep)
              Just(bm) -> acc1.set(asWritten, bm)
              Nothing -> acc1
        // A type-checked entry must NOT land in `ready-mods`: that map means
        // FINISHED, and an unfinished module there would be handed out as if it
        // had been compiled. Only genuinely new entries are kept.
        ready-mods := resolved.list.foldl(ready-mods) fn(acc, (k, v))
          if typed0.contains-key(k) then acc else acc.set(k, v)
        val view = if !is-check then resolved
                   else deps0.zip(deps).foldl(resolved) fn(acc, dr)
                     // the as-written aliases of type-checked deps, too
                     val ((asWritten, _), (dep, _)) = dr
                     if asWritten == dep || acc.contains-key(asWritten) then acc
                     else match acc.lookup(dep)
                       Just(bm) -> acc.set(asWritten, bm)
                       Nothing -> acc
        val env = view.restrict-to-closure(deps.map(fst))
        in-flight := in-flight + 1
        w.xemit(Work(nm, src, env, stage))
      fun cc-drain(): _ ()
        match cc-waiting
          Nil -> ()
          Cons(w, ws) ->
            match pending-cc
              Cons(u, us) ->
                pending-cc := us
                cc-waiting := ws
                cc-in-flight := cc-in-flight + 1
                w.xemit(CcWork(u))
                cc-drain()
              Nil ->
                // nothing to compile now, and nothing will arrive any more once
                // every front-end worker has been released
                if released >= n-workers && in-flight == 0 then
                  cc-waiting.foreach(fn(x) x.xemit(AllDone))
                  cc-released := cc-released + cc-waiting.length
                  cc-waiting := []
                ()
      fun drain(): _ ()
        match waiting
          Nil -> ()
          Cons(w, ws) ->
            val pick = if cancelled() then Nothing else next-work()
            match pick
              Just((it, stage)) ->
                waiting := ws
                dispatch(w, it, stage)
                drain()
              Nothing ->
                val nothing-left = pending-tc.is-nil && pending-roots.is-nil && pending-finish.is-nil
                if (nothing-left || cancelled()) && in-flight == 0 then
                  waiting.foreach(fn(x) x.xemit(AllDone))
                  released := released + waiting.length
                  waiting := []
                ()
      fun serve-loop(): _ ()
        // keep serving until every worker has been released, not merely until
        // there is no work left -- see `released`
        if released >= n-workers && cc-released >= n-cc then ()
        else
          val r = requests.xreceive
          if r.arg.cc then
            if r.arg.cc-finished then cc-in-flight := cc-in-flight - 1
            cc-waiting := cc-waiting ++ [r.reply]
            cc-drain()
            // a drained pool can be what releases a waiting ROOT
            drain()
          else
            match r.arg.prev
              Just(res) ->
                val (nm, mo) = res
                in-flight := in-flight - 1
                // Replay this stage's phase reports NOW, not in a batch once the
                // whole parallel run is done: the point of a running commentary is
                // that it runs. The serve loop is the only strand that gets here,
                // so this is the safe place to re-emit them under the real handler.
                // DIAGNOSTICS are still flushed separately, in build order.
                mo.phases.foreach(fn((lvl, p, m)) log-phase(lvl, p, m))
                val type-checked = match mo.outcome
                  Right(ModTyped) -> !roots.any(fn(rt) rt == nm)
                  _ -> False
                if type-checked then
                  match mo.outcome
                    Right(bm) -> typed := typed.set(nm, bm)
                    Left(_) -> ()
                  tc-outcomes := tc-outcomes.set(nm, mo)
                  match todo0.find(fn((n2, _, _, _)) n2 == nm)
                    Just(it) -> pending-finish := pending-finish ++ [it]
                    Nothing -> ()
                else
                  val full = match tc-outcomes.lookup(nm)
                    Just(tco) -> merge-stage-outcomes(tco, mo)
                    Nothing -> mo
                  typed := typed.remove(nm)
                  collected := collected ++ [(nm, full)]
                  on-progress(collected.length, todo0.length, nm)
                  match mo.outcome
                    Right(bm) ->
                      ready-mods := ready-mods.set(nm, bm)
                      // hand this module's generated C to the pool right away
                      if cc-enabled then
                        match bm.bmod/cfile
                          Just(cf) -> pending-cc := pending-cc ++ [C-unit(cf, c-unit-eimports(ready-mods, bm.bmod/core, fl.build-type))]
                          Nothing -> ()
                    Left(_)   -> failed := failed ++ [nm]
              Nothing -> ()
            waiting := waiting ++ [r.reply]
            drain()
            cc-drain()
          serve-loop()
      serve-loop()
      // detached workers: wait for every one to confirm it saw AllDone and
      // exited, so the caller never observes a build as "finished" while a
      // worker thread is still alive
      list(1, n-workers).foreach(fn(_) done-ch.xreceive)
      list(1, n-cc).foreach(fn(_) cc-done-ch.xreceive)
      requests.close
      done-ch.close
      cc-done-ch.close

      // diagnostics in ORIGINAL (stale-set) order, not completion order --
      // dispatch is now nondeterministic (whichever worker asks first), but
      // the emitted diagnostics must not depend on that
      val byName = collected
      val ordered = todo0.filter-map(fn((nm, _, _, _)) byName.find(fn((n2, _)) n2 == nm))
      (ready-mods, ordered)