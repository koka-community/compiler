// Per-module interface LOAD cost, in dependency order, plus the critical path.
// Decides whether parallel loading is limited by wave barriers (many cheap
// modules) or by one dominant module (then no scheduler helps).
//
//   ./koka -e scripts/load-cost-probe.kk -- <entry.kk> <build-dir>
import std/data/rb-map
import std/os/path
import std/os/env
import std/os/file
import compiler/common/file
import compiler/common/name
import compiler/compile/build
import compiler/compile/schedule
import compiler/common/syntax
import compiler/compile/vfs
import compiler/syntax/parse
import compiler/syntax/syntax
import compiler/common/parse

pub fun main()
  with no-vfs
  val args = get-args()
  val entry = args.head.default("scripts/probe-tiny.kk")
  val out-dir = args.drop(1).head.default(".").path
  val srcdirs = Module-dirs([".".path, "lib".path], [".".path, "lib".path].map(fn(d) d.realpath))
  val prog = parse-program-from-file(entry.path, False)
  val cache = discover-deps(prog.imports.map(fn(i) i.fullName), srcdirs, target-platform-default, out-dir)
  val entries = cache.list.map fn((nm, (src, declared, deps0, _)))
    (nm, src, deps0.canonicalize-deps(src, declared, srcdirs).map(fst))
  val adj = entries.map(fn((nm, _, ds)) (nm, ds))
  val (waves, _) = build-waves(adj)
  var mods : bmodules := rb-map/empty()
  var total := 0
  // per-module cost, loading in wave order so each has its deps available
  val costs = waves.flatmap fn(wave)
    wave.filter-map fn(nm)
      match entries.find(fn((k, _, _)) k == nm)
        Nothing -> Nothing
        Just((_, _, ds)) ->
          val kki = out-dir / (nm.module-name-to-path ++ ".kki").path
          val at = kki.common/file/file-mtime
          if at <= 0 then Nothing else
            // build the env OUTSIDE the timed region: it is the owner strand's
            // prep work, measured separately (and shown to be 1.3%), not part
            // of what a worker would do
            val env = mods.restrict-to-closure(ds)
            val ms0 = now-ms()
            match load-iface(kki, env, at, Nothing)
              Just(m) ->
                val el = now-ms() - ms0
                mods := mods.set(nm, m)
                total := total + el
                Just((nm, el, wave.length))
              Nothing -> Nothing
  println("module                              ms   wave-width")
  costs.foreach fn((nm, ms, w))
    println(nm.show-plain.pad-right(34) ++ ms.show.pad-left(6) ++ "   " ++ w.show)
  println("")
  println("total (sequential)  : " ++ total.show ++ "ms")
  // critical path: the slowest module in each wave, summed -- the floor for ANY
  // wave-barrier scheduler with unlimited workers
  val path = waves.foldl(0) fn(acc, wave)
    acc + wave.foldl(0) fn(mx, nm)
      match costs.find(fn((n2, _, _)) n2 == nm)
        Just((_, ms, _)) -> max(mx, ms)
        Nothing -> mx
  println("wave-barrier floor  : " ++ path.show ++ "ms  (sum of each wave's slowest)")
  val r = (total * 100) / max(1, path)
  println("ideal (total/floor) : " ++ (r / 100).show ++ "." ++ (r % 100).show ++ "x")
  println("waves               : " ++ waves.length.show ++ ", widest " ++ waves.max-width.show)
  // The floor for a READINESS dispatcher (a module starts the moment its own
  // deps are loaded, no barrier): the longest weighted chain through the DAG.
  // If this is close to the wave-barrier floor, barriers are not the limit and a
  // dynamic scheduler would buy nothing.
  fun cost-of(nm: name): int
    match costs.find(fn((n2, _, _)) n2 == nm)
      Just((_, ms, _)) -> ms
      Nothing -> 0
  fun deps-of-nm(nm: name): list<name>
    match entries.find(fn((k, _, _)) k == nm)
      Just((_, _, ds)) -> ds.filter(fn(d) entries.any(fn((k, _, _)) k == d))
      Nothing -> []
  fun longest(nm: name, depth: int): div int
    if depth > 200 then cost-of(nm)
    else cost-of(nm) + deps-of-nm(nm).foldl(0) fn(mx, d) max(mx, longest(d, depth + 1))
  val cpath = entries.foldl(0) fn(mx, (nm, _, _)) max(mx, longest(nm, 0))
  println("critical path       : " ++ cpath.show ++ "ms  (longest dependent chain)")
  val r2 = (total * 100) / max(1, cpath)
  println("readiness ceiling   : " ++ (r2 / 100).show ++ "." ++ (r2 % 100).show ++ "x")
