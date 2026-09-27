// Is CONCURRENT interface loading deterministic?
//
// Readiness dispatch for the pre-load made warm builds non-reproducible (~1 run
// in 3), while wave barriers and a single worker were stable -- see
// docs/koka-perf-debugging.md. Every run loaded the same 185 modules with the
// same canonical map and a closure-only env, so the suspicion is that a loaded
// module's CONTENT varies, i.e. shared mutable state in the load path.
//
// This loads ONE interface from N threads at once, with an identical env, and
// hashes each result. Differing hashes localise the race inside `load-iface`.
//
//   ./koka -O2 -e scripts/load-race-probe.kk -- <file.kki|dir> [threads]
//
// Given a DIRECTORY it loads every .kki in it across N workers (round-robin,
// the same static slicing the pre-load uses) and prints one combined
// fingerprint, so repeated runs can be compared without rebuilding the driver.
import std/data/rb-map
import std/os/path
import std/os/dir
import std/os/env
import std/async
import std/async/thread
import compiler/common/name
import compiler/common/syntax
import compiler/compile/build
import compiler/compile/vfs
import compiler/core/core
import compiler/type/type
import compiler/compile/options
import compiler/lib/log
import compiler/syntax/parse
import compiler/syntax/syntax
import compiler/common/parse

// Polynomial rolling hash. Deliberately NOT FNV with `^`: `^` is not bitwise xor
// here, and the resulting "hash" failed to distinguish strings that plainly
// differed -- adding every definition's TYPE to the fingerprint left the value
// unchanged, which is how the bug was noticed.
fun checksum(s: string): int
  s.list.foldl(7) fn(h, c)
    (h * 31 + c.int) % 1000000007

fun selftest(): console ()
  val a = "alpha".checksum
  val b = "alphb".checksum
  println("checksum selftest: " ++ (if a == b then "BROKEN (collides)" else "ok") ++ " " ++ a.show ++ " vs " ++ b.show)

// Fingerprint from NAMES only: `show-plain` is pure, so this needs none of the
// pretty-printer's handler stack and can run on a worker. A shifted generated id
// (the observed symptom, `@442@0` vs `@442@443`) lands in a name, so it shows.
// the raw fingerprint STRING, so comparisons need not trust the checksum
fun fingerprint-of(m: bmodule): _ string
  match m
    ModIface(c, idefs) ->
      val dnames = c.defs.flatmap fn(g)
        match g
          DefRec(ds)   -> ds.map(fn(d) d.def-name.show-plain ++ "::" ++ d.ktype.ktype/show)
          DefNonRec(d) -> [d.def-name.show-plain ++ "::" ++ d.ktype.ktype/show]
      val inames = idefs.map fn(i)
        i.def-name.show-plain ++ ":" ++ i.cost.show ++ ":" ++ i.is-rec.show
          ++ ":" ++ i.paramSpecialize.map(show).join("")
      (dnames ++ inames).join("|")
    _ -> "?"

fun hash-of(m: bmodule): _ int
  match m
    ModIface(c, idefs) ->
      // TYPES as well as names: a definition whose type parsed differently
      // keeps its name, so a names-only fingerprint cannot see it -- exactly
      // the blind spot that made wave and readiness look identical.
      val dnames = c.defs.flatmap fn(g)
        match g
          DefRec(ds)   -> ds.map(fn(d) d.def-name.show-plain ++ "::" ++ d.ktype.ktype/show)
          DefNonRec(d) -> [d.def-name.show-plain ++ "::" ++ d.ktype.ktype/show]
      // include COST (computed from the body) and the specialize mask, so a
      // difference in an inline definition's body -- not just its name -- shows up
      val inames = idefs.map fn(i)
        i.def-name.show-plain ++ ":" ++ i.cost.show ++ ":" ++ i.is-rec.show
          ++ ":" ++ i.paramSpecialize.map(show).join("")
      (dnames ++ inames).join("|").checksum
    _ -> -2

pub fun main()
  if get-env-value("PROBE_SELFTEST").is-just then selftest()
  with with-no-phase
  with no-vfs
  val args = get-args()
  val kki = args.head.default("").path
  val n = args.drop(1).head.default("14").parse-int.default(14)
  if kki.string.is-empty then
    println("usage: load-race-probe <file.kki|dir> [threads]")
  elif kki.string.ends-with(".kk").bool then
    // FAITHFUL mode: drive the real `preload-ifaces`, so each load gets its true
    // closure env and the inline section actually parses (with an empty env
    // `force-inlines` fails and returns [], which hides the interesting path).
    val out-dir = args.drop(1).head.default(".").path
    val srcdirs = Module-dirs([".".path, "lib".path], [".".path, "lib".path].map(fn(d) d.realpath))
    val prog = parse-program-from-file(kki, False)
    val dcache = discover-deps(prog.imports.map(fn(i) i.fullName), srcdirs, target-platform-default, out-dir)
    val mods = preload-ifaces(flags-default(target = C(LibC)), out-dir, srcdirs, dcache, [], rb-map/empty())
    val per = mods.list.map(fn((nm, m)) nm.show-plain ++ "=" ++ m.hash-of.show)
    println("modules   : " ++ per.length.show)
    println("combined  : " ++ per.join(",").checksum.show)
    if get-env-value("PROBE_PER_MODULE").is-just then
      per.foreach(fn(l) println("MOD " ++ l))
    // exact, checksum-free comparison
    if get-env-value("PROBE_DUMP").is-just then
      mods.list.foreach fn((nm, m))
        println("FP " ++ nm.show-plain ++ " " ++ m.fingerprint-of)
  elif kki.is-directory then
    val files = kki.list-directory.filter(fn(f) f.string.ends-with(".kki").bool)
    val ch = xchannel()
    val idx = files.map-indexed(fn(i, f) (i, f))
    list(0, n - 1).foreach fn(w)
      val mine = idx.filter-map(fn((i, f)) if i % n == w then Just(f) else Nothing)
      spawn-thread fn()
        mine.foreach fn(f)
          val h = match try({ load-iface(f, rb-map/empty(), 1, Nothing) })
            Ok(Just(m)) -> m.hash-of
            _           -> -1
          ch.xemit((f.string, h))
    val got = list(1, files.length).map(fn(_) ch.xreceive)
    ch.close
    // combine in FILE order, so only per-module content can change the result
    fun hash-for(f: path): string
      match got.find(fn((p, _)) p == f.string)
        Just((_, h)) -> h.show
        Nothing      -> "?"
    val combined = files.map(hash-for).join(",").checksum
    println("modules   : " ++ files.length.show ++ "   workers: " ++ n.show)
    println("combined  : " ++ combined.show)
  else
    val ch = xchannel()
    list(1, n).foreach fn(_)
      spawn-thread fn()
        val h = match try({ load-iface(kki, rb-map/empty(), 1, Nothing) })
          Ok(Just(m)) -> m.hash-of
          _           -> -1
        ch.xemit(h)
    val hs = list(1, n).map(fn(_) ch.xreceive)
    ch.close
    val distinct = hs.foldl([]) fn(acc, h) if acc.any(fn(x) x == h) then acc else Cons(h, acc)
    println("threads   : " ++ n.show)
    println("distinct  : " ++ distinct.length.show ++ (if distinct.length == 1 then "  (deterministic)" else "  <-- RACE"))
    println("hashes    : " ++ hs.map(show).join(" "))
