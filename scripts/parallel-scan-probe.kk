// Minimal repro ladder for the parallel-scan segfault (compile/build.kk's
// `waves` scans a wave sequentially; parallelising it crashes).
//
// Each level adds exactly ONE variable, so the first level that crashes names
// the unsafe state. Workers `xemit`, the owner `xreceive`s -- the only correct
// channel direction, since an xchannel's receive side must run on the loop
// that created it.
//
//   KOKA_PROBE_LEVEL=0  spawn-thread over pure arithmetic
//   KOKA_PROBE_LEVEL=1  + read the file in the worker
//   KOKA_PROBE_LEVEL=2  + parse in the worker, AFTER the main thread parsed once
//                         (lexer tables and any other lazy state already forced)
//   KOKA_PROBE_LEVEL=3  + parse in the worker with NOTHING forced first
//                         (concurrent first-touch of lazy state)
//   KOKA_PROBE_LEVEL=4  + each worker parses a DIFFERENT file
//   KOKA_PROBE_LEVEL=5  + the workers are spawned INSIDE a live effect handler,
//                         so each closure captures that handler's evidence --
//                         the real `waves` runs under vfs-lookup/log/comp-error
//
// KOKA_PROBE_WORKERS caps the worker count (1 = no concurrency, to separate
// "needs >=2 threads" from "broken even serially").
import std/async/thread
import std/os/env
import std/core/unsafe
import std/os/path
import std/os/dir
import std/os/file
import compiler/syntax/parse
import compiler/common/range
import compiler/syntax/syntax

val files = [
  "compiler/common/name.kk", "compiler/common/range.kk", "compiler/common/id.kk",
  "compiler/kind/kind.kk", "compiler/lib/pprint.kk", "compiler/common/failure.kk",
  "compiler/common/syntax.kk", "compiler/common/color-scheme.kk"
]

fun level(): ndet int
  match get-env-value("KOKA_PROBE_LEVEL")
    Just(s) -> s.parse-int.default(0)
    Nothing -> 0

fun workers(): ndet int
  match get-env-value("KOKA_PROBE_WORKERS")
    Just(s) -> s.parse-int.default(4)
    Nothing -> 4

fun parse-one(content: string, fname: string): int
  val r = unsafe-total fn()
    try fn()
      val prog = parse-program-from-string(content, fname.path, True)
      prog.imports.length
  match r
    Ok(n)    -> n
    Error(_) -> -1

// A stand-in for the ambient handlers `waves` runs under. What matters is not
// what it does but that it is live when the worker closures are created.
effect probe-log
  fun plog(msg: string): ()

fun main()
  val lvl = level()
  val n = workers()
  val paths = files.map(fn(f) f.path).filter(dir/is-file)
  println("level=" ++ lvl.show ++ " workers=" ++ n.show ++ " files=" ++ paths.length.show)
  val first = match paths
    Cons(p, _) -> p
    Nil -> throw("no probe files found; run from the repo root")

  // Level 2 forces the parser's lazy state on the main thread first.
  if lvl == 2 then
    val c = read-text-file(first)
    println("warmed: " ++ parse-one(c, "warm").show ++ " imports")
  else ()

  // Read up front for levels <= 3 so the worker does only the one new thing.
  val content = if lvl >= 1 && lvl <= 3 then read-text-file(first) else ""

  if lvl == 5 then
    with handler
      fun plog(msg) ()
    run-workers(lvl, n, paths, first, content)
  else run-workers(lvl, n, paths, first, content)

fun run-workers(lvl: int, n: int, paths: list<path>, first: path, content: string): <async,ioc,console,div,ndet> ()
  val results = xchannel()
  list(1, n).foreach fn(i)
    spawn-thread fn()
      // `exn` is not in a worker's `<async,ioc>` row, so contain it here the
      // same way `scan-deps` does rather than letting it escape.
      val r = try fn()
        match lvl
          0 -> list(1, 200000).foldl(0, fn(a, x) a + x % 7)
          1 -> read-text-file(first).count
          4 -> match paths[(i - 1) % max(1, paths.length)]
                 Just(p) -> parse-one(read-text-file(p), p.string)
                 Nothing -> -1
          _ -> parse-one(content, "probe")
      val v = match r
        Ok(x)    -> x
        Error(_) -> -2
      results.xemit((i, v))
  list(1, n).foreach fn(_)
    val (i, v) = results.xreceive
    println("  worker " ++ i.show ++ " -> " ++ v.show)
  results.close
  println("OK level=" ++ lvl.show)
