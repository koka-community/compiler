// Stage-3 derisk probe, bisection variant: NO unsafe-total, NO threads.
// If this works, the earlier segfault is unsafe-total's cast over
// handler-installing code; threads were never the issue.
import std/os/task
import std/core/unsafe
import std/os/path
import compiler/syntax/parse
import compiler/syntax/syntax
import compiler/common/parse
import compiler/common/range

fun scan-body(src: string, fname: string): _ either<string, (string, int)>
  val prog = parse-program-from-string(src, fname.path, False)
  Right((fname, prog.imports.length))

fun scan(src: string, fname: string): pure either<string, (string, int)>
  // ORDER MATTERS: try consumes exn INSIDE (evidence intact), unsafe-total
  // masks only the residual <div,ndet,fsys> -- masking exn under a live
  // handler is the documented segfault case (std/core/unsafe.kk header),
  // and is exactly what crashed the first version of this probe.
  val r = unsafe-total(fn() try(fn() scan-body(src, fname)))
  match r
    Ok(x) -> x
    Error(exn) -> Left(exn.message)

pub fun main()
  val a = "module aaa\nimport std/core\nfun f(x: int): int\n  x + 1\n"
  val b = "module bbb\nimport std/core\nimport std/os/path\nfun g(): string\n  \"hi\"\n"
  val bad = "module ccc\nfun ((((\n"
  val seq = [scan(a, "s1.kk"), scan(b, "s2.kk"), scan(bad, "s3.kk")]
  println("sequential done: " ++ seq.length.show)
  val rs = parallel([
    fn() scan(a, "p1.kk"),
    fn() scan(b, "p2.kk"),
    fn() scan(bad, "p3.kk"),
    fn() scan(a, "p4.kk") ])
  println("parallel done: " ++ rs.length.show)
  (seq ++ rs).foreach fn(r)
    match r
      Right((nm, n)) -> println("ok " ++ nm ++ " imports=" ++ n.show)
      Left(e) -> println("err " ++ e.split("\n").head.default(""))
