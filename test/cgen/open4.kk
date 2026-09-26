// See issue #511
effect abort
  ctl abort() : a

fun catch'(f : () -> <abort|e> a, h : () -> e a) : e a
  with ctl abort() { h() }
  f()

fun maybe(f : () -> <abort|e> a) : e maybe<a>
  with ctl abort() { Nothing }
  Just(f())

type abc { A; B; C }

fun show(abc : abc)
  match abc
    A -> "A"
    B -> "B"
    C -> "C"

fun abortA(abc : abc)
  match abc
    A -> abort()
    _ -> abc

fun abortB(abc : abc)
  match abc
    B -> abort()
    _ -> abc

fun distinct(abc : abc) : <abort,abort> abc
  val n = mask<abort>
    abortA(abc)
  abortB(n)

fun main() : <console,exn> ()
  println(maybe(fn() catch'(fn() distinct(A), fn() C)))
  println(maybe(fn() catch'(fn() distinct(B), fn() C)))
  println(maybe(fn() catch'(fn() distinct(C), fn() C)))
