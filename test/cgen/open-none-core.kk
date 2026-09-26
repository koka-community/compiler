// A total function can install a handler, so calling it from an effectful
// context needs `open-none` whatever module it is in: without it, `zz()` finds
// the caller's `aa` evidence at `zz`'s static index and returns 1.
import std/core/handler-inside

noinline fun zz-inside-local() : int
  with handler
    fun zz() 42
  zz()

fun main()
  with handler
    fun aa() 1
  println(zz-inside())
  println(zz-inside-local())
