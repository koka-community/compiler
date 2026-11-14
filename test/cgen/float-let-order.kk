// Inlining `second` leaves a `let` in the second argument of the tuple; the
// simplifier must not float it before the first argument, as that reorders
// the two `tick` calls.
effect tick
  fun tick(): int

fun second()
  val x = tick()
  x * 10

fun pair(): tick (int, int)
  (tick(), second())

pub fun main()
  var n := 0
  with fun tick()
    n := n + 1
    n
  println(pair().show)
