// Cost of a single effect operation, isolated.
//
//   ./koka -O2 --include=scripts -o /tmp/beo scripts/bench-effect-op.kk && /tmp/beo
//
// Three loops over the same arithmetic, differing only in how the value gets
// there. The gap between the handler rows and `explicit parameter` is what one
// tail-resumptive operation costs; the two handler rows differ only in operation
// COUNT (2/iteration vs 1), which is how we established that the cost is linear
// in operations and that monadic lifting adds nothing measurable.
//
// Reference points on this machine (30M iterations):
//   before the sticky-refcount fix   825 / 410 / 38 ms   = 13.7 ns/op
//   after  the sticky-refcount fix   623 / 306 / 37 ms   = 10.2 ns/op
import compiler/common/file

effect st1
  fun nextc(): maybe<int>
  fun bump(i: int): ()

// result MATCHED -- two operations per iteration
fun loop-match(): <st1,div> ()
  match nextc()
    Nothing -> ()
    Just(c) ->
      bump(c)
      loop-match()

// STATEMENT position -- one operation per iteration, result never bound
fun loop-stmt(n: int, i: int): <st1,div> ()
  if i >= n then () else
    bump(i + 1)
    loop-stmt(n, i + 1)

fun with-h(n: int, action: () -> <st1,div|e> a): <div|e> (a, int)
  var i := 0
  var acc := 0
  fun go()
    with handler
      fun nextc()
        if i >= n then Nothing else
          i := i + 1
          Just(i)
      fun bump(k) acc := acc + k
    action()
  val r = go()
  (r, acc)

// the control: no handler at all
fun loop-p(n: int, i: int, acc: int): div int
  if i >= n then acc else loop-p(n, i + 1, acc + i + 1)

pub fun main()
  val n = 30000000
  val t0 = now-ms()
  val (_, a) = with-h(n, loop-match)
  val t1 = now-ms()
  val (_, b) = with-h(n, fn() loop-stmt(n, 0))
  val t2 = now-ms()
  val c = loop-p(n, 0, 0)
  val t3 = now-ms()
  println("op result matched (2 ops/iter): " ++ (t1 - t0).show ++ "ms  acc=" ++ a.show)
  println("op in statement position (1)  : " ++ (t2 - t1).show ++ "ms  acc=" ++ b.show)
  println("explicit parameter (control)  : " ++ (t3 - t2).show ++ "ms  acc=" ++ c.show)
