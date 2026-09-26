// MINIMAL REPRODUCTION of the type-inference unsoundness behind the
// `import std/async/channel` segfault. See docs/async-segfault-root-cause-brief.md.
//
// This type-checks cleanly and SEGFAULTS (exit 139).
//
// `drain`'s inferred effect row is `<local<h>>` -- it has dropped `io`, `eff1`
// AND the rigid tail `e`, even though its body calls `compile-src`, whose row is
// `<io,eff1|e>`. Evidence is then built for a row the code does not actually run
// under, and `kk_evv_at` reads past the end of an empty vector:
//
//   $ koka -O1 -o /tmp/m test/evv/infer-drops-effect-row.kk && KOKA_EVV_CHECK=1 /tmp/m
//   koka: EVV CHECK: kk_evv_at: static index 0 is past the end of a 0-entry vector
//   [1]    segmentation fault
//
//   $ koka --showicore --showcoretypes -c test/evv/infer-drops-effect-row.kk
//   val drain : (() -> (local<h>) ())        <-- io, eff1 and |e all gone
//
// Three ingredients are each REQUIRED (removing any one makes it sound):
//   1. a `var` in scope (contributes `local<h>`)
//   2. a local function that assigns to that var
//   3. the call bound to an intermediate `val` before being used --
//      writing `total := compile-src(1)` directly is SOUND
//
// NOT required: `io` in the rows, the `: _ ()` annotation on `drain`,
// recursion, `foldl`/higher-order plumbing, optional parameters,
// eta-expansion, an intermediate function, `std/async`, or threads.

pub effect eff1
  fun op1(): ()

pub fun repro(compile-src: (int) -> <io,eff1|e> int): <io,eff1|e> int
  var total := 0
  fun drain(): _ ()
    val acc1 = compile-src(1)   // <-- binding to a val is load-bearing
    total := acc1
  drain()
  total

pub fun main()
  with handler
    fun op1() ()
  println(repro(fn(i) { op1(); i }))
