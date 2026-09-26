// The SOUND counterpart to infer-drops-effect-row.kk: identical except the call
// is assigned directly instead of through an intermediate `val`. Infers
// `drain : () -> <io,eff1,local<h>|e> ()` and runs correctly (prints 1, exit 0).
pub effect eff1
  fun op1(): ()

pub fun repro(compile-src: (int) -> <io,eff1|e> int): <io,eff1|e> int
  var total := 0
  fun drain(): _ ()
    total := compile-src(1)
  drain()
  total

pub fun main()
  with handler
    fun op1() ()
  println(repro(fn(i) { op1(); i }))
