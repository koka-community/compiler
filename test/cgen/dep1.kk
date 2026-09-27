
pub effect test
  ctl test-expect(): a

pub effect test-scope
  fun report-fail(): ()

pub fun basic/scope(name: string, f: () -> <test-scope,console,pure|e> ()): <console,pure|e> ()
  with handler
    fun report-fail() ()
  f()

pub fun basic/test(name: string, f: () -> <test,test-scope,console,pure|e> ()): <console,pure|e> ()
  basic/scope(
    name,
    { test-scoped(name, f) }
  )

pub fun test-scoped(name: string, f: () -> <test,test-scope,console,pure|e> ()): <console,test-scope,pure|e> ()
  with handler
    ctl test-expect()
      ()
  f()

pub fun main()
  println(42)