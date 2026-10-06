import compiler/compile/phase
import compiler/compile/progress
import compiler/common/name
import std/test

fun n( s : string ) : name
  s.new-name

pub fun suite()
  val evs = [
    PhaseEnd(n("a"), TypeCheck, 10),
    PhaseEnd(n("b"), TypeCheck, 20),
    PhaseEnd(n("a"), CodeGen, 5),
  ]

  test("per-phase totals aggregate across modules")
    expect(2)
      per-phase-totals(evs).length

  test("per-phase totals sum the same phase")
    expect(30)
      per-phase-totals(evs).lookup-phase(TypeCheck)

  test("per-module totals aggregate across phases")
    expect(2)
      per-module-totals(evs).length

  test("per-module totals sum the same module")
    expect(15)
      per-module-totals(evs).lookup-mod(n("a"))

  test("empty stream folds to nothing")
    expect(0)
      per-phase-totals([]).length

  test("events that are not PhaseEnd do not contribute")
    expect(0)
      per-phase-totals([ModDiscovered(n("a"), [n("b")]), Note("hi")]).length

fun main()
  run-tests(suite)
