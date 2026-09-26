import compiler/compile/registry
import compiler/common/name
import std/test

fun n( s : string ) : name
  s.new-name

fun suite()
  test("demand registers a module once")
    expect(1)
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, _) = r1.demand(Nothing, n("a"))
      r2.known.length

  test("demand records distinct modules in discovery order")
    expect(["a", "b"])
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, _) = r1.demand(Just(n("a")), n("b"))
      r2.known.map(show-plain)

  test("a simple chain is not a cycle")
    expect(True)
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, c) = r1.demand(Just(n("a")), n("b"))
      c.is-nothing

  test("a diamond is not a cycle")
    // a -> b, a -> c, b -> d, c -> d : d is reached twice, but no loop
    expect(True)
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, _) = r1.demand(Just(n("a")), n("b"))
      val (r3, _) = r2.demand(Just(n("a")), n("c"))
      val (r4, _) = r3.demand(Just(n("b")), n("d"))
      val (_, c)  = r4.demand(Just(n("c")), n("d"))
      c.is-nothing

  test("a back edge is reported, not deadlocked")
    expect(True)
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, _) = r1.demand(Just(n("a")), n("b"))
      val (_, c)  = r2.demand(Just(n("b")), n("a"))
      c.is-just

  test("cycle message matches build.kk's existing wording")
    expect("recursive imports: a -> b -> a")
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, _) = r1.demand(Just(n("a")), n("b"))
      val (_, c)  = r2.demand(Just(n("b")), n("a"))
      c.default("")

  test("a longer cycle names every module on the loop")
    expect("recursive imports: a -> b -> c -> a")
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (r2, _) = r1.demand(Just(n("a")), n("b"))
      val (r3, _) = r2.demand(Just(n("b")), n("c"))
      val (_, c)  = r3.demand(Just(n("c")), n("a"))
      c.default("")

  test("self-import is a cycle")
    expect("recursive imports: a -> a")
      val (r1, _) = registry/empty().demand(Nothing, n("a"))
      val (_, c)  = r1.demand(Just(n("a")), n("a"))
      c.default("")

fun main()
  run-tests(suite)
