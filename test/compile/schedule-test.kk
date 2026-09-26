import compiler/compile/schedule
import compiler/common/name
import std/test

fun n( s : string ) : name
  s.new-name

fun names( ws : list<list<name>> ) : list<list<string>>
  ws.map( fn(w) w.map(show-plain) )

fun suite()
  test("independent modules all land in one wave")
    expect([["a", "b", "c"]])
      val (waves, _) = build-waves([(n("a"), []), (n("b"), []), (n("c"), [])])
      waves.names

  test("a chain serializes into one module per wave")
    expect([["a"], ["b"], ["c"]])
      // c imports b imports a
      val (waves, _) = build-waves([(n("c"), [n("b")]), (n("b"), [n("a")]), (n("a"), [])])
      waves.names

  test("a diamond puts the two middles in the same wave")
    expect([["d"], ["b", "c"], ["a"]])
      // a -> b, a -> c, b -> d, c -> d
      val (waves, _) = build-waves([
        (n("a"), [n("b"), n("c")]),
        (n("b"), [n("d")]),
        (n("c"), [n("d")]),
        (n("d"), [])])
      waves.names

  test("imports outside the graph impose no ordering")
    // std/core is interface-only (not a key), so `a` is ready immediately
    expect([["a"]])
      val (waves, _) = build-waves([(n("a"), [n("std/core")])])
      waves.names

  test("every scheduled module appears exactly once")
    expect(4)
      val (waves, _) = build-waves([
        (n("a"), [n("b"), n("c")]),
        (n("b"), [n("d")]),
        (n("c"), [n("d")]),
        (n("d"), [])])
      waves.scheduled-count

  test("widest wave is reported")
    expect(2)
      val (waves, _) = build-waves([
        (n("a"), [n("b"), n("c")]),
        (n("b"), [n("d")]),
        (n("c"), [n("d")]),
        (n("d"), [])])
      waves.max-width

  test("a cycle is returned, not dropped or hung")
    expect(["a", "b"])
      // a -> b -> a
      val (_, cyclic) = build-waves([(n("a"), [n("b")]), (n("b"), [n("a")])])
      cyclic.map(show-plain)

  test("modules outside a cycle still schedule")
    expect([["c"]])
      val (waves, _) = build-waves([
        (n("a"), [n("b")]),
        (n("b"), [n("a")]),
        (n("c"), [])])
      waves.names

  test("wave order is independent of input order")
    expect(True)
      // same graph, dependencies listed last instead of first
      val (w1, _) = build-waves([(n("c"), [n("b")]), (n("b"), [n("a")]), (n("a"), [])])
      val (w2, _) = build-waves([(n("a"), []), (n("b"), [n("a")]), (n("c"), [n("b")])])
      w1.names == w2.names

  test("an empty graph schedules nothing")
    expect(0)
      val (waves, _) = build-waves([])
      waves.scheduled-count
