import compiler/compile/build
import compiler/common/name
import std/test
import std/data/sort

fun n( s : string ) : name
  s.new-name

fun cycles( deps : list<(string, list<string>)> ) : div list<list<string>>
  import-cycles(deps.map(fn((m, ds)) (n(m), ds.map(n)))).map(fn(c) c.map(show-plain).sort)

pub fun suite()
  test("an acyclic graph has no cycles")
    expect([])
      cycles([("c", ["b"]), ("b", ["a"]), ("a", [])])

  test("a two-module cycle")
    expect([["a", "b"]])
      cycles([("a", ["b"]), ("b", ["a"])])

  test("a self-import is a cycle")
    expect([["a"]])
      cycles([("a", ["a"])])

  test("modules that only depend on a cycle are not part of it")
    expect([["a", "b"]])
      cycles([("c", ["a"]), ("a", ["b"]), ("b", ["a"])])

  test("an interface-only import cannot close a cycle")
    expect([])
      cycles([("a", ["std/core", "b"]), ("b", ["std/core"])])

  test("two separate cycles are both reported")
    expect(2)
      cycles([("a", ["b"]), ("b", ["a"]), ("c", ["d"]), ("d", ["c"])]).length

fun main()
  run-tests(suite)
