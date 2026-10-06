import compiler/common/message
import compiler/common/range
import compiler/common/color-scheme
import compiler/lib/pprint
import std/pretty/printer
import std/test

pub fun suite()
  test("tables")
    expect(r#"
Test          : here
Something long: there"#) fn()
      "\n" ++ table([("Test".text, "here".text), ("Something long".text, "there".text)]).show

  test("doc-from-range")
    with color-scheme-default
    val source = Source("test.txt", "hello\nworld")
    val start = Pos(source, 0, 1, 1)
    val end = Pos(source, 9, 2, 3)
    expect(r#"hello
wor"#) fn()
      doc-from-range(Range(start, end, False)).show

fun main()
  run-tests(suite)