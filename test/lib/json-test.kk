import compiler/lib/json
import std/data/linear-map
import std/test

fun suite()
  test("json")
    expect(JSObj([("hello",JSString("world"))]))
      parse-json(r#"{"hello":"world" // a comment here
        }"#)

fun main()
  run-tests(suite)