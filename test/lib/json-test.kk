import compiler/lib/json
import std/data/linearmap
import std/test

fun suite()
  test("json")
    expect(JSObj([("hello",JSString("world"))]))
      parse-json(r#"{"hello":"world" // a comment here
        }"#)