import compiler/lib/json
import std/data/linearmap
import std/test

fun test()
  basic/test("json")
    expect(JSObj([("hello",JSString("world"))]))
      parse(r#"{"hello":"world" // a comment here
        }"#)