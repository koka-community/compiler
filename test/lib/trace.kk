import compiler/lib/trace
import std/test

fun suite()
  group("trace")
    test("trace and ctrace pass values through (output goes to stderr)")
      expect(0)
        ctrace(Red, "Hello, world!", 0)
      expect(1)
        trace("Hi", 1)
      expect("id")
        trace-id("id")
      expect(2)
        trace-eq("two", 2)

fun main()
  run-tests(suite)
