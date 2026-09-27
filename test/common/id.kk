import compiler/common/id
import std/test

fun suite()
  group("new-id")
    test("create id from value")
      expect(42)
        42.new-id

    test("multiple ids with same value are equal")
      expect(True)
        5.new-id == 5.new-id

  group("new-id-from")
    test("increment id")
      expect(11)
        10.new-id.new-id-from

  group("gen-id")
    test("gen-id creates id ignoring name")
      expect(True)
        gen-id("foo", 42) == 42.new-id

  group("id-nil")
    test("id-nil is zero")
      expect(0)
        id-nil

  group("id-number")
    test("extract id number")
      expect(42)
        42.new-id.id-number

  group("show-id")
    test("show-id formats with quotes")
      expect("\"42\"")
        show-id(42.new-id)

  group("comparison")
    test("ids are comparable")
      expect(True)
        10.new-id < 20.new-id

fun main()
  run-tests(suite)