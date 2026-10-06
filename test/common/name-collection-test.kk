import compiler/common/name
import compiler/common/name-collections
import std/test

pub fun suite()
  group("Name collections")
    test("Qualified Name Map")
      val qname1 = "hello/world".read-qualified-name
      expect(Found((qname1, 0)))
        single(qname1, 0).lookup("".new-name, "world".new-name)

fun main()
  run-tests(suite)