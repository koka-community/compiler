import std/core/bslice
pub fun main()
  val s = "hello".string/bytes.slice
  println([s.length, s.byte-at(0), s.subslice(1,3).length].show)
