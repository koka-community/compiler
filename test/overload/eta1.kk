import std/num/float64

pub fun main()
  // with `float64/show(f : float64, precision : ?int) : string`
  // the implicit parameter needs to be eta-expanded
  println(1.0)