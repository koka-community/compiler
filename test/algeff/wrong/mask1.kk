// issue #509

effect reader<s>
  fun ask() : s

fun test( p : () -> <reader<int>, reader<int>|e> a ) : e a
  with fun ask() 100
  with fun ask() 42
  p()

pub fun main(): console ()
  with test
  println(mask<reader<int>>(ask()) : int)