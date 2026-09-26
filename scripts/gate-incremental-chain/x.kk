// A second root sharing `b` with `r`: building it first rebuilds `b` without
// rebuilding what `r` needs above `b`.
import b

fun main()
  println(f())
