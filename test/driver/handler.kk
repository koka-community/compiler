effect ask
  fun ask(): int

fun add-twice(): ask int
  ask() + ask()

fun main()
  with fun ask() 21
  println(add-twice().show)
