fun fib(n: int): int
  if n < 2 then n else fib(n - 1) + fib(n - 2)

fun main()
  println("fib(20) = " ++ fib(20).show)
