effect yield
  ctl yield(i: int): bool

fun traverse(xs: list<int>): yield ()
  match xs
    Cons(x, xx) -> if yield(x) then traverse(xx) else ()
    Nil -> ()

fun main()
  with ctl yield(i)
    println("yielded " ++ i.show)
    resume(i <= 2)
  traverse([1,2,3,4])
