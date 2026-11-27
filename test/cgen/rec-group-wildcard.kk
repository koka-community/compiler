// A recursive group with a member without a signature (`top`) and a member with a
// partial signature (`walk`, a wildcard effect). The wildcard is inferred from
// `walk`'s body after `top` is generalized, so `top` must leave it open.
fun top(xs : list<int>)
  walk(xs, 0)

fun walk(xs : list<a>, n : int) : _ int
  match xs
    Nil -> throw("empty")
    Cons(_, Nil) -> n
    Cons(_, rest) -> if n > 100 then top([]) else walk(rest, n + 1)

// the same with a partial signature that is polymorphic in a type
fun pairs(xs : list<a>) : _ list<(a,a)>
  match xs
    Cons(x,xx) -> Cons((x,x), more(xx))
    Nil -> Nil

fun more(ys)
  pairs(ys)

pub fun main()
  println(top([1,2,3]))
  println(more([1,2]).map(fn((a,b)) a + b).show)
