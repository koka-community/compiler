import std/core/undiv

fun nub-by(xs: list<a>, f: (a, a) -> e bool): e list<a>
  match xs
    Cons(x1, rst) -> Cons(x1, rst.filter(!f(x1, _)))
    Nil -> Nil

fun monotonic(l: list<int>)
  match l
    [] -> True
    [_] -> True
    Cons(i,Cons(j,xs)) -> i < j && monotonic(Cons(j,xs))

fun indexed(l : list<a>): list<(int, a)>
  l.map-indexed(fn(i, x) (i, x))

fun contains(l: list<a>, x: a, ?(==): (a, a) -> e bool): e bool
  match l
    Cons(y, rst) -> (x == y) || contains(rst, x)
    Nil -> False

fun unzip-either(xs: list<either<a, b>>): (list<a>, list<b>)
  fun loop(ys: list<either<a, b>>, las: ctx<list<a>>, lbs: ctx<list<b>>): (list<a>, list<b>)
    match ys
      Nil -> (las ++. Nil, lbs ++. Nil)
      Cons(Left(a), a1) -> loop(a1, las ++ ctx Cons(a, hole), lbs)
      Cons(Right(b), b1) -> loop(b1, las, lbs ++ ctx Cons(b, hole))
  loop(xs, ctx hole, ctx hole)

fun zip3(l1: list<a>, l2: list<b>, l3: list<c>): list<(a,b,c)>
  match (l1, l2, l3)
    (Cons(x1, xs1), Cons(x2, xs2), Cons(x3, xs3)) -> Cons((x1, x2, x3), zip3(xs1.pretend-decreasing, xs2, xs3))
    _ -> Nil