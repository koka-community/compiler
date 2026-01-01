
fun nub-by(xs: list<a>, f: (a, a) -> e bool): e list<a>
  match xs
    Cons(x1, rst) -> Cons(x1, rst.filter(!f(x1, _)))
    Nil -> Nil

fun monotonic(l: list<int>)
  match l
    [] -> True
    [_] -> True
    Cons(i,Cons(j,xs)) -> i < j && monotonic(Cons(j,xs))