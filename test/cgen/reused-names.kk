// Issue: https://github.com/koka-lang/koka/issues/186
alias elem = int

fun sequences(xs : list<elem>)
  match xs
    Cons(a, Cons(b, xs)) ->
        if(a > b) then descending(b, [a], xs)
        else ascending(b, (fn(x) { Cons(a, x) }), xs)
    _ -> [xs] // This uses a name both in scope outside the match and inside the other match branch. Uniquify should not substitute this.

fun descending(a : elem, as_, bs)
  match bs
    Cons(b, bs) | a > b -> descending(b, Cons(a, as_), bs)
    _ -> Cons(Cons(a, as_), sequences(bs))

fun ascending(a : elem, as_, bs)
  match bs
    Cons(b, bs) | !(a > b) -> ascending(b, fn(ys) { as_(Cons(a, ys)) }, bs)
    _ -> Cons(as_([a]), sequences(bs))

fun main()
  sequences([0, 1, 2, 3])