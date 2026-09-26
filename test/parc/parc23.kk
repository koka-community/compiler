// ensure reuse works through a box

// struct pair2<a,b>(a : list<a>, b : b)   // this reuses
struct pair2<a,b>(a : a, b : b)

fun rotate( ysacc )
  match ysacc
    Pair2(Cons(y,ys),acc) -> Pair2(Cons(y,acc),ys)  // should reuse the Cons
    _ -> Pair2(Nil,Nil)

fun main()
  ()
