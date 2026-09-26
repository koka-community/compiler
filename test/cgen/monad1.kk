struct monad<m>
  pure : forall<a> a -> m<a>
  bind : forall<a,b> (m<a>, a -> m<b>) -> m<b>


//fun sequence( ms : list<m<a>>, ?monad : monad<m> ) : m<list<a>>
fun sequence( xs, ?m:monad<_> )
  match xs
    Nil -> m.pure.([])
    Cons(mx,mxx) ->
      with x  <- m.bind.(mx)
      with xx <- m.bind.(sequence(mxx))
      m.pure.(Cons(x,xx))
