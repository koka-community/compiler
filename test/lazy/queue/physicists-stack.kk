module physicists-stack

import bench

lazy type thunk<a>
  Done( xs : list<a>, p : pad )
  lazy Tail( thunk : thunk<a>, _p : pad ) ->
    match thunk
      Done( xs, p ) ->  Done( xs.tail, p )
  lazy AppRev( pre : list<a>, post : list<a> ) ->
    Done( list/(++)(pre,reverse(post)), Pad )

fbip fun whnf( xs : thunk<a> ) : div list<a>
  match xs
    Done( xs', _ ) -> xs'

type queue<a>
  Queue( working : list<a>, lenf : int, front : thunk<a>, lenr : int, rear : list<a> )

fun checkw( q : queue<a> ) : div queue<a>
  match q
    Queue( working, lenf, front, lenr, rear ) ->
      match working
        Nil -> Queue( front.whnf(), lenf, front, lenr, rear )
        working -> Queue( working, lenf, front, lenr, rear )

val physicists/empty = Queue( Nil, 0, Done( Nil, Pad ), 0, Nil )

fip fun isEmpty( ^q : queue<a> ) : bool
  match q
    Queue( _, lenf, _, _, _ ) -> lenf == 0

fip fun size( ^q : queue<a> ) : int
  match q
    Queue( _, lenf, _, lenr, _ ) -> lenf + lenr

fun check( q : queue<a> ) : div queue<a>
  match q
    Queue( _, lenf, front, lenr, rear ) ->
      if (lenr <= lenf) then checkw(q)
      else
        val front' = front.whnf()
        checkw(Queue( front', lenf + lenr, AppRev( front', rear ), 0, Nil ))

fun snoc( q : queue<a>, x : a ) : div queue<a>
  match q
    Queue( working, lenf, front, lenr, rear ) ->
      check(Queue( working, lenf, front, lenr + 1, Cons( x, rear ) ))

fun uncons( q : queue<a> ) : div maybe2<a,queue<a>>
  match q
    Queue( working, lenf, front, lenr, rear ) ->
      match working
        Nil -> Nothing2
        Cons( x, xs ) -> Just2(x, check(Queue( xs, lenf - 1, Tail( front, Pad ), lenr, rear )))

pub fun main()
  benchmain(QueueI(physicists/empty, snoc, uncons))
