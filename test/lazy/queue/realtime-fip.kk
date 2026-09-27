module realtime-fip

import bench

struct pair<a,b>(fst : a, snd : b)

noinline fun canthappen(x : a ) : a
  trace("** this should not happen **")
  x

// For the defunctionalization, we make the rotate function 'lazy'
// and put ys,acc in a pair to keep SRotate a binary constructor.
// We could also make SCons a ternary constructor, but that
// would imply a pretty big space overhead.
lazy type stream<a>
  SNil
  SCons( x : a, xs : stream<a> )
  lazy SRotate( xs : stream<a>, ysacc : pair<list<a>, stream<a>> ) ->
    match ysacc
      Pair(Cons(y,ys),acc) ->
        match xs
          SNil        -> SCons(y,acc)
          SCons(x,xx) -> SCons(x,SRotate(xx,Pair(ys,SCons(y,acc))))
      _ -> canthappen(SNil)

value type queue<a>
  Queue( front : stream<a>, rear : list<a>, sched : stream<a> )

val realtime/empty = Queue( SNil, Nil, SNil )

fbip fun is-empty(  Queue(front,_,_) : queue<a> ) : div bool
  match front
    SNil -> True
    _    -> False

fun exec( Queue(front,rear,sched) : queue<a> ) : div queue<a>
  match sched
    SCons(_,srotate) -> Queue(front,rear,srotate)
    SNil ->
      val f = SRotate(front,Pair(rear,SNil))
      Queue(f,Nil,f)

fun snoc( Queue(front,rear,sched)  : queue<a>, x : a ) : div queue<a>
  Queue(front, Cons(x,rear), sched).exec

fun uncons( Queue(front,rear,sched) : queue<a> ) : div maybe2<a,queue<a>>
  match front
    SNil -> Nothing2
    SCons(x,xx) -> Just2(x,Queue(xx,rear,sched).exec)

pub fun main()
  benchmain(QueueI(realtime/empty,snoc,uncons))
