struct monoid<a>
  zero : a
  plus : (a,a) -> a


val intplus/monoid = Monoid(0,(+))
val intmul/monoid  = Monoid(1,(*))

fun suml( xs, ?m:monoid<_> )
  xs.foldl(m.zero,m.plus)


fun sum2( x:a, y:a, ?m:monoid<a> ) : a
  m.plus(m.plus.(x,y),m.zero)

fun list/monoid( ?m:monoid<a>)  : monoid<list<a>>
  Monoid([m.zero], fn(xs,ys) zipwith(xs,ys,m.plus))

