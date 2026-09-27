struct monoid<a>
  zero : () -> a        // with a unit function monoid/mzero and monoid/call/mzero have the same signature :-(
  plus : (a,a) -> a


val intplus/monoid = Monoid({0},(+))
val intmul/monoid  = Monoid({1},(*))

fun suml( xs : list<a>, ?m:monoid<a> ) : a
  xs.foldl((m.zero)(),m.plus)

fun suml'( xs, ?m:monoid<_> )
  xs.foldl((m.zero)(),m.plus)

fun sum2( x:a, y:a, ?m:monoid<a> ) : a
  m.plus.(m.plus.(x,y),m.zero.())

fun list1/monoid( ?m:monoid<a>)  : monoid<list<a>>
  Monoid({[m.zero.()]}, fn(xs,ys) zipwith(xs,ys,m.plus))

// fun list2/monoid( ?m:monoid<a>)  : monoid<list<a>>
//   Monoid({[m.call/zero()]}, fn(xs,ys) zipwith(xs,ys,m.plus))

fun list3/monoid( ?m:monoid<a>)  : monoid<list<a>>
  Monoid({[m.monoid/zero.()]}, fn(xs,ys) zipwith(xs,ys,m.plus))

