// --------------------------------------------------------
//
// --------------------------------------------------------

div effect diverge
  ctl fix( f : (a -> <div,diverge> b, a) -> diverge b, x : a ) : b

effect test
  fun op( f : (int -> test int) -> int ) : int


val diverge = handler
  ctl fix(f,x) resume( f(fn(y){ fix(f,y) }, x) )


