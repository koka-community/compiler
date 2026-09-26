type stream<a>
  SNil
  SCons( head : a, tail : stream<a> )
  lazy SApp( pre : stream<a>, post : stream<a> ) ->
    match pre
      SCons(x,xx) -> SCons(x,SApp(xx,post))
      SNil        -> post

fun foo( m : maybe<stream<int>> ) : int
  match m
    Just(SCons(x,_xx)) -> x
    Just(SNil)         -> 0
    Nothing            -> 0
