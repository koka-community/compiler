type stream<a>
  SNil
  SCons( head : a, tail : stream<a> )
  lazy SApp( pre : stream<a>, post : stream<a> ) ->
    match pre
      SCons(x,xx) -> SCons(x,SApp(xx,post))
      SNil        -> post
      SApp(p,q)   -> SNil


