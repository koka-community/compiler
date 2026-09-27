// basic I/O
effect bio
  // Write a string to a file descriptor
  fun write( fd : filedesc, s : string ) : ()

alias filedesc = int

val stdout = 0

fun echo( s : string ) : bio ()
  write(stdout,s)

fun bio( action : () -> <bio|e> a) : e (a,string)
  var buf := ""
  with fun write(fd,s) buf := buf ++ s
  (action(),buf)

fun bio2( action : () -> <bio|e> a) : e (a,string)
  var buf := ""
  with return(x) (x,buf)
  with fun write(fd,s) buf := buf ++ s
  action()

fun bio3( action )
  var buf := ""
  with fun write(fd,s) buf := buf ++ s
  (action(),buf)

fun bio4( action )
  var buf := ""
  with fun write(fd,s) buf := buf ++ s
  (mask<local>(action),buf)

fun bio5( action : () -> <bio|e> a) : e (a,string)
  var buf := ""
  with fun write(fd,s) buf := buf ++ s
  (mask<local>(action),buf)

