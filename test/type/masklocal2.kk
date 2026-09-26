// emit a string
effect fun emit( s : string ) : ()

fun pretty-emit1(action : () -> <console,emit,exn|e> a) : <console|e> error<a>
  try
    with fun emit(s) s.println
    emit("hi")
    action()

fun pretty-emit2(action : () -> <emit|e> a) : e (a,string)
  var out := ""
  with fun emit(s) out := out ++ s ++ "\n"
  (action(),out)

fun pretty-emit3(action : () -> <emit|e> a) : e string
  var out := ""
  with fun emit(s) out := out ++ s ++ "\n"
  action()
  out
