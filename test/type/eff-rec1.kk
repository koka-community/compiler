div effect cow
  ctl moo() : (() -> <cow,div> ())


val cow = handler
  ctl moo()
    println("moo")
    resume( { moo()() } )

fun main()
  with cow
  moo()()
