// see issue #360
effect ctl myeffect() : ()

fun main() : <console> ()
    with finally
      println("top")
    with ctl myeffect()  ()
    with finally
      println("mid")
    with ctl myeffect()  myeffect()
    with finally
      println("cleanup")
    myeffect()