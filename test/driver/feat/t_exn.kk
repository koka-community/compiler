fun risky(x: int): exn int
  if x < 0 then throw("negative") else x
fun main()
  with handler
    ctl throw-exn(e) 
      println("caught: " ++ e.message)
      0
  println(risky(5).show)
  println(risky(-1).show)
