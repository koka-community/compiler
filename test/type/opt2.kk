noinline fun plus(x:int, y:int, z:int=1)
  x+y+z

fun psum( xs:list<int>, ?plus) : int
  xs.foldl(0,plus)

pub fun main()
  [1,2,3].psum(?plus=plus)
