noinline fun plus(x:int,y:int,z:int=1)
  x+y+z

pub fun main()
  [1,2,3].foldl(0,plus)
