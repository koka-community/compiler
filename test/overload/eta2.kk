noinline fun plus(x:int,y:int,z:int=1)
  x+y+z

noinline fun foo( xs : list<a>, zero : a, ?plus : (a,a) -> a) : a
  xs.foldl(zero,?plus)

pub fun main()
  [1,2,3].foo(0)