struct num<a>
  (+) : ( x : a, y : a ) -> a
  (*) : (a,a) -> a

val int/num : num<int>
  = Num( (+), (*) )

pub fun main()
  (num.(+))(1,2).println