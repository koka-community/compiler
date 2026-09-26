import mpat-lib

// See mpat-lib.kk: `cross` is inlined from the .kki inline section; if the
// branch patterns round-trip in the wrong order the scrutinees swap and
// `cross(South, North)` wrongly returns True.
fun main()
  println( cross(South, North) )
  println( cross(North, South) )
  println( cross(East(1), West(2)) )
  println( cross(East(1), East(2)) )
