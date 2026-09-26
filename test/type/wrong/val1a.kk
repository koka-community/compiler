pub fun main()
  val r = ref([])
  r := [1]
  println( if (!r).head.default(True) then "true" else "false" )
