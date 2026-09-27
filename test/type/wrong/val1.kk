pub fun main()
  val r : forall<a> ref<global,list<a>> = ref([])
  r := [1]
  println( if (!r).head.default(True) then "true" else "false" )
