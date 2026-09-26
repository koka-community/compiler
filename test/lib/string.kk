// See https://github.com/koka-lang/koka/issues/486
fun main()
  val some-string = "hello"
  println("some-string = [" ++ some-string ++ "]")
  println("some-string.vector.string = [" ++ some-string.vector.string ++ "]")
