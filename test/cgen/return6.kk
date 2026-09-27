// issue #643
fun test(c: char): maybe<char>
  val c1 =
    match f(c)
      Just(c1) ->
        c1
      Nothing ->
        return Nothing // or `return test(c)`

  Just(c1)

fun f(c: char): maybe<char>
  val x = match Just(c)
    Just(_cx) -> return Nothing
    Nothing  -> Just(c)
  x

fun main()
  ()