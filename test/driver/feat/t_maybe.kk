fun lookup-it(x: int): maybe<int>
  if x > 0 then Just(x * 2) else Nothing
fun main()
  match lookup-it(5)
    Just(v) -> println("got " ++ v.show)
    Nothing -> println("nothing")
  match lookup-it(-1)
    Just(v) -> println("got " ++ v.show)
    Nothing -> println("nothing")
