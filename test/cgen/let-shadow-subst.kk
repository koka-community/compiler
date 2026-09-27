// Inlining this `main` into the generated `@main` beta-reduces the `for`
// wrapper; its fresh parameter name coincided with the name of `xs`'s later
// read (`xs@0@10003`), and simplify then substituted through that rebinding, so
// the `match` below read the local-var ref cell as a list (a crash at -O2).
fun main()
  var xs := []
  for(1,2) fn(i) xs := Cons(i, xs)
  println(xs.length)
