// a tiny self-contained module for the end-to-end check driver
// (no imports and no primitive environments: only literals and lambdas)
val one = 1

fun ident(x)
  x

fun twice(f, x)
  f(f(x))

fun compose(f, g)
  fn(x) f(g(x))

val hello = "hello driver"

fun apply-ident()
  ident(one)
