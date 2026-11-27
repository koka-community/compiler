// A recursive group with a fully annotated member (`g`) and a member with a
// polymorphic signature (`f`): `g` is in scope once while `f` is checked.
fun f(x : a, n : int) : div int
  g(n)

fun g(n : int) : div int
  if n > 0 then f(True, n - 1) else 0

// the same with an implicit parameter and an overloaded name
type expr<t>
  Literal(l : lit)
  Ann(e : expr<t>, t : t)

fun expr/show(e : expr<t>, ?show : (t) -> _ string) : _ string
  match e
    Literal(l) -> "Literal " ++ l.show
    Ann(e', t) -> e'.show ++ " : " ++ t.show

type lit
  LitInt(value : int)

fun lit/show(l : lit) : string
  match l
    LitInt(v) -> v.show

pub fun main()
  println(f("x", 3))
  println(Ann(Literal(LitInt(1)), 2).show)
