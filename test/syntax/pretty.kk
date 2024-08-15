import compiler/syntax/pretty
import compiler/syntax/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/lib/pprint
import std/test

fun main()
  val v = "v".new-name
  val vvar = Var(v, False, null)
  val tint = TpCon("int".new-name, null)
  val texn = TpCon("exn".new-name, null)
  val vzero = Literal(LitInt(0, null))
  val pzero = PatLit(LitInt(0, null), null)
  basic/test("expression pretty printing")
    expect("v")
      vvar.pretty(?pretty=fn(t) empty).show
    expect("fn() v")
      Lam([], vvar, null).pretty(?pretty=fn(t) empty).show
    expect("fn(v) v")
      Lam([ValueBinder(v, Nothing, Nothing, null, null)], vvar, null).pretty(?pretty=fn(t) empty).show
    expect("fn(v: int = 0) v")
      Lam([ValueBinder(v, Just(tint), Just(vzero), null, null)], vvar, null).pretty(?pretty=fn(t) t.pretty).show
    expect("v()")
      App(vvar, [], null).pretty(?pretty=fn(t) empty).show
    expect("0")
      vzero.pretty(?pretty=fn(t) empty).show
    expect("'c'")
      Literal(LitChar("c", null)).pretty(?pretty=fn(t) empty).show
    expect("'\n'")
      Literal(LitChar("\n", null)).pretty(?pretty=fn(t) empty).show
    expect(r#"
mask<exn>
  throw("Hi")
    "#.trim())
      Inject(texn, App(Var("throw".new-name, False, null), [(Nothing, Literal(LitString("Hi", null)))], null), False, null).pretty(?pretty=fn(t) t.pretty).show
    expect(r#"
mask behind<exn>
  throw("Hi")
    "#.trim())
      Inject(texn, App(Var("throw".new-name, False, null), [(Nothing, Literal(LitString("Hi", null)))], null), True, null).pretty(?pretty=fn(t) t.pretty).show
  basic/test("pattern pretty printing")
    val patBind = ValueBinder(v, Nothing, PatWild(null), null, null)
    val patBindInt = ValueBinder(v, Just(tint), PatWild(null), null, null)
    expect("0")
      pzero.pretty(?pretty=fn(t) empty).show
    expect("_")
      PatWild(null).pretty(?pretty=fn(t) empty).show
    expect("v : int")
      PatVar(patBindInt, null).pretty(?pretty=fn(t) t.pretty).show
    expect("Cons")
      PatCon("Cons".new-name, [], null, null).pretty(?pretty=fn(t) empty).show
    expect("Cons(v)")
      PatCon("Cons".new-name, [(Nothing, PatVar(patBind, null))], null, null).pretty(?pretty=fn(t) empty).show
    expect("(0)")
      PatParens(pzero, null).pretty(?pretty=fn(t) empty).show
    expect("0 : int")
      PatAnn(pzero, tint, null).pretty(?pretty=fn(t) t.pretty).show