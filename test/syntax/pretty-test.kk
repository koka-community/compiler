import compiler/syntax/pretty
import compiler/syntax/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/lib/pprint
import std/test

fun suite()
  val v = "v".new-name
  val vvar = Var(v, False, null)
  val tint = TpCon("int".new-name, null)
  val texn = TpCon("exn".new-name, null)
  val vzero = Literal(LitInt(0, null))
  val pzero = PatLit(LitInt(0, null), null)
  group("pretty-printing")
    test("expressions")
      expect("v")
        vvar.pretty.show
      expect("fn()\n  v")
        Lam([], vvar, False, null).pretty.show
      expect("fn(v)\n  v")
        Lam([ValueBinder(v, Nothing, Nothing, null, null)], vvar, False, null).pretty.show
      expect("fn(v: int = 0)\n  v")
        Lam([ValueBinder(v, Just(tint), Just(vzero), null, null)], vvar, False, null).pretty.show
      expect("v()")
        App(vvar, [], null).pretty.show
      expect("0")
        vzero.pretty.show
      expect("'c'")
        Literal(LitChar("c", null)).pretty.show
      expect("'\n'")
        Literal(LitChar("\n", null)).pretty.show
      expect(r#"
mask<exn>
  throw("Hi")
      "#.trim())
        Inject(texn, App(Var("throw".new-name, False, null), [(Nothing, Literal(LitString("Hi", null)))], null), False, null).pretty.show
      expect(r#"
mask behind<exn>
  throw("Hi")
      "#.trim())
        Inject(texn, App(Var("throw".new-name, False, null), [(Nothing, Literal(LitString("Hi", null)))], null), True, null).pretty.show
    test("patterns")
      val patBind = ValueBinder(v, Nothing, PatWild(null), null, null)
      val patBindInt = ValueBinder(v, Just(tint), PatWild(null), null, null)
      expect("0")
        pzero.pretty.show
      expect("_")
        PatWild(null).pretty.show
      expect("v : int")
        PatVar(patBindInt, null).pretty.show
      expect("Cons")
        PatCon("Cons".new-name, [], null, null).pretty.show
      expect("Cons(v)")
        PatCon("Cons".new-name, [(Nothing, PatVar(patBind, null))], null, null).pretty.show
      expect("(0)")
        PatParens(pzero, null).pretty.show
      expect("0 : int")
        PatAnn(pzero, tint, null).pretty.show