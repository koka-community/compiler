import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/common/range
import compiler/common/name
import compiler/common/syntax
import std/pretty/pprint
import compiler/type/type

fun range(?kk-module: string, ?kk-line: string)
  val line = parse-int(?kk-line).default(1)
  val mod = Source(?kk-module, "")
  Range(Pos(mod, 0, line, 0), Pos(mod, 0, line, 0), False)
fun bind(n: name, e: userExpr, ?range: range)
  match e
    Lam -> DefNonRec(Def(ValueBinder(n, (), e, ?range, ?range), range, Private, DefFun([], NoFip(False)), InlineAuto, ""))
    _ -> DefNonRec(Def(ValueBinder(n, (), e, ?range, ?range), range, Private, DefVal, InlineAuto, ""))
fun let(b: name, e: userExpr, body: (userExpr) -> userExpr, ?range: range) Let(b.bind(e), body(Var(b, False, ?range)), ?range)
fun expr(i: int, ?range: range) Literal(LitInt(i, range))
fun name(s: string) new-name(s)
fun opName(s: string, ?range: range) Var(new-name(s), True, range)
fun arg(e: userExpr) (Nothing, e)
fun (+)(e1: userExpr, e2: userExpr, ?range: range) App("+".opName, [e1.arg, e2.arg], range)
fun defh(hname: name, ops: list<(operationSort,name,list<(name,userType)>,userType)>, ?range: range)
  "effect".text |+| hname.show.pretty |--| ops.map(fn(op)
      op.fst.pretty |+| op.snd.pretty |.| op.thd.map(fn((n, t)) n.pretty |.| colon |+| t.pretty).tupled |.| colon |+| op.field4.pretty
    ).vcat.indent(2)
fun tstring(?range: range) TpCon("string".name, ?range)
fun tint(?range: range) TpCon("int".name, ?range)
fun def-fn(n: name, args: list<(name,userType)>, body: () -> userExpr, ?range: range) 
  DefNonRec(Def(ValueBinder(n, (), Lam(args.map(fn((a,t)) ValueBinder(a, Just(t), Nothing, ?range, ?range)), body(), True, ?range), ?range, ?range), range, Private, DefFun([], NoFip(False)), InlineAuto, ""))

fun example-main()
  val ex = 
    with def-fn("main".name, [])
    with x <- let("x".name, 1.expr)
    x + 1.expr
  defh("opx".name, [(OpFun, "xe".name, [("a".name, tstring())], tint())]).println
  ex.pretty.println