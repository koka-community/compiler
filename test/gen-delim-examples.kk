import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/common/range
import compiler/common/name
import compiler/common/syntax
import std/pretty/pprint
import std/num/random
import compiler/type/type

fun range(?kk-module: string, ?kk-line: string)
  val line = parse-int(?kk-line).default(1)
  val mod = Source(?kk-module, "")
  Range(Pos(mod, 0, line, 0), Pos(mod, 0, line, 0), False)
fun bind(n: name, e: userExpr, ?range: range)
  match e
    Lam -> DefNonRec(Def(ValueBinder(n, (), e, ?range, ?range), range, Private, DefFun([], NoFip(False)), InlineAuto, ""))
    _ -> DefNonRec(Def(ValueBinder(n, (), e, ?range, ?range), range, Private, DefVal, InlineAuto, ""))
fun let(b: name, e: userExpr, body: (userExpr) -> _ userExpr, ?range: range) 
  Let(b.bind(e), body(Var(b, False, ?range)), ?range)
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
fun def-fn(n: name, args: list<(name,userType)>, body: () -> _ userExpr, ?range: range) 
  DefNonRec(Def(ValueBinder(n, (), 
            Lam(args.map(fn((a,t)) ValueBinder(a, Just(t), Nothing, ?range, ?range)), body(), True, ?range), ?range, ?range)
            ,range , Private, DefFun([], NoFip(False)), InlineAuto, ""))

effect gen-delim
  fun add-handler(doc: doc, op: name): ()
  fun add-def(def: doc): ()
  fun get-handler(): name
  fun rand-e(): gen
  fun new-id(): name

effect binders
  fun get-binders(): list<userExpr>
effect handlers
  fun get-ops(): list<name>
  
fun bind-nm(n, f)
  with override
    fun get-binders()
      Cons(Var(n, False, null), get-binders())
  f()

fun handles(op: name, f: () -> <handlers|e> userExpr): <handlers|e> userExpr
  with override
    fun get-ops()
      Cons(op, get-ops())
  f()

type gen
  GenVar 
  GenApp
  GenHandler
  GenOp
  GenLet
  GenLam

fun gen(): <gen-delim,handlers,binders,pure,random|e> userExpr
  match rand-e()
    // 0 -> expr(random-int())
    GenVar -> 
      val binders = get-binders()
      if binders.is-empty then gen()
      else
        binders[random-int() % binders.length].unjust
    GenHandler -> 
      val name = get-handler()
      val nm = new-id()
      App(Handler(HandlerNormal, HandlerNoScope, HandlerNoOverride, Nothing, Nothing, [], Nothing, Just(gen()), Nothing, 
                  [HandlerBranch(name, [ValueBinder(nm, Nothing, (), null, null)], gen(), OpControl, null, null)],
                   null, null), 
          [(Nothing, handles(name, gen))], null)
    GenOp -> 
      val ops = get-ops()
      if ops.is-empty then gen()
      else
        val op = ops[random-int() % ops.length].unjust // TODO: Ensure argument is an int
        App(Var(op, False, null), [(Nothing, gen())], null)
    GenLet -> 
      val x = new-id()
      let(x, gen()) fn(_)
        with bind-nm(x)
        gen()
    GenLam -> 
      val x = new-id()
      Lam([ValueBinder(x, Nothing, Nothing, null, null)], bind-nm(x, gen), False, null)
    GenApp -> App(gen(), [(Nothing, gen())], null)

fun example-main()
  var prog := ""
  var ops := []
  var id := 0
  with handler
    fun get-ops() []
  with handler
    fun get-binders() []
  with handler
    fun add-handler(h, op)
      prog := prog ++ "\n" ++ h.show
      ops := Cons(op, ops)
    fun add-def(d)
      prog := prog ++ "\n" ++ d.show
    fun get-handler()
      ops[random-int() % ops.length].unjust
    fun rand-e()
      val r = random-int() % 40
      if r < 10 then GenVar
      else if r < 12 then GenLet
      else if r < 14 then GenApp
      else if r < 16 then GenLam
      else if r < 17 then GenHandler
      else GenOp
    fun new-id()
      val ident = "x" ++ id.show
      id := id + 1
      ident.new-name
  for(10) fn(i)
    val op = new-id()
    add-handler(defh(new-id(), [(OpFun, op, [(new-id(), tint())], tint())]), op)
  for(20) fn(i) 
    add-def(def-fn(("analyze-" ++ new-id().nameStem).new-name, [], gen).pretty)

fun example2()
  val ex = 
    with def-fn("main".name, [])
    with x <- let("x".name, 1.expr)
    x + 1.expr
  defh("opx".name, [(OpFun, "xe".name, [("a".name, tstring())], tint())]).println
  ex.pretty.println
