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
fun let(b: name, e: userExpr, body: (userExpr) -> _ userExpr, ?range: range) Let(b.bind(e), body(Var(b, False, ?range)), ?range)
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
  fun new-id(): name

effect depth
  fun rand-e(): gen
  val depth: int

type gen
  GenVar 
  GenApp
  GenHandler
  GenOp
  GenLet
  GenLam

effect binders
  fun get-binders(): list<userExpr>

effect handlers
  fun get-all-ops(): list<name>

effect hnd
  fun needs-handler(op: name): ()
  
fun bind-nm(n, f)
  with fun get-binders()
      Cons(Var(n, False, null), get-binders())
  f()

fun handles(op: name, f: () -> hnd userExpr): hnd userExpr
  with override
    fun needs-handler(op1)
      if op1 == op then ()
      else needs-handler(op1)
  f()

// fun maybe-gen-hnd(f)
//   var handled := Nothing
//   with override     
//     fun get-all-ops() get-all-ops()
//     fun get-ops()
//       get-ops()
//     fun needs-handler(op1)
//       handled := Just(op1)
//   create-handler()
//   f()

fun gen-noop(): <gen-delim,handlers,binders,pure,random,depth> userExpr
  match rand-e()
    // 0 -> expr(random-int())
    GenVar -> 
      val binders = get-binders()
      if binders.is-empty then gen-noop()
      else binders[random-int() % binders.length].unjust
    GenHandler -> gen-noop()
    GenOp -> gen-noop()
    GenLet -> 
      val x = new-id()
      // with maybe-gen-hnd
      val bind = gen-noop()
      val body = 
           with bind-nm(x)
           gen-noop()
      let(x, bind) fn(_) body
    GenLam -> 
      val x = new-id()
      val bod = bind-nm(x, gen-noop)
      Lam([ValueBinder(x, Nothing, Nothing, null, null)], bod, False, null)
    GenApp -> 
      // with maybe-gen-hnd
      val f = gen-noop()
      val arg = gen-noop()
      App(f, [(Nothing, arg)], null)

fun finish-handlers(e: userExpr, hnds): hnd userExpr
  hnds.foldl(e) fn(acc, h) acc

fun inc-depth(f)
  with override
    fun rand-e()
      if depth >= maxDepth then GenVar
      else rand-e()
    val depth = depth + 1
  f()

val maxDepth = 5

fun gen(): <gen-delim,handlers,binders,pure,depth,random> (() -> hnd userExpr)
  with inc-depth
  trace("gen at depth " ++ depth.show)
  match rand-e()
    // 0 -> expr(random-int())
    GenVar -> 
      val binders = get-binders()
      if binders.is-empty && depth > maxDepth then throw("Too deep") 
      else if binders.is-empty then gen()
      else
        val res = binders[random-int() % binders.length].unjust
        fn() res
    GenHandler -> 
      val name = get-handler()
      val nm = new-id()
      val ret-var = new-id()
      val op-var = new-id()
      val res-var = new-id()
      val ret = bind-nm(ret-var, gen) // Add return binder
      val op = bind-nm(res-var, {bind-nm(op-var, gen)}) // Add resume and argument binders
      val body = gen()
      fn() App(Handler(HandlerNormal, HandlerNoScope, HandlerNoOverride, Nothing, Nothing, [], Nothing, 
                   Just(Lam([ValueBinder(ret-var, Nothing, Nothing, null, null)], ret(), False, null)), Nothing, 
                   [HandlerBranch(name, [ValueBinder(nm, Nothing, (), null, null)], 
                   Lam([ValueBinder(res-var, Nothing, Nothing, null, null)], op(), False, null), 
                   OpControl, null, null)],
                   null, null), 
                   [(Nothing, handles(name, body))], range/null)
    GenOp -> 
      val ops = get-all-ops()
      if ops.is-empty then gen()
      else
        val op = ops[random-int() % ops.length].unjust // TODO: Ensure argument is an 
        val arg = gen()
        fn() 
          needs-handler(op)
          App(Var(op, False, null), [(Nothing, arg())], null)
    GenLet -> 
      val x = new-id()
      // with maybe-gen-hnd
      val bind = gen()
      val body = 
           with bind-nm(x)
           gen()
      fn() let(x, bind()) fn(_) body()
    GenLam -> 
      val x = new-id()
      val bod = bind-nm(x, gen)
      fn() Lam([ValueBinder(x, Nothing, Nothing, null, null)], bod(), False, null)
    GenApp -> 
      // with maybe-gen-hnd
      val f = gen()
      val arg = gen()
      fn() App(f(), [(Nothing, arg())], null)

fun main()
  var prog := ""
  var ops := []
  var id := 0
  with fun get-all-ops() ops
  with handler
    fun rand-e()
      val r = random-int() % 4
      if r < 1 then GenVar
      else if r < 2 then GenLet
      else if r < 3 then GenApp
      else GenLam
      // else if r < 16 then GenLam
      // else if r < 17 then GenHandler
      // else GenOp
    val depth = 0
  with handler
    return(_) prog
    fun add-handler(h, op)
      prog := prog ++ "\n" ++ h.show
      ops := Cons(op, ops)
    fun add-def(d) prog := prog ++ "\n" ++ d.show
    fun get-handler() ops[random-int() % ops.length].unjust
    fun new-id()
      val ident = "x" ++ id.show
      id := id + 1
      ident.new-name
  for(1) fn(_)
    val op = new-id()
    add-handler(defh(new-id(), [(OpFun, op, [(new-id(), tint())], tint())]), op)
  for(1) fn(_) 
    var hnds := []
    with fun needs-handler(op) hnds := Cons(op, hnds)
    with fun get-binders() []
    val def = def-fn(("analyze-" ++ new-id().nameStem).new-name, [], {gen()().finish-handlers(hnds)})
    if hnds.is-empty then add-def(def.pretty)
    else ()

fun example2()
  val ex = 
    with def-fn("main".name, [])
    with x <- let("x".name, 1.expr)
    x + 1.expr
  defh("opx".name, [(OpFun, "xe".name, [("a".name, tstring())], tint())]).println
  ex.pretty.println
