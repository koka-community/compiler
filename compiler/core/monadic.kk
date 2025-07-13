import compiler/core/core
import compiler/type/assumption
import compiler/core/corevar
import compiler/type/type
import compiler/type/typevar
import compiler/kind/kind
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name-prim
import compiler/common/name
import compiler/common/range
import compiler/platform/config

alias monadicEff = <comp-flags,monadic,uniquePhase,pure>

effect monadic
  val currentDef: list<def>
  val isInBind: bool

fun runMon(f)
  handle(f)
    val currentDef = Nil
    val isInBind = False

fun mon-transform()
  with runMon()
  set-core-defs(monDefGroups(get-core-defs()))

// tansform definition groups
fun monDefGroups(dgs: defGroups)
  dgs.map(monDefGroup)

fun monDefGroup(dg): monadicEff defGroup
  match dg
    DefRec(defs) -> DefRec(defs.map(fn(d) d.monDef(True)))
    DefNonRec(d) -> DefNonRec(d.monDef(False))

fun setCurrentDef(d, f)
  with override
    val currentDef = Cons(d, currentDef)
    val isInBind = isInBind
  f()

// transform a definition
fun monDef(d: def, isRecursive: bool)
  if !d.is-mon-def then
    d
  else
    with setCurrentDef(d)
    d(defExpr = d.defExpr.mon-expr(True)(id))

alias trans<a> = transX<a, a>
alias transX<a, b> = (a -> monadicEff b) -> monadicEff b

fun mon-expr(e: expr): monadicEff trans<expr>
  e.mon-expr(False)

fun mon-expr(expr: expr, topLevel: bool): monadicEff trans<expr>
  match expr
    // Optimized open binding
    // note: we cannot just check for `effFrom.is-mon-effect` as the effFrom
    // might be total but inside we may still need a monadic translation if `f`
    // constains handlers itself for example
    App(App(eopen as TypeApp(Var(open), [_, _, _, _]), [f]), args) | open.get-name == nameEffectOpen && !f.is-mon-expr ->
      val args' = args.map(mon-expr)
      fn(k) applies(args', fn(argss) k(App(App(eopen, [f]), argss)))
    App(TypeApp(App(eopen as TypeApp(Var(open), [_, _, _, _]), [f]), targs), args) | open.get-name == nameEffectOpen && !f.is-mon-expr ->
      val args' = args.map(mon-expr)
      fn(k) applies(args', fn(argss) k(App(TypeApp(App(eopen, [f]), targs), argss)))
    // lift open applications
    App(eopen as TypeApp(Var(open), [_, _, _, _]), [f]) | open.get-name == nameEffectOpen ->
      val f' = f.mon-expr
      fn(k) f'(fn(ff) k(App(eopen, [ff])))
    // regular cases
    Lam(args, eff, body) ->
      val body' = body.mon-expr
      fn(k) k(Lam(args, eff, body'(id)))
    App(f, args) ->
      val f' = f.mon-expr
      val args' = args.map(mon-expr)
      val ftp = f.typeOf
      val feff =
        val (_, _, rho) = ftp.split-type-scheme
        match rho.split-funType
          Just((_, feff, _)) -> feff
          _ -> fail("core/monadic app: illegal application")
      if (f.is-never-mon || !(ftp.isMonType || f.is-always-mon)) then
        fn(k) f'(fn(ff) applies(args', fn(argss) k(App(ff, argss))))
      else
        val namey = "y".unique-name
        fn(k)
          val resTp = expr.typeOf
          val tnamey = TName(namey, resTp)
          val contBody = k(Var(tnamey, InfoNone))
          val cont = match contBody
            // optimize (fun (y) {lex x = y in ..})
            Let([DefNonRec(d as Def(defExpr=Var(v)))], body) | v.get-name == namey ->
              Lam([TName(d.def-name, d.ktype)], feff, body)
            // TODO: optimize (fun (y) {lift(expr)})?
            body -> Lam([tnamey], feff, body)
          f'(fn(ff) applies(args', fn(argss) app-bind(resTp, feff, contBody.typeOf, ff, argss, cont)))
    Let(defgs, body) ->
      defgs.mon-let-groups(body)
    Case(exprs, bs) ->
      val exprs' = mon-trans(mon-expr, exprs)
      val bs' = bs.map(mon-branch)
      if !bs.any(is-mon-branch) then
        fn(k) exprs'(fn(xss) k(Case(xss, bs')))
      else
        val nameC = "c".unique-name
        val resTp = expr.typeOf
        val tnameC = TName(nameC, resTp)
        fn(k)
          val effTp = typeTotal
          val contBody = k(Var(tnameC, InfoNone))
          val cont = Lam([tnameC], effTp, contBody)
          exprs'(fn(xss) apply-bind(resTp, effTp, contBody.typeOf, Case(xss, bs'), cont))
    v as Var ->
      fn(k) k(v)
    // type application and abstraction
    TypeLam(tvars, body) ->
      val body' = body.mon-expr(topLevel)
      fn(k) body'(fn(xx) k(TypeLam(tvars, xx)))
    TypeApp(body, tps) ->
      val body' = body.mon-expr(topLevel)
      fn(k) body'(fn(xx) k(TypeApp(xx, tps)))
    _ -> fn(k) k(expr)

fun mon-branch(Branch(pat, guards): branch)
  Branch(pat, guards.map(mon-guard))

fun mon-guard(Guard(guards, body): guard)
  Guard(guards, (body.mon-expr)(id)) // guards are total!

fun mon-let-groups(dgs: defGroups, body: expr)
  match dgs
    Nil -> body.mon-expr
    Cons(dg, dgs') ->
      val dg' = dg.mon-let-group
      val expr' = dgs'.mon-let-groups(body)
      fn(k) dg'(fn(xdg) Let(xdg, expr'(k)))

fun mon-let-group(dg: defGroup)
  match dg
    DefRec(defs) ->
      val ldefs = mon-trans(fn(d) mon-let-def(True, d), defs)
      fn(k) ldefs(fn(xss) k(xss.map(fn((xds, yds, nds)) ([DefRec(xds)] ++ (if yds.is-nil then [] else [DefRec(yds)]) ++ nds.map(DefNonRec))).concat))
    DefNonRec(d) ->
      val ldef = mon-let-def(False, d)
      fn(k) ldef(fn((xds, yds, nds)) k([xds,yds,nds].concat.map(DefNonRec)))

fun mon-let-def(isRec: bool, d: def): monadicEff transX<(list<def>, list<def>, list<def>), expr>
  with setCurrentDef(d)
  val expr' = d.defExpr.mon-expr(True)
  fn(k) expr'(fn(xx:expr) k(([d(defExpr=xx)], [], [])))

fun mon-trans(f: (a -> monadicEff transX<b, c>), xs: list<a>): monadicEff transX<list<b>,c>
  match xs
    Nil -> fn(k) k([])
    Cons(x, xx) ->
      val x' = f(x)
      val xx' = mon-trans(f, xx)
      fn(k) x'(fn(y) xx'(fn(ys) k(Cons(y, ys))))

fun applies(l: list<trans<a>>, f: (list<a>) -> monadicEff a): monadicEff a
  match l
    Nil -> f([])
    Cons(x, xx) -> x(fn(y) applies(xx, fn(ys) f(Cons(y, ys))))

fun app-bind(tpArg, tpEff, tpRes, f, args, cont)
  apply-bind(tpArg, tpEff, tpRes, App(f, args), cont)

fun apply-bind(tpArg, tpEff, tpRes, expr, cont)
  match cont
    Lam([aname], _, Var(v)) | v.get-name == aname.get-name -> expr
    _ -> mon-make-bind(tpArg, tpEff, tpRes, expr, cont)

fun mon-make-bind(tpArg, tpEff, tpRes, arg, next)
  App(TypeApp(Var(TName(nameBind, typeBind), InfoArity(2, 3)), [tpArg, tpRes, tpEff]), [arg, next])

val typeBind = TForAll([tvarA, tvarB, tvarE], [], 
    TFun([
      (nil, type-yld(TVar(tvarA))), 
      (nil, TFun([(nil, TVar(tvarA))], TVar(tvarE), type-yld(TVar(tvarB))))], TVar(tvarE), type-yld(TVar(tvarB))))

fun type-yld(tp: ktype) 
  tp // TSyn(TypeSyn(nametype-yld, kind-fun(kindStar, kindStar), 0, Nothing), [tp], tp)

val tvarA = TypeVar(0, kindStar, Bound)
val tvarB = TypeVar(1, kindStar, Bound)
val tvarE = TypeVar(2, kindEffect, Bound)

// Check if expressions need monadic translation

// Some expressions always need mon translation
fun is-always-mon(e: expr)
  match e
    TypeApp(e') -> e'.is-always-mon
    Var(v) -> v.get-name == nameUnsafeTotal // TODO: remove these special cases (previously also included nameYieldOp && namePerform(0))
    _ -> False

// Some expressions never need mon translation
fun is-never-mon(e: expr)
  match e
    App(TypeApp(Var(open), [effFrom, _, _, _]), [_]) | open.get-name == nameEffectOpen ->
      effFrom.is-type-total // TODO: more cases? generally handler free
    TypeApp(e') -> e'.is-never-mon
    Var(v) -> v.get-name == nameDeref // TODO: remove special case?
    _ -> e.isTotal

// Does this definition need any mon translation (sometimes deeper inside)
fun is-mon-def(d: def)
  d.defExpr.is-mon-expr' || d.ktype.isMonType

fun is-mon-expr(e: expr): bool
  unsafe-total
    unsafe-no-div
      e.is-mon-expr'

fun is-mon-expr'(e: expr)
  match e
    App(TypeApp(Var(open), [_, effTo]), [f]) | open.get-name == nameEffectOpen ->
      effTo.is-mon-effect || f.is-mon-expr'
    App(f, args) -> Cons(f, args).any(is-mon-expr')
    Lam(_, eff, body) -> eff.is-mon-effect || body.is-mon-expr'
    TypeApp(TypeLam(_, body), targs) -> targs.any(isMonType) || body.is-mon-expr'
    TypeApp(Var, targs) -> targs.any(isMonType) || e.typeOf.isMonType
    TypeApp(body, targs) -> targs.any(isMonType) || body.is-mon-expr'
    TypeLam(_, body) -> body.is-mon-expr'
    Let(defs, body) -> defs.any(is-mon-defGroup) || body.is-mon-expr'
    Case(exprs, bs) -> exprs.any(is-mon-expr') || bs.any(is-mon-branch)
    _ -> e.typeOf.isMonType

fun is-mon-defGroup(dg: defGroup)
  match dg
    DefRec(defs) -> defs.any(is-mon-def)
    DefNonRec(d) -> is-mon-def(d)

fun is-mon-branch(Branch(_, guards): branch)
  guards.any(is-mon-guard)

fun is-mon-guard(Guard(g, e): guard)
  g.is-mon-expr' || e.is-mon-expr'

