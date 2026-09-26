// Updated as of 7/23/26: Commit dd91082
module compiler/core/monadic-lift

import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/syntax
import compiler/type/type
import compiler/kind/kind
import compiler/core/core
import compiler/core/corevar
import compiler/type/typevar
import std/data/rb-set
import compiler/platform/config
import compiler/common/unique

pub fun monadic-lift()
  with run-lifted()
  set-core-defs(get-core-defs().lift-defgroups(True))

//   transform definition groups
fun lift-defgroups(dgs: def-groups, topLevel: bool)
  dgs.map(_.lift-defgroup(topLevel)).concat

effect lifted
  fun emit(dg: def-group): ()
  fun collect(): list<def-group>
  val currentDef: list<def>

fun run-lifted(f: () -> _ a): _ a 
  // `dgs` accumulates by prepending, so `collect` must REVERSE to hand back emission order.
  // Order is load-bearing: `lift-expr-inl` recurses into the continuation body
  // BEFORE lifting the enclosing continuation, so an inner lift is emitted
  // first and the outer lift's body refers to it. Handing them back reversed
  // puts the outer lift ahead of the inner one, and `inl-def-groups` -- which
  // only registers a group as an inline candidate AFTER processing it -- can
  // then never inline the inner lift into the outer one.
  var dgs := []
  with handler
    fun emit(dg) 
      dgs := Cons(dg, dgs)
    fun collect() 
      val dgs' = dgs.reverse
      dgs := []
      dgs'
    val currentDef = Nil
  f()

// transform definition groups
fun lift-defgroup(dg: def-group, topLevel: bool)
  if topLevel then
    match dg
      DefNonRec(d) ->
        val d' = d.lift-def(topLevel)
        collect() ++ [DefNonRec(d')]
      DefRec(ds) ->
        val ds' = ds.map(_.lift-def(topLevel))
        // `[DefRec (groups' ++
        // defs')]` -- lifted wrapper defs go INTO the SAME DefRec as the
        // original defs (not as separate preceding top-level groups), since
        // a wrapper generated from within a recursive def's own body calls
        // back into that def (and vice versa): they're genuinely one mutually
        // recursive group. Keeping them as separate groups (the port's
        // previous `collect() ++ [DefRec(ds')]`) broke the C backend's
        // per-DefRec forward-declare-all-then-define-all invariant, since
        // the wrapper's (now-standalone, non-recursive) group got emitted --
        // body and all -- before the real DefRec group whose signature it
        // needed was even forward-declared.
        [DefRec(collect().flatten ++ ds')]
  else
    match dg
      DefNonRec(d) -> [DefNonRec(d.lift-def(topLevel))]
      DefRec(ds) -> [DefRec(ds.map(_.lift-def(topLevel)))]
  
fun lift-def(d: def, topLevel: bool)
  with override
    val currentDef = Cons(d, currentDef)
    fun emit(dg) emit(dg)
    fun collect() collect()
  val expr' = if topLevel then d.defExpr.lift-expr-inl(topLevel).snd else d.defExpr.lift-expr(topLevel)
  d(defExpr = expr')

// Transform expressions

fun lift-expr-inl(expr': expr, topLevel: bool): _ (expr, expr)
  match expr'
    App(tpapp as TypeApp(Var(TName(nameB)), [tpArg, tpRes, tpEff]), [bexpr, Lam([arg], eff, body)]) | nameB == nameBind ->
      val (body', ibody') = body.lift-expr-inl(False)
      val bexpr' = bexpr.lift-expr(False)
      val f = Lam([arg], eff, body').lift-local-fun(typeTotal)
      val bind = App(tpapp, [bexpr', f])
      val a = TypeVar(0, kindStar, Bound)
      val b = TypeVar(1, kindStar, Bound)
      val e = TypeVar(2, kindEffect, Bound)
      val typeBind2 = TForAll([a, b, e], 
        TFun([(nil, TVar(a)), 
                 (nil, TFun([(nil, TVar(a))], TVar(e), TVar(b))),
                 (nil, TFun([(nil, TVar(a))], TVar(e), TVar(b))),
                 ], TVar(e), TVar(b)))
      val ibind = App(TypeApp(Var(TName(nameBind2, typeBind2), InfoArity(3, 3)), [tpArg, tpRes, tpEff]), [bexpr', f, (Lam([arg], eff, ibody'))])
      (bind, ibind)
    Let(defgs, body) ->
      val defgs' = defgs.lift-defgroups(False)
      val (body', ibody') = body.lift-expr-inl(False)
      (Let(defgs', body'), Let(defgs', ibody'))
    Case(exprs, bs) ->
      val exprs' = exprs.map(_.lift-expr(False))
      val (bs', ibs') = bs.map(liftBranchInl).unzip
      (Case(exprs', bs'), Case(exprs', ibs'))
    TypeLam(tvars, body) ->
      val (body', ibody') = body.lift-expr-inl(topLevel)
      (TypeLam(tvars, body'), TypeLam(tvars, ibody'))
    TypeApp(body, tps) ->
      val (body', ibody') = body.lift-expr-inl(topLevel)
      (TypeApp(body', tps), TypeApp(ibody', tps))
    Lam(args, eff, body) ->
      val (body', ibody') = body.lift-expr-inl(False)
      (Lam(args, eff, body'), Lam(args, eff, ibody'))
    _ ->
      val newE = expr'.lift-expr(topLevel)
      (newE, newE)

fun liftBranchInl(Branch(pat, guards): branch): _ (branch, branch)
  val (guards', iguards') = guards.map(liftGuardInl).unzip
  (Branch(pat, guards'), Branch(pat, iguards'))

fun liftGuardInl(Guard(guard, body): guard)
  val guard' = guard.lift-expr(False)
  val (body', ibody') = body.lift-expr-inl(False)
  (Guard(guard', body'), Guard(guard', ibody'))

fun lift-expr(expr': expr, topLevel: bool): _ expr
  match expr'
    App(tpApp as TypeApp(Var(TName(nameB))), [bexpr, Lam([arg], eff, body)]) | nameB == nameBind ->
      val body' = body.lift-expr(False)
      val bexpr' = bexpr.lift-expr(False)
      val f = Lam([arg], eff, body').lift-local-fun(typeTotal)
      App(tpApp, [bexpr', f])
    App(f, args) ->
      val f' = f.lift-expr(False)
      val args' = args.map(_.lift-expr(False))
      App(f', args')
    Lam(args, eff, body) ->
      val body' = body.lift-expr(False)
      Lam(args, eff, body')
    Let(defgs, body) ->
      val defgs' = defgs.lift-defgroups(False)
      val body' = body.lift-expr(False)
      Let(defgs', body')
    Case(exprs, bs) ->
      val exprs' = exprs.map(_.lift-expr(False))
      val bs' = bs.map(liftBranch)
      Case(exprs', bs')
    TypeLam(tvars, body) ->
      val body' = body.lift-expr(topLevel)
      TypeLam(tvars, body')
    TypeApp(body, tps) ->
      val body' = body.lift-expr(topLevel)
      TypeApp(body', tps)
    _ -> expr'

fun lift-local-fun(e: expr, eff: keffect)
  // upstream: `tnamesList (freeLocals expr)` / `tvsList (ftv expr)` -- sorted
  val fvs = e.free-locals.tnames-list
  val tvs = e.free-type-vars.tvs-sorted
  val (expr2, lift-def) = e.make-def(fvs, tvs)
  emit(DefNonRec(lift-def))
  expr2

fun make-def(e: expr, fvs: list<tName>, tvs: list<type-var>)
    
  fun unwild(TName(name, tp): tName)
    TName(if name.nameStem == "" || name.is-wildcard then name.un-wildcard else name, tp)
  val (tpars, pars, eff, body) = match e
    TypeLam(tpars, Lam(pars, eff, lbody)) -> (tpars, pars.map(unwild), eff, lbody)
    Lam(pars, eff, lbody) -> ([], pars.map(unwild), eff, lbody)
    _ -> failure/fail("core/monadic-lift make-def lifting non function? " ++ e.show)
  val alltpars = tvs ++ tpars
  val allpars = fvs ++ pars
  val allargs = allpars.map(Var(_, InfoNone))
  val liftedFun = add-type-lambdas(alltpars, Lam(allpars, eff, body))
  val liftedTp = liftedFun.type-of
  fun lifted-def(nm, inl)
    Def(nm, liftedTp, liftedFun, Private, DefFun([]), InlineAuto, range/null, "// monadic lift")
  fun fun-expr(n: name)
    Var(TName(n, liftedTp), InfoArity(alltpars.length, allargs.length))
  fun eta-expr(n: name)
    match (tvs, fvs)
      (Nil, Nil) -> n.fun-expr
      _ -> add-type-lambdas(tpars, Lam(pars, eff, App(beta/add-type-apps(alltpars, fun-expr(n)), allargs)))
  val (name, inl) = unique-name-current-def()
  (name.eta-expr, name.lifted-def(inl))
  
// branches
fun liftBranch(Branch(pat, guards): branch)
  val guards' = guards.map(liftGuard)
  Branch(pat, guards')

fun liftGuard(Guard(guard, body): guard)
  val guard' = guard.lift-expr(False)
  val body' = body.lift-expr(False)
  Guard(guard', body')

fun unique-name-current-def()
  val d = currentDef.last.unjust
  val i = new-unique()
  val udef-name = to-hidden-unique-name(i, "mlift", d.def-name)
  (udef-name, d.kinline)