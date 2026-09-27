// Ported as of 2026-01-29; approx upstream baseline commit d114919 of Core/UnReturn.hs (backfilled 2026-07-23)
module compiler/core/unreturn

import compiler/core/core
import compiler/common/name
import compiler/common/name-prim
import compiler/platform/config
import compiler/common/failure
import compiler/type/type
import compiler/common/syntax
import compiler/common/range
import compiler/common/unique

value type kexpr
  U(e: expr) // unchanged
  I(e: expr) // identity
  R(e: expr) // returned
  F(e: ((expr -> ur-eff expr) -> ur-eff expr)) // CPS Transformed, needs continuation

pub fun unreturn()
  with handler
    val current-eff = Nothing
  set-core-defs(tdgs/unreturn(get-core-defs()))

pub fun tdgs/unreturn(def-groups: list<def-group>): _ list<def-group>
  def-groups.map(tdg/unreturn)

pub fun tdg/unreturn(dg: def-group)
  match dg
    DefRec(defs) -> DefRec(defs.map(topdef/unreturn))
    DefNonRec(d) -> DefNonRec(d.topdef/unreturn)

pub fun topdef/unreturn(d: def): _ def
  val (make-def, kexpr) = d.def/unreturn
  match kexpr
    U(e) -> make-def(e)
    I(e) -> make-def(e)
    _ -> failure/fail("core/unreturn urTopDef: should not happen: return inside top level definition")

effect ur
  val current-eff: maybe<keffect>

alias ur-eff = <ur,comp-flags,pure,core-phase,unique>

fun current-effect(eff: keffect, k: () -> _ a): _ a
  with override
    val current-eff = Just(eff)
  k()

pub fun def/unreturn(d: def): ur-eff (expr -> def, kexpr)
  val kexpr = d.defExpr.expr/unreturn
  (fn(e) d(defExpr = e), kexpr)

pub fun expr/unreturn(e: expr): ur-eff kexpr
  match e
    // lambdas and type lambdas use UnK to contain returns inside their body
    Lam(pars, eff, body) ->
      with current-effect(eff)
      e.emapUnK(fn(b) Lam(pars, eff, b), body.expr/unreturn)
    TypeLam(tvars, body) ->
      e.emapUnK(fn(b) TypeLam(tvars, b), body.expr/unreturn)
    // Type applications may contain return (? todo check this)
    TypeApp(body, targs) ->
      Just(e).emapK(fn(b) TypeApp(b, targs), body.expr/unreturn)
    // bindings
    Let(defgs, body) ->
      e.let/unreturn(defgs, body.expr/unreturn)
    // case: scrutinee cannot contain return due to grammar
    Case(scruts, branches) ->
      e.case/unreturn(scruts, branches)
    // return
    App(Var(v), [arg]) | v.get-name == nameReturn -> R(arg.unreturn-pure)
    // pure expressions that do not contain return (as checked by the grammar)
    App(f, args) ->
      I(App(f.unreturn-pure, args.map(unreturn-pure)))
    _ -> U(e)

fun unreturn-pure(e: expr): ur-eff expr
  e.expr/unreturn.to-expr

fun to-expr(k: kexpr)
  match k
    U(org) -> org
    I(e') -> e'
    _ -> failure/fail("core/unreturn unreturn-pure: should not happen: return inside pure expression")

alias alter<x> = (x -> ur-eff def-group)
alias maybechanged = either<(alter<list<expr>>, list<kexpr>), (alter<expr>, kexpr)>

pub fun let/unreturn(org: expr, defgroups: list<def-group>, kbody: kexpr): ur-eff kexpr
  fun dg/unreturn(dg: def-group)
    match dg
      DefRec(dfs) ->
        val (mkDefs, kexprs) = dfs.map(def/unreturn).unzip
        Left((fn(es) DefRec(mkDefs.zipwith(es, fn(make, d) make(d))), kexprs))
      DefNonRec(d) ->
        val (mkDef, kexpr) = d.def/unreturn
        Right((fn(e) DefNonRec(mkDef(e)), kexpr))
  fun is-unchanged(e: maybechanged): bool
    match e
      Left((_, dgs)) -> dgs.all(is-u)
      Right((_, dg)) -> dg.is-u
  fun add-def(d: def-group, e: expr): expr
    match e
      Let(defs, e') -> Let(Cons(d, defs), e')
      _ -> Let([d], e)
  fun fold(l: list<maybechanged>, kexpr: kexpr)
    match l
      Nil -> kexpr
      Cons(Left((mkDefGroup, kexprs)), kdefgs) -> 
        kdefgs.fold(Nothing.emapK(fn(e) add-def(mkDefGroup(kexprs.map(to-expr)), e), kexpr))
      Cons(Right((mkDefGroup, kdefexpr)), kdefgs) -> 
        fun combine(e1: expr, e2: expr)
          add-def(mkDefGroup(e1), e2)
        kdefgs.fold(Nothing.bind(combine, kdefexpr, kexpr))
  val kdefgs = defgroups.map(dg/unreturn)
  if kdefgs.all(is-unchanged) then
    Just(org).emapK(fn(e) make-let(defgroups, e), kbody)
  else kdefgs.reverse.fold(kbody)

pub fun case/unreturn(org: expr, scruts: list<expr>, branches: list<branch>): ur-eff kexpr
  val (mkBranches, kexprss) = branches.map(branch/unreturn).unzip
  val ks = kexprss.concat
  if ks.all(is-u) then U(org)
  elif ks.all(fn(k) k.is-u || k.is-i) then
    I(Case(scruts, kexprss.zipwith(mkBranches, fn(kexprs, mk) mk(kexprs.map(to-expr)))))
  elif ks.filter(fn(k) !k.is-r).length <= 1 then
    // Directly inline
    fun f(c)
      Case(scruts, kexprss.zipwith(mkBranches, fn(kexprs, mk) mk(kexprs.map(fn(k) applyK(c, k)))))
    F(f)
  else
    // generate a local continuation function
    val name = "cont".unique-name
    val pname = "x".unique-name
    val eff = current-eff.unjust
    val tp = org.type-of
    val parName = TName(pname, tp)
    val parVar = Var(parName, InfoNone)
    fun f(c)
      val lam = Lam([parName], eff, c(parVar))
      val defTp = lam.type-of
      val def = Def(name, defTp, lam, Private, DefFun([Own]), InlineAuto, range/null, "")
      val defVar = Var(TName(name, defTp), InfoNone)
      fun app(e)
        App(defVar, [e])
      // upstream: `makeLet [DefNonRec def] $ Case ...` -- the continuation
      // def must be BOUND; without the Let the generated `@cont-x` var
      // dangled free in the def (parc then dup'd an unbound name and the C
      // backend crashed with "gen-fun-sig: expected lambda" on the wrapper)
      make-let([DefNonRec(def)],
        Case(scruts, kexprss.zipwith(mkBranches, fn(kexprs, mk) mk(kexprs.map(fn(k) applyK(app, k))))))
    F(f)

pub fun branch/unreturn(b: branch)
  val (mkGuards, kexprs) = b.guards.map(guard/unreturn).unzip
  (fn(es) Branch(b.patterns, mkGuards.zipwith(es, fn(make, e) make(e))), kexprs)

pub fun guard/unreturn(g: guard)
  val kexpr = g.body.expr/unreturn
  (fn(e) Guard(g.test, e), kexpr)

fun applyK(c: expr -> _ expr, k: kexpr): _ expr
  match k
    U(e) -> c(e)
    I(e) -> c(e)
    R(e) -> e // If returning, the continuation is ignored
    F(f) -> f(c)

fun emapUnK(org: expr, g, k)
  match k
    U(_) -> U(org)
    I(e) -> I(g(e))
    R(r) -> I(g(r))
    F(f) -> I(g(f(fn(i) i)))

fun emapK(mbOrg: maybe<expr>, g, k)
  match k
    U(e) -> match mbOrg
      Nothing -> I(g(e))
      Just(org) -> U(org)
    I(e) -> I(g(e))
    R(r) -> R(g(r))
    F(f) -> F(fn(c) g(f(c)))

fun bind(mbOrg: maybe<expr>, combine, ke1, ke2)
  match (ke1, ke2)
    (R(r), _) -> R(r)
    (U(a), k) -> match k
      U(b) -> match mbOrg
        Nothing -> I(combine(a, b))
        Just(org) -> U(org)
      I(e) -> I(combine(a, e))
      R(r) -> R(combine(a, r))
      F(g) -> F(fn(c) combine(a, g(c)))
    (I(e1), k) -> match k
      U(b) -> I(combine(e1, b))
      I(e2) -> I(combine(e1, e2))
      R(r) -> R(combine(e1, r))
      F(g) -> F(fn(c) combine(e1, g(c)))
    (F(f), k) -> match k
      U(b) -> F(fn(c) f(fn(e) combine(e, c(b))))
      I(e) -> F(fn(c) f(fn(e1) combine(e1, c(e))))
      R(r) -> R(f(fn(e) combine(e, r)))
      F(g) -> F(fn(c) f(fn(e) combine(e, g(c))))



  


