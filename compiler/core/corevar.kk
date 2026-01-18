import compiler/type/type
import compiler/common/syntax
import compiler/common/range
import compiler/core/core
import std/data/linearset
import std/data/linearmap
import compiler/common/name
import compiler/type/typevar

pub infixr 5 (|->)

fun is-top-level(d: def)
  val freeVar = d.defExpr.free-vars.list.map(fn(TName(nm)) nm).filter(fn(nm) !nm.is-qualified && d.def-name.unqualify != nm)
  val freeTv = d.defExpr.free-type-vars
  freeVar.is-nil && freeTv.is-empty

fun expr/free-locals(e: expr)
  e.free-vars.filter(fn(TName(nm)) !nm.is-qualified)

fun branch/free-locals(b: branch)
  b.free-vars.filter(fn(TName(nm)) !nm.is-qualified)

fun list/free-vars(l: list<a>, ?free-vars: (a) -> _ linearSet<tName>): _ linearSet<tName>
  l.map(free-vars).unions

fun expr/free-vars(e0: expr): _ linearSet<tName>
  match e0
    Lam(tnames, _, e) -> e.free-vars - tnames
    Var(tn) -> tnames/empty + tn
    App(e1, e2) -> e1.free-vars + e2.free-vars
    TypeLam(_, e) -> e.free-vars
    TypeApp(e) -> e.free-vars
    Con -> tnames/empty
    ELit -> tnames/empty
    Let(dfgps, e) -> free-vars(dfgps, e)
    Case(exprs, bs) -> exprs.free-vars + bs.map(free-vars).unions

fun branch/free-vars(Branch(patterns, guards): branch): _ linearSet<tName>
  guards.map(free-vars).unions - patterns.map(bound-vars).unions

fun guard/free-vars(Guard(test, expr): guard): _ linearSet<tName>
  test.free-vars + expr.free-vars

fun pat/bound-vars(p: pattern): _ linearSet<tName>
  match p
    PatCon(_, args) -> args.map(bound-vars).unions
    PatVar(tn) -> tnames/empty + tn
    PatLit -> tnames/empty
    PatWild -> tnames/empty

fun dgs/free-vars(def-groups: def-groups, e: expr): _ linearSet<tName>
  match def-groups
    [] -> e.free-vars
    Cons(dg, dgs) -> 
      val fv1: linearSet<tName> = (free-vars(dgs, e) - dg.bound-vars)
      dg.free-vars + fv1

fun dg/free-vars(defg: def-group): _ linearSet<tName>
  defg.flatten.map(free-vars).unions

fun dg/bound-vars(defg: def-group): _ linearSet<tName>
  defg.flatten.map(bound-vars).unions

fun def/bound-vars(Def(nm, tp): def): _ linearSet<tName>
  LinearSet([TName(nm, tp)])

fun def/free-vars(Def(_, _, e): def): _ linearSet<tName>
  e.free-vars

// Term substitutions
noinline fun list/(|->)(sub: list<(tName, expr)>, l: list<a>, ?(|->): (list<(tName, expr)>, a) -> _ a): _ list<a>
  l.map(sub |-> _)

fun dg/(|->)(sub: list<(tName, expr)>, dg: def-group): _ def-group
  match dg
    DefRec(defs) -> DefRec(sub |-> defs)
    DefNonRec(def) -> DefNonRec(sub |-> def)

fun def/(|->)(sub: list<(tName, expr)>, d: def): _ def
  val dname = d.def-name
  val sub' = sub.filter(fn((nm, _)) nm.get-name != dname)
  d(defExpr = sub' |-> d.defExpr)

fun expr/(|->)(sub: list<(tName, expr)>, ex: expr): _ expr
  match ex
    Lam(tnames, eff, expr) ->
      val sub' = sub.filter(fn((nm, _)) !tnames.any(_ == nm))
      Lam(tnames, eff, sub' |-> expr)
    Var(tn, _) -> sub.lookup(_ == tn).default(ex)
    App(e1, e2) -> App(sub |-> e1, sub |-> e2)
    TypeLam(tvs, e) -> TypeLam(tvs, sub |-> e)
    TypeApp(e, tp) -> TypeApp(sub |-> e, tp)
    Con -> ex
    ELit -> ex
    Let(dgs, e) ->
      val defnames = dgs.flatten.map(def-name)
      val sub' = sub.filter(fn((nm, _)) !defnames.any(_ == nm.get-name))
      Let(sub' |-> dgs, sub' |-> e)
    Case(exprs, bs) -> Case(sub |-> exprs, sub |-> bs)

noinline fun branch/(|->)(sub: list<(tName, expr)>, Branch(patts, guards): branch): _ branch
  val bvpat = patts.map(bound-vars).unions
  val sub' = sub.filter(fn((nm, _)) !bvpat.member(nm))
  Branch(patts, sub' |-> guards)

noinline fun guard/(|->)(sub: list<(tName, expr)>, Guard(test, expr): guard): _ guard
  Guard(sub |-> test, sub |-> expr)
