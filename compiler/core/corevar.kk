// Ported as of 2026-01-18; approx upstream baseline commit 94c4762 of Core/CoreVar.hs (backfilled 2026-07-23)
module compiler/core/corevar

import compiler/type/type
import std/core/undiv
import std/core/unsafe
import compiler/common/syntax
import compiler/common/range
import compiler/core/core
import std/data/rb-set
import std/data/sort
import compiler/common/name
import compiler/type/typevar
import std/data/rb-map
import compiler/common/name-collections

pub infixr 5 (|->)

// Unlike core.kk's simple `add-type-apps`,
// applying type arguments to a `TypeLam` substitutes DIRECTLY (beta) instead
// of building `TypeApp(TypeLam ...)`. Instantiation (type/operations,
// type/unify subsume) relies on this: without it, instantiating an
// already-generalized recursive def wraps its core in `TypeApp(TypeLam ...)`
// and RE-generalization then nests a second TypeLam -- the def no longer
// matches `TypeLam(tvs, Lam ...)` so def-level simplify eta-contracts the
// body away and the C backend crashes with "gen-fun-sig: expected lambda"
// (cgen/mutual1, cgen/returnscrut, medium/garcia-wachs).
pub fun beta/add-type-apps(ts: list<type-var>, e: expr): total expr
  match (ts, e)
    (Nil, _) -> e
    (_, TypeApp(e', args)) -> TypeApp(e', args ++ ts.map(TVar))
    (Cons(t, ts'), TypeLam(Cons(tpar, tpars), body)) ->
      beta/add-type-apps(ts'.pretend-decreasing, add-type-lambdas(tpars, unsafe-total({new/sub([(tpar, TVar(t))]).expr/substitute(body)})))
    _ -> TypeApp(e, ts.map(TVar))

// upstream `tnamesList` = `S.toList`: name order, which the set iterates in
pub fun tnames-list(ts: rbset<tName>): list<tName>
  ts.list

// Type-variable id order (`tvs` is an int-map whose `list`
// is not guaranteed ascending, so this one still sorts)

pub fun tvs-sorted(ts: tvs): list<type-var>
  ts.list.sort(?(<) = fn(a: type-var, b: type-var) a.tid < b.tid)

pub fun is-top-level(d: def)
  val freeVar = d.defExpr.free-vars.list.map(fn(TName(nm)) nm).filter(fn(nm) !nm.is-qualified && d.def-name.unqualify != nm)
  val freeTv = d.defExpr.free-type-vars
  freeVar.is-nil && freeTv.is-empty

pub fun expr/free-locals(e: expr)
  e.free-vars.filter(fn(TName(nm)) !nm.is-qualified)

pub fun branch/free-locals(b: branch)
  b.free-vars.filter(fn(TName(nm)) !nm.is-qualified)

pub fun list/free-vars(l: list<a>, ?free-vars: (a) -> _ rbset<tName>): _ rbset<tName>
  l.map(free-vars).unions

pub fun expr/free-vars(e0: expr): _ rbset<tName>
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

pub fun branch/free-vars(Branch(patterns, guards): branch): _ rbset<tName>
  guards.map(free-vars).unions - patterns.map(bound-vars).unions

pub fun guard/free-vars(Guard(test, expr): guard): _ rbset<tName>
  test.free-vars + expr.free-vars

pub fun pat/bound-vars(p: pattern): _ rbset<tName>
  match p
    PatCon(_, args) -> args.map(bound-vars).unions
    PatVar(tn, subpat) -> (tnames/empty + tn) + subpat.bound-vars // also bind sub-pattern vars
    PatLit -> tnames/empty
    PatWild -> tnames/empty

pub fun dgs/free-vars(def-groups: def-groups, e: expr): _ rbset<tName>
  match def-groups
    [] -> e.free-vars
    Cons(dg, dgs) -> 
      val fv1: rbset<tName> = (free-vars(dgs, e) - dg.bound-vars)
      dg.free-vars + fv1

// A DefRec subtracts its OWN bound names (the recursive defs reference themselves/each other; those are not free).
pub fun dg/free-vars(defg: def-group): _ rbset<tName>
  match defg
    DefRec(defs) -> defs.map(free-vars).unions - defs.map(bound-vars).unions
    DefNonRec(d) -> d.free-vars

pub fun dg/bound-vars(defg: def-group): _ rbset<tName>
  defg.flatten.map(bound-vars).unions

pub fun def/bound-vars(Def(nm, tp): def): _ rbset<tName>
  tnames/empty + TName(nm, tp)

pub fun def/free-vars(Def(_, _, e): def): _ rbset<tName>
  e.free-vars

// Term substitutions
pub noinline fun list/(|->)(sub: list<(tName, expr)>, l: list<a>, ?(|->): (list<(tName, expr)>, a) -> _ a): _ list<a>
  l.map(sub |-> _)

pub fun dg/(|->)(sub: list<(tName, expr)>, dg: def-group): _ def-group
  match dg
    DefRec(defs) -> DefRec(sub |-> defs)
    DefNonRec(def) -> DefNonRec(sub |-> def)

pub fun def/(|->)(sub: list<(tName, expr)>, d: def): _ def
  val dname = d.def-name
  val sub' = sub.filter(fn((nm, _)) nm.get-name != dname)
  d(defExpr = sub' |-> d.defExpr)

pub fun expr/(|->)(sub: list<(tName, expr)>, ex: expr): _ expr
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
      val (dgs', sub') = subst-def-groups(sub, dgs)
      Let(dgs', sub' |-> e)
    Case(exprs, bs) -> Case(sub |-> exprs, sub |-> bs)

// Substitute into a let's definition groups in order: a group that binds a name
// shadows it for the groups after it and for the body, so the substitution stops
// there. Names are not always unique (a fresh name can coincide with a binder
// minted by another counter), and substituting past a rebinding captures its
// occurrences. Returns the substitution left for the body.
fun subst-def-groups(sub: list<(tName, expr)>, dgs: list<def-group>): _ (list<def-group>, list<(tName, expr)>)
  match dgs
    Nil -> (Nil, sub)
    Cons(dg, rest) ->
      val dg' = sub.dg/(|->)(dg)
      val names = [dg].flatten.map(def-name)
      val sub1 = sub.filter(fn((nm, _)) !names.any(_ == nm.get-name))
      val (rest', sub2) = subst-def-groups(sub1, rest)
      (Cons(dg', rest'), sub2)

pub noinline fun branch/(|->)(sub: list<(tName, expr)>, Branch(patts, guards): branch): _ branch
  val bvpat = patts.map(bound-vars).unions
  val sub' = sub.filter(fn((nm, _)) !bvpat.member(nm))
  Branch(patts, sub' |-> guards)

pub noinline fun guard/(|->)(sub: list<(tName, expr)>, Guard(test, expr): guard): _ guard
  Guard(sub |-> test, sub |-> expr)

//--------------------------------------------------------------------------
// Module-dependency extraction (upstream Core/CoreVar.hs
// extractDepsFromInlineDefs / extractDepsFromDefs / extractDepsFromSignatures)
//--------------------------------------------------------------------------

// free type constructors of a core expression (upstream `ftc` via HasTypeVar:
// collects the type constructors of every type embedded in the expression)
pub fun expr/free-type-constructors(ex: expr): pure type-cons
  match ex
    Lam(pars, eff, e) ->
      (pars.map(type-of) ++ [eff]).free-type-constructors.union(e.pretend-decreasing.free-type-constructors)
    Var(tn) -> tn.type-of.free-type-constructors
    Con(tn) -> tn.type-of.free-type-constructors
    App(f, args) -> Cons(f, args).map(fn(e) e.pretend-decreasing.expr/free-type-constructors).unions
    TypeLam(_, e) -> e.pretend-decreasing.free-type-constructors
    TypeApp(e, tps) -> e.pretend-decreasing.expr/free-type-constructors.union(tps.free-type-constructors)
    ELit -> rb-set/empty()
    Let(dgs, e) ->
      dgs.flatten.map(fn(d) d.ktype.free-type-constructors.union(d.defExpr.pretend-decreasing.expr/free-type-constructors)).unions
        .union(e.pretend-decreasing.free-type-constructors)
    Case(exprs, branches) ->
      exprs.map(fn(e) e.pretend-decreasing.expr/free-type-constructors).unions.union(
        branches.map(fn(b) b.pretend-decreasing.branch/free-type-constructors).unions)

fun branch/free-type-constructors(Branch(pats, guards): branch): pure type-cons
  pats.map(pattern/free-type-constructors).unions.union(
    guards.map(fn(Guard(t, e)) t.expr/free-type-constructors.union(e.expr/free-type-constructors)).unions)

fun pattern/free-type-constructors(pat: pattern): pure type-cons
  match pat
    PatCon(tname, pats, _, targs, _, tres) ->
      tname.type-of.free-type-constructors
        .union((targs ++ [tres]).free-type-constructors)
        .union(pats.map(fn(p) p.pretend-decreasing.pattern/free-type-constructors).unions)
    PatVar(tname, p) -> tname.type-of.free-type-constructors.union(p.pretend-decreasing.pattern/free-type-constructors)
    PatWild -> rb-set/empty()
    PatLit -> rb-set/empty()

fun deps-from-expr(e: expr): pure list<name>
  val varmods = e.free-vars.list.map(fn(tn) tn.get-name.qualifier)
  val tconmods = e.expr/free-type-constructors.list.map(fn(tc) tc.name.qualifier)
  (varmods ++ tconmods).filter(fn(nm) !nm.is-nil)

pub fun names-nub(ns: list<name>): list<name>
  ns.foldl([]) fn(acc, nm)
    if acc.any(fn(x) x == nm) then acc else Cons(nm, acc)

pub fun extract-deps-from-inline-defs(inlineDefs: list<inline-def>): pure list<name>
  inlineDefs.map(fn(d) d.expr.deps-from-expr).concat.names-nub

pub fun extract-deps-from-defs(dgs: def-groups): pure list<name>
  dgs.flatten.map(fn(d) d.defExpr.deps-from-expr).concat.names-nub

pub fun extract-deps-from-signatures(c: core): pure list<name>
  c.extract-signatures.free-type-constructors.list.map(fn(tc) tc.name.qualifier).filter(fn(nm) !nm.is-nil).names-nub
