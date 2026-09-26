// Ported as of 2026-01-18; approx upstream baseline commit 372ffa3 of Core/Unroll.hs (backfilled 2026-07-23)
module compiler/core/unroll

import compiler/core/core
import compiler/type/type
import compiler/common/name
import compiler/common/syntax
import compiler/common/unique
import compiler/core/corevar
import std/core/undiv
import std/data/rb-set

pub fun defs/unroll(unrollMax: int)
  set-core-defs(unroll(get-core-defs()))

pub fun dgs/unroll(def-groups: list<def-group>)
  def-groups.map(unroll).concat

pub fun dg/unroll(def-group: def-group)
  match def-group
    DefRec([d]) -> d.unroll
    _ -> [def-group]

pub fun recdef/unroll(d: def)
  val dgs = match d.defExpr
    Lam(pars, eff, body) -> unroll(d, [], pars, eff, body)
    TypeLam(tpars, Lam(pars, eff, body)) -> unroll(d, tpars, pars, eff, body)
    _ -> []
  if dgs.is-nil then [DefRec([d])] else dgs

pub fun body/unroll(d: def, tpars: list<type-var>, pars: list<tName>, eff: keffect, body: expr)
  match body
    // `Case exprs (branches@((Branch pats _):(_:_)))`: at least TWO
    // branches. Matching one-or-more is NOT equivalent: with a single branch
    // `extract-nonrec-branches`'s overlap early-exit can still return a
    // non-empty `recs`, so the `nonrecbs > 0 && recbs > 0` guard below passes
    // and a one-branch match gets unrolled into a recursive helper plus a
    // wildcard branch that calls it -- producing a function that returns the
    // wrong result.
    Case(exprs, brnchs as Cons(Branch(pats), Cons)) | pretend-no-div{exprs.all(fn(x:expr) x.cost == 0)} ->
      match extract-nonrec-branches(d.defTname, [], brnchs)
        (nonrecbs, recbs) | nonrecbs.length > 0 && recbs.length > 0 ->
          val dname = d.defTname
          val rname = dname.unique-tname-from
          val info = InfoArity(tpars.length, pars.length)
          val sub = [(dname, Var(rname, info))]
          val rdef = d(def-name=rname.get-name, defExpr=(sub |-> d.defExpr), vis=Private)
          // Using make-type-app: NO TypeApp node when there are no type args
          // (a bare `TypeApp(e, [])` around a monomorphic def later crashes
          // specialize's fn-type-params, which requires a matching TypeLam)
          val rcall = App(make-type-app(Var(rname, info), tpars.map(TVar)), pars.map(Var(_, InfoNone)))
          val wild = Branch(pats.map(fn(_) PatWild), [Guard(exprTrue, rcall)])
          fun mkFun(b)
            val l = Lam(pars, eff, b)
            if tpars.is-nil then l else TypeLam(tpars, l)
          val ddef = d(defExpr=mkFun(Case(exprs, nonrecbs ++ [wild])), kinline=InlineAlways,
            doc="// unrolling of singleton matches of " ++ rname.get-name.show ++ "\n")
          // TODO: Verbose doc
          [DefRec([rdef]), DefNonRec(ddef)]
        _ -> []
    _ -> [] // TODO: small let bindings?

fun extract-nonrec-branches(dname: tName, recs: list<branch>, bs: list<branch>): _ (list<branch>, list<branch>)
  match bs
    // Stop on end
    Nil -> (Nil, recs)
    // stop also when we cannot push down patterns of recursive branches any further
    Cons(b, _) | pretend-no-div({recs.any(_.match-can-overlap(b))}) ->
      (Nil, recs ++ [b] ++ bs)
    // otherwise
    Cons(b as Branch(pats, guards), bs') ->
      // we only want cheap matches in the unrolling, and they should be non-recursive    
      if pats.any(!_.is-singleton-pat) || guards.free-vars.member(dname) then
        // assume it contains a recursive call
        // push down as long the other patterns don't match to maximize non-recursive matches
        extract-nonrec-branches(dname, (recs ++ [b]), bs')
      else
        // surely non-recursive, keep going
        val (bs1, bs2) = extract-nonrec-branches(dname, recs, bs')
        val newb = if recs.is-nil then b else b.dont-skip
        (Cons(newb, bs1), bs2)

// is this a singleton (which can be matched without memory access)
fun is-singleton-pat(p: pattern): bool
  match p
    PatVar(_, p') -> p'.is-singleton-pat
    PatCon(_, []) -> True
    PatWild -> True
    PatLit -> True
    _ -> False

// Patterns could overlap? (can be conservative, returning True is always ok)
fun match-can-overlap(Branch(pats1, _): branch, Branch(pats2, _): branch)
  fun pat-can-overlap(pp: (pattern, pattern))
    match pp
      (PatWild, _) -> True
      (_, PatWild) -> True
      (PatVar(_, p1), p2) -> pat-can-overlap((p1, p2))
      (p1, PatVar(_, p2)) -> pat-can-overlap((p1, p2))
      (PatLit(lit1), PatLit(lit2)) -> lit1 == lit2
      (PatCon(name1), PatCon(name2)) -> name1 == name2 // TODO: make more precise
      _ -> True
  pats1.zip(pats2).any(pat-can-overlap)

fun dont-skip(Branch(pats, guards): branch)
  fun no-skip(pat: pattern)
    match pat
      PatVar(name, p) -> PatVar(name, p.no-skip)
      PatCon(patName, ps, repr, typeArgs, kexists, typeRes, info, _) ->
        PatCon(patName, ps.map(no-skip), repr, typeArgs, kexists, typeRes, info, False)
      _ -> pat 
  Branch(pats.map(no-skip), guards)

// Don't call `std/core`'s `unique()`! That makes builds non-deterministic
fun unique-tname-from(tn: tName): _ tName
  TName(to-hidden-unique-name(new-unique(), "unroll", tn.get-name), tn.type-of)
