module compiler/type/typevar

import compiler/type/type
import compiler/core/core
import compiler/type/kind
import compiler/kind/kind
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/unique
import std/data/linearset
import std/data/linearmap
import std/core/undiv
import std/core-extras // list.contains

pub infixr 5 (|->)

// The free unifiable (e.g. 'Meta') type variables
pub fun fuv(tvs: tvs): tvs
  tvs.filter(_.flavour.is-meta)
// The free 'Skolem' type variables
pub fun fsv(tvs: tvs): tvs
  tvs.filter(_.flavour.is-skolem)
// The free 'Bound' type variables
pub fun fbv(tvs: tvs): tvs
  tvs.filter(_.flavour.is-bound)
// All type variables (including the bound ones)
pub fun all-tv(a: a, ?bound-type-vars: (a) -> e tvs, ?free-type-vars: (a) -> e tvs): e tvs
  a.bound-type-vars.union(a.free-type-vars)

//--------------------------------------------------------------------------
//  Substitution
//
//  For a substitution it should hold that:
//  (s1@@s2) |-> x  <==>  s1 |-> (s2 -> x)
//
//  We can implement this by:
//  1) at composition we apply the first substitution to the other, and
//     finding an identifier is a simple lookup.
//  or,
//  2) we compose by simple union and perform a fixpoint at lookup.
//
//  We have chosen (1) here, but it can be interesting to compare
//  performance with strategy (2).
//--------------------------------------------------------------------------}

// A substitution from type variables to 'Tau's.
pub struct sub
  map: linearMap<type-var, ktype>
  tvs: tvs

pub fun sub/unsub(s: sub): linearMap<type-var, ktype>
  s.map

pub fun sub/count(Sub(sub): sub): int
  sub.list.length

pub val sub/null = Sub(LinearMap([]), LinearSet([]))

pub fun sub/is-null(Sub(sub): sub): bool
  sub.list.is-empty

pub fun new/sub(sub: list<(type-var, ktype)>): pure sub
  if sub.all(fn((tv, t)) tv.kind == t.kind) then
    Sub(LinearMap([]) + sub, sub.map(fst).tvs.union(sub.map(snd).free-type-vars))
  else
    throw("type/typevar: subNew kind mismatch")

pub fun sub/dom(Sub(sub): sub): tvs
  (sub.list.map(fst)).tvs

pub fun sub/range(s: sub): list<ktype>
  s.list.map(snd)

pub fun sub/list(s: sub): list<(type-var, ktype)>
  s.map.list

pub fun sub/common(s1: sub, s2: sub): exn list<(type-var, (tau, tau))>
  s1.list.map(fn(s) s2.lookup(s.fst).map((s.fst, (s.snd, _)))).concat-maybe

pub fun sub/single(tvar: type-var, tau: tau)
  // Top assertion is invalid; it can happen (and happens) in the CoreF typechecker when
  // typechecking (forall a. f a) with f :: forall b. b -> b, that a bound variable (b) with
  // number ID must be substituted for another bound variable (a), which *could* have the same
  // ID. If we want to avoid this, we must ensure that all IDs are distinct; in particular,
  // the IDs of built-in types such as .select must be distinct from further IDs generated
  // by the compiler.
  if tau.free-type-vars.member(tvar) then
    throw("type/typevar: subSingle: recursive type " ++ tvar.show-tv)
  if tau.kind != tvar.kind then
    throw("type/typevar: subSingle: kind mismatch " ++ tau.show ++ " " ++ tvar.show)
  Sub(LinearMap([(tvar, tau)]), free-type-vars(tau).add(tvar))

pub fun sub/lookup(Sub(s): sub, tvar: type-var): exn maybe<tau>
  match s.lookup-index(tvar) 
    Nothing -> Nothing 
    Just(i) ->
      val (ktvar, tau) = s.elem-at(i).unjust
      if !(ktvar.flavour == tvar.flavour) then 
        throw("type/typevar: subLookup: flavour mismatch " ++ ktvar.show ++ " " ++ tvar.show)
      if !(ktvar.kind == tvar.kind) then 
        throw("type/typevar: subLookup: kind mismatch " ++ ktvar.show ++ " " ++ tvar.show)
      Just(tau)

pub fun sub/remove(Sub(sub, tvs): sub, tvars: list<type-var>): sub
  Sub(sub.remove-all(tvars), tvs - tvars)

pub fun subtvs/remove(s: sub, tvars: tvs): sub
  s.remove(tvars.list)

pub fun sub/find(Sub(sub): sub, tv: type-var): exn tau
  match sub.lookup(tv)
    Nothing -> TVar(tv)
    Just(tau) -> tau

pub fun show-tv(tv: type-var): string
  tv.tid.show

// (s1 \@\@ s2) |-> x == s1 |-> (s2 |-> x)
pub fun sub/compose(sub1 as Sub(s1, tv1): sub, sub2 as Sub(_, tv2): sub): pure sub
  Sub(s1.union((sub1 |-> sub2).unsub), tv1.union(tv2)) // Assume: left biased union

pub fun sub/extend(sub: sub, tv: type-var, tau: tau): pure sub
  single(tv, tau).compose(sub)

// Insert a new substitution. (Note: breaks abstraction barrier)
pub fun sub/insert(Sub(s, tvs): sub, tvar: type-var, tau: tau)
  if tau.free-type-vars.member(tvar) then
    throw("type/typevar: insert: recursive type " ++ tvar.show-tv)
  elif !tau.is-tau then
    throw("type/typevar: insert: not a tau " ++ tau.show)
  else
    Sub(s.add(tvar, tau), union(tvs, tau.free-type-vars.add(tvar)))

pub fun sub/inserts(Sub(sub, tvars): sub, assoc: list<(type-var, tau)>)
  Sub(LinearMap([]) + assoc + sub.list, // ASSUME: left-biased union
      unions([tvars, assoc.map(fst).tvs, assoc.map(snd).free-type-vars]))


// Type variables

// A set of type variables
pub alias tvs = linearSet<type-var>
pub val tvs/empty:tvs = LinearSet([])
// All the tvar functions defer to Set functions, just alias here

pub fun tv/single(tv: type-var) 
  [tv]

pub fun new/tvs(tv: list<type-var>): tvs
  LinearSet([]) + tv

pub fun tvs/common(tvs1: tvs, tvs2: tvs): bool
  !tvs1.disjoint(tvs2)

pub fun tvslist/max(tvs: list<type-var>): int
  tvs.foldl(0, fn(n, tv) max(n, tv.tid))

pub fun tvs/max(tvs: tvs): int
  tvs.list.foldl(0, fn(n, tv) max(n, tv.tid))

// Entities with type variables

// Return the free unifiable type variables in a particular order
pub fun ofuv(x: a, ?odftv: (a) -> e list<type-var>): e list<type-var>
  x.oftv.filter(is-meta)

// Return the free type variables in a particular order
pub fun oftv(x: a, ?odftv: (a) -> e list<type-var>): e list<type-var>
  val vs = x.odftv.nub 
  fun is-special(k : kind)
    k == kindEffect || k == kindHeap || k == kindLabel || k == kind-fun(kindLabel, kindEffect)
  val (es, ws) = vs.partition(_.kind.is-special)
  ws ++ es

pub alias type-cons = linearSet<type-con>

//////////////////////////////////////////////////////////////////////////////////////////////
// Utilities for types and expressions
// Unlike in Haskell these are not in a typeclass
// As such we don't need to implement (e.g. bound type vars) 
//  for types is doesn't make sense for, even if the type requires a different type operator
/////////////////////////////////////////////////////////////////////////////////////////////

// Substitution operator
pub fun sub/(|->)(s: sub, a: a, ?substitute: (sub, a) -> e a): e a
  if s.is-null then a
  else substitute(s, a)

// Substitute a substitution into another substitution
pub fun sub/substitute(sub: sub, Sub(s, tvs2): sub): pure sub
  val Sub(_, tvs1) = sub
  Sub(s.map(fn(k, v) sub.substitute(v)), tvs1.union(tvs2))

// Type utilities for lists
pub fun list/free-type-vars(ps: list<a>, ?free-type-vars: (a) -> div tvs): div tvs
  ps.map(free-type-vars).unions
pub fun list/bound-type-vars(ps: list<a>, ?bound-type-vars: (a) -> div tvs): div tvs
  ps.map(bound-type-vars).unions
pub fun list/free-type-constructors(ps: list<a>, ?free-type-constructors: (a) -> div type-cons): div type-cons
  ps.map(free-type-constructors).unions
pub fun list/substitute(s: sub, ps: list<a>, ?substitute: (sub, a) -> pure a): pure list<a>
  ps.map(substitute(s, _))

// Type utilities for ktype
pub fun ktype/free-type-vars(tp: ktype): div tvs
  match tp
    TForAll(vars, t) -> t.free-type-vars - vars
    TFun(args, eff, res) -> (args.map(_.snd) ++ [res, eff]).free-type-vars
    TCon -> tvs/empty
    TVar(tv) -> LinearSet([tv])
    TApp(t, args) -> t.free-type-vars + args.free-type-vars
    TSyn(_, xs, t) -> t.free-type-vars + xs.free-type-vars
pub fun ktype/bound-type-vars(tp: ktype): div tvs
  match tp
    TForAll(vars, t) -> t.bound-type-vars + vars
    TFun(args, eff, res) -> (args.map(_.snd) ++ [res, eff]).bound-type-vars
    TSyn(_, _, t) -> t.bound-type-vars
    TApp(t, arg) -> t.bound-type-vars + arg.bound-type-vars
    _ -> tvs/empty
pub fun ktype/free-type-constructors(tp: ktype): div type-cons
  match tp
    TForAll(_, t) -> t.free-type-constructors
    TFun(args, eff, res) -> (args.map(_.snd) ++ [res, eff]).free-type-constructors
    TCon(c) -> LinearSet([c])
    TVar(_) -> LinearSet([])
    TApp(t, args) -> t.free-type-constructors + args.free-type-constructors
    TSyn(_, xs, t) -> t.free-type-constructors + xs.free-type-constructors
pub fun ktype/substitute(s: sub, tp: ktype): pure tau
  match tp
    TForAll(vars, t) -> TForAll(vars, s.remove(vars) |-> t) // TODO: Assertion
    TFun(args, eff, res) -> TFun(args.map(fn(a) (a.fst, s |-> a.snd)), s |-> eff, s |-> res)
    TCon -> tp
    TVar(tv) -> s.find(tv)
    TApp(t, args) -> TApp(s |-> t, args.map(s |-> _))
    TSyn(syn, xs, t) -> TSyn(syn, s |-> xs, s |-> t)

// Type utilities for expressions
pub fun exp/free-type-vars(e0: expr): div tvs
  match e0
    Lam(tn, eff, e) -> 
      val tv1: tvs = tn.free-type-vars + eff.free-type-vars
      tv1 + e.free-type-vars
    Var(tn) -> tn.free-type-vars
    App(a, b) -> a.free-type-vars + b.free-type-vars
    TypeLam(tvs, e) -> e.free-type-vars - tvs
    TypeApp(e, tp) -> e.free-type-vars + tp.free-type-vars
    Con(tn) -> tn.free-type-vars
    ELit -> tvs/empty
    Let(def-groups, e) -> def-groups.map(free-type-vars).unions + e.free-type-vars
    Case(es, bs) -> es.free-type-vars + bs.map(free-type-vars).unions
pub fun expr/substitute(s: sub, e: expr): pure expr
  match e
    Lam(tn, eff, e) -> Lam(s |-> tn, s |-> eff, s |-> e)
    Var(tn, x) -> Var(s |-> tn, x)
    App(a, b) -> App(s |-> a, s |-> b)
    TypeLam(tvs, e) -> 
      val sub' = s.remove(tvs)
      TypeLam(tvs, sub' |-> e)
    TypeApp(e, tp) -> TypeApp(s |-> e, s |-> tp)
    Con(tn, repr) -> Con(s |-> tn, repr)
    ELit(l) -> ELit(l)
    Let(def-groups, e) -> Let(def-groups.map(s |-> _), s |-> e)
    Case(es, bs) -> Case(s |-> es, bs.map(s |-> _))

// Type utilities for definition groups
pub fun dg/free-type-vars(dg: def-group): div tvs
  match dg
    DefRec(defs) -> defs.map(free-type-vars).unions
    DefNonRec(e) -> free-type-vars(e)
pub fun dg/substitute(s: sub, dg: def-group): pure def-group
  match dg
    DefRec(defs) -> DefRec(defs.map(s |-> _))
    DefNonRec(e) -> DefNonRec(s |-> e)

// Type utilities for definitions
pub fun def/free-type-vars(d: def): div tvs
  d.ktype.free-type-vars + d.defExpr.free-type-vars
pub fun def/substitute(s: sub, Def(name, scheme, expr, vis, isVal, inl, nameRng, doc): def): pure def
  Def(name, s |-> scheme, s |-> expr, vis, isVal, inl, nameRng, doc)

// Type utilities for branches
pub fun branch/free-type-vars(bs: branch): div tvs
  match bs
    Branch(p, e) -> 
      e.free-type-vars - p.bound-type-vars + p.free-type-vars
pub fun branch/substitute(s: sub, Branch(p, e): branch): pure branch
  val sub' = s.remove(p.bound-type-vars)
  Branch(s |-> p, sub' |-> e)

// Type utilities for patterns
pub fun pat/free-type-vars(p: pattern): div tvs
  match p
    PatVar(tn, pat) -> tn.free-type-vars + pat.free-type-vars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1:tvs = tn.free-type-vars + args.free-type-vars
      val tv2:tvs = tv1 + targs.free-type-vars 
      val tv3:tvs = tv2 + tres.free-type-vars
      tv3 - exists0
    PatWild -> tvs/empty
    PatLit(_) -> tvs/empty
pub fun pat/bound-type-vars(p: pattern): div tvs
  match p
    PatVar(tn, pat) -> tn.bound-type-vars + pat.bound-type-vars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1: tvs = tn.bound-type-vars + args.bound-type-vars
      val tv2: tvs = tv1 + targs.bound-type-vars
      val tv3: tvs = tv2 + tres.bound-type-vars
      tv3 + exists0.tvs
    PatWild -> tvs/empty
    PatLit(_) -> tvs/empty
pub fun pat/substitute(s: sub, p: pattern): pure pattern
  match p
    PatVar(tn, pat) -> PatVar(s |-> tn, s |-> pat)
    PatCon(tn, args, repr, targs, exists0, tres,  conInfo, skip) ->
      val sub' = s.remove(exists0)
      PatCon(s |-> tn, sub' |-> args, repr, sub' |-> targs, exists0, sub' |-> tres, conInfo, skip)
    PatWild -> PatWild
    PatLit(l) -> PatLit(l)

// Type utilities for guards
pub fun guard/free-type-vars(Guard(e, e2): guard): div tvs
  e.free-type-vars + e2.free-type-vars
pub fun guard/substitute(s: sub, Guard(e, e2): guard): pure guard
  Guard(s |-> e, s |-> e2)

// Type utilities for type names
pub fun tn/free-type-vars(TName(_, tp): tName): div tvs
  tp.free-type-vars
pub fun tn/bound-type-vars(TName(_, tp): tName): div tvs
  tp.bound-type-vars
pub fun tn/substitute(s: sub, TName(n, tp): tName): pure tName
  TName(n, s |-> tp)


pub fun ordered-free-type-vars(tp: ktype) : list<type-var>
  match tp
    TForAll(vars, tp') -> tp'.ordered-free-type-vars.filter(fn(tv) !vars.contains(tv))
    TFun(args, eff, res) -> (args.map(snd) ++ [eff, res]).flatmap(_.pretend-decreasing.ordered-free-type-vars)
    TCon() -> []
    TVar(tv) -> [tv]
    TApp(tp', args) -> tp'.ordered-free-type-vars ++ args.flatmap(_.pretend-decreasing.ordered-free-type-vars)
    TSyn(_, xs, t) -> t.ordered-free-type-vars ++ xs.flatmap(_.pretend-decreasing.ordered-free-type-vars)

// Strictly positive and negative type variables
pub fun posneg-effects(tp : ktype)
  val tvs1 = positive(tp)
  val tvs2 = negative(tp)
  val pos = tvs1 - tvs2
  val neg = tvs2 - tvs1
  (pos.filter(_.kind == kindEffect), neg.filter(_.kind == kindEffect))

pub fun positive(tp: ktype): tvs
  tp.posneg(True)
pub fun negative(tp: ktype): tvs
  tp.posneg(False)

pub fun posneg(tp: ktype, is-pos: bool): tvs
  match tp
    TForAll(vars, tp') -> tp'.posneg(is-pos) - vars
    TFun(args, eff, res) -> eff.posneg(is-pos) + res.posneg(is-pos) + args.map(_.snd.pretend-decreasing.posneg(!is-pos)).unions
    TCon() -> tvs/empty
    TVar(tv) -> if is-pos then linear-set([tv]) else tvs/empty
    TApp(tp', args) -> tp'.posneg(is-pos) + args.map(_.pretend-decreasing.posneg(is-pos)).unions
    TSyn(_, _, t) -> t.posneg(is-pos)

// Operations requiring unique

pub fun fresh-typevar(k: kind, fl: flavour)
  val idbase = match fl
    Meta -> "_v"
    Skolem -> "$v"
    Bound -> "v"
  val id = unique-id(idbase)
  TypeVar(id, k, fl)

pub fun match-types(ts1: list<ktype>, ts2: list<ktype>): pure bool
  ts1.zipwith(ts2, match-type).all(id)

pub fun typevar/match-effect(eff1: tau, eff2: tau): pure bool
  match-type(eff1.order-effect, eff2.order-effect)

pub fun match-type(tp1: ktype, tp2: ktype): pure bool
  match (tp1.expand-syn, tp2.expand-syn)
    (TForAll(vs1, t1), TForAll(vs2, t2)) -> 
      if vs1 == vs2 then eq-type(t1, t2)
      elif vs1.length == vs2.length && vs1.zipwith(vs2, fn(v1, v2) v1.kind == v2.kind).all(id) then
        val s = vs1.zip(vs2.map(TVar)).sub
        match-type(s |-> t1, t2)
      else False
    (TFun(pars1, eff1, t1), TFun(pars2, eff2, t2)) -> 
      match-types(pars1.map(snd), pars2.map(snd)) && 
        typevar/match-effect(eff1, eff2) && 
          match-type(t1, t2)
    (TCon(c1), TCon(c2)) -> c1 == c2
    (TVar(v1), TVar(v2)) -> v1 == v2
    (TApp(t1, ts1), TApp(t2, ts2)) -> t1.match-type(t2) && match-types(ts1, ts2)
    _ -> False


// For debugging purposes since we cannot include type/pretty
fun show-type-var(tv: type-var): string
  tv.tid.show ++ "::" ++ tv.kind.show

fun show-tp(tp: ktype): string
  match tp
    TVar(tv) -> show-type-var(tv)
    TCon(c) -> c.name.show ++ "::" ++ c.kind.show
    TApp(tp, args) ->
       show-tp(tp) ++ "<" ++ args.map(_.pretend-decreasing.show-tp).join(", ") ++ ">"
    TSyn(syn, xs, t) ->
      "(syn:" ++ syn.name.show ++ " :: " ++ syn.kind.show ++ "<" ++ xs.map(_.pretend-decreasing.show-tp).join(", ") ++ "> [" ++ show-tp(t) ++ "])"
    _ -> "?"