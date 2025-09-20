import compiler/type/type
import compiler/core/core
import compiler/type/kind
import compiler/kind/kind
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import std/data/linearset
import std/data/linearmap
import std/core/undiv

pub infixr 5 (|->)

// The free unifiable (e.g. 'Meta') type variables
fun fuv(tvs: tvs): tvs
  tvs.filter(fn(tv) tv.flavour.is-meta)
// The free 'Skolem' type variables
fun fsv(tvs: tvs): tvs
  tvs.filter(fn(tv) tv.flavour.is-skolem)
// The free 'Bound' type variables
fun fbv(tvs: tvs): tvs
  tvs.filter(fn(tv) tv.flavour.is-bound)
// All type variables (including the bound ones)
fun all-tv(a: a, ?bound-type-vars: (a) -> e tvs, ?free-type-vars: (a) -> e tvs): e tvs
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
value struct sub
  map: linearMap<typeVar, ktype>
  tvs: tvs

fun sub/unsub(s: sub): linearMap<typeVar, ktype>
  s.map

fun sub/count(Sub(sub): sub): int
  sub.list.length

val sub/null = Sub(LinearMap([]), LinearSet([]))

fun sub/is-null(Sub(sub): sub): bool
  sub.list.is-empty

fun new/sub(sub: list<(typeVar, ktype)>): pure sub
  if sub.all(fn((tv, t)) tv.kind == t.kind) then
    Sub(LinearMap([]) + sub, sub.map(fst).tvs.union(sub.map(snd).free-type-vars))
  else
    throw("type/typevar: subNew kind mismatch")

fun sub/dom(Sub(sub): sub): tvs
  (sub.list.map(fst)).tvs

fun sub/range(s: sub): list<ktype>
  s.list.map(snd)

fun sub/list(s: sub): list<(typeVar, ktype)>
  s.map.list

fun sub/common(s1: sub, s2: sub): exn list<(typeVar, (tau, tau))>
  s1.list.map(fn(s) s2.lookup(s.fst).map(fn(t) (s.fst, (s.snd, t)))).concat-maybe

fun sub/single(tvar: typeVar, tau: tau)
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

fun sub/lookup(Sub(_): sub, tvar: typeVar): exn maybe<tau>
  throw("Not implemented")
  // TODO: Need map lookup with key

fun sub/remove(Sub(sub, tvs): sub, tvars: list<typeVar>): sub
  Sub(sub.remove-all(tvars), tvs - tvars)

fun subtvs/remove(s: sub, tvars: tvs): sub
  s.remove(tvars.list)

fun sub/find(Sub(sub): sub, tv: typeVar): exn tau
  match sub.lookup(tv)
    Nothing -> TVar(tv)
    Just(tau) -> tau

fun show-tv(tv: typeVar): string
  tv.tid.show

// (s1 \@\@ s2) |-> x == s1 |-> (s2 |-> x)
fun sub/compose(sub1 as Sub(s1, tv1): sub, sub2 as Sub(_, tv2): sub): pure sub
  Sub(s1.union((sub1 |-> sub2).unsub), tv1.union(tv2)) // Assume: left biased union

fun sub/extend(sub: sub, tv: typeVar, tau: tau): pure sub
  single(tv, tau).compose(sub)

// Insert a new substitution. (Note: breaks abstraction barrier)
fun sub/insert(Sub(s, tvs): sub, tvar: typeVar, tau: tau)
  if tau.free-type-vars.member(tvar) then
    throw("type/typevar: insert: recursive type " ++ tvar.show-tv)
  elif !tau.is-tau then
    throw("type/typevar: insert: not a tau " ++ tau.show)
  else
    Sub(s.add(tvar, tau), union(tvs, tau.free-type-vars.add(tvar)))

fun sub/inserts(Sub(sub, tvars): sub, assoc: list<(typeVar, tau)>)
  Sub(LinearMap([]) + assoc + sub.list, // ASSUME: left-biased union
      unions([tvars, assoc.map(fst).tvs, assoc.map(snd).free-type-vars]))


// Type variables

// A set of type variables
alias tvs = linearSet<typeVar>
val tvs/empty:tvs = LinearSet([])
// All the tvar functions defer to Set functions, just alias here

fun tv/single(tv: typeVar) 
  [tv]

fun new/tvs(tv: list<typeVar>): tvs
  LinearSet([]) + tv

fun tvs/common(tvs1: tvs, tvs2: tvs): bool
  !tvs1.disjoint(tvs2)

fun tvslist/max(tvs: list<typeVar>): int
  tvs.foldl(0, fn(n, tv) max(n, tv.tid))

fun tvs/max(tvs: tvs): int
  tvs.list.foldl(0, fn(n, tv) max(n, tv.tid))

// Entities with type variables

// Return the free unifiable type variables in a particular order
fun ofuv(x: a, ?oftv: (a) -> e list<typeVar>): e list<typeVar>
  x.oftv.filter(is-meta)

// TODO: add nub to standard library
// fun oftv(x: a, ?odftv: (a) -> e list<typeVar>): list<typeVar>
//   all-tv(x, odftv, oftv)

fun list/free-type-vars(ps: list<a>, ?free-type-vars: (a) -> div tvs): div tvs
  ps.map(free-type-vars).unions

fun ktype/free-type-vars(tp: ktype): div tvs
  match tp
    TForAll(vars, t) -> 
      val tv1 :tvs = t.free-type-vars
      tv1 - vars
    TFun(args, eff, res) -> 
      val tv1: tvs = args.map(fn(a) a.snd.free-type-vars).unions 
      val tv2: tvs = tv1 + res.free-type-vars
      tv2 + eff.free-type-vars
    TCon -> tvs/empty
    TVar(tv) -> LinearSet([tv])
    TApp(t, args) -> t.free-type-vars + args.map(fn(a) a.free-type-vars).unions
    TSyn(_, xs, t) -> t.free-type-vars + xs.map(free-type-vars).unions

fun exp/free-type-vars(e0: expr): div tvs
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
    Let(defGroups, e) -> defGroups.map(free-type-vars).unions + e.free-type-vars
    Case(es, bs) -> es.free-type-vars + bs.map(free-type-vars).unions

fun dg/free-type-vars(dg: defGroup): div tvs
  match dg
    DefRec(defs) -> defs.map(free-type-vars).unions
    DefNonRec(e) -> free-type-vars(e)

fun def/free-type-vars(d: def): div tvs
  d.ktype.free-type-vars + d.defExpr.free-type-vars

fun branch/free-type-vars(bs: branch): div tvs
  match bs
    Branch(p, e) -> 
      e.free-type-vars - p.bound-type-vars + p.free-type-vars

fun pat/free-type-vars(p: pattern): div tvs
  match p
    PatVar(tn, pat) -> tn.free-type-vars + pat.free-type-vars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1:tvs = tn.free-type-vars + args.free-type-vars
      val tv2:tvs = tv1 + targs.free-type-vars 
      val tv3:tvs = tv2 + tres.free-type-vars
      tv3 - exists0
    PatWild -> tvs/empty
    PatLit(_) -> tvs/empty

fun guard/free-type-vars(gd: guard): div tvs
  match gd
    Guard(e, e2) -> e.free-type-vars + e2.free-type-vars

fun tn/free-type-vars(TName(_, tp): tName): div tvs
  tp.free-type-vars

fun list/bound-type-vars(l: list<a>, ?bound-type-vars: (a) -> div tvs): div tvs
  l.map(bound-type-vars).unions

fun pat/bound-type-vars(p: pattern): div tvs
  match p
    PatVar(tn, pat) -> tn.bound-type-vars + pat.bound-type-vars
    PatCon(tn, args, _, targs, exists0, tres) ->
      val tv1: tvs = tn.bound-type-vars + args.bound-type-vars
      val tv2: tvs = tv1 + targs.bound-type-vars
      val tv3: tvs = tv2 + tres.bound-type-vars
      tv3 + exists0.tvs
    PatWild -> tvs/empty
    PatLit(_) -> tvs/empty

fun ktype/bound-type-vars(tp: ktype): div tvs
  match tp
    TForAll(vars, t) -> 
      val tv1: tvs = t.bound-type-vars
      tv1 + vars
    TFun(args, eff, res) -> 
      val tv1: tvs = args.map(tuple2/snd).bound-type-vars + res.bound-type-vars 
      tv1 + eff.bound-type-vars
    TSyn(_, _, t) -> t.bound-type-vars
    TApp(t, arg) -> t.bound-type-vars + arg.bound-type-vars
    _ -> tvs/empty

fun tn/bound-type-vars(TName(_, tp): tName): div tvs
  tp.bound-type-vars

fun sub/(|->)(s: sub, a: a, ?substitute: (sub, a) -> e a): e a
  if s.is-null then a
  else substitute(s, a)


fun sub/list/substitute(s: sub, l: list<a>, ?substitute: (sub, a) -> <div|e> a): <div|e> list<a>
  if s.is-null then l
  else l.map(s.substitute(_))

fun sub/substitute(sub: sub, Sub(s, tvs2): sub): pure sub
  val Sub(_, tvs1) = sub
  Sub(s.map(fn(k, v) sub.substitute(v)), tvs1.union(tvs2))

fun ktype/substitute(s: sub, tp: ktype): pure tau
  match tp
    TForAll(vars, t) ->
      val sub' = s.remove(vars)
      TForAll(vars, sub' |-> t)
    TFun(args, eff, res) -> TFun(args.map(fn(a) (a.fst, s |-> a.snd)), s |-> eff, s |-> res)
    TCon -> tp
    TVar(tv) -> s.find(tv)
    TApp(t, args) -> TApp(s |-> t, args.map(fn(t') s |-> t'))
    TSyn(syn, xs, t) -> TSyn(syn, xs, s |-> t)

fun tn/substitute(s: sub, tn: tName): pure tName
  match tn
    TName(n, tp) -> TName(n, s |-> tp)

fun pat/substitute(s: sub, p: pattern): pure pattern
  match p
    PatVar(tn, pat) -> PatVar(s |-> tn, s |-> pat)
    PatCon(tn, args, repr, targs, exists0, tres,  conInfo, skip) ->
      val sub' = s.remove(exists0)
      PatCon(s |-> tn, sub' |-> args, repr, sub' |-> targs, exists0, sub' |-> tres, conInfo, skip)
    PatWild -> PatWild
    PatLit(l) -> PatLit(l)

fun expr/substitute(s: sub, e: expr): pure expr
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
    Let(defGroups, e) -> Let(defGroups.map(fn(dg) s |-> dg), s |-> e)
    Case(es, bs) -> Case(s |-> es, bs.map(fn(b) s |-> b))

fun dg/substitute(s: sub, dg: defGroup): pure defGroup
  match dg
    DefRec(defs) -> DefRec(defs.map(fn(d) s |-> d))
    DefNonRec(e) -> DefNonRec(s |-> e)

fun def/substitute(s: sub, Def(name, scheme, expr, vis, isVal, inl, nameRng, doc): def): pure def
  Def(name, s |-> scheme, s |-> expr, vis, isVal, inl, nameRng, doc)

fun branch/substitute(s: sub, Branch(p, e): branch): pure branch
  val sub' = s.remove(p.bound-type-vars)
  Branch(s |-> p, sub' |-> e)

fun guard/substitute(s: sub, g: guard): pure guard
  match g
    Guard(e, e2) -> Guard(s |-> e, s |-> e2)

// TODO: More
fun fresh-typevar(k: kind, fl: flavour)
  val idbase = match fl
    Meta -> "_v"
    Skolem -> "$v"
    Bound -> "v"
  val id = unique-id(idbase)
  TypeVar(id, k, fl)

fun match-types(ts1: list<ktype>, ts2: list<ktype>): pure bool
  ts1.zipwith(ts2, match-type).all(id)

fun typevar/match-effect(eff1: tau, eff2: tau): pure bool
  match-type(eff1.order-effect, eff2.order-effect)

fun match-type(tp1: ktype, tp2: ktype): pure bool
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
