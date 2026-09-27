// Ported as of 2026-01-18; approx upstream baseline commit bc34c8e of Kind/InferKind.hs (backfilled 2026-07-23)
module compiler/kind/infer-kind

import compiler/lib/pprint
import compiler/common/failure
import compiler/common/id
import compiler/common/nice
import compiler/common/name
import compiler/common/name-prim
import compiler/common/color-scheme
import compiler/common/name-collections
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/pretty
import std/data/int-map
import std/data/int-set
import std/num/int64
import std/data/rb-set
import std/data/sort
import std/data/rb-map

pub infixr 5 (|->)
// Inference Kind: These kinds contain meta kind variables
pub type inf-kind
  KIVar(kid: id)
  KICon(k: kind)
  KIApp(k1: inf-kind, k2: inf-kind)

pub fun (==)(k1: inf-kind, k2: inf-kind): _ bool
  match (k1, k2)
    (KIVar(kid1), KIVar(kid2)) -> kid1 == kid2
    (KICon(k1), KICon(k2)) -> k1 == k2
    (KIApp(k11, k12), KIApp(k21, k22)) -> k11 == k21 && k12 == k22
    _ -> False

pub alias inf-kgamma = name-map<inf-kind>

pub val infKindStar = KICon(kindStar)
pub val infKindHandled = KICon(kindHandled)
pub val infKindLabel = KICon(kindLabel)
pub fun inf-kind-fun(k1: inf-kind, k2: inf-kind)
  KIApp(KIApp(KICon(kindArrow), k1), k2)

pub fun inf-kind-funN(kinds: list<inf-kind>, k: inf-kind)
  kinds.foldr(k, inf-kind-fun)

pub fun is-infkind-scope(infk: inf-kind)
  match infk
    KICon(k) -> k == kindScope
    _ -> False

pub fun is-infkind-label(infk: inf-kind)
  match infk
    KICon(k) -> k == kindLabel
    _ -> False

// Lift KApp nodes to KIApp
pub fun lift-kapp(infkind: inf-kind)
  match infkind
    KIVar -> infkind
    KIApp(k1, k2) -> KIApp(k1.lift-kapp, k2.lift-kapp)
    KICon(KCon(_)) -> infkind
    KICon(KApp(k1, k2)) -> KIApp(KICon(k1).lift-kapp, KICon(k2).lift-kapp)

// extract arguments
pub fun inf-extract-kind-fun(infkind: inf-kind)
  // UPSTREAM ISSUE: upstream's patterns write `KICon kindArrow` where
  // `kindArrow` is a fresh pattern VARIABLE (shadowing the constant), so
  // upstream accidentally matches ANY constructor head. We deliberately keep
  // the arrow-equality guards -- a binary kind application with a non-arrow
  // head shouldn't occur, so behavior only differs on ill-formed input.
  fun inj(k1, (ks, k))
    (Cons(k1, ks), k)
  match infkind
    KIApp(KIApp(KICon(ka), k1), k2) | ka == kindArrow -> k1.inj(k2.inf-extract-kind-fun)
    KIApp(KICon(KApp(ka, k1)), k2) | ka == kindArrow -> KICon(k1).inj(k2.inf-extract-kind-fun)
    KICon(KApp(KApp(ka, k1), k2)) | ka == kindArrow -> KICon(k1).inj(KICon(k2).inf-extract-kind-fun)
    _ -> ([], infkind)

pub fun is-infkind-handled(ikind: inf-kind): _ bool
  match ikind.inf-extract-kind-fun
    ([KICon(k1), KICon(k2)], KICon(k3)) -> is-kind-handled(kind-fun(k1, kind-fun(k2, k3)))
    _ -> False

// Substitution
// PERF: keyed by the kind-var id in a Patricia-tree int-map (upstream:
// `newtype KSub = KSub (IM.IdMap InfKind)`, Kind/InferKind.hs). `compose` runs
// once per unification, so an association list makes it O(n*m) -- it dominated
// a cold compile at 34% of self time. Trie union is O(n+m) and shares subtrees.
pub alias ksub = int-map<inf-kind>
pub val ksubEmpty: ksub = empty-intmap
pub alias kvs = id-set

pub fun ksub-single(id: id, infkind: inf-kind): ksub
  int-map/from-list([(id.int64, infkind)])

pub fun compose(sub1: ksub, sub2: ksub): ksub
  int-map/union(sub1, sub1 |-> sub2) // left-biased union: sub1 wins

pub fun inf/(|->)(sub: ksub, k: inf-kind): inf-kind
  match k
    KIVar(kid) -> sub.lookup(kid.int64).default(k)
    KIApp(k1, k2) -> KIApp(sub |-> k1, sub |-> k2)
    KICon(k) -> KICon(k)
 
pub fun sub/(|->)(sub1: ksub, sub2: ksub): ksub
  int-map/map(sub2, fn(v) inf/(|->)(sub1, v))

pub fun sub/fkv(sub: ksub): _ kvs
  sub.list.map(fn((_, s)) s.fkv).unions

pub fun inf/fkv(k: inf-kind): kvs
  match k
    KIVar(kid) -> int-set/empty().insert(kid.int64)
    KIApp(k1, k2) -> k1.fkv.union(k2.fkv)
    KICon(_) -> int-set/empty()

// Pretty printing
fun infkind/show(infkind: inf-kind): _ string
  with nice-kind-env()
  infkind.fkv.list.foreach(fn(kid) extend-nice(kid.int))
  infkind.pp-infkind(precInfKindTop).pprint/show

pub fun nice-infkinds(kinds: list<inf-kind>): _ list<doc>
  with nice-kind-env()
  // upstream `kvsList (fkv kinds)` iterates a Data.Set: sorted by kind-var id
  kinds.map(fkv).unions.list.map(int).sort(?(<) = fn(id1: id, id2: id) id1 < id2).map(extend-nice)
  kinds.map(_.lift-kapp.pp-infkind(precInfKindTop))

fun pp-infkind(k: inf-kind, prec: int): _ doc
  fun collect-funargs(ik: inf-kind)
    match ik
      KIApp(KIApp(KICon(KCon(nm)), k1), k2) | nm == "->".new-name -> Cons(k1, k2.collect-funargs)
      _ -> [ik]
  fun collect-args(ik: inf-kind)
    match ik
      KIApp(k1, k2) -> k1.collect-args ++ [k2]
      _ -> [ik]
  match k
    KIVar(id) -> get-nice-doc(id)
    KICon(k') -> k'.pp-kind(prec)
    KIApp(KIApp(KICon(KCon(nm)), k1), k2) | nm == nameKindFun ->
      val doc = match k2.collect-funargs
        [res] -> k1.pp-infkind(precInfKindArrow) |+| "->".text |+| res.pp-infkind(precInfKindArrow - 1)
        Cons(res, args) -> Cons(k1, args).comma-parens(fn(p') p'.pp-infkind(precInfKindTop)) |+| "->".text |+| res.pp-infkind(precInfKindArrow - 1)
        _ -> throw("kind/inferKind KIApp function")
      doc.pparens(prec, precInfKindArrow)
    KIApp ->
      val doc = match k.collect-args
        Cons(k', ks) -> k'.pp-infkind(precInfKindApp - 1) |+| ks.comma-parens(fn(p') p'.pp-infkind(precInfKindTop))
        _ -> throw("kind/inferKind KIApp")
      doc.pparens(prec, precInfKindApp)

fun nice-kind-env(f: () -> _ a): _ a
  var nice := int-map/empty()
  var kindIndex := -1
  var saved := []
  with handler
    fun extend-nice(k: id)
      kindIndex := kindIndex + 1
      // "k", "k1", "k2", ... (the letter pool is just 'k')
      if kindIndex == 0 then
        nice := nice.extend(k, "k")
      else
        nice := nice.extend(k, "k" ++ kindIndex.show)
      ()
    fun get-nice(k: id)
      nice.nice/show(k)
    fun get-nice-doc(k: id)
      nice.nice/pretty(k)
    fun nice-push()
      saved := Cons((nice, kindIndex), saved)
    fun nice-pop()
      match saved
        Cons((n, i), rest) ->
          nice := n
          kindIndex := i
          saved := rest
        Nil -> ()
  f()

alias prec = int
val precInfKindTop = 0
val precInfKindArrow = 1
val precInfKindApp = 2
val precInfKindAtom = 3