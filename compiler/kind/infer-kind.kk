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
import std/data/linearmap
import std/data/linearset

pub infixr 5 (|->)
// Inference Kind: These kinds contain meta kind variables
type infKind
  KIVar(kid: id)
  KICon(k: kind)
  KIApp(k1: infKind, k2: infKind)

fun (==)(k1: infKind, k2: infKind): div bool
  match (k1, k2)
    (KIVar(kid1), KIVar(kid2)) -> kid1 == kid2
    (KICon(k1), KICon(k2)) -> k1 == k2
    (KIApp(k11, k12), KIApp(k21, k22)) -> k11 == k21 && k12 == k22
    _ -> False

alias infKGamma = linearMap<name, infKind>

val infKindStar = KICon(kindStar)
val infKindHandled = KICon(kindHandled)
val infKindLabel = KICon(kindLabel)
fun inf-kind-fun(k1: infKind, k2: infKind)
  KIApp(KIApp(KICon(kindArrow), k1), k2)

fun inf-kind-funN(kinds: list<infKind>, k: infKind)
  kinds.foldr(k, inf-kind-fun)

fun is-infkind-scope(infk: infKind)
  match infk
    KICon(k) -> k == kindScope
    _ -> False

fun is-infkind-label(infk: infKind)
  match infk
    KICon(k) -> k == kindLabel
    _ -> False

// Lift KApp nodes to KIApp
fun lift-kapp(infkind: infKind)
  match infkind
    KIVar -> infkind
    KIApp(k1, k2) -> KIApp(k1.lift-kapp, k2.lift-kapp)
    KICon(KCon(_)) -> infkind
    KICon(KApp(k1, k2)) -> KIApp(KICon(k1).lift-kapp, KICon(k2).lift-kapp)

// extract arguments
fun inf-extract-kind-fun(infkind: infKind)
  fun inj(k1, (ks, _))
    (Cons(k1, ks), k1)
  match infkind
    KIApp(KIApp(KICon(ka), k1), k2) | ka == kindArrow -> k1.inj(k2.inf-extract-kind-fun)
    KIApp(KICon(KApp(ka, k1)), k2) | ka == kindArrow -> KICon(k1).inj(k2.inf-extract-kind-fun)
    KICon(KApp(KApp(ka, k1), k2)) | ka == kindArrow -> KICon(k1).inj(KICon(k2).inf-extract-kind-fun) 
    _ -> ([], infkind)

fun is-infkind-handled(ikind: infKind): div bool
  match ikind.inf-extract-kind-fun
    ([KICon(k1), KICon(k2)], KICon(k3)) -> is-kind-handled(kind-fun(k1, kind-fun(k2, k3)))
    _ -> False

// Substitution
alias ksub = id-map<infKind>
val ksubEmpty = LinearMap([])
alias kvs = id-set

fun ksub-single(id: id, infkind: infKind): ksub
  LinearMap([(id, infkind)])

fun compose(sub1: ksub, sub2: ksub): ksub
  sub1.union(sub1 |-> sub2)

fun inf/(|->)(sub: ksub, k: infKind): infKind
  match k
    KIVar(kid) -> sub.lookup(kid).default(k)
    KIApp(k1, k2) -> KIApp(sub |-> k1, sub |-> k2)
    KICon(k) -> KICon(k)
 
fun sub/(|->)(sub1: ksub, sub2: ksub): ksub
  sub2.map(fn(k, v) inf/(|->)(sub1, v))

fun sub/fkv(sub: ksub): pure kvs
  sub.list.map(fn((_, s)) s.fkv).unions

fun inf/fkv(k: infKind): kvs
  match k
    KIVar(kid) -> LinearSet([]) + kid
    KIApp(k1, k2) -> k1.fkv.union(k2.fkv)
    KICon(_) -> LinearSet([])

// Pretty printing
fun infkind/show(infkind: infKind): <comp-flags,pure,colorSchemeEffect> string
  with nice-kind-env()
  infkind.fkv.list.foreach(extend-nice)
  infkind.pp-infkind(precInfKindTop).pprint/show

fun nice-infkinds(kinds: list<infKind>): <pure,comp-flags,colorSchemeEffect> list<doc>
  with nice-kind-env()
  kinds.map(fkv).unions.list.map(extend-nice)
  kinds.map(_.lift-kapp.pp-infkind(precInfKindTop))

fun pp-infkind(k: infKind, prec: int): <pure, niceEff<id>, comp-flags, colorSchemeEffect> doc
  fun collect-funargs(ik: infKind)
    match ik
      KIApp(KIApp(KICon(KCon(nm)), k1), k2) | nm == "->".new-name -> Cons(k1, k2.collect-funargs)
      _ -> [ik]
  fun collect-args(ik: infKind)
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

fun nice-kind-env(f: () -> <niceEff<id>|e> a): e a
  var nice := LinearMap([])
  var kindIndex := -1
  with handler
    fun extend-nice(k: id)
      kindIndex := kindIndex + 1
      if kindIndex == 0 then
        nice := nice.extend(k, "k")
      else
        nice := nice.extend(k, (kindIndex + 'k'.int).char.string)
      ()
    fun get-nice(k: id)
      nice.nice/show(k)
    fun get-nice-doc(k: id)
      nice.nice/pretty(k)
  f()

alias prec = int
val precInfKindTop = 0
val precInfKindArrow = 1
val precInfKindApp = 2
val precInfKindAtom = 3