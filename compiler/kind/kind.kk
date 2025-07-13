import compiler/common/name
import compiler/common/name-prim
import std/core/undiv
// Updated 7/12/25; Commit #752748d

type kind
  KCon(constant: kindCon) // Kind constants: "*","->","!","H","P"
  KApp(a: kind, b: kind) // Application (only allowed for functions as yet)

fun kind/(==)(a: kind, b: kind): bool
  match (a, b)
    (KCon(c1), KCon(c2)) -> c1 == c2
    (KApp(a1, b1), KApp(a2, b2)) -> pretend-decreasing(a1) == a2 && pretend-decreasing(b1) == b2
    _ -> False

fun kind/(!=)(a: kind, b: kind): bool
  !(a == b)

fun kind/show(k: kind): string
  match k
    KCon(c) -> c.name/name/show
    KApp(a, b) -> show(a) ++ " " ++ show(b)

// Kind constant
alias kindCon = name

pub fun kind/has-kind-star-result(k: kind): bool
  k.extract-kind-fun.snd == kindStar

pub fun has-kind-label-result(k: kind): bool
  k.extract-kind-fun.snd.is-kind-any-label

val kindStar = KCon(nameKindStar) // V (or "*")
val kindLabel = KCon(nameKindLabel) // X, atomic effects
val kindArrow = KCon(nameKindFun) // -> 
val kindEffect = KCon(nameKindEffect) // Effect row E
val kindScope = KCon(nameKindScope) // S
val kindHeap = KCon(nameKindHeap) // H
val kindLocal = kind-fun(kindHeap, kindLabel)
val kindHandled = kind-fun(kindEffect, kind-fun(kindStar, kindStar)) // user defined effects (E,V) -> V (HX)
val kindHandled1 = kindHandled // (user defined) linear effects: (E,V) -> V   (HX1)
val kindExtend = kind-fun(kindLabel, kind-fun(kindEffect, kindEffect)) // Effect extension (X,E) -> E
fun kind-con(n: int): kind
  kind-con-over(replicate(kindStar, n))
fun kind-con-over(ks: list<kind>): kind
  ks.foldr(kindStar, kind-fun)
fun kind-fun-n(ks: list<kind>, k: kind): kind
  ks.foldr(k, kind-fun)
fun kind-fun(k1: kind, k2: kind): kind
  KApp(KApp(kindArrow, k1), k2)
fun is-kind-fun(k: kind): bool
  match k
    KApp(KApp(k0, _), _) -> k0 == kindArrow
    _ -> False
pub fun extract-kind-fun(k: kind): (list<kind>, kind)
  match k
    KApp(KApp(k0, k1), k2) ->
      if k0 == kindArrow then
        val (args, res) = pretend-decreasing(k2).extract-kind-fun()
        (Cons(k1, args), res)
      else
        ([], k)
    _ -> ([], k)

fun is-kind-handled(k: kind): bool
  match k.extract-kind-fun
    ([k1, k2], k3) -> k1 == kindEffect && k2 == kindStar && k3 == kindStar
    _ -> False

fun is-kind-any-label(k: kind): bool
  k == kindHandled || k == kindHandled1 || k == kindLabel

// Standard kind constant with their kind
val buildinKinds = [
  (nameKindStar, kindStar),
  (nameKindFun, kindArrow),
  (nameKindEffect, kindEffect),
  (nameKindLabel, kindLabel),
  (nameKindHeap, kindHeap),
  (nameKindScope, kindScope),
  // (nameKindHandled, kindHandled),
  // (nameKindHandled1, kindHandled1),
]