import compiler/type/type
import compiler/kind/kind
import compiler/common/name
import compiler/common/name-prim
import std/core/undiv
// Updated to #752748d on 7/13/25

fun effect-is-affine(eff: keffect)
  val (labs, tl) = eff.extract-ordered-effect
  tl.is-effect-empty && labs.all(label-is-affine)

fun label-is-linear(eff: keffect)
  match eff.expand-syn
    TApp(TCon(tc), [_]) | tc.name == nameTpHandled1 || tc.name == nameTpNHandled1 -> True
    TApp(TCon(tc), [_]) | !(tc.name == nameTpHandled) && !(tc.name == nameTpNHandled) ->
      val k = eff.kind // Allow alloc<global> etc
      k == kindLabel || k == kindEffect
    TCon(tc as TypeCon(_)) -> 
      val k = tc.kind // Builtin? too liberal? does not include exn
      k == kindLabel || k == kindEffect
    _ -> False

fun label-is-affine(eff: keffect): _ bool
  match eff.expand-syn
    TApp(TCon(tc), [_]) | tc.name == nameTpHandled1 || tc.name == nameTpNHandled1 -> True
    // Allow exn
    TApp(TCon(tc), [TCon(tcx)]) | tc.name == nameTpHandled && tcx.name == nameTpPartial -> True
    TApp(TCon(tc), [_]) | !(tc.name == nameTpHandled) && !(tc.name == nameTpNHandled) ->
      val k = eff.kind // Allow alloc<global> etc
      k == kindLabel || k == kindEffect
    TCon -> True // Builtin effects
    _ -> False

// has effects that are reflected in the evidence vector
fun contains-handled-effect(exclude: list<name>, eff: keffect): _ bool
  // val (ls,_) = eff.extract-effect-extend
  // ls.any(_.get-handled-effect(exclude).is-just)
  !eff.extract-handled-effect.fst.is-empty

// Get the effects that are reflected in the evidence vector
fun extract-handled-effect(eff: ktype): _ (list<ktype>, tau)
  val (ls, tl) = eff.extract-ordered-effect
  (ls.filter(is-handled-effect), tl)

// Is an effect reflected in the evidence vector?
fun is-handled-effect(tp: ktype)
  match tp.expand-syn
    // not named effects since these are not int he evidence vector
    TApp(TCon(TypeCon(name)), [_]) -> name == nameTpHandled || name == nameTpHandled1
    _ -> False

fun handled-to-label(e: ktype): _ ktype
  if e.kind == kindHandled1 then TApp(tconHandled1, [e]) else TApp(tconHandled, [e])

type handled-sort
  ResumeOnce
  ResumeMany

// What effect does an operatoin have? Used for monadic translation.
// Note: this includes named effects even though these are not in the evidence vector.
fun get-operation-effect(tp: ktype): _ maybe<(handled-sort, name)>
  get-operation-effectx(tp, [])

fun get-operation-effectx(tp: ktype, exclude: list<name>): _ maybe<(handled-sort, name)>
  match tp.expand-syn
    TApp(TCon(TypeCon(name)), [t])
      | name == nameTpHandled || name == nameTpNHandled -> get-operation-effect-of(ResumeMany, exclude, t)
      | name == nameTpHandled1 || name == nameTpNHandled1 -> get-operation-effect-of(ResumeOnce, exclude, t)
    // TApp(TCon(TypeCon(hxName)))
    //   -> if tp.kind == kindHandled && exclude.find(_ == hxName).is-nothing then Just((ResumeMany, hxName))
    //      elif tp.kind == kindHandled1 && exclude.find(_ == hxName).is-nothing then Just((ResumeOnce, hxName))
    //      elif hxName == nameTpScope && exclude.find(_ == hxName).is-nothing then Just((ResumeMany, hxName))
    //      else Nothing
    // TCon(TypeCon(hxName, kind))
    //   | kind == kindHandled && exclude.find(_ == hxName).is-nothing -> Just((ResumeMany, hxName))
    //   | kind == kindHandled1 && exclude.find(_ == hxName).is-nothing -> Just((ResumeOnce, hxName))
    _ -> Nothing

fun get-operation-effect-of(hsort: handled-sort, exclude: list<name>, tp: ktype)
  match tp.expand-syn
    TCon(TypeCon(hxName)) -> 
      if !exclude.any(_ == hxName) then Just((hsort, hxName)) else Nothing
    TApp(TCon(TypeCon(hxName))) ->
      if !exclude.any(_ == hxName) then Just((hsort, hxName)) else Nothing
    _ -> Nothing

pub fun ktype/kind(tp: ktype): _ kind
  match tp
    TForAll(_, t) -> t.kind
    TFun -> kindStar
    TVar(v) -> v.kind
    TCon(c) -> c.kind
    TSyn(syn, xs) -> kind-apply(xs, syn.kind)
    TApp(tp, args) -> kind-apply(args, tp.kind)

fun kind-apply(tps: list<ktype>, k: kind): _ kind
  match (tps, k)
    ([], _) -> k
    (Cons(_, rest), KApp(KApp, k2)) -> kind-apply(rest.pretend-decreasing, k2)
    _ -> throw("type/kind kind-apply: illegal kind in application")

  