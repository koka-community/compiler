import compiler/common/range
import compiler/common/name
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/core/core
import compiler/type/assumption
import compiler/common/syntax
import compiler/platform/config
import std/data/linearset

pub infixr 5 (|->)

fun requires-implicits(tp: ktype)
  match tp.split-fun-scheme
    Just((_, _, pars, _, _)) -> pars.filter(fn(p) p.fst.is-implicit-param-name)
    _ -> []

fun is-optional-or-implicit(p: (name, ktype))
  p.fst.is-implicit-param-name || p.snd.is-optional

fun split-optional-implicit(pars: list<(name, ktype)>)
  val (fixed, rst) = pars.span(fn(p) !p.is-optional-or-implicit)
  val (opts, nameds) = rst.span(fn(p) p.snd.is-optional)
  (fixed, opts, nameds)

fun has-optional-or-implicits(pars: list<(name, ktype)>)
  pars.any(is-optional-or-implicit)

type evidence
  Ev(evName: tName, pred: pred, evRange: range)

fun (|->)(s: sub, e: evidence): pure evidence
  val newPred = (|->)(s, e.pred)
  e(pred=newPred)

fun free-type-vars(e: evidence)
  free-type-vars(e.pred)

// fun bound-type-vars(e: evidence)
//   typevar/bound-type-vars(e.pred)

// TODO: ftc

fun show(e: evidence)
  show(e.pred)

// instantiate a type
fun instantiate(tp: ktype, r: range)
  val (_, _, rho, _) = tp.instantiate-noex(r)
  rho

// Instantiate a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun instantiate-ex(tp: ktype, r: range)
  val (ids, preds, rho, coref) = tp.instantiate-exfl(Meta, r)
  val (erho, coreg) = rho.extend
  (ids, preds, erho, fn(e) coreg(coref(e)))

// Instantiate a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun instantiate-noex(tp: ktype, r: range)
  val (ids, preds, rho, coref) = tp.instantiate-exfl(Meta, r)
  (ids, preds, rho, fn(e) coref(e))

//  Ensure the result of function always gets an extensible effect type
// This is necessary to do on instantiation since we simplify such effect variables
// away during generalization. Effectively, the set of accepted programs does not
// change but the types look simpler to the user.
fun extend(tp: ktype)
  match tp.expand-syn
    TFun(args, eff, res) ->
      val (ls, tl) = eff.extract-ordered-effect
      if tl.is-effect-empty then
        val tv = fresh-tvar(kindEffect, Meta)
        val openEff = ls.effect-extends(tv)
        val openTp = TFun(args, openEff, res)
        (openTp, fn(c) open-effect(eff, openEff, tp, openTp, c))
      else
        (tp, id)
    _ -> (tp, id)

// Skolemize a type
fun skolemize(tp: ktype, r: range)
  val (_, _, rho, _) = tp.skolemize-ex(r)
  rho

// Skolemize a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun skolemize-ex(tp: ktype, r: range)
  tp.instantiate-exfl(Skolem, r)

// General instantiation for skolemize and instantiate
fun instantiate-exfl(tp: ktype, fl: flavour, r: range): <uniquePhase, comp-flags, pure> (list<typeVar>, list<evidence>, ktype, expr -> e expr)
  match tp.split-type-scheme
    ([], [], rho) -> ([], [], rho, id)
    (vars, preds, rho) ->
      val (tvars, sub) = fresh-subx(TVar, fl, vars, rho.all-tv())
      val srho = sub |-> rho
      val spreds = preds.map(fn(p) sub |-> p)
      val pnames = spreds.map(pred-name)
      val corevars = pnames.map(fn(n) Var(n, InfoNone))
      val evidence = pnames.zip(spreds).map(fn((n, p)) Ev(n, p, r))
      (tvars, evidence, srho, if corevars.is-nil then id else id)

fun pred-name(p: pred)
  val name = match p
    PredSub -> fresh-name("sub")
    PredIFace(iname) -> fresh-name(iname.show)
  TName(name, p.pred-type)

fun fresh-sub(fl: flavour, vars: list<typeVar>)
  val tvars = vars.map(fn(tv) fresh-typevar(tv.kind, fl))
  val sub = vars.zip(tvars.map(TVar)).sub
  (tvars, sub)

fun fresh-subx(make-type: (typeVar -> ktype), fl: flavour, vars: list<typeVar>, exclude: tvs)
  val tvars = vars.map(fn(tv) fresh-typevarx(tv.kind, fl, exclude))
  val sub = vars.zip(tvars.map(make-type)).sub
  (tvars, sub)

// ensure we don't use a fresh type variable that already occurs in the type
fun fresh-typevarx(k: kind, fl: flavour, exclude: tvs)
  val tv = fresh-typevar(k, fl)
  if exclude.member(tv) then fresh-typevarx(k, fl, exclude) 
  else tv

fun fresh-skolems(k: kind, n: int)
  fresh-tvars(k, Skolem, n)

fun fresh-tvars(k: kind, fl: flavour, n: int): uniquePhase list<ktype>
  list(1, n).map(fn(_) fresh-tvar(k, fl))

fun fresh-tvar(k: kind, fl: flavour): uniquePhase ktype
  TVar(fresh-typevar(k, fl))

fun fresh-effect()
  fresh-tvar(kindEffect, Meta)

fun fresh-star()
  fresh-tvar(kindStar, Meta)

