import compiler/common/range
import compiler/common/name
import compiler/common/unique
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/core/core
import compiler/type/assumption
import compiler/common/syntax
import compiler/platform/config
import std/data/linear-set
import std/core/undiv
// Updated 11/19/25 to commit #7083c02

pub infixr 5 (|->)

fun requires-implicits(tp: ktype)
  match tp.split-fun-scheme
    Just((_, pars, _, _)) -> pars.filter(_.fst.is-implicit-param-name)
    _ -> []

fun is-optional-or-implicit(p: (name, ktype))
  p.fst.is-implicit-param-name || p.snd.is-optional

fun split-optional-implicit(pars: list<(name, ktype)>): (list<(name, ktype)>, list<(name, ktype)>, list<(name, ktype)>)
  val (fixed, rst) = pars.span(!_.is-optional-or-implicit)
  val (opts, nameds) = rst.span(_.snd.is-optional)
  (fixed, opts, nameds)

fun has-optional-or-implicits(pars: list<(name, ktype)>)
  pars.any(is-optional-or-implicit)

// Instantiation

// instantiate a type
fun instantiate(tp: ktype, r: range)
  val (_, rho, _) = tp.instantiate-noex(r)
  rho

// Instantiate a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun instantiate-ex(tp: ktype, r: range)
  val (ids, rho, coref) = tp.instantiate-exfl(Meta, r)
  val (erho, coreg) = rho.extend
  (ids, erho, fn(e) coreg(coref(e)))

// Instantiate a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun instantiate-noex(tp: ktype, r: range)
  tp.instantiate-exfl(Meta, r)

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
  val (_, rho, _) = tp.skolemize-ex(r)
  rho

// Skolemize a type and return the instantiated quantifiers, name/predicate pairs for evidence,
// the instantiated type, and a core transformer function (which applies type arguments and evidence)
fun skolemize-ex(tp: ktype, r: range)
  tp.instantiate-exfl(Skolem, r)

// General instantiation for skolemize and instantiate
fun instantiate-exfl(tp: ktype, fl: flavour, r: range): _ (list<type-var>, ktype, expr -> expr)
  match tp.split-type-scheme
    ([], rho) -> ([], rho, id)
    (vars, rho) ->
      val (tvars, sub) = fresh-subx(TVar, fl, vars, rho.all-tv())
      (tvars, sub |-> rho, fn(e) add-type-apps(tvars,e))

fun fresh-sub(fl: flavour, vars: list<type-var>)
  val tvars = vars.map(fn(tv) fresh-typevar(tv.kind, fl))
  val sub = vars.zip(tvars.map(TVar)).sub
  (tvars, sub)

fun fresh-subx(make-type: (type-var -> ktype), fl: flavour, vars: list<type-var>, exclude: tvs)
  val tvars = vars.map(fn(tv) fresh-typevarx(tv.kind, fl, exclude))
  val sub = vars.zip(tvars.map(make-type)).sub
  (tvars, sub)

// ensure we don't use a fresh type variable that already occurs in the type
fun fresh-typevarx(k: kind, fl: flavour, exclude: tvs)
  val tv = fresh-typevar(k, fl)
  if exclude.member(tv) then fresh-typevarx(k, fl, exclude) 
  else tv

// Fresh type variables
// Return fresh skolem variables
fun fresh-skolems(k: kind, n: int)
  fresh-tvars(k, Skolem, n)

fun fresh-tvars(k: kind, fl: flavour, n: int): _ list<ktype>
  list(1, n).map(fn(_) fresh-tvar(k, fl))

fun fresh-tvar(k: kind, fl: flavour): _ ktype
  TVar(fresh-typevar(k, fl))

fun fresh-effect()
  fresh-tvar(kindEffect, Meta)

fun fresh-star()
  fresh-tvar(kindStar, Meta)



// Heap divergence constraints
fun heap-never-contained-in(free : tvs, hp0: ktype, tp0: ktype) : bool
  val hp = hp0.expand-syn
  fun never-contained-in(tp: ktype)
    match tp
      TForAll(_, t) -> t.never-contained-in
      TFun(tpars, teff, tres) -> (tpars.map(snd) ++ [teff, tres]).all(_.pretend-decreasing.never-contained-in)
      TApp(t, args) -> Cons(t, args).all(_.pretend-decreasing.never-contained-in)
      TSyn(_, targs, t) -> Cons(t, targs).all(_.pretend-decreasing.never-contained-in)
      TCon(tcon) -> 
        match hp
          TCon(hcon) -> tcon != hcon
          _ -> tcon.kind != kindHeap
      TVar(tvar) -> 
        match hp
          TVar(htv) -> // if we are generalizing htv but not tvar, tvar can never contain htv
            tvar.flavour != Meta || (!free.member(htv) && free.member(tvar))
          _ -> //  but in all other case tvar might get a type containing htv
            tvar.flavour != Meta
  never-contained-in(tp0)


fun heap-always-contained-in(free : tvs, hp0: ktype, tp0: ktype) : bool
  val hp = hp0.expand-syn
  fun always-contained-in(tp: ktype)
    match tp
      TForAll(_, t) -> t.always-contained-in
      TFun(tpars, teff, tres) -> (tpars.map(snd) ++ [teff, tres]).any(_.pretend-decreasing.always-contained-in)
      TApp(t, args) -> Cons(t, args).any(_.pretend-decreasing.always-contained-in)
      TSyn(_, targs, t) -> Cons(t, targs).any(_.pretend-decreasing.always-contained-in)
      TCon(tcon) -> 
        match hp
          TCon(hcon) -> tcon == hcon
          _ -> False
      TVar(tvar) -> 
        match hp
          TVar(htv) -> tvar == htv
          _ -> False
  always-contained-in(tp0)
