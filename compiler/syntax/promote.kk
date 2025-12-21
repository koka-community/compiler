//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
//
// Peform implicit promotions:
//
// * Quantify over free type variables in type signatures of definitions.
//
// * Change unbound, unparenthesized type variables that only occur in label positions
//   to label constants.
//
// * Change unparenthesized variables in label positions to label constants.
//   (Or should that be: /
//   Change unbound unparenthesized variables that only occur in label positions to
//   label constants./)
// Updated as of 07/12/25: Commit 752748d not including extend / makeEffectExtends / extract which are not used nor exported

import compiler/common/name
import compiler/common/range
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/syntax/syntax
import std/data/linearset

fun promote-type(tp: user-type): div user-type
  val free = tp.free-type-vars
  if free.is-empty then tp
  else
    val (someVars, forallVars) = free.list.partition(is-some-var)
    quantify(QSome, someVars.map(to-type-binder), quantify(QForall, forallVars.map(to-type-binder), tp))

fun promote-free(bound: list<user-type-binder>, tps: list<user-type>): div list<user-type-binder>
  (tps.free-type-vars - (names/empty + bound.map(name))).list.map(to-type-binder)

// Type variable promotion
// Take annotation on parameters and result type, and transform it into
// a single type annotation using some and forall qualifiers.
// i.e.
// function some(a) forall(b) foo( x : a, y : b, z) : c { .. }
// ~>
// foo : some(a,a1) forall(b,c) (a,b,a1) -> total c = fun(x,y,z) { .. }
fun promote(some-pars: list<user-type-binder>, forall-pars: list<user-type-binder>, preds: list<user-type>, mb-res-tp: maybe<(maybe<user-type>, user-type)>, uexpr: user-expr): pure user-expr
  val (argres-tps, expr') = argres-types(uexpr, mb-res-tp)
  if argres-tps.all(_.snd.is-right) then uexpr // no annotation, no promotion
  else
    promote-ex(some-pars, forall-pars, preds, argres-tps, expr')

fun argres-types(uexpr: user-expr, mb-res-tp: maybe<(maybe<user-type>, user-type)>)
  match uexpr
    Parens(e, n, pre, r) -> 
      val (es, e') = argres-types(e, mb-res-tp)
      (es, Parens(e', n, pre, r))
    Ann(e, t, r) -> 
      val (es, e') = argres-types(e, mb-res-tp)
      (es, Ann(e', t, r))
    Lam(args, e, tl, r) ->
      val (es, e1) = e.res-type(mb-res-tp)
      val (fs, args') = args.map(fn(binder)
        match binder.binderType
          Nothing -> ((binder.name, Right(r)), binder)
          Just(t) ->
            val optTp = match binder.expr
              Just | !binder.name.is-implicit-param-name -> TpApp(TpCon(nameTpOptional, t.range), [t], t.range)
              _ -> t
            ((binder.name, Left(optTp)), binder(binderType=Nothing))
      ).unzip
      (fs ++ es, Lam(args', e1, tl, r))
    _ -> ([], uexpr)

fun res-type(expr: user-expr, mb-res-tp: maybe<(maybe<user-type>, user-type)>)
  match expr
    Parens(e, n, pre, r) -> 
      val (es, e') = e.res-type(mb-res-tp)
      (es, Parens(e', n, pre, r))
    _ -> 
      match mb-res-tp
        Just((mbteff, tres)) -> 
          ([
            (nil, match mbteff { Nothing -> Right(expr.range); Just(teff) -> Left(teff) }),
            (nil, Left(tres))],
            expr)
        Nothing -> ([(nil, Right(expr.range)), (nil, Right(expr.range))], expr)

fun promote-ex(some-pars: list<user-type-binder>, forall-pars: list<user-type-binder>, preds: list<user-type>, argres-tps: list<(name, either<user-type, range>)>, body: user-expr)
  // promote quantified variables of TpCon to TpVar
  val quantified = names/empty + some-pars.map(name) + forall-pars.map(name)
  val argres-types1 = argres-tps.map(promote-tp-vars(_, quantified))

  // create full type by inserting some types if no parameter was annotated
  val (namess, argres-types2) = list(1, argres-types1.length).zip(argres-types1).map(insert-some).unzip
  val Cons(res-type', Cons(eff-tp, rargs-tps)) = argres-types2
  val names = namess.concat
  val eff = eff-tp.snd // extend
  val fun-tp = TpFun(rargs-tps.reverse, eff, res-type'.snd, body.range) // TODO: better range?
  
  // Quantify over free type variables
  val implicit = (fun-tp.free-type-vars - (quantified + names)).list
  
  // Create fully quantified type
  val (imp-some, imp-forall) = implicit.partition(is-some-var)
  val full-tp =
    quantify(QSome, some-pars ++ (names ++ imp-some).map(to-type-binder),
    quantify(QForall, forall-pars ++ imp-forall.map(to-type-binder), 
    fun-tp))
  Ann(body, full-tp, body.range.combine(full-tp.range))

fun insert-some((i, (name, either-tp)): (int, (name, either<user-type, range>)))
  match either-tp
    Left(t) -> ([], (name, t))
    Right(r) ->
      val tn = i.new-implicit-typevar-name
      ([tn], (name, TpVar(tn, r)))

fun is-some-var(n: name)
  n.is-wildcard

fun quantify(q: user-quantifier, tbinders: list<user-type-binder>, tp: user-type): user-type
  tbinders.foldr(tp, fn(tb, t) TpQuan(q, tb, t, combine(tb.range, t.range)))

fun to-type-binder(n: name): user-type-binder
  TypeBinder(n, KindNone, null, null)

fun name/promote-tp-vars(x: (name, either<user-type, range>), vars: name-set): div (name, either<user-type, range>)
  match x
    (_, Right) -> x
    (name, Left(u)) -> (name, Left(u.promote-tp-vars(vars)))

fun ut/promote-tp-vars(tp: user-type, vars: name-set): div user-type
  match tp
    TpQuan(quant, tb, t, rng) -> TpQuan(quant, tb, t.promote-tp-vars(vars - tb.name), rng)
    TpFun(args, eff, t, rng) -> TpFun(args.map(fn((name, t1)) (name, t1.promote-tp-vars(vars))), eff.promote-tp-vars(vars), t.promote-tp-vars(vars), rng)
    TpApp(t, args, rng) -> TpApp(t.promote-tp-vars(vars), args.map(fn(t') t'.promote-tp-vars(vars)), rng)
    TpVar(name, rng) -> TpVar(name, rng)
    TpCon(name, rng) -> if vars.member(name) then TpVar(name, rng) else TpCon(name, rng)
    TpParens(t, rng) -> TpParens(t.promote-tp-vars(vars), rng)
    TpAnn(t, k) -> TpAnn(t.promote-tp-vars(vars), k)
