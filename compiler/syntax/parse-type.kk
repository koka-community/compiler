//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

module compiler/syntax/parse-type
import std/os/path
import std/os/file
import std/data/sort
import compiler/syntax/lexeme
import compiler/syntax/layout
import compiler/syntax/syntax
import compiler/syntax/builders
import compiler/syntax/promote
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/parse

// Updated to commit #752748d (of Parse.hs)

pub fun parse-type-annot(): parse userType
  parse-keyword(":")
  parse-type()

pub fun parse-parameter-type-annotation(): parse userType
  parse-keyword(":")
  parse-choices("", [
    {
      val rng = parse-special("?")
      val tp = parse-type()
      TpApp(TpCon(nameTpOptional, rng), [tp], rng.combine(tp.range))
    },
    {
      val rng = parse-special-op("$")
      val (eff, res) = parse-result-type()
      TpApp(TpCon(nameTpDelay, rng), [eff, res], rng.combine(res.range))
    },
    parse-type
  ])

pub fun parse-type-scheme(): parse userType
  promote-type(parse-choices("type signature", [parse-quant-some, parse-type]))

pub fun parse-type(): parse userType
  parse-choices("type", [parse-quant-forall, parse-quant-some, parse-type-qualifier])

pub fun parse-s-quantifier(): parse list<userTypeBinder>
  parse-maybe-list({parse-keyword("some"); parens(parse-type-binders)})

fun parse-quant-some(): parse userType
  parse-quantifier(QSome, parse-type)

fun parse-quant-forall(): parse userType
  parse-quantifier(QForall, parse-type-qualifier)

fun parse-quant-exists(): parse userType
  parse-quantifier(QExists, parse-type)

fun parse-quantifier(quan: userQuantifier, next)
  val rng = parse-keyword(if quan.is-qsome then "some" else if quan.is-qexists then "exists" else "forall")
  val params = angles(parse-type-binders)
  val tp = next()
  params.foldr(tp) fn(name, t) 
    TpQuan(quan, name, t, rng.combine(t.range))

fun parse-type-qualifier(): parse userType
  parse-qualifier(parse-arrow-type())

fun parse-qualifier(tp: userType): parse userType
  tp

pub fun parse-predicate()
  parse-choices("predicate", [{parse-type-app(parse-type-id())}])

fun parse-arrow-type(): parse userType
  val (tps, rng1) = parse-type-atom()
  parse-choices("", [
    { parse-keyword("->"); 
      val (teff, tres) = parse-result-type(); 
      TpFun(tps, teff, tres, rng1.combine(tres.range))
    },
    { tuple(tps, rng1) }
  ])

fun parse-effect-type(): parse userType
  val rng1 = parse-left-angle()
  val labels:list<userType> = parse-sep-by("", parse-row-label, parse-comma)
  val (ext, brng) = parse-row-extend()
  val rng = parse-right-angle()
  labels.foldr(ext(rng)) fn(x, acc) 
    make-effect-extend(x, acc, brng)

fun parse-row-extend()
  parse-choices("", [
    { val brng = parse-vertical-bar(); 
      val tp = parse-choices("", [parse-effect-type, parse-type-id]); 
      (fn(x) tp, brng)
    },
    { (make-effect-empty, null) }
  ])

fun parse-row-label(): parse userType
  val tid = parse-type-id()
  match tid
    TpVar(name, rng) ->
      parse-error("encountered effect variable " ++ name.show ++ " when an effect label was expected\n  hint: effect variables must be after `|` (e.g. `<labels|e>`), or by themselves (e.g. `e`)", rng)
    t -> parse-type-app(t)

pub fun parse-result-type(): parse (userType, userType)
  val (mbeff, tres) = parse-tresult()
  val teff = mbeff.default(make-tp-total(tres.range.before))
  (teff, tres)

pub fun parse-tresult(): parse (maybe<userType>, userType)
  val (tps1, rng1) = parse-type-atom()
  parse-choices("", [
    { val (tps, rng) = parse-type-atom(); 
      (Just(tuple(tps1, rng)), tuple(tps, rng)) }, 
    { 
      (Nothing, tuple(tps1, rng1))
    }])

fun parse-type-atom(): parse (list<(name, userType)>, range)
  fun single(tp: userType)
    ([(nil, tp)], tp.range)
  fun make-tuple(n: int, rng: range)
    TpCon(name-tuple(n).unqualify, rng)
  parse-choices("type atom", [
    { val tp1 = parse-type-id(); 
      val tp2 = parse-type-app(tp1); 
      single(tp2) },
    {
      val rng1 = parse-left-paren()
      parse-choices("", [
        {
          val tps = parse-sep-by("", parse-param-typex, parse-comma)
          val rng2 = parse-right-paren()
          (tps.map(fn((name, _, tp)) (name, tp)), rng1.combine(rng2))
        },
        {
          val cs = parse-many1("", parse-comma)
          val rng2 = parse-right-paren()
          val tp = parse-type-app(make-tuple(cs.length + 1, rng1.combine(rng2)))
          single(tp)
        }
      ])
    },
    { single(parse-effect-type()) }
  ])

fun parse-type-app(tp: userType): parse userType
  parse-choices("", [
    {
      val rng1 = parse-left-angle()
      val targs = parse-sep-by("", parse-annotated-type-kind, parse-comma)
      val rng2 = parse-right-angle()
      TpApp(tp, targs, tp.range.combine(rng2).combine(rng1))
    },
    { tp }
  ])

pub fun parse-param-type(): parse (name, range, userType)
  val (id, rng) = parse-choices("", [parse-identifier, parse-wildcard, {(nil, null)}])
  parse-keyword(":")
  val tp = parse-parameter-type(rng)
  (id, rng, tp)

fun parse-param-typex(): parse (name, range, userType)
  parse-choices("parameter type", [
    {
      val (id, rng) = parse-try
        val res = parse-choices("", [parse-identifier, parse-wildcard]); 
        parse-keyword(":"); 
        res
      val tp = parse-parameter-type(rng)
      (id, rng, tp)
    },
    {
      val tp = parse-parameter-type(null)
      (nil, tp.range, tp)
    }
  ])

fun parse-parameter-type(r: range): parse userType
  parse-choices("parameter type", [
    {
      val rng2 = parse-special("?")
      val tp = parse-type()
      TpApp(TpCon(nameTpOptional, r), [tp], rng2.combine(tp.range))
    },
    parse-type
  ])

fun parse-annotated-type-kind(): parse userType
  val tp = parse-type()
  parse-choices("TypeAnnotation", [
    { parse-special-op("::"); TpAnn(tp, parse-kind()) },
    { tp }
  ])

fun parse-type-id(): parse userType
  val (id, rng) = parse-choices("Type", [parse-qualified-var-id, parse-type-id-context, parse-wildcard])
  if id.is-wildcard || id.is-type-var then TpVar(id, rng) else TpCon(id, rng)

pub fun parse-type-binder-def(): parse (userKind -> userTypeBinder)
  val (id, rng) = parse-type-binder-id()
  fn(k:userKind) TypeBinder(id, k, rng, rng)

pub fun parse-type-binders(): parse list<userTypeBinder>
  parse-sep-by("type binder", parse-type-binder, parse-comma)

fun parse-type-binder(): parse userTypeBinder
  val (id, rng) = parse-var-id() // TODO: Here and in a few other pieces need to add error context
  val kind = parse-kind-annotation()
  TypeBinder(id, kind, rng, rng)

pub fun parse-kind-annotation(): parse userKind
  parse-choices("kind", [{
    parse-special-op("::")
    parse-kind()
  },
  { KindNone }])

// Kinds

pub fun parse-kind(): parse userKind
  parse-choices("kind", [
   {
    val params = parse-parens-commas(parse-kind)
    parse-keyword("->")
    val res = parse-kind()
    params.foldr(res, KindArrow)
   },
   {
    val k = parse-kind-atom()
    parse-choices("kind", 
     [{
      parse-keyword("->")
      val k2 = parse-kind()
      KindArrow(k, k2)
      }, 
      {k}])
   }
  ])

fun parse-kind-atom(): parse userKind
  parse-choices("kind constant (V,E,H,S,X,or HX)", [
   {
    val (k, rng) = parens-ranged(parse-kind)
    KindParens(k, rng)
   },
   { KindCon(nameKindStar, parse-special-con-id("V")) },
   { KindCon(nameKindLabel, parse-special-con-id("X")) },
   { KindCon(nameKindEffect, parse-special-con-id("E")) },
   { KindCon(nameKindHeap, parse-special-con-id("H")) },
   { KindCon(nameKindScope, parse-special-con-id("S")) },
   { make-kind-handled(parse-special-con-id("HX")) }
  ])

fun make-kind-handled(rng: range)
  KindArrow(KindCon(nameKindEffect, rng), KindArrow(KindCon(nameKindStar, rng), KindCon(nameKindStar, rng)))