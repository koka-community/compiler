//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Syntax building helpers, taken from parse.kk
module compiler/syntax/builders
import std/os/path
import std/os/file
import std/core/undiv
import std/data/sort
import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/name-prim
import compiler/common/parse // not actually parsing, but need it for types
import compiler/syntax/syntax
import compiler/syntax/promote
// Updated to commit #ddac17b (of Parse.hs)

// Effect definitions
// 
// We don't return a syntactic construction for effects
// but immediately build the underlying data structures.
// ---------------------------------------------------------
// the following types are used to represent intermediate syntactic
// structures
pub type op-decl
  OpDecl(
    opdoc: string,
    name: name,
    kwdrng: range,
    namerng: range, 
    lin: bool, // linear
    sort: operation-sort,
    exists0: list<type-binder<user-kind>>,
    pars: list<value-binder<user-type, maybe<user-expr>>>,
    parsrng: range,
    mbteff: maybe<user-type>,
    tres: user-type,
    declrng: range
  )

// TODO: We still use "instance" for "named" effects, rename it more consistently
pub type effect-decl
  EffectDecl(
    vis: visibility,
    vis2: visibility,
    declStart: range,
    effRange: range,
    doc: string,
    kind: data-kind,
    lin: bool, // linear
    inst: bool, // instance
    scoped: bool, // scoped
    name: name,
    nameRng: range,
    exists0: list<type-binder<user-kind>>,
    declKind: user-kind,
    paramRange: range,
    extras: effect-extra,
    decls: list<op-decl>,
    declRng: range
  )

pub type effect-extra
  EffectExtra(extra: list<user-type>) // Extra operation effects besides the regular effect (partial for non-scoped)
  EffectReplace(replace: list<user-type>) // Replace operation effect by these (umbrella type, and partial)

pub alias parse = <token-parse, parse-error, pure>
pub value type statement
  StatFun(e: (user-expr -> <parse> user-expr))
  StatExpr(e: user-expr)
  StatVar(e: user-def)

pub value type clause
  ClauseRet(expr: user-expr)
  ClauseFinally(expr: user-expr)
  ClauseInitially(expr: user-expr)
  ClauseBranch(expr: user-handler-branch)

pub fun clause/range(c: clause): range
  match c
    ClauseRet(e) -> e.range
    ClauseFinally(e) -> e.range
    ClauseInitially(e) -> e.range
    ClauseBranch(e) -> e.range

pub alias param = (visibility, value-binder<user-type, maybe<user-expr>>);
pub alias trans-expr = ((user-expr) -> user-expr)
pub alias binder = (clause, maybe<trans-expr>)

pub value type top-def
  DefValue(def: user-def)
  DefType(def: user-typedef)
  DefExtern(def: external)

// Automatically generated.
// Shows a string representation of the `topDef` type.
pub fun topDef/show(this : top-def) : _ string
  match this
    DefValue(def) -> "DefValue(def: " ++ def.show ++ ")"
    DefType(def) -> "DefType(def: " ++ def.show ++ ")"
    DefExtern(def) -> "DefExtern(def: " ++ def.show ++ ")"


pub fun make-app(expr: expr<t>, args: list<expr<t>>, rT: (t) -> range): expr<t>
  App(expr, args.map((Nothing, _)), combine(Cons(expr.range, args.map(range))))

pub fun make-tp-pure(rng: range): kuser-type<k>
  TpCon(nameTpPure, rng)

pub fun make-tp-total(rng: range): kuser-type<k>
  TpCon(nameEffectEmpty, rng)

pub fun make-effect-empty(rng: range): kuser-type<k>
  TpCon(nameEffectEmpty, rng)

pub fun make-effect-extend(label: kuser-type<k>, ext: kuser-type<k>, rng: range, ?range: (k) -> range): kuser-type<k>
  TpApp(TpCon(nameEffectExtend, rng), [label, ext], label.range.combine(ext.range))

pub fun type-from-params(rng:range, pars: list<value-binder<user-type, maybe<user-expr>>>, teff: user-type, tres: user-type): div user-type
  promote-type(TpFun(pars.map(fn(p) (p.name, p.binderType)), teff, tres, rng))

pub fun gen-args(pars: list<value-binder<user-type, maybe<user-expr>>>): list<(maybe<(name, range)>, user-expr)>
  pars.map(fn(p) (Nothing, Var(p.name, False, p.range.before)))

pub fun gen-parameter-args(tp: user-type)
  match tp
    TpQuan(QSome) -> parse-error("external types cannot contain unspecified ('_') types", tp.range)
    TpQuan(QExists) -> parse-error("external types cannot contain existential types", tp.range)
    TpQuan(_, _, t) -> t.gen-parameter-args
    TpParens(t) -> t.gen-parameter-args
    TpAnn(t, _) -> t.gen-parameter-args
    TpFun(pars) -> pars.gen-fun-parameter-args
    _ -> parse-error("external declarations must have a function type", tp.range)

pub fun gen-fun-parameter-args(pars: list<(name, user-type)>)
  pars.map-indexed(fn(i, p) p.gen-parameter-arg(i + 1)).unzip 

pub fun gen-parameter-arg((name:name, _:user-type), idx: int)
  val fullName = if name == nil then new-hidden-name-ex("arg", idx.show) else name
  (ValueBinder(fullName, Nothing, Nothing, null, null), (Nothing, Var(fullName, False, null)))

pub fun tp-var(tb: type-binder<k>)
  TpVar(tb.name, tb.range)

pub fun tp-con(tb: type-binder<k>)
  TpCon(tb.name, tb.range)

pub fun make-user-constructor(const: name, foralls: list<user-type-binder>, resTp: user-type, exists0: list<user-type-binder>, pars: list<(visibility, value-binder<user-type, maybe<user-expr>>)>, mbLazyExpr : maybe<(fipT, user-expr)>, nameRng: range, rng: range, vis: visibility, doc: string)
  val conParams = pars.map(fn((v, p)) (v, p(expr=Nothing)))
  val cName = const.new-creator-name
  val params = pars.map(fn((_, p)) p(binderType=if p.expr.is-just then make-optional(p.binderType) else p.binderType))
  val lParams = params.map(fn(ValueBinder(name', _, expr, nameRng', rng')) ValueBinder(name', Nothing, expr, nameRng', rng') )
  val arguments = params.map(fn(p) (Nothing, Var(p.name, False, p.name-range)))
  val tpParams = params.map(fn(p) (p.name, p.binderType))
  val tpFull = quantify(QForall, foralls, TpFun(tpParams, make-tp-total(nameRng), resTp, rng))
  val body = Ann(Lam(lParams, App(Var(const, False, nameRng), arguments, rng), True, rng), tpFull, rng)
  val binder = ValueBinder(cName, (), body, nameRng, nameRng)
  val creator = Def(binder, rng, vis, DefFun([]), InlineAlways, doc) 
  (UserCon(const, exists0, conParams, Nothing, mbLazyExpr, nameRng, rng, vis, doc), if pars.any(_.snd.expr.is-just) then [creator] else [])

pub fun split-top-defs(dfs: list<top-def>): (list<user-def>, list<user-typedef>, list<external>)
  fun split(dfs': list<top-def>, user-defs: ctx<list<user-def>>, typedefs: ctx<list<user-typedef>>, externDefs: ctx<list<external>>): (list<user-def>, list<user-typedef>, list<external>)
    match dfs'
      Cons(DefValue(d), rst) -> rst.split(user-defs ++ ctx Cons(d, hole), typedefs, externDefs)
      Cons(DefType(d), rst) -> rst.split(user-defs, typedefs ++ ctx Cons(d, hole), externDefs)
      Cons(DefExtern(d), rst) -> rst.split(user-defs, typedefs, externDefs ++ ctx Cons(d, hole))
      Nil -> (user-defs ++. Nil, typedefs ++. Nil, externDefs ++. Nil)
  dfs.split(ctx hole, ctx hole, ctx hole)

pub fun make-effect-decl(decl: effect-decl): <parse-error,pure> list<top-def>
  // TODO: Use record operations
  val EffectDecl(vis, _, vrng, erng, doc, tpSort, singleShot, isInstance, isScoped, id, irng, tpars, effkind, _, effectsExtra, operations, oprng) = decl
  val rng = vrng.combine(erng).combine(irng)
  val krng = rng.hide
  val grng = rng.combine(oprng).hide

  val (tparsScoped, tparsNonScoped) = if isScoped then (tpars.take(1), tpars.drop(1)) else ([], tpars)
  
  // effect eff<a,b,c>
  // infkind::<_,_,_E,V> -> V
  val infKind = match effkind
    KindNone -> tpars.map(kind).foldr(KindCon(if isInstance then nameKindStar elif singleShot then nameKindHandled1 else nameKindHandled, null)) fn(e, acc)
      KindArrow(e, acc)
    _ -> effkind
  val ename = TypeBinder(id, infKind, irng, rng)
  // effTpH: eff<a,b,c>
  val effTpH = TpApp(TpCon(ename.name, ename.range), tpars.map(tp-var), krng)
  // effTp: handled<eff<a,b,c>>
  val effTp = TpApp(TpCon(make-tp-handled(isInstance, singleShot), ename.range), [effTpH], rng)
  // declare the effect type (for resources, generate a hidden constructor to check the types)
  val docEffect = "effect `:" ++ id.show ++ "`\n" // Don't extend the doc with operations as it is shown when hovering with `ctrl`
  val docx = doc
  // Effect handler type
  val kindEffect = KindCon(nameKindEffect, krng)
  val kindStar = KindCon(nameKindStar, krng)
  val kindScope = KindCon(nameKindScope, krng)
  val hndName = id
  val hndTpName = ename
  val hndEffTp = TypeBinder("e".new-hidden-name, KindCon(nameKindEffect, krng), krng, krng)
  val hndResTp = TypeBinder("r".new-hidden-name, kindStar, krng, krng)
  val hndTp = TpApp(hndTpName.tp-con, (tpars ++ [hndEffTp, hndResTp]).map(tp-var), grng)

  // Effect tag
  val tagName = id.to-effect-tag-name
  val tagDef = Def(ValueBinder(tagName, (), Ann(App(Var(nameHTag, False, krng), 
  // TODO: This needs to be prefixed with the actual module name
    [(Nothing, Literal(LitString(id.show ++ "@" ++ irng.source.name.path.basename, krng)))], krng), 
      quantify(QForall, tpars, TpApp(TpCon(nameTpHTag, krng), 
        [TpApp(TpCon(hndName, krng), tpars.map(tp-var), krng)], krng)), krng),
       krng, krng), krng, vis, DefVal, InlineNever, "// runtime tag for the " ++ docEffect)

  // parse the operations and return the constructor fields and function definitions
  val opCount = operations.length
  fun ltOp(op1: op-decl, op2: op-decl): bool
    op1.name.unqualify.show < op2.name.unqualify.show
  
  val orderedOperations = operations.sort(?(<) = ltOp)
  val (opFields, opSelects, opDefs, opValDefs) = 
          val res = list(0, opCount - 1).zip(orderedOperations).map fn(op) 
                make-operation-decl(opCount, vis, tparsScoped, tparsNonScoped, docEffect, docx, hndName, 
                               id, isInstance, effectsExtra, effTp, hndTpName.tp-con, 
                               ([hndEffTp, hndResTp]), op)
          res.unzip4
  
  // Handler datatype
  val hndFieldCfc = ValueBinder("cfc".new-hidden-name, TpCon(nameTpInt, krng), Nothing, krng, krng) // first field is the control-flow-context for the handler
  val hndFields = Cons(hndFieldCfc, opFields)
  val hndCon = UserCon(hndName.to-handler-con-name, [], hndFields.map((Private, _)), Nothing, Nothing, krng, grng, vis, "")
  val hndTpDecl = DataType(hndTpName, tpars ++ [hndEffTp, hndResTp], [hndCon], grng, vis, tpSort, 
                            DataDefNormal, DataEffect(isInstance, singleShot), 
                            docx)
  
  // Declare the handle function
  val handleRetTp = TypeBinder("b".new-hidden-name, kindStar, krng, krng)
  val handleName = id.to-handle-name
  val handleEff = 
    if isInstance && !isScoped then hndEffTp.tp-var 
    else make-effect-extend(effTp, hndEffTp.tp-var, rng=krng)
  
  val scopedTpVars = if isScoped then [TypeBinder("s".new-hidden-name, kindScope, krng, krng)] ++ tparsNonScoped else tpars
  val actionArgTp = if isInstance then [("hname".new-name, TpApp(TpCon(nameTpEv, krng), [effTpH], krng))] else []
  val actionTp = TpFun(actionArgTp, handleEff, handleRetTp.tp-var, grng)
  val handleTp = quantify(QForall, scopedTpVars ++ [handleRetTp, hndEffTp, hndResTp], TpFun(
    [("hnd".new-name, TpApp(TpCon(hndName, grng), (scopedTpVars ++ [hndEffTp, hndResTp]).map(tp-var), grng)),
    ("ret".new-name, TpFun([("res".new-name, handleRetTp.tp-var)], hndEffTp.tp-var, hndResTp.tp-var, grng)),
    ("action".new-name, if isScoped then quantify(QForall, tparsScoped, actionTp) else actionTp)],
    hndEffTp.tp-var, hndResTp.tp-var, grng
  ))
  val params = [
    ValueBinder("hnd".new-name, Nothing, Nothing, krng, grng),
    ValueBinder("ret".new-name, Nothing, Nothing, krng, grng),
    ValueBinder("action".new-name, Nothing, Nothing, krng, grng)]
  val arguments = [
    (Nothing, Var(tagName, False, krng)),
    (Nothing, Var("hnd".new-name, False, krng)),
    (Nothing, Var("ret".new-name, False, krng)),
    (Nothing, Var("action".new-name, False, krng))
  ]
  val handleInner = App(Var(if isInstance then nameNamedHandle else nameHandle, False, grng), arguments, grng)
  val handleBody = Ann(Lam(params, handleInner, False, grng), handleTp, grng)
  val handleDef = Def(ValueBinder(handleName, (), handleBody, irng, rng), grng, vis, DefFun([]), InlineNever, "// handler for the " ++ docEffect)
  [DefValue(tagDef), DefType(hndTpDecl), DefValue(handleDef)] ++ opSelects.map(DefValue) ++ opDefs.map(DefValue) ++ opValDefs.concat-maybe.map(DefValue)

pub fun make-operation-decl(opCount: int, vis: visibility, forallsScoped: list<user-type-binder>, forallsNonScoped: list<user-type-binder>, 
                       docEffect: string, docEffectDecl: string, hndName: name, effName: name, isInstance: bool,
                       effectsExtra: effect-extra, effTp: user-type, hndTp: user-type, hndTpVars: list<user-type-binder>, 
                       opx: (int, op-decl)): <parse-error,pure> (value-binder<user-type, maybe<user-expr>>, user-def, user-def, maybe<user-def>) 
  val foralls = forallsScoped ++ forallsNonScoped
  // todo: use record operations
  val (opIndex, op) = opx
  val OpDecl(doc, id, _kwrng, idrng, _lin, opSort, exists0, pars, prng, _mbTeff, tres) = op
  val rng = combine([idrng, prng, tres.range])
  val krng = rng.hide
  val grng = krng // for generated code
  val opEffTps = match effectsExtra
    EffectExtra(extra) -> Cons(effTp, extra)
    EffectReplace(extra) -> extra 
  // for now add a divergence effect to named effects/resources when there are type variables...
  // this is too conservative though; we should generate the `ediv` constraint instead but
  // that is a TODO for now
  val teff0 = opEffTps.foldr(krng.make-effect-empty, fn(e, acc) make-effect-extend(e, acc, rng=krng))
  val nameA = ".a".new-name
  val tp-varA = TpVar(nameA, null)
  val exists1 = if !exists0.is-empty then exists0 else promote-free(foralls, (pars.map(binderType) ++ [teff0, tres]))
  fun notDiv(tp)
    match tp
      TpCon(name, _) -> !(name == nameTpDiv)
      _ -> True
  val teff = if !(forallsNonScoped ++ exists1).is-empty && isInstance && opEffTps.all(notDiv) then make-effect-extend(TpCon(nameTpDiv, krng), teff0, rng = krng) else teff0
  // create a constructor field for the operation as `clauseId : clauseN<a1,..,aN,b,e,r>`
  val forallParams = foralls.map(fn(par) TpVar(par.name, krng))
  val tpParams = forallParams ++ exists1.map(fn(par) TpVar(par.name, krng))
  fun make-clause-field-name(name: name): exn name
    make-hidden-name(opSort.show, if name.is-value-operation-name then name.from-value-operation-name else name)
  val clauseId = make-clause-field-name(id)
  val (clauseName, clauseParsTp) = 
    if pars.length <= 2 then // Set by std/core/hnd
      (name-tp-clause(pars.length), pars.map(binderType)) 
    else (name-tp-clause(1), [TpApp(TpCon(name-tp-tuple(pars.length), krng), pars.map(binderType), krng)]) // As tuple on clause1
  val clauseRhoTp = TpApp(TpCon(clauseName, krng), clauseParsTp ++ Cons(tres, Cons(TpApp(hndTp, foralls.map(tp-var), krng), hndTpVars.map(tp-var))), krng)
  val clauseTp = quantify(QForall, exists1, clauseRhoTp)
  val conField = ValueBinder(clauseId, clauseTp, Nothing, krng, krng)

  // create an operation selector explicitly so we can hide the handler constructor
  val selectId = id.to-op-selector-name
  fun create-select()
    val hndArg = "hnd".new-name
    val hndParam = ValueBinder(hndArg, Nothing, Nothing, krng, grng)
    val i = opIndex;
    val fieldCount = opCount + 1 // for the cfc field
    val patterns = list(0, i).map(fn(_) (Nothing, PatWild(grng))) ++ // up (including i) due to cfc field
      [(Nothing, PatVar(ValueBinder(clauseId, Nothing, PatWild(grng), grng, grng)))] ++ 
      list(i+2, fieldCount - 1).map(fn(_) (Nothing, PatWild(grng)))
    val branch = Branch(PatCon(hndName.to-handler-con-name, patterns, grng, grng), 
                          [Guard(guardTrue, Var(clauseId, False, grng))])
    val innerBody = Case(Var(hndArg, False, grng), [branch], False, grng)
    val fullTp = quantify(QForall, foralls ++ exists1 ++ hndTpVars, 
                         TpFun([(hndArg, 
                         TpApp(hndTp, (foralls ++ hndTpVars).map(tp-var), grng))], 
                           make-tp-total(grng), clauseRhoTp, grng))
    val body = Ann(Lam([hndParam], innerBody, False, grng), fullTp, grng)
    val binder = ValueBinder(selectId, (), body, krng, krng)
    Def(binder, krng, vis, DefFun([Borrow]), InlineAlways, ("// select `" ++ id.show ++ "` operation out of the " ++ docEffect ++ " handler"))
  val opSelect = create-select()

  val docDef = if doc.is-empty then "" else doc ++ "\n" ++ 
                (if id.is-value-operation-name
                  then  "// Call then `val " ++ id.from-value-operation-name.show ++ "` operation of the " ++ docEffect
                  else "// Call then `" ++ opSort.show ++ " " ++ id.show ++ "` operation of the " ++ docEffect)    
  // create a typed perform wrapper: fun op(x1:a1,..,xN:aN) : <l> b { performN(evv-at(0),clause-op,x1,..,xN) }
  fun create-op()    
    val nameRng = idrng.hide
    val perform = Var(name-perform(pars.length), False, krng)
    val zeroIdx = App(Var(nameInternalSSizeT, False, krng), [(Nothing, Literal(LitInt(0, krng)))], krng)
    val resourceName = "hname".new-hidden-name
    val resourceTp = 
      match effTp
        TpApp(_, [effTpH]) -> TpApp(TpCon(nameTpEv, krng), [effTpH], krng)
        _ -> parse-error("syntax/parse (builder.kk) operation-decl: expected handled<effect_type>", rng) 
    val resourceBinder = ValueBinder(resourceName, resourceTp, Nothing, krng, grng)
    val params0 = pars.map(fn(par) par(binderType=if par.expr.is-just then par.binderType.make-optional else par.binderType))
    val params = if isInstance then Cons(resourceBinder, params0) else params0
    val arguments = params0.map(fn(par) (Nothing, Var(par.name, False, par.name-range)))
    val lParams = params.map(fn(ValueBinder(name, _, expr, nameRng', rng')) ValueBinder(name, Nothing, expr, nameRng', rng') )
    val tplParams = params.map(fn(par) (par.name, par.binderType))
    val tpFull = quantify(QForall, foralls ++ exists1, TpFun(tplParams, teff, tres, grng))
    val inner = 
      if isInstance then Var(resourceName, False, krng)
      else App(Var(nameEvvAt, False, krng), [(Nothing, zeroIdx)], krng)
    val innerBody = App(perform, [(Nothing, inner), (Nothing, Var(selectId, False, krng))] ++ arguments, grng)
    val body = Ann(Lam(lParams, innerBody, True, krng), tpFull, krng)
    val binder = ValueBinder(id, (), body, nameRng, nameRng)
    Def(binder, idrng, vis, DefFun([]), InlineAlways, docDef)
  val opDef = create-op()

  if id.is-value-operation-name then
    // create a temporary value definition for type checking
    val opName = id.from-value-operation-name
    val qualTpe = promote-type(TpApp(TpCon(nameTpValueOp, krng), [tres], krng))
    val phantom = Var(nameValueOp, False, krng)
    val annot = Ann(phantom, qualTpe, null)
    (conField, opSelect, opDef, Just(Def(ValueBinder(opName, (), annot, idrng.hide, krng), idrng, vis, DefVal, InlineNever, docDef)))
  else (conField, opSelect, opDef, Nothing)

// Given a name and an expression, this function generates
// - a binder for a fresh name (let's say `val x$name$3 = expr; body`), binding the expression
// - a tail resuming expression i.e. `resume(x$name$3, params...)`
// TODO: add parameters to resume (replace user-expr by list<value-binder<t,e>> -> user-expr)

pub fun bind-expr-to-val(opname: name, oprange: range, expr: user-expr): (user-expr -> user-expr, list<value-binder<t,e>> -> user-expr)
  val fresh = "value".make-fresh-hidden-name(opname, oprange)
  val freshVar = Var(fresh, False, oprange)
  val erange = expr.range
  val binder = Def(ValueBinder(fresh, (), expr, oprange, erange), oprange, Private, DefVal, InlineAuto, "")
  (fn(b) Bind(binder, b, erange), fn(params) freshVar)

pub fun make-optional(tp: kuser-type<k>, ?range: (kuser-type<k>) -> range): kuser-type<k>
  TpApp(TpCon(nameTpOptional, tp.range), [tp], tp.range)

pub fun any-statement-var(l: list<statement>): maybe<user-def>
  match l
    Cons(StatVar(def'), _) -> Just(def')
    Cons(_, tl) -> tl.any-statement-var
    Nil -> Nothing

pub fun local-scope(vdef: user-def, exp: user-expr): user-expr
  val erng = exp.range
  val drng = vdef.range
  val nrng = vdef.binder.name-range
  App(Var(nameRunLocal, False, nrng.hide), [(Nothing, Lam([], exp, False, erng))], drng)

pub fun combine(e1: statement, exp: user-expr): <parse> user-expr
  match e1
    StatFun(f) -> f(exp)
    StatExpr(e) ->
      val r = e.range
      Bind(Def(ValueBinder("_".new-name, (), e, r, r), r, Private, DefVal, InlineAuto, ""), exp, r)
    StatVar(def') ->
      val ValueBinder(name, (), expr, nameRng, rng) = def'.binder
      App(Var(nameLocalVar, False, rng.hide), 
      // Put parens over the lambda so it comes later during type inference (so the type of expr can be propagated in)
      // see test/ambient/ambient3: TODO: Is this still the case
       [(Nothing, expr), 
        (Nothing, Parens(
          Lam([ValueBinder(name, Nothing, Nothing, nameRng, nameRng)], exp, False, def'.range.combine(exp.range)),
           name, "var", nameRng))],
           rng.combine(expr.range))

pub fun make-return(e: user-expr, r: range): user-expr
  App(Var(nameReturn, False, r), [(Nothing, e)], r.combine(e.range))

pub fun expr/un-parens(e: expr<t>): expr<t>
    match e
      Parens(p) -> p.un-parens
      _ -> e

pub fun pat/un-parens(e: pattern<t>): pattern<t>
    match e
      PatParens(p) -> p.un-parens
      _ -> e

pub fun apply-to-continuation(wrng: range, params: list<value-binder<maybe<t>, maybe<expr<t>>>>, expr: expr<t>, body: expr<t>): expr<t>  
  val lam = Lam(params, body, False, wrng.combine(body.range))
  val f = Parens(lam, "with".new-name, "expr", wrng) // Parens makes it last in type inference so types can better propagate (ambients/heap1) (todo: no longer the case right?)
  val funarg = [(Nothing, f)]
  val fullrange = wrng.combine(f.range)
  match expr.un-parens
    App(f', args, _) -> App(f', (args ++ funarg), fullrange)
    atom -> App(atom, funarg, fullrange)

pub fun apply-maybe(rng: range, reinit: maybe<user-expr>, finally: maybe<user-expr>, f: user-expr): user-expr
  match (reinit, finally)
    (Nothing, Nothing) -> f
    _ -> 
      val applyH = App(f, [(Nothing, Var("act".new-hidden-name, False, rng))], rng)
      val bodyF = match finally
        Just(fin) -> App(Var(nameFinally, False, rng), [(Nothing, fin),(Nothing, Lam([], applyH, False, rng))], rng)
        Nothing -> applyH
      val bodyI = match reinit
        Just(ini) -> App(Var(nameInitially, False, rng), [(Nothing, ini), (Nothing, Lam([], bodyF, False, rng))], rng)
        Nothing -> bodyF
      Lam([ValueBinder("act".new-hidden-name, Nothing, Nothing, rng, rng)], bodyI, False, rng)

pub fun extract-binders(l: list<binder>): (list<clause>, (user-expr -> user-expr))
  l.foldr(([], fn(x) x)) fn(b, (cs, binders): (list<clause>, (user-expr -> user-expr)))
    match b
      (clause, Nothing) -> (Cons(clause, cs), binders)
      (clause, Just(binder)) -> (Cons(clause, cs), fn(e) binders(binder(e)))

pub fun partition-clauses(clauses: list<clause>, rng: range): parse-error (maybe<user-expr>, maybe<user-expr>, maybe<user-expr>, list<user-handler-branch>)
  fun separate(clauses': list<clause>, ret: maybe<user-expr>, fin: maybe<user-expr>, init: maybe<user-expr>, br: ctx<list<user-handler-branch>>): <parse-error> (maybe<user-expr>, maybe<user-expr>, maybe<user-expr>, list<user-handler-branch>)
    match clauses'
      Cons(ClauseRet(e), rst) -> 
        if ret.is-just then
          parse-error("There can be at most one 'return' clause in a handler body", e.range)
        else
          separate(rst, Just(e), fin, init, br)
      Cons(ClauseFinally(e), rst) -> 
        if fin.is-just then
          parse-error("There can be at most one 'finally' clause in a handler body", e.range)
        else
          separate(rst, ret, Just(e), init, br)
      Cons(ClauseInitially(e), rst) -> 
        if init.is-just then 
          parse-error("There can be at most one 'initially' clause in a handler body", e.range)
        else
          separate(rst, ret, fin, Just(e), br)
      Cons(ClauseBranch(e), rst) -> separate(rst, ret, fin, init, br ++ (ctx Cons(e, hole)))
      Nil -> (ret, fin, init, br ++. Nil)
  separate(clauses, Nothing, Nothing, Nothing, ctx hole)

pub val userTpRange = fn(tp: user-type) tp.range

pub fun make-nil(r: range): expr<user-type>
  make-app(Var(nameListNil, False, r), [], userTpRange)

pub fun make-cons(r: range, x: expr<t>, xs: expr<t>, rT: (t) -> range): expr<t>
  make-app(Var(nameCons, False, r), [x, xs], rT)

pub fun make-nil-pattern(rng: range): pattern<t>
  PatCon(nameListNil, [], rng, rng)

pub fun make-cons-pattern(x: pattern<t>, xs: pattern<t>): pattern<t>
  PatCon(nameCons, [(Nothing, x), (Nothing, xs)], x.range, x.range)

pub fun tuple(tps: list<(name, user-type)>, r: range): user-type
  match tps
    Cons(tp, Nil) -> tp.snd
    _ -> TpApp(TpCon(name-tp-tuple(tps.length), r), tps.map(snd), r)

pub fun eta-expand(e: user-expr): user-expr
  val (e', binders) = e.eta-transform
  if binders.is-empty then e'
  else Lam(binders, e', False, e.range)

fun eta-transform(ue : user-expr): (user-expr, list<value-binder<maybe<user-type>, maybe<user-expr>>>)
  match ue
    Var(name, isOp, rng) | name.is-eta-hole -> 
      val name' = "eta".unique-range-hidden-name(rng)
      (Var(name', isOp, rng), [ValueBinder(name', Nothing, Nothing, range/null, range/null)])
    Ann(e, tp, r) ->
      val (e', binders) = e.eta-transform
      (Ann(e', tp, r), binders)
    Parens(e, nm, pre, r) ->
      val (p', binders) = e.eta-transform
      (Parens(p', nm, pre, r), binders)
    App(f, args, r) ->
      val (f', binders) = f.eta-transform
      val (args', binders') = args.map(fn((n, e)){
          val (e', bs) = e.pretend-decreasing.eta-transform
          ((n, e'), bs)
        }).unzip
      (App(f', args', r), binders ++ binders'.concat)
    _ -> (ue, [])

fun test()
  "Helpers!".println