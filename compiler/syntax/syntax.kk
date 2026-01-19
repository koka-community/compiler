//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 07/12/25: Commit 752748d

import std/num/float64
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linear-set
import std/core-extras
import std/core/undiv

effect val current-program : program<user-type, user-kind>

fun current-modname(): current-program name
  current-program.name

pub struct program<t, k>
  source: source
  name: name
  name-range: range
  typedefs: list<typedef-group<t,k>>
  defs: def-groups<t>
  imports: imports
  externals: externals
  fix-defs: fix-defs
  doc: string

fun program/show(Program(_, n, _, typedefs, defs, imports, externals, fix-defs, _):program<t,k>, ?t/show: (t) -> _ string, ?k/show: (k) -> _ string): _ string
  n.name/name/show ++ ":\n" ++ "typedefs " ++ typedefs.list/show ++ "\n" ++ "defs " ++ defs.list/show ++ "\n" ++ 
  "imports " ++ imports.list/show ++ "\n" ++ "externals " ++ externals.list/show ++ "\n" ++ 
  "fix-defs " ++ fix-defs.list/show ++ "\n"
  
alias user-program = program<user-type, user-kind>;
alias user-expr = expr<user-type>;
alias user-def = def<user-type>;
alias user-def-group = def-group<user-type>;
alias user-typedef = typedef<user-type, user-type, user-kind>;
alias user-typedef-group = typedef-group<user-type, user-kind>;
alias user-user-con = user-con<user-type, user-type, user-kind>;
alias user-pattern = pattern<user-type>
alias user-branch = branch<user-type>
alias user-guard = guard<user-type>
alias user-handler-branch = handler-branch<user-type>
alias user-value-binder = value-binder<()>
alias user-type-binder = type-binder<user-kind>

alias externals = list<external>;

type external
  External(
    name: name, 
    t: user-type, 
    params: list<param-info>, 
    name-range: range, 
    range: range, 
    inlineCall: list<(target, external-call)>, 
    vis: visibility, 
    fipAnnot: fipT, 
    doc: string)
  ExternalImport(
    eImport: list<(target,list<(string, string)>)>, 
    range: range)

fun external/show(e: external): _ string
  match e
    External(name, t, params, name-range, range, inlineCall, vis, fipAnnot, doc) -> 
      "External " ++ name.name/name/show ++ " " ++ t.show ++ " " ++ params.list/show ++ " " ++ name-range.show ++ " " ++ range.show ++ " " ++ 
      inlineCall.list/show ++ " " ++ vis.show ++ " " ++ fipAnnot.show ++ " " ++ doc.show
    ExternalImport(eImport, range) -> "ExternalImport " ++ eImport.list/show(?show=fn((t:target, l:list<(string,string)>)) t.show ++ " " ++ l.list/show) ++ " " ++ range.show

value type external-call
  ExternalInline(content: string)
  ExternalCall(call: string)

fun externcall/show(e: external-call): string
  match e
    ExternalInline(content) -> "ExternalInline " ++ content
    ExternalCall(call) -> "ExternalCall " ++ call

alias fix-defs = list<fix-def>;

type fix-def
  FixDef(
    name: name,
    fixity: fixity,
    range: range,
    vis: visibility
  )

fun fixdef/show(f: fix-def): string
  f.name.name/name/show ++ " " ++ f.fixity.show ++ " " ++ f.range.show ++ " " ++ f.vis.show

alias imports = list<kimport>;

struct kimport
  name: name // module name
  fullName: name // fully qualified module name
  nameRange: range
  fullNameRange: range
  range: range // range of the full import declaration
  vis: visibility // visibility of the module
  open: bool // Used in the IDE to make all definitions visible

fun kimport/show(i: kimport): string
  i.name.name/name/show ++ " " ++ i.fullName.name/name/show ++ " " ++ i.range.show ++ " " ++ i.vis.show

alias typedef-groups<t,k> = list<typedef-group<t,k>>;

value type typedef-group<t,k>
  TypeDefRec(defs: list<typedef<t,t,k>>)
  TypeDefNonRec(tdef: typedef<t,t,k>)

fun typedefgroup/show(t: typedef-group<t,k>, ?t/show: (t) -> _ string, ?k/show: (k) -> _ string): _ string
  match t
    TypeDefRec(defs) -> "TypeDefRec " ++ defs.list/show
    TypeDefNonRec(d) -> "TypeDefNonRec " ++ d.show

type typedef<t,u,k>
  Synonym(
    binder: type-binder<k>, 
    params: list<type-binder<k>>, 
    synonym: t, 
    range: range, 
    vis: visibility, 
    doc: string)
  DataType(
    binder: type-binder<k>, 
    params: list<type-binder<k>>, 
    constrs: list<user-con<t,u,k>>, 
    range: range, 
    vis: visibility, 
    sort: data-kind, 
    ddef: data-def, 
    deffect: data-effect, 
    doc: string)

fun typedef/show(td: typedef<t,u,k>, ?t/show: (t) -> _ string, ?u/show: (u) -> _ string, ?k/show: (k) -> _ string): _ string
  match td
    Synonym(binder, params, synonym, range, vis, doc) -> "Synonym " ++ binder.show ++ " " ++ params.list/show ++ " " ++ synonym.t/show ++ " " ++ range.show ++ " " ++ vis.show ++ " " ++ doc.show
    DataType(binder, params, constrs, range, vis, sort, ddef, deffect, doc) -> 
      "DataType " ++ binder.show ++ " " ++ params.list/show ++ " " ++ constrs.list/show ++ " " ++ 
      range.show ++ " " ++ vis.show ++ " " ++ sort.show ++ " " ++ ddef.show ++ " " ++ deffect.show ++ " " ++ doc.show

type type-binder<k>
  TypeBinder(
    name: name,
    kind: k,
    name-range: range,
    range: range
  )

fun tb/show(t: type-binder<k>, ?show: (k) -> _ string): _ string
  t.name.show ++ " " ++ t.kind.show ++ " " ++ t.name-range.show ++ " " ++ t.range.show

type user-con<t, u, k>
  UserCon(
    name: name, 
    existentials: list<type-binder<k>>,
    params: list<(visibility, value-binder<t, maybe<expr<u>>>)>,
    result: maybe<t>, // used internally for limited GADT's (for now)
    mblazy: maybe<(fipT, expr<u>)>, // lazy constructor?
    name-range: range,
    range: range, // full range
    vis: visibility,
    doc: string  
  )

fun con/show(u: user-con<t,u,k>, ?t/show: (t) -> _ string, ?u/show: (u) -> _ string, ?k/show: (k) -> _ string): _ string
  u.name.show ++ " " ++ u.existentials.list/show ++ " " ++ u.params.list/show ++ " " ++ u.result.show ++ " " ++ u.name-range.show ++ " " ++ u.range.show ++ " " ++ u.vis.show ++ " " ++ u.doc.show

alias def-groups<t> = list<def-group<t>>;
  
type def-group<t>
  DefRec(defs: list<def<t>>)
  DefNonRec(d: def<t>)

fun dg/show(d: def-group<t>, ?show: (t) -> _ string): _ string
  match d
    DefRec(defs) -> "DefRec " ++ defs.list/show
    DefNonRec(d) -> "DefNonRec " ++ d.show

alias defs<t> = list<def<t>>;

type value-binder<t,e>
  ValueBinder(
    name: name,
    binderType: t, // Always present for constructors
    expr: e, // always present for definitions as 'Expr t'
                  // functions and constructor parameters use 'Maybe (Expr t)' for default values.
                  // Pattern bindings ('PatVar') use unit '()'.
    name-range: range,
    range: range // full range
  )

fun vb/show(v: value-binder<t,v>, ?t/show: (t) -> _ string, ?e/show: (v) -> _ string): _ string
  v.name.show ++ " " ++ v.binderType.t/show ++ " " ++ v.expr.e/show ++ " " ++ v.name-range.show ++ " " ++ v.range.show

struct def<t>
  binder: value-binder<(), expr<t>>
  range: range
  visibility: visibility
  sort: def-sort
  defInline: def-inline
  doc: string;

fun def/show(d: def<t>, ?show: (t) -> _ string): _ string
  d.binder.show ++ " " ++ d.range.show ++ " " ++ d.visibility.show ++ " " ++ d.sort.show ++ " " ++ d.defInline.show ++ " " ++ d.doc

fun defIsVal(d: def<t>): bool
  !d.sort.is-fun

val guardTrue = Var(nameTrue, False, range/null)

type expr<t>
  Lam(binder: list<value-binder<maybe<t>,maybe<expr<t>>>>, e: expr<t>, top-level: bool, range: range)
  Let(d: def-group<t>, e: expr<t>, range: range)
  Bind(d: def<t>, e: expr<t>, range: range)
  App(e: expr<t>, args: list<(maybe<(name, range)>, expr<t>)>, range: range)
  Var(name: name, isOp: bool, range: range) // The var is an op
  Literal(l: lit, range: range = l.range)
  Ann(e: expr<t>, t: t, range: range)
  Case(e: expr<t>, cases: list<branch<t>>, lazy: bool, range: range)
  Parens(e: expr<t>, name: name, d: string, range: range) // name and string are used for the range map
  Inject(t: t, e: expr<t>, behind: bool, range: range)
  Handler(
    sort: handler-sort, 
    scope: handler-scope, 
    hOverride: handler-override, 
    allowMask: maybe<bool>, 
    hEffect: maybe<t>, 
    localPars: list<value-binder<maybe<t>, ()>>, 
    initially: maybe<expr<t>>,
    hReturn: maybe<expr<t>>, 
    finally: maybe<expr<t>>, 
    branches: list<handler-branch<t>>, 
    declRange: range, 
    range: range)

// fun expr/show(expr: expr<t>): string
//   ""

fun expr/show(expr: expr<t>, ?show: (t) -> _ string): _ string
  match expr
    // Lam(binder, e, rng) -> "Lam " ++ binder.list/show ++ " " ++ e.show ++ " " ++ rng.show
    // Let(d, e, rng) -> "Let " ++ d.dg/show ++  " " ++ e.expr/show ++ " " ++ rng.show 
    // Bind(d, e, rng) -> "Bind " ++ d.show ++ " " ++ e.show ++ " " ++ rng.show
    // App(e, args, rng) -> "App " ++ e.show ++ " " ++ args.list/show(?show=fn((mn, e')) mn.show(?show=fn((n,_)) n.show) ++ "=" ++ expr/show(e')) ++ " " ++ rng.show
    Var(n, isOp, rng) -> "Var " ++ n.show ++ " " ++ isOp.show ++ " " ++ rng.show
    Literal(l) -> "Literal " ++ l.show
    Ann(e, t, rng) -> "Ann " ++ e.show ++ " " ++ t.show ++ " " ++ rng.show
    // Case(e, cases, rng) -> "Case " ++ e.show ++ " " ++ cases.list/show ++ " " ++ rng.show
    Parens(e, n, d, rng) -> "Parens " ++ e.show ++ " " ++ n.show ++ " " ++ d ++ " " ++ rng.show
    // Inject(t, e, behind, rng) -> "Inject " ++ t.show ++ " " ++ e.show ++ " " ++ behind.show ++ " " ++ rng.show
    _ -> ""
    // Handler(sort, scope, hOverride, allowMask, hEffect, localPars, initially, hReturn, fin, branches, declRange, rng) -> 
      // "Handler " ++ sort.show ++ " " ++ scope.show ++ " " ++ hOverride.show ++ " " ++ 
      // allowMask.show ++ " " ++ hEffect.show ++ " " ++ localPars.list/show ++ " " ++ 
      // initially.show ++ " " ++ hReturn.show ++ " " ++ fin.show ++ " " ++
      // branches.list/show ++ " " ++ declRange.show ++ " " ++ rng.show

// FROM Infer.hs
fun is-annot(e: expr<t>): bool
  match e 
    Parens(e') -> e'.is-annot
    Ann() -> True
    Let(_, e') -> e'.is-annot
    Bind(_, e') -> e'.is-annot
    _ -> False

fun root-expr(e: expr<t>): expr<t>
  match e
    Parens(e') -> e'.root-expr
    _ -> e

fun wrap-optional(expr: expr<t>): expr<t>
  App(Var(nameOptional, False, null), [(Nothing, expr)], expr.range)

val optionalNone = Var(nameOptionalNone, False, null)

fun expr/uses-locals(expr: expr<t>, lvars : name-set): _ bool
  match expr
    App(Var(newLocal, False), [_, (_, Parens(Lam([ValueBinder(name)], body)))]) | newLocal == nameLocalVar -> body.uses-locals(lvars.remove(name)) // Fragile, expects this form from the parser
    Lam(_, e) -> e.uses-locals(lvars)
    Let(defs, e) -> defs.uses-locals(lvars) || e.uses-locals(lvars)
    Bind(def, e) -> def.uses-locals(lvars) || e.uses-locals(lvars)
    App(f, nargs) -> Cons(f, nargs.map(snd)).uses-locals(lvars)
    Ann(e) -> e.uses-locals(lvars)
    Case(e, brs) -> e.uses-locals(lvars) || brs.uses-locals(lvars)
    Parens(e) -> e.uses-locals(lvars)
    Handler(_, _, _, _, _, _, reinit, ret, fin, ops) -> 
      reinit.uses-locals(lvars) || ret.uses-locals(lvars) || fin.uses-locals(lvars) || ops.uses-locals(lvars)
    Inject(_, e) -> e.uses-locals(lvars)
    Var(n, _, _) -> lvars.member(n)
    _ -> False

fun list/uses-locals(l: list<a>, lvars: name-set, ?uses-locals: (a, name-set) -> _ bool): _ bool
  match l
    Cons(x, xs) -> x.uses-locals(lvars) || xs.uses-locals(lvars)
    Nil -> False
fun maybe/uses-locals(m: maybe<a>, lvars: name-set, ?uses-locals: (a, name-set) -> _ bool): _ bool
  match m
    Just(x) -> x.uses-locals(lvars)
    Nothing -> False
fun def-group/uses-locals(dg: def-group<t>, lvars: name-set): _ bool
  match dg
    DefRec(defs) -> defs.uses-locals(lvars)
    DefNonRec(d) -> d.uses-locals(lvars)
fun def/uses-locals(d: def<t>, lvars: name-set): _ bool
  d.binder.expr.uses-locals(lvars)
fun guard/uses-locals(g: guard<t>, lvars: name-set): _ bool
  g.guardTest.uses-locals(lvars) || g.guardExpr.uses-locals(lvars)
fun branch/uses-locals(b: branch<t>, lvars: name-set): _ bool
  b.branchGuard.uses-locals(lvars)
fun op/uses-locals(o: handler-branch<t>, lvars: name-set): _ bool
  o.branchExpr.uses-locals(lvars)

fun extract-matched-names(e: expr<t>)
  fun extract-matched-namesx(expr: expr<t>)
    match expr
      Var(name, _, _) -> [name]
      _ -> []
  match e
    Parens(e') -> e'.extract-matched-names
    App(Var(name), args) | name.is-name-tuple -> args.map(_.snd.extract-matched-namesx).concat
    _ -> e.extract-matched-namesx

fun eta-expand(n: int, rng: range, fbody: (expr<t> -> expr<t>) -> expr<t>): expr<t>
  val nameFixed = list(1, n).map(fn(i) make-hidden-name("arg", ("x" ++ i.show).new-name))
  val argsFixed = nameFixed.map((Nothing, Var(_, False, rng)))
  val body = fbody(fn(f') App(f', argsFixed, rng))
  Lam(nameFixed.map(ValueBinder(_, Nothing, Nothing, rng, rng)), body, False, rng)

fun is-annotated-binder(vb: value-binder<maybe<t>,e>): bool
  vb.binderType.is-just

type handler-override
  HandlerOverride
  HandlerNoOverride

fun hov/show(h: handler-override): string
  match h
    HandlerOverride -> "HandlerOverride"
    HandlerNoOverride -> "HandlerNoOverride"

type handler-scope
  HandlerScoped
  HandlerNoScope

fun hs/show(h: handler-scope): string
  match h
    HandlerScoped -> "HandlerScoped"
    HandlerNoScope -> "HandlerNoScope"

type handler-branch<t>
  HandlerBranch(
    branchName: name,
    branchPars: list<value-binder<maybe<t>, ()>>,
    branchExpr: expr<t>,
    branchSort: operation-sort,
    branchNameRange: range,
    branchPatRange: range
  )

fun hb/show(h: handler-branch<t>, ?show: (t) -> _ string): _ string
  h.branchName.show ++ " " ++ h.branchPars.list/show ++ " " ++ h.branchExpr.show ++ " " ++
  h.branchSort.show ++ " " ++ h.branchNameRange.show ++ " " ++ h.branchPatRange.show
  
struct branch<t>
  branchPattern: pattern<t>
  branchGuard: list<guard<t>>

fun branch/show(b: branch<t>, ?show: (t) -> _ string): _ string
  b.branchPattern.show ++ " " ++ b.branchGuard.list/show
  
struct guard<t>
  guardTest: expr<t>
  guardExpr: expr<t>

fun guard/show(g: guard<t>, ?show: (t) -> _ string): _ string
  g.guardTest.show ++ " " ++ g.guardExpr.show

type pattern<t>
  PatWild(range: range)
  PatVar(patvar: value-binder<maybe<t>, pattern<t>>, range: range= patvar.range)
  PatAnn(p: pattern<t>, t: t, range: range)
  PatCon(name: name, args: list<(maybe<(name, range)>, pattern<t>)>, nameRange: range, range: range)
  PatParens(p: pattern<t>, range: range)
  PatLit(value: lit, range:range = value.range)

fun pat/show(p: pattern<t>, ?show: (t) -> _ string): _ string
  match p
    PatWild(range) -> "PatWild " ++ range.show
    // PatVar(patvar) -> "PatVar " ++ patvar.show
    // PatAnn(p, t, range) -> "PatAnn " ++ p.show ++ " " ++ t.show ++ " " ++ range.show
    // PatCon(name, args, nr, range) -> 
    //   "PatCon " ++ name.name/name/show ++ " " ++ // args.list/show(?show=fn((mn, p')) mn.show(?show=fn((n,_)) n.name/name/show) ++ p'.show) ++
    //   " " ++ nr.show ++ " " ++ range.show
    // PatParens(p, range) -> "PatParens " ++ p.show ++ " " ++ range.show
    // PatLit(value) -> "PatLit " ++ value.show
    _ -> ""

type lit
  LitInt(value: int, range: range)
  LitFloat(value: float64, range: range)
  LitChar(value: string, range: range)
  LitString(value: string, range: range)

fun lit/show(l: lit): string
  match l
    LitInt(v, r) -> v.show ++ " " ++ r.show
    LitFloat(v, r) -> v.show ++ " " ++ r.show
    LitChar(v, r) -> v ++ " " ++ r.show
    LitString(v, r) -> v ++ " " ++ r.show

// Types and kinds
alias user-types<k> = list<kuser-type<k>>

type user-quantifier
  QSome
  QForall
  QExists

fun uquant/show(u: user-quantifier): string
  match u
    QSome -> "QSome"
    QForall -> "QForall"
    QExists -> "QExists"

// Higher ranked types
type kuser-type<k>
  TpQuan(q: user-quantifier, b: type-binder<k>, kind: kuser-type<k>, range: range)
  TpFun(a: list<(name, kuser-type<k>)>, b: kuser-type<k>, c: kuser-type<k>, range: range)
  TpApp(a: kuser-type<k>, b: list<kuser-type<k>>, range: range)
  TpVar(name: name, range: range)
  TpCon(name: name, range: range)
  TpParens(t: kuser-type<k>, range: range)
  TpAnn(t: kuser-type<k>, kind: k)

alias user-type = kuser-type<user-kind>

fun ut/show(u: user-type): _ string
  match u
    TpQuan(q, b, kind, range) -> "TpQuan " ++ q.show ++ " " ++ b.show ++ " " ++ kind.show ++ " " ++ range.show
    TpFun(a, b, c, range) -> "TpFun " ++ a.list/show(?show=fn((n, ut)) n.name/name/show ++ ":" ++ ut.show) ++ " " ++ b.show ++ " " ++ c.show ++ " " ++ range.show
    TpApp(a, b, range) -> "TpApp " ++ a.show ++ " " ++ b.list/show ++ " " ++ range.show
    TpVar(n, range) -> "TpVar " ++ n.name/name/show ++ " " ++ range.show
    TpCon(n, range) -> "TpCon " ++ n.name/name/show ++ " " ++ range.show
    TpParens(t, range) -> "TpParens " ++ t.show ++ " " ++ range.show
    TpAnn(t, kind) -> "TpAnn " ++ t.show ++ " " ++ kind.show

type user-kind
  KindCon(name: name, range: range)
  KindArrow(from: user-kind, to: user-kind)
  KindParens(kind: user-kind, range: range)
  KindNone // Flags no explicit kind annotation

fun uk/show(u: user-kind): string
  match u
    KindCon(name, range) -> "KindCon " ++ name.name/name/show ++ " " ++ range.show
    KindArrow(from, to) -> "KindArrow " ++ from.show ++ " " ++ to.show
    KindParens(kind, range) -> "KindParens " ++ kind.show ++ " " ++ range.show
    KindNone -> "KindNone"



// Range

fun kut/range(tp: kuser-type<k>, ?range: (k) -> range): range
  match tp
    TpQuan(range=r) -> r
    TpFun(range=r) -> r
    TpApp(range=r) -> r
    TpVar(range=r) -> r
    TpCon(range=r) -> r
    TpParens(range=r) -> r
    TpAnn(userTp, kind) -> Range(userTp.range.start, kind.range.end, False)

fun uk/range(uk: user-kind): range
  match uk
    KindCon(range=range) -> range
    KindArrow(k1, k2) -> Range(k1.range.start, k2.range.end, k1.range.hidden || k2.range.hidden)
    KindParens(range=range) -> range
    KindNone -> range/null

fun uhb/range(uhb: user-handler-branch): range
  uhb.branchPatRange.combine(uhb.branchExpr.range)

// free type variables
fun maybe/free-type-vars(m: maybe<a>, ?free-type-vars: (a) -> _ name-set): _ name-set
  match m
    Nothing -> LinearSet([])
    Just(x) -> ?free-type-vars(x)

fun list/free-type-vars(l: list<a>, ?free-type-vars: (a) -> _ name-set): _ name-set
  l.foldl(LinearSet([]), fn(s:name-set, x) s + ?free-type-vars(x))

fun kut/free-type-vars(tp: kuser-type<k>): _ name-set
  match tp
    TpQuan(_, TypeBinder(name), tp, _) -> tp.free-type-vars - name
    TpFun(args, eff, tp) -> free-type-vars(Cons(tp,Cons(eff,args.map(snd))))
    TpApp(tp, args) -> tp.free-type-vars + args.free-type-vars
    TpVar(name) -> LinearSet([name])
    TpCon -> LinearSet([])
    TpParens(tp) -> tp.free-type-vars
    TpAnn(tp) -> tp.free-type-vars

// access definitions
fun def/body(d: def<t>): expr<t>
  d.binder.expr

fun def/name(d: def<t>): name
  d.binder.name

fun def/type(d: def<t>): maybe<t>
  match d.binder.expr
    Ann(_, tp) -> Just(tp)
    _ -> Nothing

fun typedef/name(d: typedef<t,u,k>): name
  d.binder.name

fun typdef/name-range(d: typedef<t,u,k>): range
  d.binder.name-range

fun program/null(n: name)
  Program(source/null, n, range/null, [], [], [preludeImport], [], [], "")

// Import declaration for the standard prelude
val preludeImport = Kimport(nameSystemCore, nameSystemCore, null, null, null, Private, False)

fun make-program(n: name, tdefs: list<typedef<t,t,k>>, defs: list<def<t>>): program<t,k>
  Program(source/null, n, range/null, [TypeDefRec(tdefs)], [DefRec(defs)], [], [], [], "")

fun add-imports(p: program<t,k>, imps: list<kimport>): program<t,k>
  Program(p.source, p.name, p.name-range, p.typedefs, p.defs, imps ++ p.imports, p.externals, p.fix-defs, p.doc)

fun remove-tdefs(tdefs: list<typedef<t,t,k>>, tdefs0: list<typedef<t,t,k>>): list<typedef<t,t,k>>
  tdefs0.foldl(tdefs, fn(acc, tdef) acc.filter(fn(tdef') tdef'.name != tdef.name))

fun remove-defs(defs: list<def<k>>, defs0: list<def<k>>): list<def<k>>
  defs0.foldl(defs, fn(acc, def) acc.filter(fn(def') def'.name != def.name))

fun add-defs(p: program<t,k>, tdefs0: list<typedef<t,t,k>>, defs0: list<def<t>>): _ program<t,k>
  val tdefs' = match p.typedefs
    [] -> [TypeDefRec(tdefs0)]
    [TypeDefRec(ts)] -> [TypeDefRec(ts.remove-tdefs(tdefs0) ++ tdefs0)]
    _ -> fail("syntax/syntax: can not add type definitions to processed tree")
  val defs' = match p.defs
    [] -> [DefRec(defs0)]
    [DefRec(ds)] -> [DefRec(ds.remove-defs(defs0) ++ defs0)]
    _ -> fail("syntax/syntax: can not add definitions to processed tree")
  Program(p.source, p.name, p.name-range, tdefs', defs', p.imports, p.externals, p.fix-defs, p.doc)

fun remove-all-defs(p: program<t,k>): program<t,k>
  p(defs=[])

fun program-remove-def(p: program<t,k>, nm: name): program<t,k>
  fun filter-tdef(tdefg: typedef-group<t,k>): typedef-group<t,k>
    match tdefg
      TypeDefRec(tdefs) -> TypeDefRec(tdefs.filter(fn(tdef) tdef.name != nm))
      TypeDefNonRec(tdef) -> TypeDefNonRec(tdef)
  fun filterDef(defg: def-group<t>): def-group<t>
    match defg
      DefRec(defs) -> DefRec(defs.filter(fn(def) def.name != nm))
      DefNonRec(def) -> DefNonRec(def)
  Program(p.source, p.name, p.name-range, p.typedefs.map(filter-tdef), p.defs.map(filterDef), p.imports, p.externals, p.fix-defs, p.doc)

fun program-find(p: program<t,k>, nm: name): maybe<range>
  fun trange(tdefg: typedef-group<t,k>): list<(name, range)>
    match tdefg
      TypeDefRec(tdefs) -> tdefs.map(fn(tdef) (tdef.name, tdef.name-range))
      TypeDefNonRec(tdef) -> [(tdef.name, tdef.name-range)]
  fun drange(defg: def-group<t>): list<(name, range)>
    match defg
      DefRec(defs) -> defs.map(fn(def) (def.name, def.range))
      DefNonRec(def) -> [(def.name, def.range)]
  val names = p.typedefs.map(trange).concat ++ p.defs.map(drange).concat
  names.find(fn((n, _)) n == nm).map(snd)
