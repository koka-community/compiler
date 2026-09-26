// Port of src/Core/Check.hs -- the Core-F type checker.
//
// A well-formedness / type-preservation check over Core, run between
// optimization passes when `--checkcore` is given. It never changes the
// program: on the first mismatch it reports ONE warning (upstream
// `liftError (warningMsg (warningMessageKind ErrStatic rangeNull doc))`) and
// abandons the rest of the check: the first mismatch is the useful one.
//
// Upstream threads a `CheckEnv` record (liberalEff, allowPartialApps, gamma,
// prettyEnv, currentDef) through a reader monad. Here the two constant fields
// and the current-definition stack are ambient value effects, while `gamma` is
// threaded explicitly -- it is extended at every binder for fidelity with
// upstream's `extendGamma`, but nothing reads it: upstream's only consumer is
// `lookupVar`, called solely from the dead `findConstrArgs`. `check` takes the
// type of a `Var`/`Con` from the `TName` itself.
//
// Not ported: `findConstrArgs`. Its only call site is commented out upstream
// too (`checkPattern`'s `PatCon` branch), so porting it would add a dead
// dependency on `instantiateNoEx`.
module compiler/core/check

import std/data/rb-set
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/color-scheme
import compiler/common/unique
import compiler/platform/config
import compiler/common/syntax
import compiler/lib/pprint
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/assumption
import compiler/type/pretty
import compiler/type/unify
import compiler/core/core
import compiler/core/corevar
import compiler/core/pretty

// upstream `CheckEnv`, one ambient value per field
effect val liberal-eff: bool
effect val allow-partial-apps: bool
effect val current-check-def: list<def>

// upstream's `Err` short-circuit: the first failure ends the whole check
effect check-abort
  final ctl check-fail(d: doc): a

// The checker's ambient row. Spelled out because the mutually recursive
// walk (check-def -> check -> check-defgroups -> check-def) re-installs
// `current-check-def` on the way round, and inference cannot decide on its
// own that the re-installed handler discharges the same effect.
alias check-eff = <liberal-eff,allow-partial-apps,current-check-def,check-abort,
                   colors,comp-flags,unique,div,exn>

pub fun check-core(liberal-effects: bool, allow-partials: bool, gamma0: gamma): _ ()
  with handler
    final ctl check-fail(d) msg/add-warning(warning-message-kind(d, range/null, ErrStatic))
  with val liberal-eff = liberal-effects
  with val allow-partial-apps = allow-partials
  with val current-check-def = []
  check-defgroups(gamma0, get-core-defs())
  ()

//----------------------------------------------------------------------
// Definition groups
//
// To check a recursive definition group, assume the type of each definition
// is correct, add all of them to the environment, then check each definition.
//----------------------------------------------------------------------

// Each group's own definitions are in
// scope while checking that group (so a recursive group may refer to itself)
// and for everything after it. Upstream passes the continuation; here the
// extended gamma is returned instead, which the caller hands to the body.
fun check-defgroups(g: gamma, dgs: def-groups): check-eff gamma
  match dgs
    Nil -> g
    Cons(dg, rest) ->
      val g2 = g.defgroup-gamma(dg)
      dg.check-defgroup(g2)
      check-defgroups(g2, rest)

fun defgroup-defs(dg: def-group): list<def>
  match dg
    DefRec(ds) -> ds
    DefNonRec(d) -> [d]

fun defgroup-gamma(g: gamma, dg: def-group): _ gamma
  g.extends(dg.defgroup-defs.map(fn(d) core-def-info(d, 0)))

fun check-defgroup(dg: def-group, g: gamma): check-eff ()
  dg.defgroup-defs.foreach(fn(d) check-def(g, d))

fun check-def(g: gamma, d: def): check-eff ()
  with val current-check-def = Cons(d, current-check-def)
  val tp = check(g, d.defExpr)
  match-sub("checking annotation on definition", {d.def/doc-default}, d.ktype, tp)

fun core-name-info(tn: tName): _ (name, name-info)
  (tn.get-name, create-name-infoX(Public, tn.get-name, 0, DefVal, range/null, tn.type-of, ""))

//----------------------------------------------------------------------
// Expressions
//----------------------------------------------------------------------

fun check(g: gamma, ex: expr): check-eff ktype
  match ex
    Lam(pars, eff, body) ->
      val tpRes = check(g.extends(pars.map(core-name-info)), body)
      TFun(pars.map(fn(TName(nm, tp)) (nm, tp)), eff, tpRes)
    Var(tname) -> tname.type-of
    Con(tname) -> tname.type-of
    App(f, args) ->
      val tpFun = check(g, f)
      val tpArgs = args.map(fn(a) check(g, a))
      match tpFun.split-fun-type
        Nothing -> check-fail("expecting function type in application".text)
        Just((tpPars, eff, tpRes)) ->
          tpPars.zip(tpArgs).foreach fn(((_, formal), actual))
            match-sub("comparing formal and actual argument", {ex.expr/doc-default}, formal, actual)
          if !allow-partial-apps then tpRes
          else
            val morePars = tpPars.drop(tpArgs.length)
            if morePars.is-nil then tpRes else TFun(morePars, eff, tpRes)
    TypeLam(tvars, body) -> quantify-type(tvars, check(g, body))
    TypeApp(e, tps) ->
      val tpTForall = check(g, e)
      val (tvars, tp) = tpTForall.split-type-scheme
      // actual equality on kinds is fine: any kind variables have been
      // substituted by the time kind application ran
      if tps.length > tvars.length ||
         tvars.zip(tps).any(fn((t, tp2)) t.kind != tp2.kind) then
        check-fail("kind error in type application:".text |+| ex.expr/doc-default |-|
                   " applied to:".text |+| tpTForall.ktp/pretty)
      else
        tforall(tvars.drop(tps.length), new/sub(tvars.zip(tps)) |-> tp)
    ELit(l) -> l.type-of
    Let(dgs, body) ->
      val g2 = check-defgroups(g, dgs)
      check(g2, body)
    Case(exprs, branches) ->
      val tpScrutinees = exprs.map(fn(e) check(g, e))
      val tpBranches = branches.map(fn(b) check-branch(g, tpScrutinees, b)).concat
      map-conseq(tpBranches) fn(t1, t2)
        type-match("verifying that all branches have the same type", {ex.expr/doc-default}, t1, t2)
      match tpBranches
        Cons(t) -> t
        Nil -> check-fail("case expression without branches".text)

fun map-conseq(ts: list<ktype>, f: (ktype, ktype) -> e ()): e ()
  match ts
    Cons(t1, rest as Cons(t2)) ->
      f(t1, t2)
      map-conseq(rest, f)
    _ -> ()

// Quantify only when there are variables left
fun tforall(vars: list<type-var>, tp: ktype): ktype
  if vars.is-nil then tp else quantify-type(vars, tp)

//----------------------------------------------------------------------
// Branches and patterns
//----------------------------------------------------------------------

fun check-branch(g: gamma, tpScrutinees: list<ktype>, Branch(patterns, guards): branch): check-eff list<ktype>
  tpScrutinees.zip(patterns).foreach(check-pattern)
  val vars = patterns.map(bound-vars).unions.list.map(core-name-info)
  val g2 = g.extends(vars)
  guards.map(fn(gu) check-guard(g2, gu))

fun check-guard(g: gamma, Guard(guard, ex): guard): check-eff ktype
  val gtp = check(g, guard)
  type-match("verify that the guard is a boolean expression", {guard.expr/doc-default}, gtp, typeBool)
  check(g, ex)

fun check-pattern((tpScrutinee, pat): (ktype, pattern)): _ ()
  match pat
    PatCon(_, args, _, tpargs) -> tpargs.zip(args).foreach(check-pattern)
    PatVar(tname) ->
      type-match("comparing constructor argument to case annotation", {pat.pat/doc-default}, tpScrutinee, tname.type-of)
    PatLit(l) ->
      type-match("comparing literal pattern to scrutinee", {pat.pat/doc-default}, tpScrutinee, l.type-of)
    PatWild -> ()

//----------------------------------------------------------------------
// Type comparison
//----------------------------------------------------------------------

// `b` may be used where an `a` is expected. With liberal effects, a function
// type matches when its arguments and result match and its HANDLED effects
// agree -- the unhandled part of the row may differ.
fun match-sub(whn: string, fdoc: () -> _ doc, a: ktype, b: ktype): _ ()
  if !liberal-eff then type-match(whn, fdoc, a, b)
  else match (a.split-fun-type, b.split-fun-type)
    (Just((targs1, teff1, tres1)), Just((targs2, teff2, tres2))) | targs1.length == targs2.length ->
      type-match(whn, fdoc, tres1, tres2)
      targs1.zip(targs2).foreach(fn(((_, t1), (_, t2))) type-match(whn, fdoc, t1, t2))
      match-sub-eff(whn, fdoc, teff1, teff2)
    _ -> type-match(whn, fdoc, a, b)

fun match-sub-eff(whn: string, fdoc: () -> _ doc, eff1: ktype, eff2: ktype): _ ()
  val (ls1, _) = eff1.extract-handled-effect
  val (ls2, _) = eff2.extract-handled-effect
  if ls1.length != ls2.length
    then show-check("handled effects do not match", whn, eff1, eff2, fdoc)
    else ls1.zip(ls2).foreach(fn((t1, t2)) type-match(whn, fdoc, t1, t2))

// In Core, comparing types means EXACT matches only: a unification that
// succeeds but produces a non-empty substitution is itself a failure.
// upstream `match`; renamed because `match` is a Koka keyword
fun type-match(whn: string, fdoc: () -> _ doc, a: ktype, b: ktype): _ ()
  match run-unify({ unify(a, b) })
    (Left(err), _) -> show-check("cannot unify (" ++ err.show ++ ")", whn, a, b, fdoc)
    (Right, subst) ->
      if subst.is-null then ()
      else show-check("non-empty substitution", whn, a, b, { pprint/empty })

fun show-check(err: string, whn: string, a: ktype, b: ktype, fdoc: () -> _ doc): _ a
  check-fail(show-message(err, whn, a, b, fdoc))

fun show-message(err: string, whn: string, a: ktype, b: ktype, fdoc: () -> _ doc): _ doc
  val docs = nice-types-default([a, b])
  val docA = docs.head.default(pprint/empty)
  val docB = docs.drop(1).head.default(pprint/empty)
  [err.text, "    ".text |+| docA, "  =~".text |+| docB,
   "when".text |+| whn.text, fdoc().indent(2)].vcat.align
