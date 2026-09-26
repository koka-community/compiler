// Port of Backend/C/ParcReuseSpec.hs (constructor reuse specialization)
// Reflects the upstream fix in commit 5013fd54b ("Fix: use Lit for constructor
// tags instead of Var in ParcReuseSpec"): constructor tags are emitted as
// integer literals (`ELit(LitInt(tag))`), never as `Var`.
module compiler/backend/c/parc-reuse-spec

import compiler/common/name
import compiler/common/name-prim
import compiler/common/failure
import compiler/common/unique
import compiler/type/type
import compiler/type/pretty
import compiler/kind/newtypes
import compiler/core/core
import compiler/lib/pprint
import std/core/undiv

//--------------------------------------------------------------------------
// Specialize reuse applications
//--------------------------------------------------------------------------

// Entry point: specialize `@alloc-at` applications on reused constructors
// throughout a whole core program. Mirrors `parcReuseSpecialize` upstream;
// `Newtypes` and `Pretty.Env` are ambient effects here (`newtypes-eff`,
// `pretty-eff`) instead of explicit reader parameters.
pub fun parc-reuse-specialize(c: core): _ core
  with val ru-current-def = []
  c(defs = c.defs.ru-def-groups)

//--------------------------------------------------------------------------
// Definition groups
//--------------------------------------------------------------------------

fun ru-def-groups(dgs: def-groups): _ def-groups
  dgs.map(ru-def-group)

fun ru-def-group(dg: def-group): _ def-group
  match dg
    DefRec(defs) -> DefRec(defs.map(ru-def))
    DefNonRec(d) -> DefNonRec(d.ru-def)

fun ru-def(d: def): _ def
  with ru-with-current-def(d)
  d(defExpr = d.defExpr.ru-expr)

//--------------------------------------------------------------------------
//
//--------------------------------------------------------------------------

fun ru-expr(expr: expr): _ expr
  match expr
    App(alloc as Var(allocAt, _), [reuse as Var(reuseName, info), conApp]) | nameAllocAt == allocAt.get-name ->
      val conApp' = conApp.ru-expr
      match ru-specialize(reuseName, info, conApp')
        Just(newExpr) -> newExpr
        Nothing -> App(alloc, [reuse, conApp'])
    TypeLam(tpars, body) -> TypeLam(tpars, body.ru-expr)
    TypeApp(body, targs) -> TypeApp(body.ru-expr, targs)
    Lam(pars, eff, body) -> Lam(pars, eff, body.ru-expr)
    App(f, args) -> App(f.ru-expr, args.map(ru-expr))

    Let([], body) -> body.ru-expr
    Let(Cons(DefNonRec(def), dgs), body) ->
      val def' = def.ru-def
      val rest = ru-expr(Let(dgs.pretend-decreasing, body))
      make-let([DefNonRec(def')], rest)
    Let(_, _) -> failure/fail("backend/c/parc-reuse-spec ru-expr: unexpected recursive let in reuse specialization")

    Case(scrutinees, branches) -> Case(scrutinees.map(ru-expr), branches.map(ru-branch))

    // Var, ELit, Con
    _ -> expr

fun ru-branches(branches: list<branch>): _ list<branch>
  branches.map(ru-branch)

fun ru-branch(b: branch): _ branch
  Branch(b.patterns, b.guards.map(ru-guard))

fun ru-guard(g: guard): _ guard
  Guard(g.test.ru-expr, g.body.ru-expr)

//--------------------------------------------------------------------------
// Specialization
//--------------------------------------------------------------------------

// Try to specialize an allocation at a reuse.
// We will only do this if we can get the necessary ConInfo
// and save at least a fourth of the necessary assignments.
fun ru-specialize(reuseName: tName, info: var-info, conApp: expr): _ maybe<expr>
  match (conApp, info)
    (App(conx, args), InfoReuse(PatCon(patConName, patConPatterns))) ->
      match conx.extract-conx
        Just((cname, repr)) ->
          match get-con-info(conx.type-of, cname.get-name)
            Just(ci) ->
              val matches = args.zipwith(patConPatterns, try-match)
              val needsTag = !(patConName == cname)
              val oldTagBenefit = if needsTag then 0 else 1
              val specialize = oldTagBenefit + matches.filter(is-match).length >= 1 + ((1 + args.length) / 4)
              if specialize then
                Just(ru-spec-conx(reuseName, cname, repr, ci, needsTag, repr.tag, conApp.type-of, fn(cargs) App(conx, cargs), matches))
              else Nothing
            Nothing -> Nothing
        Nothing -> Nothing
    _ -> Nothing

fun extract-conx(e: expr): maybe<(tName, con-repr)>
  match e
    Con(cname, repr) -> Just((cname, repr))
    TypeApp(Con(cname, repr), _) -> Just((cname, repr))
    _ -> Nothing

// Move dups before the allocation and emit:
// if (reuseName != NULL) { set tag and fields } else { allocate constructor without reuse }
fun ru-spec-conx(reuseName: tName, conName: tName, conRepr: con-repr, conInfo: con-info, needsTag: bool, tag: int,
                 resultType: ktype, makeConApp: (list<expr>) -> expr, matches: list<ru-match>): _ expr
  val (defss, assigns) = matches.map(ru-to-assign).unzip
  val fields = conInfo.params.map(fst)
  val nonMatching = fields.zip(assigns).filter(fn((_, (_, isMatch))) !isMatch).map(fn((nm, (e, _))) (nm, e))
  val reuseExpr =
    if needsTag
      then gen-con-tag-fields-assign(resultType, conName, conRepr, reuseName, tag, nonMatching)
      else gen-con-fields-assign(resultType, conName, conRepr, reuseName, nonMatching)
  val specExpr = make-if-expr(gen-reuse-is-valid(reuseName), reuseExpr, makeConApp(assigns.map(fst)))
  make-let(defss.concat, specExpr)

// A field either matches the pattern (no new assignment needed, possibly with
// a `dup` to move before the allocation) or needs to be (re-)assigned.
pub type ru-match
  RuMatch(pre: list<expr>, arg: expr)
  RuNoMatch(arg: expr)

pub fun is-match(m: ru-match): bool
  match m
    RuMatch -> True
    RuNoMatch -> False

// Determine if we write the same value back that is currently in this place.
// This is the case if the expression is:
//   - the same variable as in the pattern
//   - a dup on the same variable as in the pattern
//   - a unit constructor that was also in the pattern
// We do not check for non-unit constructors because these may be reused
// (and specialized) as well.
pub fun try-match(expr: expr, pat: pattern): ru-match
  match (expr, pat)
    // direct match (x == x)
    (Var(vname, _), PatVar(pname, _)) | vname == pname -> RuMatch([], expr)
    // match dup (x == dup(x))
    (App(Var(dname, _), [v as Var(vname, _)]), PatVar(pname, _)) | dname.get-name == nameDup && vname == pname -> RuMatch([expr], v)
    (Con(cname, _), PatCon(patName=patConName, pattern=[])) | cname == patConName -> RuMatch([], expr)
    (Con(cname, _), PatVar(_, PatCon(patName=patConName, pattern=[]))) | cname == patConName -> RuMatch([], expr)
    _ -> RuNoMatch(expr)

fun ru-to-assign(m: ru-match): _ (list<def-group>, (expr, bool /* is match? */))
  match m
    RuMatch(pres, arg) -> (pres.map(fn(pre) DefNonRec(make-def(name/nil, pre))), (arg, True))
    RuNoMatch(expr) ->
      if expr.is-total
        then ([], (expr, False))
        else
          val nm = unique-name("ru")
          val d = DefNonRec(make-def(nm, expr))
          val v = Var(TName(nm, expr.type-of), InfoNone)
          ([d], (v, False))

fun gen-reuse-is-valid(reuseName: tName): expr
  val typeReuseIsValid = TFun([(name/nil, typeReuse)], typeTotal, typeBool)
  App(Var(TName(nameReuseIsValid, typeReuseIsValid), InfoExternal("kk_likely(#1!=NULL)")), [Var(reuseName, InfoNone)])

// gen-con-tag-scan-fields-assign tp conName reuseName [(field1,expr1)...(fieldN,exprN)]
// generates:  c = (conName*)reuseName; c->scan_fsize = scan; c->tag = tag; c->field1 := expr1; ... ; c->fieldN := exprN; (tp*)(c)
// (currently unused within this pass; exposed for the not-yet-ported ParcReuse.hs)
pub fun gen-con-tag-scan-fields-assign(resultType: ktype, conName: tName, conRepr: con-repr, reuseName: tName, tag: int, scan: int, fieldExprs: list<(name, expr)>): _ expr
  val fieldTypes = fieldExprs.map(fn((nm, e)) (nm, e.type-of))
  val typeConFieldsAssign = TFun([(name/nil, reuseName.type-of), (name/nil, typeInt), (name/nil, typeInt)] ++ fieldTypes, typeTotal, resultType)
  App(Var(TName(nameConTagScanFieldsAssign, typeConFieldsAssign), InfoArity(0, fieldExprs.length + 2)),
      [Var(reuseName, InfoConField(conName, conRepr, TName(name/nil, typeReuse))), ELit(LitInt(tag)), ELit(LitInt(scan))] ++ fieldExprs.map(snd))

// gen-con-tag-fields-assign tp conName reuseName [(field1,expr1)...(fieldN,exprN)]
// generates:  c = (conName*)reuseName; c->tag = tag; c->field1 := expr1; ... ; c->fieldN := exprN; (tp*)(c)
pub fun gen-con-tag-fields-assign(resultType: ktype, conName: tName, conRepr: con-repr, reuseName: tName, tag: int, fieldExprs: list<(name, expr)>): _ expr
  val fieldTypes = fieldExprs.map(fn((nm, e)) (nm, e.type-of))
  val typeConFieldsAssign = TFun([(name/nil, reuseName.type-of), (name/nil, typeInt)] ++ fieldTypes, typeTotal, resultType)
  App(Var(TName(nameConTagFieldsAssign, typeConFieldsAssign), InfoArity(0, fieldExprs.length + 1)),
      [Var(reuseName, InfoConField(conName, conRepr, TName(name/nil, typeReuse))), ELit(LitInt(tag))] ++ fieldExprs.map(snd))

// gen-con-fields-assign tp conName reuseName [(field1,expr1)...(fieldN,exprN)]
// generates:  c = (conName*)reuseName; c->field1 := expr1; ... ; c->fieldN := exprN; (tp*)(c)
pub fun gen-con-fields-assign(resultType: ktype, conName: tName, conRepr: con-repr, reuseName: tName, fieldExprs: list<(name, expr)>): _ expr
  val fieldTypes = fieldExprs.map(fn((nm, e)) (nm, e.type-of))
  val typeConFieldsAssign = TFun([(name/nil, reuseName.type-of)] ++ fieldTypes, typeTotal, resultType)
  App(Var(TName(nameConFieldsAssign, typeConFieldsAssign), InfoArity(0, fieldExprs.length + 1)),
      [Var(reuseName, InfoConField(conName, conRepr, TName(name/nil, typeReuse)))] ++ fieldExprs.map(snd))

fun get-con-info(dataType: ktype, conName: name): _ maybe<con-info>
  match dataType.extract-data-name
    Just(dataName) ->
      match dataName.newtypes-lookup-any
        Just(dataInfo) -> dataInfo.constrs.find(fn(ci) ci.name == conName)
        Nothing -> Nothing
    Nothing -> Nothing

fun extract-data-name(tp: ktype): _ maybe<name>
  match tp.expand-syn
    TFun(_, _, t) -> extract-data-name(t)
    TCon(TypeCon(nm, _)) -> Just(nm)
    _ -> Nothing

//--------------------------------------------------------------------------
// Utilities for readability
//--------------------------------------------------------------------------

// create a unique name specific to this module
fun ru-unique-tname(tp: ktype): <unique> tName
  TName(unique-name("ru"), tp)

//--------------------------------------------------------------------------
// Reuse "monad": current-def is only needed for trace messages, so it is
// modeled as a small reader-like effect (`effect val` + `with override`),
// following compiler/core/fun-lift.kk's `currentDef` pattern. Newtypes and
// the pretty-print environment are the existing ambient `newtypes-eff` /
// `pretty-eff` effects, and fresh names come from the shared `unique`
// effect (compiler/common/unique.kk) instead of a private counter.
//--------------------------------------------------------------------------

effect val ru-current-def: list<def>

fun ru-with-current-def(d: def, f)
  with override
    val ru-current-def = [d] ++ ru-current-def
  f()

//--------------------------------------------------------------------------
// Tracing
//--------------------------------------------------------------------------

fun ru-trace-doc(f: (pretty-env) -> doc): _ ()
  trace-doc(fn() f(pp-env))

fun ru-trace(msg: string): _ ()
  val defs = ru-current-def
  trace("Backend.C.ParcReuseSpec: " ++ defs.map(def-name).show-list(name/name/show) ++ ": " ++ msg)
