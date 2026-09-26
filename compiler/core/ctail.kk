// Port of Core/CTail.hs: Tail Recursion Modulo Cons (TRMC)
// See: "Tail Recursion Modulo Context -- An Equational Approach",
//      Daan Leijen and Anton Lorenzen, POPL'22.
//
// Ported as of 2026-08-01; approx upstream baseline of Core/CTail.hs (707 lines)
//
// Detects self-recursive calls that occur as a (possibly nested) constructor
// field in tail position ("modulo cons") and rewrites the definition to build
// up a constructor *context* (`cctx`) instead, turning the recursion into a
// true tail call. Shares the `nameCCtx*`/`typeCCtx`/`ctx-path` machinery with
// compiler/core/analysis-cctx.kk (which implements the *forward* `ctx` literal
// desugaring); this pass implements the independent *backward* accumulator
// construction. The two passes share no code -- this one defines its own
// makeFieldAddrOf/makeCCtxEmpty/makeCCtxExtend/makeCCtxApply
// rather than importing Core.AnalysisCCtx's versions -- so this port follows
// the same shape but reuses this port's `lookup`/`make-empty`/`make-field-addr-of`
// from analysis-cctx.kk where the logic is exactly identical).
//
// NOT wired into compiler/main/driver.kk's core-phase pipeline (upstream's
// ctail pass isn't invoked from run-core-phase in this port either -- the
// pipeline comment in driver.kk lists unreturn/simplify/lift-functions/
// mon-transform/open-resolve/simplify/monadic-lift but no ctail stage yet).
// This file only adds the standalone pass; wiring it up is left to a
// follow-up change since the task here is the port itself.

module compiler/core/ctail

import compiler/common/name
import compiler/common/name-prim
import compiler/common/unique
import compiler/common/failure
import compiler/common/syntax
import compiler/kind/kind
import compiler/kind/newtypes
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/core/core
import compiler/core/corevar
import compiler/core/analysis-cctx
import std/data/rb-set

//--------------------------------------------------------------------------
// Entry point
//--------------------------------------------------------------------------

// Upstream `ctailOptimize :: Pretty.Env -> TargetPlatform -> Newtypes -> Gamma -> Bool -> CorePhase b ()`.
// `Pretty.Env` was only used for tracing (dropped, like other ported passes --
// simplify.kk/monadic.kk carry no such tracing infra either) and `Gamma` is
// read into upstream's `Env` but never actually consulted anywhere in
// Core/CTail.hs's body, so it is dropped from the port's signature too
// (documented here rather than silently ported as dead weight).
pub fun ctail-optimize(tpl: target-platform, nt: newtypes, use-context-path: bool)
  with withNewtypes(nt)
  with val ctail-target-platform = tpl
  with val ctail-use-context-path = use-context-path
  with val ctail-fn-name = TName(name/nil, typeUnit)
  with val ctail-slot = Nothing
  with val ctail-is-multi = True
  with val ctail-always-affine = False
  with val ctail-current-def = []
  set-core-defs(get-core-defs().ctail-def-groups(True))

//--------------------------------------------------------------------------
// Definition groups
//--------------------------------------------------------------------------

fun ctail-def-groups(dgs: def-groups, top-level: bool): ctail-eff def-groups
  dgs.map(fn(dg) dg.ctail-def-group(top-level)).concat

// Only single self-recursive DefRecs with an
// eligible modulo-cons tail call are rewritten; everything else passes through
fun ctail-def-group(dg: def-group, top-level: bool): ctail-eff list<def-group>
  match dg
    DefRec([d]) ->
      if defTName(d).ctail-has-tail-call(True, d.defExpr) then d.ctail-def(top-level) else [dg]
    _ -> [dg]

/* we generate
   - if the runtime can copy contexts (use-context-path)
     we always generate a single definition, optimized a bit if the effect
     is affine for sure (always-affine)
   - otherwise, a single definition if the effect is affine for sure
   - or two definitions for multiple resumptions (is-multi)
*/
fun ctail-def(d: def, top-level: bool): ctail-eff list<def-group>
  with ctail-with-current-def(d)
  match d.ktype.ctail-has-result-ref-type
    Nothing -> [DefRec([d])]
    Just((tforall, targs, teff, tres)) ->
      val ctailSlotType = type-cctx(tres)
      val ctailName     = "trmc".make-hidden-name(d.def-name)
      val ctailSlotNm   = "acc".new-hidden-name
      val ctailType     = tforall.ctail-forall(TFun(targs ++ [(ctailSlotNm, ctailSlotType)], teff, tres))
      val ctailTName    = TName(ctailName, ctailType)
      val ctailTSlot    = TName(ctailSlotNm, ctailSlotType)

      val alwaysAffine = teff.effect-is-affine
      val cdefExpr = ctail-with-context(ctailTName, False, alwaysAffine, Just(ctailTSlot)) fn()
        d.defExpr.ctail-make-cdef-expr(ctailTSlot).ctail-expr(True)

      val cdef = d(def-name = ctailName, ktype = ctailType, defExpr = cdefExpr)
      val needsMulti = !(ctail-use-context-path || alwaysAffine)
      val ctailMultiSlotType = TFun([(name/nil, tres)], typeTotal, tres)
      val ctailMultiName   = "trmcm".make-hidden-name(d.def-name)
      val ctailMultiSlotNm = "accm".new-hidden-name
      val ctailMultiType   = tforall.ctail-forall(TFun(targs ++ [(ctailMultiSlotNm, ctailMultiSlotType)], teff, tres))
      val ctailMultiTName  = TName(ctailMultiName, ctailMultiType)
      val ctailMultiTSlot  = TName(ctailMultiSlotNm, ctailMultiSlotType)
      val ctailMultiVar    = Var(ctailMultiTName, InfoArity(tforall.length, targs.length + 1))

      val wrapExpr = ctail-with-context(ctailTName, False, alwaysAffine, Nothing) fn()
        ctailTSlot.ctail-wrapper(if needsMulti then Just(ctailMultiVar) else Nothing, d.defExpr)

      // todo: check if rec is needed (only if there are non-tail calls left over)
      if !needsMulti then
        [DefRec([cdef, d(defExpr = wrapExpr)])]
      else
        val cdefMultiExpr = ctail-with-context(ctailMultiTName, True, alwaysAffine, Just(ctailMultiTSlot)) fn()
          d.defExpr.ctail-make-cdef-expr(ctailMultiTSlot).ctail-expr(True)
        val cdefMulti = d(def-name = ctailMultiName, ktype = ctailMultiType, defExpr = cdefMultiExpr)
        [DefRec([cdef, cdefMulti, d(defExpr = wrapExpr)])]

fun ctail-make-cdef-expr(e: expr, slot: tName): exn expr
  match e
    TypeLam(targs, body) -> TypeLam(targs, body.ctail-make-cdef-expr(slot))
    Lam(args, eff, body) -> Lam(args ++ [slot], eff, body)
    _ -> failure/fail("core/ctail: illegal ctail function shape")

fun ctail-has-result-ref-type(tp: ktype): <newtypes-eff,exn,div> maybe<(list<type-var>,list<(name,ktype)>,keffect,ktype)>
  match tp.split-fun-scheme
    Just(t) ->
      val (_, _, _, tres) = t
      if tres.ctail-has-ref-type then Just(t) else Nothing
    Nothing -> Nothing

fun ctail-has-ref-type(tp: ktype): <newtypes-eff,exn,div> bool
  match tp.expand-syn
    TApp(t, _) -> t.ctail-has-ref-type
    TCon(c) -> !c.name.ctail-is-value-type-name
    _ -> False

// Only asks whether the *representation* is a value
// (unlike analysis-cctx.kk's `ensure-valid-hole-type`, which additionally
// checks the `data-info` `value` declaration; upstream CTail.hs deliberately
// only inspects the derived representation here)
fun ctail-is-value-type-name(nm: name): <newtypes-eff,exn> bool
  match newtypes-lookup-any(nm)
    Just(dataInfo) ->
      val (drepr, _) = dataInfo.data-repr(data/is-value)
      drepr.is-value
    Nothing -> False

// upstream local `tForall` helper (only wraps in `TForAll` when there are
// quantifiers, mirroring `Type.Type.tForall`)
fun ctail-forall(vars: list<type-var>, rho: ktype): ktype
  match vars
    Nil -> rho
    _ -> TForAll(vars, rho)

//--------------------------------------------------------------------------
// Create a wrapper: this costs one allocation but prevents code duplication
//--------------------------------------------------------------------------

fun ctail-wrapper(slot: tName, mbMulti: maybe<expr>, e: expr): ctail-eff expr
  match e
    TypeLam(targs, Lam(args, eff, body)) ->
      val body' = ctail-wrapper-body(body.type-of, slot, mbMulti, targs, args)
      TypeLam(targs, Lam(args, eff, body'))
    Lam(args, eff, body) ->
      val body' = ctail-wrapper-body(body.type-of, slot, mbMulti, [], args)
      Lam(args, eff, body')
    _ -> failure/fail("core/ctail ctail-wrapper: illegal ctail function shape")

fun ctail-wrapper-body(resTp: ktype, slot: tName, mbMulti: maybe<expr>, targs: list<type-var>, args: list<tName>): ctail-eff expr
  val tailVar = ctail-fun-expr()
  val tpl = ctail-target-platform
  val ctailCall = App(make-type-app(tailVar, targs.map(fn(tv) TVar(tv))),
                       args.map(fn(nm) Var(nm, InfoNone)) ++ [make-empty(resTp, tpl)])
  match mbMulti
    Nothing -> ctailCall
    Just(ctailMultiVar) ->
      val x = resTp.ctail-unique-tname
      val ctailMultiCall = App(make-type-app(ctailMultiVar, targs.map(fn(tv) TVar(tv))),
                                args.map(fn(nm) Var(nm, InfoNone)) ++ [Lam([x], typeTotal, Var(x, InfoNone))])
      ctail-make-if-is-affine(ctailCall, ctailMultiCall)

fun ctail-make-if-is-affine(onTrue: expr, onFalse: expr): expr
  val tnEvvIsAffine = TName(nameEvvIsAffine, TFun([], typeTotal, typeBool))
  make-if-expr(App(Var(tnEvvIsAffine, InfoArity(0, 0)), []), onTrue, onFalse)

//--------------------------------------------------------------------------
// Does there exist a tail call definition?
//--------------------------------------------------------------------------

fun ctail-has-tail-call(defName: tName, top: bool, e: expr): <div,exn> bool
  match e
    TypeLam(_, body) -> ctail-has-tail-call(defName, top, body)
    TypeApp(body, _) -> ctail-has-tail-call(defName, top, body)
    Let(_, body)      -> ctail-has-tail-call(defName, top, body)
    Lam(_, _, body)   -> if top then ctail-has-tail-call(defName, False, body) else False
    Case(_, branches) -> branches.any(fn(b) ctail-has-tail-call-branch(defName, b))
    App(TypeApp(Con, _), args) -> ctail-has-tail-call-arg(defName, args.reverse)
    App(Con, args)              -> ctail-has-tail-call-arg(defName, args.reverse)
    _ -> False

fun ctail-has-tail-call-branch(defName: tName, b: branch): <div,exn> bool
  b.guards.any(fn(g) ctail-has-tail-call-guard(defName, g))

fun ctail-has-tail-call-guard(defName: tName, g: guard): <div,exn> bool
  ctail-has-tail-call(defName, False, g.body)

fun ctail-has-tail-call-arg(defName: tName, rargs: list<expr>): <div,exn> bool
  match rargs
    Nil -> False
    Cons(rarg, rargs') ->
      // `free-in` is `div` (goes through `free-vars`), so it cannot appear in
      // a match *guard* (guards must be total) -- checked in the branch body instead
      fun fallback(): <div,exn> bool
        rarg.is-total && ctail-has-tail-call-arg(defName, rargs')
      match rarg
        App(TypeApp(Var(nm, _), _), _) | defName == nm -> True
        App(Var(nm, _), _)             | defName == nm -> True
        App(TypeApp(Con, _), fargs) ->
          if defName.free-in(fargs) && ctail-has-tail-call-arg(defName, fargs.reverse) then True else fallback()
        App(Con, fargs) ->
          if defName.free-in(fargs) && ctail-has-tail-call-arg(defName, fargs.reverse) then True else fallback()
        // todo: emit warning that TRMC does not apply?
        _ -> fallback()

fun free-in(nm: tName, es: list<expr>): <div,exn> bool
  es.free-vars.member(nm)

//--------------------------------------------------------------------------
// Convert to a tail-call function using an accumulator (slot)
//--------------------------------------------------------------------------

fun ctail-expr(e: expr, top: bool): ctail-eff expr
  val dname = ctail-current-def-name()
  fun tail-result(body: expr): ctail-eff expr
    match ctail-slot
      Nothing   -> body
      Just(slot) -> ctail-make-cctx-apply(ctail-target-platform, ctail-is-multi, ctail-always-affine, slot, body)
  fun handle-con-app(cname: tName, fcon: expr, fargs: list<expr>): ctail-eff expr
    fun mk-cons(cpath: ctx-path, args: list<expr>): ctail-eff (list<def-group>, expr)
      ctail-bind-args(args) fn(xs) ([], fcon.ctail-mk-con-app(cpath, xs))
    val useCtx = !ctail-is-multi && ctail-use-context-path && !ctail-always-affine
    match ctail-try-arg(useCtx, dname, cname, Nothing, mk-cons, fargs.length, fargs.reverse)
      Nothing -> tail-result(App(fcon, fargs))
      Just((defs, res)) -> make-let(defs, res)
  fun handle-tail-call(mkCall: (expr, expr) -> expr): ctail-eff expr
    match ctail-slot
      Nothing    -> e
      Just(slot) -> mkCall(ctail-fun-expr(), Var(slot, InfoNone))
  match e
    TypeLam(tpars, body) -> TypeLam(tpars, body.ctail-expr(top))
    Lam(pars, eff, body) | top -> Lam(pars, eff, body.ctail-expr(top))
    Let(dgs, body) -> Let(dgs, body.ctail-expr(top))
    Case(xs, branches) -> Case(xs, branches.map(ctail-branch))
    TypeApp(body, targs) ->
      val expr' = body.ctail-expr(top)
      match (expr', ctail-slot)
        (App(v as Var(ctailmSlot, _), [arg]), Just(slot)) | ctailmSlot.get-name == slot.get-name ->
          App(v, [TypeApp(arg, targs)])  // push down typeapp
        (App(v as TypeApp(Var(ctailApply, _), _), [acc, arg]), _) | ctailApply.get-name == nameCCtxApply ->
          App(v, [acc, TypeApp(arg, targs)])  // push down typeapp into ctail set
        _ -> TypeApp(expr', targs)
    App(f as TypeApp(Con(cname, _), _), fargs) -> handle-con-app(cname, f, fargs)
    App(f as Con(cname, _), fargs)             -> handle-con-app(cname, f, fargs)
    App(TypeApp(Var(nm, _), targs), fargs) | nm == dname ->
      handle-tail-call(fn(v, slot) App(TypeApp(v, targs), fargs ++ [slot]))
    App(Var(nm, _), fargs) | nm == dname ->
      handle-tail-call(fn(v, slot) App(v, fargs ++ [slot]))
    _ -> tail-result(e)

fun ctail-mk-con-app(fcon: expr, cpath: ctx-path, xs: list<expr>): exn expr
  match cpath
    CtxField(_) -> match fcon
      Con(conName, conRepr)               -> App(Con(conName, conRepr.update-ctx-path(cpath)), xs)
      TypeApp(Con(conName, conRepr), targs) -> App(TypeApp(Con(conName, conRepr.update-ctx-path(cpath)), targs), xs)
      _ -> failure/fail("core/ctail mk-con-app: invalid constructor")
    _ -> App(fcon, xs)

fun ctail-bind-args(args: list<expr>, useIt: (list<expr>) -> ctail-eff (list<def-group>, expr)): ctail-eff (list<def-group>, expr)
  val (defss, args') = args.map(ctail-bind-arg).unzip
  val (defs, e) = useIt(args')
  (defss.concat ++ defs, e)

fun ctail-bind-arg(arg: expr): ctail-eff (list<def-group>, expr)
  if arg.is-total then ([], arg)
  else
    val x = arg.type-of.ctail-unique-tname
    ([DefNonRec(make-tdef(x, arg))], Var(x, InfoNone))

fun ctail-branch(b: branch): ctail-eff branch
  Branch(b.patterns, b.guards.map(ctail-guard))

fun ctail-guard(g: guard): ctail-eff guard
  Guard(g.test, g.body.ctail-expr(False))

//--------------------------------------------------------------------------
// See if the tailcall is inside a (nested) constructor application
//--------------------------------------------------------------------------

fun ctail-try-arg(useCtxPath: bool, dname: tName, cname: tName, mbC: maybe<tName>,
                   mkApp: (ctx-path, list<expr>) -> ctail-eff (list<def-group>, expr),
                   field: int, rargs: list<expr>): ctail-eff maybe<(list<def-group>, expr)>
  match rargs
    Nil -> Nothing
    Cons(rarg, rargs') ->
      fun mkAppNew(args: list<expr>): ctail-eff (list<def-group>, expr)
        val cpath = useCtxPath.ctail-get-ctx-path(cname, field)
        mkApp(cpath, rargs'.reverse ++ args)
      // returns a (ctx-path, args) -> ... closure: the context path and the
      // remaining arguments arrive at different points in the walk
      fun mkAppNested(x: tName, fcon: expr)
        fn(fcpath: ctx-path, args: list<expr>) : ctail-eff (list<def-group>, expr)
          val cpath = useCtxPath.ctail-get-ctx-path(cname, field)
          val (defs, e) = ctail-bind-args(rargs'.reverse) fn(xs) mkApp(cpath, xs ++ [Var(x, InfoNone)])
          val condef = DefNonRec(make-tdef(x, fcon.ctail-mk-con-app(fcpath, args)))
          ([condef] ++ defs, e)
      // `free-in` is `div`, so (as above) it cannot appear in a match guard;
      // checked in the branch body, falling back to the generic "total arg" case
      fun fallback(): ctail-eff maybe<(list<def-group>, expr)>
        if rarg.is-total
          then ctail-try-arg(useCtxPath, dname, cname, mbC, fn(cpath, args) mkApp(cpath, args ++ [rarg]), field - 1, rargs')
          else Nothing
      fun recurse-into(cname2: tName, f: expr, fargs: list<expr>): ctail-eff maybe<(list<def-group>, expr)>
        val x = rarg.type-of.ctail-unique-tname
        ctail-try-arg(useCtxPath, dname, cname2, Just(x), mkAppNested(x, f), fargs.length, fargs.reverse)
      match rarg
        App(TypeApp(Var(nm, _), targs), fargs) | dname == nm ->
          Just(ctail-found-arg(cname, mbC, mkAppNew, field, fn(v, acc) App(TypeApp(v, targs), fargs ++ [acc]), rarg.type-of))
        App(Var(nm, _), fargs) | dname == nm ->
          Just(ctail-found-arg(cname, mbC, mkAppNew, field, fn(v, acc) App(v, fargs ++ [acc]), rarg.type-of))
        // recurse into other con
        App(f as TypeApp(Con(cname2, _), _), fargs) ->
          if dname.free-in(fargs) then recurse-into(cname2, f, fargs) else fallback()
        App(f as Con(cname2, _), fargs) ->
          if dname.free-in(fargs) then recurse-into(cname2, f, fargs) else fallback()
        _ -> fallback()

fun ctail-get-ctx-path(useContextPath: bool, cname: tName, fieldIdx: int): <newtypes-eff,exn,div> ctx-path
  if !useContextPath then CtxNone
  else match cname.lookup(fieldIdx)
    Left(msg)      -> failure/fail(msg)  // todo: allow this? see test/cgen/ctail7
    Right(fldName) -> CtxField(fldName)

//--------------------------------------------------------------------------
// Found a tail call inside a constructor application
//--------------------------------------------------------------------------

fun ctail-found-arg(cname: tName, mbC: maybe<tName>,
                     mkConsApp: (list<expr>) -> ctail-eff (list<def-group>, expr),
                     field: int, mkTailApp: (expr, expr) -> expr, resTp: ktype): ctail-eff (list<def-group>, expr)
  match ctail-slot
    Nothing -> failure/fail("core/ctail ctail-found-arg: inlined trmc is not supported")
    Just(slot) ->
      val ctailVar = ctail-fun-expr()
      if ctail-is-multi then
        val x = resTp.ctail-unique-tname
        val (defs, cons) = mkConsApp([Var(x, InfoNone)])
        val acc = Lam([x], typeTotal, App(Var(slot, InfoNone), [cons]))
        (defs, mkTailApp(ctailVar, acc))
      else match cname.lookup(field)
        Left(msg) -> failure/fail(msg)  // todo: allow this? see test/cgen/ctail7
        Right(fieldName) ->
          val holeExpr = resTp.ctail-make-hole
          val (defs, cons) = mkConsApp([holeExpr])
          val consName = cons.type-of.ctail-unique-tname
          val comp = ctail-make-cctx-extend(ctail-target-platform, slot, consName, mbC.default(consName), cname, fieldName.get-name, resTp, ctail-always-affine)
          (defs ++ [DefNonRec(make-tdef(consName, cons))], mkTailApp(ctailVar, comp))

//--------------------------------------------------------------------------
// Primitives
//--------------------------------------------------------------------------

// Polymorphic hole
fun ctail-make-hole(tp: ktype): expr
  val a = TypeVar(0, kindStar, Bound)
  val funType = TForAll([a], TFun([], typeTotal, TVar(a)))
  App(TypeApp(Var(TName(nameCCtxHoleCreate, funType), InfoExternal("")), [tp]), [])

// Note: the initial empty context and the field-address-of primitive are
// exactly the same shape as analysis-cctx.kk's `make-empty`/`make-field-addr-of`
// (this port reuses those directly rather than duplicating them, unlike
// upstream where Core.CTail.hs keeps its own copies of `makeCCtxEmpty` and
// `makeFieldAddrOf` since it does not import Core.AnalysisCCtx.hs at all).

// Extend a context with a non-empty context
// (no explicit return-effect annotation: `unsupported-external` traces on the
// unreachable fallback target, same as analysis-cctx.kk's `make-empty` etc.
// leaving the effect row to be inferred rather than pinned to pure)
fun ctail-make-cctx-extend(tpl: target-platform, slot: tName, resName: tName, objName: tName, conName: tName,
                            fieldName: name, tp: ktype, alwaysAffine: bool)
  val fieldOf = make-field-addr-of(Var(objName, InfoNone), conName, fieldName, tp)
  val a = TypeVar(0, kindStar, Bound)
  val funType = TForAll([a], TFun([(name/nil, type-cctx(TVar(a))), (name/nil, TVar(a)), (name/nil, TApp(typeFieldAddr, [TVar(a)]))],
                                   typeTotal, type-cctx(TVar(a))))
  val external = match tpl.tpl-target
    C(_) -> "kk_cctx_extend" ++ (if alwaysAffine then "_linear" else "") ++ "(#1,#2,#3,kk_context())"
    JS(_) -> "$std_core_types._cctx_extend(#1,#2,#3)"
    _    -> unsupported-external("kk_cctx_extend")
  App(TypeApp(Var(TName(nameCCtxExtend, funType), InfoExternal(external)), [tp]),
      [Var(slot, InfoNone), Var(resName, InfoNone), fieldOf])

// Apply a context to its final value.
fun ctail-make-cctx-apply(tpl: target-platform, isMulti: bool, alwaysAffine: bool, slot: tName, e: expr)
  if isMulti then
    App(Var(slot, InfoNone), [e])  // slot `a -> a` is an accumulating function; apply to resolve
  else
    // slot is a `ctail<a>`
    val tp = match slot.type-of
      TApp(_, [t])   -> t
      TSyn(_, [t], _) -> t
      _ -> failure/fail("core/ctail ctail-make-cctx-apply: illegal slot type")
    val a = TypeVar(-1, kindStar, Bound)
    val funType = TForAll([a], TFun([(name/nil, type-cctx(TVar(a))), (name/nil, TVar(a))], typeTotal, TVar(a)))
    val external = match tpl.tpl-target
      C(_) -> "kk_cctx_apply" ++ (if alwaysAffine then "_linear" else "") ++ "(#1,#2,kk_context())"
      JS(_) -> "$std_core_types._cctx_apply(#1,#2)"
      _    -> unsupported-external("kk_cctx_apply")
    App(TypeApp(Var(TName(nameCCtxApply, funType), InfoExternal(external)), [tp]), [Var(slot, InfoNone), e])

//--------------------------------------------------------------------------
// Utilities for readability
//--------------------------------------------------------------------------

// create a unique name specific to this pass
fun ctail-unique-tname(tp: ktype): <unique> tName
  TName("trmc".unique-name, tp)

//--------------------------------------------------------------------------
// CTail effect: reader-style environment as independent `effect val` ops
// (each overridden individually via `with override val ... = ...`, exactly
// like compiler/type/infer-effect.kk's `infer-env`/`scope-depth`/`local-depth`
// -- stacked single-op effects rather than one hand-rolled multi-field Reader
// record) plus the shared `unique`/`newtypes-eff` effects for the
// stateful/lookup parts -- no hand-rolled Reader/State monad transformer.
//--------------------------------------------------------------------------

alias ctail-eff = <ctail-target-platform,ctail-use-context-path,ctail-fn-name,ctail-slot,
                    ctail-is-multi,ctail-always-affine,ctail-current-def,
                    // `pure` IS `<exn,div>` -- listing all three duplicated both labels
                    unique,newtypes-eff,pure>

effect val ctail-target-platform: target-platform
effect val ctail-use-context-path: bool
effect val ctail-fn-name: tName          // TName of the ctail (trmc-suffixed) variant currently being built
effect val ctail-slot: maybe<tName>      // current accumulator/context slot, if any
effect val ctail-is-multi: bool
effect val ctail-always-affine: bool
effect val ctail-current-def: list<def>  // stack of original (pre-ctail) defs being processed

// Builds the `Var` for a tail call to the current
// ctail variant, with an arity `InfoArity` computed from its type
fun ctail-fun-expr(): <ctail-fn-name> expr
  val tn = ctail-fn-name
  val info = match tn.type-of.split-fun-scheme
    Just((foralls, targs, _, _)) -> InfoArity(foralls.length, targs.length)
    Nothing -> InfoNone
  Var(tn, info)

fun ctail-current-def-name(): <ctail-current-def,exn> tName
  match ctail-current-def
    Cons(d, _) -> defTName(d)
    Nil -> failure/fail("core/ctail: no current definition")

fun ctail-with-current-def(d: def, action: () -> ctail-eff a): ctail-eff a
  with override val ctail-current-def = Cons(d, ctail-current-def)
  action()

// Overrides the four context fields together (they
// always change as one unit at every upstream `withContext` call site)
fun ctail-with-context(name: tName, isMulti: bool, alwaysAffine: bool, mbSlot: maybe<tName>, action: () -> ctail-eff a): ctail-eff a
  with override val ctail-fn-name = name
  with override val ctail-slot = mbSlot
  with override val ctail-is-multi = isMulti
  with override val ctail-always-affine = alwaysAffine
  action()
