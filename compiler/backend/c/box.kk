// Ported as of 2026-01-29; approx upstream baseline commit 7083c02 of Backend/C/Box.hs (backfilled 2026-07-23)
module compiler/backend/c/box

import compiler/core/core
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/unique
import compiler/lib/pprint
import compiler/common/syntax
import compiler/type/type
import compiler/type/kind
import compiler/type/pretty
import compiler/kind/kind
import compiler/common/failure
import compiler/platform/config
import compiler/common/color-scheme
import compiler/core/simplify
import std/core/undiv

// Box / unbox transformation

pub fun box-core(c: core): _ core
  c(defs=box-def-groups(c.defs))

fun box-def-groups(dgs: def-groups)
  dgs.map(box-def-group)

fun box-def-group(dg: def-group)
  match dg
    DefRec(defs) -> DefRec(defs.map(box-def))
    DefNonRec(d) -> DefNonRec(box-def(d))

fun box-def(d: def): _ def
  val bexpr = box-expr(box-type(d.ktype), d.defExpr)
  val bdef = d(defExpr = bexpr)
  // simplify the whole def to avoid simplifying away functions to values (e.g. `fun(x){g(x)} -> val f = g`)
  // (upstream: uniqueSimplify True /*unsafe*/ False /*ndebug*/ 3 /*runs*/ 6 /*duplicationMax*/)
  bdef.unique-simplify(True, False, 3, 6)

fun unique-simplify(bdef: def, unsafe0: bool, ndebug: bool, nRuns: int, dupMax: int): _ def
  var dgs := [DefNonRec(bdef)]
  with handler
    fun get-core-defs() dgs
    fun set-core-defs(d') dgs := d'
    fun phaseError(s) throw("backend/c/box unique-simplify: " ++ s)
  simplify-defs(unsafe0, ndebug, nRuns, dupMax)
  match dgs
    [DefNonRec(d')] -> d'
    _ -> failure/fail("backend/c/box unique-simplify: simplify changed def group structure")

// upstream Box.hs "special internals" name list
fun is-boxing-special-internal(nm: name): bool
  nm == nameLazyMemoizeTarget || nm == nameLazyMemoize || nm == nameLazyEnter ||
  nm == nameLazyLeave || nm == nameLazyIsWhnf || nm == nameLazyPtrIsWhnf ||
  nm == nameDataTypePtrIsThreadShared || nm == nameDataTypePtrIsUnique ||
  nm == nameLazyIndirectCompress

// add box/unbox such that the type of `expr` matches `BoxType`
fun box-expr(tp: ktype, ex: expr)
  match ex
    // remove type abstraction and applications
    TypeLam(_, e) -> box-expr(tp, e)
    TypeApp(e, _) -> box-expr(tp, e)
    // special internals: the lazy primitives have
    // polymorphic signatures but compile to concrete C intrinsics on the
    // datatype representation -- box each argument at its OWN type (no
    // coercion to the polymorphic signature, which would box e.g. the lazy
    // value into a `kk_box_t` before `kk_datatype_ptr_is_unique`)
    App(TypeApp(f as Var(nm), _), args) | is-boxing-special-internal(nm.get-name) ->
      App(f, args.map(fn(a) box-expr(box-typeof(a), a)))
    // Regular
    App(e, args) ->
      val argTps = args.map(box-typeof)
      val eTp = TFun(argTps.map((nil, _)), typeTotal, tp)
      val bargs = args.map(fn(a) box-expr(box-typeof(a), a))
      val be = box-expr(eTp, e)
      App(be, bargs)
    Lam(tparams, eff, body) ->
      // upstream: `bbody <- boxExpr (boxTypeOf body) body` -- the body is
      // boxed against ITS OWN natural type, not `tp` (the type expected for
      // the WHOLE lambda, i.e. a function type). Boxed against `tp`, every
      // nested Case/branch inside a lambda body is boxed as if it had to look
      // like a FUNCTION -- e.g. an mlift_* wrapper's yielding branch is
      // (CFun,CFun)-coerced into an eta-expanded closure adapter instead of
      // staying the plain concrete (e.g. int) value it is, corrupting the
      // def's C return-type derivation (`kk_function_t` for `kk_integer_t`).
      val fnTp = ex.box-typeof
      val bbody = box-expr(body.box-typeof, body)
      bcoerce(fnTp, tp, Lam(tparams, eff, bbody))
    Let(def-groups, body) ->
      val bdgs = def-groups.box-def-groups
      val bbody = box-expr(tp, body)
      Let(bdgs, bbody)
    Case(exprs, branches) ->
      val exprTps = exprs.map(box-typeof)
      val bexprs = exprTps.zip(exprs).map(fn((tp', e)) box-expr(tp', e))
      val bbranches = branches.map(box-branch(exprTps, tp, _))
      Case(bexprs, bbranches)
    _ -> bcoerce(ex.box-typeof, tp, ex)

fun box-branch(patTps: list<ktype>, tp: ktype, b: branch)
  val (bpatterns, defss) = patTps.zip(b.patterns).map(fn((pt, p)) box-pattern(pt, p)).unzip
  fun binds(ex: expr)
    make-let(defss.concat.map(DefNonRec), ex)
  val bguards = b.guards.map(box-guard(tp, binds, _))
  Branch(bpatterns, bguards)

fun box-guard(tp: ktype, binds: expr -> pure expr, Guard(test, expr): guard)
  val btest = box-expr(typeBool, test)
  val bexpr = binds(box-expr(tp, expr))
  Guard(btest, bexpr) // TODO: binds come to late to appear in guards but we need binds for function wrappers?.. perhaps create a special pattern just for the C backend?

// add bindings and box/unbox such that pattern matches the required boxtype
fun box-pattern(fromTp: ktype, p: pattern)
  if p.is-patWild then
    return box-patternX(fromTp, p)
  val toTp = match p
    PatCon(typeRes=res) -> res
    PatVar(tname) -> tname.type-of
    PatLit(l) -> l.type-of
  if fromTp.c-type != toTp.c-type then
    val mcoerce = bcoerceX(fromTp, toTp, Var(TName(nil, fromTp), InfoNone))
    match mcoerce
      Just ->
        val isComplexCoerce =
          match (fromTp.c-type, toTp.c-type)
            (CFun, _) -> True
            (_, CFun) -> True
            _ -> False
        // We just insert a specially named Box pattern bound to fresh variable -- the backend recognizes this
        // and generates unbox/box expressions appropiately so nested patterns are handled correctly
        // Unfortunately, this does not work for function wrappers (as we need to generate a
        // wrapped unbox/box function around it); for those we rename and generate an explicit binding
        // binding; this works as a function type is never pattern matched further.
        // TODO: this may fail if the function is used in a guard test itself where it is not bound yet.
        //       we could work around this by substituting explicitly in the guard in that case.
        if isComplexCoerce then
          // function match
          match p
            PatVar(tname, PatWild) ->
              // ok, no nested match
              val i = new-unique()
              val uname = new-hidden-name("fun-unbox-x" ++ i.show)
              val coerce = bcoerce(fromTp, toTp, Var(TName(uname, fromTp), InfoNone))
              val def = make-tdef(TName(tname.get-name, toTp), coerce)
              (PatVar(TName(uname, fromTp), PatWild), [def])
            _ ->
              failure/fail("backend/c/from-core box-pattern: nested match on a function?")
        else // regular box / unbox
          val i = new-unique()
          val uname = new-hidden-name("box-x" ++ i.show)
          val (bpat, defs) = box-patternX(toTp, p)
          (PatVar(TName(uname, type-boxStar), pat-box(toTp, type-boxStar, bpat)), defs)
      _ ->
        box-patternX(fromTp, p)
  else box-patternX(fromTp, p)    

fun box-patternX(fromTp: ktype, p: pattern)
  match p
    PatCon(name, pars, repr, targs, exists0, tres, conInfo, skip) ->
      val (bparams, defss) = conInfo.params.map(snd).zip(pars).map(fn((ftp, par)) box-pattern(ftp, par)).unzip
      (PatCon(name, bparams, repr, targs, exists0, tres, conInfo, skip), defss.concat)
    PatVar(tname, arg) ->
      val (barg, defs) = box-pattern(tname.type-of, arg)
      (PatVar(tname, barg), defs)
    PatLit -> (p, [])
    PatWild -> (p, [])

// coerce `expr` of `fromTp` to `toTp`
fun bcoerce(fromTp: ktype, toTp: ktype, ex: expr)
  val mb = bcoerceX(fromTp, toTp, ex)
  match mb
    Just(e) -> e
    Nothing -> ex

fun bcoerceX(fromTp: ktype, toTp: ktype, ex: expr)
  val coerceTp = TFun([(nil, fromTp)], typeTotal, toTp)
  val boxVar = box-var-at-tp(coerceTp)
  val unboxVar = unbox-var-at-tp(coerceTp)
  match (fromTp.c-type, toTp.c-type)
    (CBox, CBox) -> Nothing
    (CBox, CData) -> Just(App(unboxVar, [ex]))
    (CData, CBox) -> Just(App(boxVar, [ex]))
    // boxed functions need to be wrapped to take all arguments and results as boxed as well :-(
    // set test/cgen/box3 and test/cgen/box3a
    (CBox, CFun) ->
      val boxedToTp = toTp.boxed-funtp
      val unboxed = App(unbox-var-at-tp(TFun([(nil, fromTp)], typeTotal, boxedToTp)), [ex])
      Just(bcoerce(boxedToTp, toTp, unboxed)) // unwrap function; we must return Just even if no further wrapping was needed
    (CFun, CBox) ->
      val boxedFromTp = fromTp.boxed-funtp
      val boxed = bcoerce(fromTp, boxedFromTp, ex) //wrap function
      val wrapped = App(box-var-at-tp(TFun([(nil, boxedFromTp)], typeTotal, toTp)), [boxed])
      Just(wrapped)
    // coerce between function arguments/results
    (CFun(fromPars, fromRes), CFun(toPars, toRes)) ->
      // upstream: `not (all(==) && fromRes==toRes)` = wrap if EITHER params
      // differ OR the result differs. Mind the De Morgan: `!all(==) &&
      // fromRes==toRes` would wrap only when params differ AND results match,
      // so a call whose PARAM and RESULT representations both mismatch (e.g.
      // std/core/hnd's @open-none1 called with a concrete-typed marker arg
      // where its signature is `<a,b,e1,e2> (f: a->e1 b, x1: a) -> e2 b` -- x1
      // AND the result are both TVar-vs-concrete mismatches) would skip the
      // coercion wrapper and leak an unboxed value into a kk_box_t slot.
      if !(fromPars.zip(toPars).all(fn((t1, t2)) t1 == t2) && fromRes == toRes) then
        match toTp.split-fun-scheme
          Just((_, toParTps, toEffTp, toResTp)) ->
            match fromTp.split-fun-scheme
              Just((_, fromParTps, fromEffTp, fromResTp)) -> Just(box-bind-expr-as-value(fromTp, toTp, ex, box-coerce-fun(toParTps, toEffTp, toResTp, fromParTps, fromEffTp, fromResTp, _)))
              _ -> failure/fail("backend/c/box bcoerceX: expecting function (from): " ++ fromTp.pretty.show)
          _ -> failure/fail("backend/c/box bcoerceX: expecting function (to): " ++ toTp.pretty.show)
      else Nothing
    _ -> Nothing

fun box-var-at-tp(tp: ktype)
  Var(TName(nameBox, tp), InfoExternal("box(#1)"))

fun unbox-var-at-tp(tp: ktype)
  Var(TName(nameUnbox, tp), InfoExternal("unbox(#1)"))

fun box-coerce-fun(toParTps: list<(name, ktype)>, toEffTp: ktype, toResTp: ktype, fromParTps: list<(name, ktype)>, fromEffTp: ktype, fromResTp: ktype, ex: expr): _ expr
  val names = toParTps.map(fn(_) unique-name("b"))
  val pars = names.zipwith(toParTps.map(snd), fn(n, t) TName(n, t))
  val args = pars.map(Var(_, InfoNone))
  val bargs = zip3(args, toParTps.map(snd), fromParTps.map(snd)).map(fn((arg, parToTp, parFromTp)) bcoerce(parToTp, parFromTp, arg))
  val bapp = bcoerce(fromResTp, toResTp, App(ex, bargs))
  Lam(pars, toEffTp, bapp)

fun box-bind-expr-as-value(fromTp: ktype, toTp: ktype, ex: expr, f: expr -> _ expr)
  if ex.is-total then f(ex)
  else
    val v = unique-tname("bv", fromTp)
    val body = f(Var(v, InfoNone))
    Let([DefNonRec(make-tdef(v, ex))], body)

// type without quantification
fun box-typeof(ex: expr)
  match ex.type-of.split-type-scheme
    (_, tp) -> tp

fun box-type(tp: ktype)
  match tp
    TForAll(_, t) -> t.box-type
    TFun(pars, eff, res) -> TFun(pars.map(fn((nm, tpx)) (nm, tpx.box-type)), eff.box-type, res.box-type)
    TApp(t, ts) -> TApp(t.box-type, ts.map(_.kind.type-box))
    TSyn(syn, args, t) -> TSyn(syn, args.map(box-type), t.box-type)
    _ -> tp

fun boxed-funtp(tp: ktype)
  match tp
    TForAll(_, t) -> t.boxed-funtp
    TSyn(_, _, t) -> t.boxed-funtp
    TFun(pars, eff, _res) ->
      TFun(pars.map(fn((nm, _)) (nm, boxed-tv())), eff, boxed-tv())
    _ -> failure/fail("backend/c/box boxed-funtp: " ++ tp.pretty.show)

fun boxed-tv()
  TVar(TypeVar(new-unique(), kindStar, Bound))

fun type-box(k: kind)
  TCon(TypeCon(nameTpBox, k))

type cType
  CBox
  CFun(args: list<cType>, res: cType)
  CData

fun c-type(k: ktype)
  match k
    TForAll(_, t) -> t.c-type
    TFun(pars, _eff, res) -> CFun(pars.map(fn((_, t)) t.c-type), res.c-type)
    TApp(t) -> t.c-type
    TCon -> CData
    TVar -> CBox
    TSyn(_, _, t) -> t.c-type

fun ct/(==)(c1: cType, c2: cType): div bool
  match (c1, c2)
    (CBox, CBox) -> True
    (CData, CData) -> True
    (CFun(args1, res1), CFun(args2, res2)) -> args1 == args2 && res1 == res2
    _ -> False

fun (!=)(c1: cType, c2: cType): div bool
  !(c1 == c2)

val type-boxStar = kindStar.type-box

fun is-box-pat(p: pattern)
  match p
    PatCon(name) -> name.get-name == nameBoxCon
    _ -> False

fun pat-box(tpPat: ktype, tpRes: ktype, p: pattern)
  PatCon(TName(nameBoxCon, boxConInfo.typeScheme), [p], boxConRepr, [tpPat], [], tpRes, boxConInfo, True)

val boxConRepr = ConSingle(nameTpBox, DataSingle(False), value-repr-scan(1), CtxNone, 0)
val tva = TypeVar(0, kindStar, Bound)
val tp = TForAll([tva], TFun([(nil, TVar(tva))], typeTotal, type-boxStar))
val boxConInfo = ConInfo(nameBox, nameTpBox, [tva], [], [(nil, TVar(tva))], tp, 
                        Inductive, null, [null], [Public], True, [(nil, TVar(tva))], 
                        value-repr-scan(1), Nothing, 1, Public, "") // size is wrong with knowing the platform?

fun unique-tname(nm: string, tp: ktype)
  val n = unique-name(nm)
  TName(n, tp)
