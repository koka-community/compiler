// Updated as of 7/23/26: Commit 9bc234e
module compiler/core/analysis-cctx

import pretty/pprint
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/failure
import compiler/common/unique
import compiler/common/syntax
import compiler/kind/newtypes
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/assumption
import compiler/core/core
import compiler/platform/config

// take a context and check if it is well-formed and return a well-typed context expression
pub fun analyze(rng: range, gamma: gamma, expr: expr, tpl: target-platform = target-platform-c64): _ (expr, list<doc>)
  with handler
    val cctx-target-platform = tpl
    val cctx-gamma = gamma
    return(x) (x, [])
    final ctl emit-ctx-err(e) (make-empty(gamma, expr.type-of, tpl), [e])
    final ctl emit-ctx-errs(e) (make-empty(gamma, expr.type-of, tpl), e)
  expr.cctx-create

effect cctx-eff
  val cctx-target-platform: target-platform
  val cctx-gamma: gamma
  final ctl emit-ctx-err(d: doc): a
  final ctl emit-ctx-errs(d: list<doc>): a

fun tryC(f: () -> _ a): _ either<list<doc>,a>
  val tpl = cctx-target-platform
  val gamma = cctx-gamma
  with override
    val cctx-target-platform = tpl
    val cctx-gamma = gamma
    return(x) Right(x)
    final ctl emit-ctx-err(e) Left([e])
    final ctl emit-ctx-errs(e) Left(e)
  f()

value struct chole
  addr: expr
  ktype: ktype;

value struct cctx
  defs: list<def>
  top: expr
  hold: chole;

fun cctx-create(e: expr)
  // empty context
  if e.is-hole then make-empty(cctx-gamma, e.type-of, cctx-target-platform)
  else
    // non-empty context
    val (Cctx(defs, top, Chole(addr, holeTp))) = e.expr
    val cctx = make-create(cctx-gamma, cctx-target-platform, top.type-of, holeTp, top, addr)
    Let(defs.map(DefNonRec), cctx)

fun expr(e: expr)
  match e
    // constructor 
    App(Con(name, repr), args) | repr.has-ctx-path && args.is-cons ->
      make-con(name, repr, [], args)
    App(TypeApp(Con(name, repr), targs), args) | repr.has-ctx-path && args.is-cons ->
      make-con(name, repr, targs, args)
    _ -> emit-ctx-errs([])

fun make-con(cName: t-name, cRepr: con-repr, targs: list<ktype>, args: list<expr>)
  match args.span(!_.is-hole)
    (pre, Cons(h, post)) ->
      con-final(cName, cRepr, targs, pre, h, post)
    _ -> con-recurse(cName, cRepr, targs, args)

fun con-recurse(cName: t-name, cRepr: con-repr, targs: list<ktype>, args: list<expr>)
  val (pre,cctx,post) = find([], [], args)
  (pre ++ post).foreach(check-no-hole)
  val (ds, vars) = pre.map(make-unique-def).unzip
  val fname = cName.get-field-name(pre.length + 1)
  val ctxrepr = cRepr.update-ctx-path(CtxField(fname))
  val (d1, var1) = make-unique-def(App(make-type-app(Con(cName, ctxrepr), targs), vars ++ [cctx.top] ++ post))
  cctx(defs=ds ++ cctx.defs ++ [d1], top=var1)

fun con-final(cName: t-name, cRepr: con-repr, targs: list<ktype>, pre: list<expr>, chole: expr, post: list<expr>)
  (pre ++ post).foreach(check-no-hole)
  val fname = cName.get-field-name(pre.length + 1)
  val holetp = chole.type-of
  val ctxrepr = cRepr.update-ctx-path(CtxField(fname))
  holetp.ensure-valid-hole-type
  val (d1, var1) = make-unique-def(App(make-type-app(Con(cName, ctxrepr), targs), pre ++ [chole] ++ post))
  val (d2, addr) = make-unique-def(make-field-addr-of(cctx-gamma, var1, cName, fname.get-name, holetp))
  Cctx([d1, d2], var1, Chole(addr, holetp))

fun check-no-hole(e: expr): ()
  () // note: not needed as it is already checked during type inference

fun find(errs: list<doc>, acc: list<expr>, args: list<expr>): _ (list<expr>, cctx, list<expr>)
  match args
    // no args
    Nil -> emit-ctx-errs(errs)
    // try recursively
    Cons(arg, args') ->
      match tryC({arg.expr})
        Left(errs') -> find(errs ++ errs', Cons(arg, acc), args')
        Right(cctx) -> (acc.reverse, cctx, args')

fun make-unique-def(e: expr)
  val name = unique-name("cctx")
  (make-def(name, e), Var(TName(name, e.type-of), InfoNone))

fun is-hole(e: expr)
  match e
    App(TypeApp(Var(TName(hname, _htp)), [_tp, _etp]), []) -> hname == nameCCtxHoleCreate
    App(App(TypeApp(Var(open), [_effFrom, _effTo, _tpFrom, _tpTo]), [TypeApp(Var(hname))]), []) ->
      open.get-name == nameEffectOpen && hname.get-name == nameCCtxHoleCreate
    _ -> False

// A primitive of `std/core/types` applied to type and value arguments. The type scheme is
// taken from its declaration (so `--checkcore` checks the use against the declaration).
pub fun make-cctx-prim(gamma: gamma, name: name, external: string, targs: list<ktype>, args: list<expr>): pure expr
  val scheme = match gamma.lookupQ(name)
    [info] -> info.scheme
    _ -> failure/fail("core/analysis-cctx make-cctx-prim: cannot find " ++ name.show)
  val arityOk = match scheme.split-fun-scheme
    Just((tvars, pars, _, _)) -> tvars.length == targs.length && pars.length == args.length
    Nothing -> False
  assert("core/analysis-cctx make-cctx-prim: wrong number of arguments for " ++ name.show ++ ": " ++ scheme.show, arityOk,
    App(make-type-app(Var(TName(name, scheme), core/InfoExternal(external)), targs), args))

// Polymorphic hole
pub fun make-hole(gamma: gamma, tp: ktype): pure expr
  make-cctx-prim(gamma, nameCCtxHoleCreate, "", [tp], [])

// Initial empty context (ctx hole)
pub fun make-empty(gamma: gamma, tp: ktype, tpl: target-platform)
  val external = match tpl.tpl-target
    C(_) -> "kk_cctx_empty(kk_context())"
    JS(_) -> "$std_core_types._cctx_empty()"
    _ -> unsupported-external("kk_cctx_empty")
  make-cctx-prim(gamma, nameCCtxEmpty, external, [tp], [])

// Create a context (ctx Cons(e, Cons(2, hole)))
fun make-create(gamma: gamma, tpl: target-platform, tp: ktype, holetp: ktype, top: expr, holeaddr: expr)
  val external = match tpl.tpl-target
    C(_) -> "kk_cctx_create(#1,#2,kk_context())"
    JS(_) -> "$std_core_types._cctx_create(#1,#2)"
    _ -> unsupported-external("kk_cctx_create")
  make-cctx-prim(gamma, nameCCtxCreate, external, [tp, holetp], [top, holeaddr])

// The address of a field in a constructor (for context holes)
pub fun make-field-addr-of(gamma: gamma, obj: expr, cName: t-name, fieldName: name, fieldTp: ktype): pure expr
  make-cctx-prim(gamma, nameFieldAddrOf, "", [obj.type-of, fieldTp],
    [obj, ELit(LitString(show-tupled(cName.get-name))), ELit(LitString(show-tupled(fieldName)))])

// Set the index of the field in a constructor to follow the path to the hole at runtime.
fun make-set-ctx-path(obj: expr, cName: t-name, fieldName: name)
  val tp = obj.type-of
  val funType = TFun([(nil, tp), (nil, typeString), (nil, typeString)], typeTotal, tp)
  App(Var(TName(nameCCtxSetCtxPath, funType), core/InfoExternal("@cctx-setcp(#1,#2,#3)")), 
    [obj, ELit(LitString(show-tupled(cName.get-name))), ELit(LitString(show-tupled(fieldName)))])


fun get-field-name(cName: t-name, fieldIdx: int)
  match cName.lookup(fieldIdx)
    Left(err) -> failure/fail("core/analysiscctx: " ++ err)
    Right(name) -> name

fun ensure-valid-hole-type(tp: ktype)
  match tp.data-type-name-of 
    Left(TVar) -> emit-ctx-err("the hole in the constructor context has an unresolved or polymorphic type".text)
    Left -> emit-ctx-err("the hole in the constructor context has an invalid data type".text)
    Right(nm) -> 
      match newtypes-lookup-any(nm)
        Just(dataInfo) ->
          val (drepr, _) = dataInfo.data-repr(is-value)
          if dataInfo.def.is-value || drepr.is-value then
            emit-ctx-err("the hole in a constructor context cannot be a value type".text)
          ()

fun data-type-name-of(tp: ktype)
  match tp.expand-syn
    TApp(t) -> t.data-type-name-of
    TCon(tc) -> Right(tc.name)
    t -> Left(t)

fun data-type-name-res(tp: ktype)
  match tp.data-type-name-of
    Right(name) -> name
    Left(t) -> failure/fail("core/ctail data-type-name-res: illegal result type: " ++ t.show)

fun data-type-name(cName: t-name)
  match cName.type-of.split-fun-scheme
    Just((_, _, _, tres)) -> tres.data-type-name-res
    _ -> failure/fail("core/ctail get-data-type-name: illegal constructor type: " ++ cName.show)

pub fun lookup(cName: t-name, fieldIdx: int)
  match newtypes-lookup-any(cName.data-type-name)
    Just(dinfo) ->
      val (drepr, _) = dinfo.data-repr(is-value)
      if drepr.is-value then
        Left("contexts cannot go through a value type (" ++ cName.get-name.show ++ ")")
      else
        match dinfo.constrs.filter(_.name == cName.get-name)
          [c] -> 
            match c.params.drop(fieldIdx - 1)
              Cons((fname, ftp)) -> Right(TName(fname, ftp))
              _ -> failure/fail("core/ctail get-field-name: field index is off: " ++ cName.show ++ ", field " ++ fieldIdx.show ++ ", in " ++ c.params.show-list(fn((n, _)) n.show))
          _ -> failure/fail("core/ctail get-field-name: constructor not found: " ++ cName.show ++ ", field " ++ fieldIdx.show ++ ", in " ++ dinfo.constrs.map(show).join(","))
      
