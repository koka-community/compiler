// Updated as of 7/23/26: Commit 0b3296d
module compiler/core/open-resolve

import compiler/common/name
import compiler/common/range
import compiler/common/name-prim
import compiler/common/failure
import compiler/common/unique
import compiler/platform/config
import compiler/common/syntax
import compiler/core/core
import compiler/core/corevar
import compiler/type/assumption
import compiler/type/typevar
import compiler/type/type
import compiler/type/pretty
import compiler/type/kind
import compiler/kind/kind
import compiler/lib/pprint
import std/data/rb-map
import std/core/undiv
import compiler/common/name-collections

// pair each label in a row with its "mask level": 0 for the first occurrence
// of a label name, 1 for the second, etc. (upstream `addLevels`, issue #511 --
// duplicate labels, e.g. from re-establishing an effect via `mask<eff>`, must
// resolve to DIFFERENT evidence frames, not always the outermost one)
fun add-levels(ls: list<ktype>): _ list<(ktype, int)>
  fun prev(name-prev: name, level-prev: int, rest: list<ktype>): _ list<(ktype, int)>
    match rest
      Nil -> Nil
      Cons(l, ls') ->
        val name = l.label-name
        val level = if name-prev == name then level-prev + 1 else 0
        Cons((l, level), prev(name, level, ls'))
  match ls
    Nil -> Nil
    Cons(l, ls') -> Cons((l, 0), prev(l.label-name, 0, ls'))

pub effect open-eff
  fun get-gamma(): gamma

pub fun open-resolve()
  set-core-defs(resolve(get-core-defs()))

// transform definition groups
fun dgs/resolve(dgs: def-groups): _ def-groups
  dgs.map(resolve)

fun dg/resolve(dg: def-group): _ def-group
  match dg
    DefRec(dfs) -> DefRec(dfs.map(resolve))
    DefNonRec(df) -> DefNonRec(resolve(df))

// Transform a definition
fun def/resolve(d: def)
  d(defExpr=d.defExpr.resolve)

fun expr/resolve(ex: expr)
  match ex
    App(eopen as TypeApp(Var(open), [effFrom, effTo, tpFrom, tpTo]), [f]) | open.get-name == nameEffectOpen ->
      resolve-open(eopen, effFrom, effTo, tpFrom, tpTo, resolve(f))
    // regular cases
    Lam(args, eff, body) -> Lam(args, eff, body.resolve)
    App(f, args) -> App(f.resolve, args.map(resolve))
    Let(dfgs, body) -> Let(dfgs.resolve, body.resolve)
    Case(exprs, bs) -> Case(exprs.map(resolve), bs.map(resolve))
    TypeLam(tvars, body) -> TypeLam(tvars, body.resolve)
    TypeApp(f, tps) -> TypeApp(f.resolve, tps)
    _ -> ex // var,lit

fun branch/resolve(Branch(pat, guards): branch)
  Branch(pat, guards.map(resolve))

fun guard/resolve(Guard(test, body): guard)
  Guard(test.resolve, body.resolve)

// Insert open call
fun resolve-open(eopen: expr, effFrom: ktype, effTo: ktype, tpFrom: ktype, tpTo: ktype, expr: expr)
  match tpTo
    TFun(targs, _, tres) ->
      val n = targs.length
      val (lsFrom, tlFrom) = effFrom.extract-handled-effect
      val (lsTo, tlTo) = effTo.extract-handled-effect
      if effFrom.match-type(effTo) then
        // exact match just use expr
        expr
      elif !effFrom.is-effect-fixed then
        failure/fail("core/open-resolve resolve-open: todo: masking handled effect " ++ effFrom.pretty.show)
      elif tlFrom.match-type(tlTo) && lsFrom.length == lsTo.length && lsFrom.zip(lsTo).all(fn((t1, t2)) t1.match-type(t2)) then
        // same handled effects, just use expr
        expr
      else
        // not equal in handled effects, insert open
        // `gammaLookupQ`, an EXACT lookup that also finds hidden
        // names. `gamma-lookup` filters candidates through `is-visible` (public only)
        // and matches qualifier paths, so it cannot see the `@tag` of a hidden effect
        // such as `std/async/internal/#async-ioc` -- which every `open` over that
        // effect needs.
        fun resolve(nm: name)
          match get-gamma().lookupQ(nm)
            [info] -> info.core-expr(info.cname)
            _ -> failure/fail("core/open-resolve resolve-open: unknown name: " ++ nm.show)
        val params = list(1, targs.length).zip(targs).map(fn((i, t)) TName(new-hidden-name("x" ++ i.show), t.snd))
        val exprName = TName(new-hidden-name("x0"), tpFrom)
        val exprVar = Var(exprName, InfoNone)
        fun expr-app(lam: expr)
          App(Lam([exprName], typeTotal, lam), [expr])
        fun wrapper-thunk(openExpr: expr, evExprs: list<expr>)
          expr-app(Lam(params, effTo, 
            App(TypeApp(openExpr, [tres, effFrom, effTo]), 
              evExprs ++ [Lam([], effTo, App(exprVar, params.map(Var(_, InfoNone))))])))
        fun wrapper(openExpr: expr, evExprs: list<expr>)
          expr-app(Lam(params, effTo, 
            App(TypeApp(openExpr, targs.map(snd) ++ [tres, effFrom, effTo]), 
              evExprs ++ [exprVar] ++ params.map(Var(_, InfoNone)))))
        fun ev-index-of(l: ktype)
          val (htagTp, hndTp) =
            val (name, _, tpArgs) = l.label-name-ex
            // use the effect label name itself (NOT the @hnd handler-datatype name):
            // Simplify's effect-offset does `label-name(hndTp)` and matches it against
            // the effect-row labels, so hndTp's head must be the effect con `<eff>`, not
            // `<eff>/@hnd`.
            val hndCon = TCon(TypeCon(name, kind-fun-n(tpArgs.map(kind) ++ [kindEffect, kindStar], kindStar)))
            // `type-app`, not the raw `TApp` constructor: upstream's `typeApp t []`
            // returns `t` unchanged, so for a label with no type parameters (e.g.
            // `exn`) hndTp must be the bare `TCon`. Building `TApp(TCon exn, [])`
            // is semantically the same type but structurally different, and any
            // pass that compares types by structure -- `Core.Check`'s `unify`
            // being the one that caught it -- sees two `htag<exn>` that will not
            // unify.
            (make-type-app(resolve(name.to-effect-tag-name), tpArgs), hndCon.type-app(tpArgs))
          App(TypeApp(resolve(nameEvvIndex), [effTo, hndTp]), [htagTp])
        // account for duplicate labels in the row (issue #511): the Nth
        // occurrence of the same label needs the Nth evidence frame for it,
        // found via `@evv-index-mask` instead of the plain (always-first) index
        fun ev-index-of-mask((l, level): (ktype, int))
          if level == 0 then l.ev-index-of
          else App(TypeApp(resolve(nameEvvIndexMask), [effTo]), [l.ev-index-of, make-ev-index(level)])
        val tails-match = tlFrom.match-type(tlTo)
        match lsFrom
          Nil -> // no handled effect, use cast
            // a cast only when the tails match too: opening `total` into `<ndet|e>` needs
            // an open-none, since `e` may be instantiated with handled effects at runtime
            if lsTo.is-nil && tails-match then expr
            else
                if expr.is-handler-free then expr
                elif n <= 4 then wrapper(resolve(n.name-open-none), []) // fails in perf1c with exceeded stack size if --optmaxdup < 500 (since it prevents a tailcall)
                else
                  // expr -- fails in nim as it's evidence is not cleared
                  wrapper-thunk(resolve(0.name-open-none), [])
          [l] -> // just one: use open-atN for efficiency
            if n <= 4 then wrapper(resolve(name-open-at(n)), [l.ev-index-of])
            else wrapper-thunk(resolve(name-open-at(0)), [l.ev-index-of])
          _ ->
            val indices = make-vector(typeEvIndex, lsFrom.add-levels.map(ev-index-of-mask))
            if n <= 3 then
              wrapper(resolve(n.name-open), [indices])
            else
              wrapper-thunk(resolve(0.name-open), [indices])
    _ -> failure/fail("core/open-resolve resolve-open: open applied to a non-function? " ++ effTo.pretty.show)

// Can a call of this function expression skip `open-none`, running under the
// caller's evidence vector instead of an empty one? Only if the call can never
// look up evidence: code compiled for a closed row finds evidence at static
// offsets into its own row, so it must not run under extra evidence. It can do
// that by installing a handler, or by running any Koka code whose row is closed.
// A function's type rules out neither, so an unknown function is never handler
// free, whatever module it is in.
fun is-handler-free(ex: expr)
  match ex
    TypeLam(_, body) -> is-handler-free(body)
    TypeApp(f, _) -> is-handler-free(f)
    Lam(_, eff, body) -> !contains-handled-effect([], eff) && is-handler-free(body)
    App(f, args) -> is-handler-free(f) && args.all(is-handler-free)
    // an external runs no Koka code of its own, but may call a function it is
    // passed; the identity (`#1`, the casts) calls nothing
    Var(vname, core/InfoExternal(format)) ->
      match vname.type-of.split-fun-scheme
        Just((_, pars, eff, _)) -> !contains-handled-effect([], eff) && (format == "#1" || !pars.any(fn((_, tp)) tp.mentions-fun))
        Nothing -> True
    Var(vname) -> vname.type-of.split-fun-scheme.is-nothing
    Con -> True
    ELit -> True
    _ -> False

fun mentions-fun(tp: ktype): bool
  match tp
    TFun -> True
    TForAll(_, t) -> t.mentions-fun
    TApp(t, ts) -> t.mentions-fun || ts.any(_.pretend-decreasing.mentions-fun)
    TSyn(_, _, t) -> t.mentions-fun
    _ -> False
