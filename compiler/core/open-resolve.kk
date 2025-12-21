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
import compiler/type/type
import compiler/type/pretty
import compiler/type/kind
import compiler/kind/kind
import compiler/lib/pprint

alias openEff = <openEffect, comp-flags, unique, pure, documentation>

effect openEffect
  fun get-gamma(): gamma

fun open-resolve()
  set-core-defs(resolve(get-core-defs()))

// transform definition groups
fun dgs/resolve(dgs: def-groups): openEff def-groups
  dgs.map(resolve)

fun dg/resolve(dg: def-group): openEff def-group
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
      val (lsFrom, tlFrom) = effFrom.extractHandledEffect
      val (lsTo, tlTo) = effTo.extractHandledEffect
      if effFrom == effTo then
        // exact match just use expr
        expr
      elif !effFrom.isEffectFixed then
        fail("core/open-resolve resolve-open: todo: masking handled effect " ++ effFrom.pretty.show)
      elif tlFrom.match-type(tlTo) && lsFrom.length == lsTo.length && lsFrom.zip(lsTo).all(fn((t1, t2)) t1 == t2) then
        // same handled effects, just use expr
        expr
      else
        // not equal in handled effects, insert open
        fun resolve(nm: name)
          match get-gamma().gamma-lookup(nm)
            [(qname, info)] -> info.core-expr(qname)
            _ -> fail("core/open-resolve resolve-open: unknown name: " ++ nm.show)
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
            val hndCon = TCon(TypeCon(name.to-handler-name, kind-fun-n(tpArgs.map(kind) ++ [kindEffect, kindStar], kindStar)))
            (make-type-app(resolve(name.to-effect-tag-name), tpArgs), TApp(hndCon, tpArgs))
          App(TypeApp(resolve(nameEvvIndex), [effTo, hndTp]), [htagTp])
        match lsFrom
          Nil -> // no handled effect, use cast
            match lsTo
              Nil -> expr
              _ -> 
                if expr.is-handler-free then expr // fully total with using any operations that need evidence; just leave it as is
                elif n <= 4 then wrapper(resolve(n.name-open-none), []) // fails in perf1c with exceeded stack size if --optmaxdup < 500 (since it prevents a tailcall)
                else 
                  // expr -- fails in nim as it's evidence is not cleared
                  wrapper-thunk(resolve(0.name-open-none), []) 
          [l] -> // just one: use open-atN for efficiency
            if n <= 4 then wrapper(resolve(name-open-at(n)), [l.ev-index-of])
            else wrapper-thunk(resolve(name-open-at(0)), [l.ev-index-of])
          _ ->
            val indices = make-vector(typeEvIndex, lsFrom.map(ev-index-of))
            if n <= 3 then
              wrapper(resolve(n.name-open), [indices])
            else
              wrapper-thunk(resolve(0.name-open), [indices])
    _ -> fail("core/open-resolve resolve-open: open applied to a non-function? " ++ effTo.pretty.show)

// is a function expression handler free?: meaning if invoked it will never need evidence (invoke an operation) or change the eveidence (use a handler)
fun is-handler-free(ex: expr)
  match ex
    TypeLam(_, body) -> is-handler-free(body)
    TypeApp(f, _) -> is-handler-free(f)
    Lam(_, eff, body) -> !contains-handled-evidence([], eff) && is-handler-free(body)
    App(f, args) -> is-handler-free(f) && args.all(is-handler-free)
    Var(vname, core/InfoExternal) -> 
      match vname.type-of.handler-free-fun-type
        Nothing -> True
        Just(ok) -> ok
    Var(vname) ->
      match vname.type-of.handler-free-fun-type
        Nothing -> True
        Just(ok) -> ok && vname.get-name.is-system-core-name
    Con -> True
    ELit -> True
    _ -> False

fun handler-free-fun-type(tp: ktype)
  match tp.split-fun-scheme
    Just((_, _, eff, _)) -> Just(!contains-handled-evidence([], eff))
    _ -> Nothing