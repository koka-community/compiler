module compiler/type/infer

import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/failure
import compiler/common/unique
import compiler/common/message
import compiler/platform/config
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/import-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/assumption
import compiler/type/infgamma
import compiler/type/unify
import compiler/type/pretty
import compiler/type/operations
import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/syntax/range-map
import compiler/core/core
import compiler/lib/pprint
import std/data/linearmap
import std/data/linearset
import std/data/sort
import std/core/undiv
import std/core/unsafe
import compiler/lib/core
import compiler/type/infer-effect


//////////////////////////////////////////
// Infer Types
//////////////////////////////////////////


//////////////////////////////////////////
// Definition Groups
//////////////////////////////////////////


//////////////////////////////////////////
// Definition
//////////////////////////////////////////

fun unskolemize(tp: ktype): _ ktype
  val svs = tp.fsv.list
  val uvs = svs.map(fn(tv) fresh-tvar(tv.kind, Meta))
  val sub' = svs.zip(uvs).sub
  val tpu = sub' |-> tp
  tpu






fun checkValue(rng: range) Check("Values cannot have an effect", rng)
fun checkPolyValue(rng: range) Check("Polymorphic values cannot have an effect", rng)
fun unused-warning(rng: range)
  inf-warning(rng, "expression has no effect and is unused".text |-|
                   " hint: did you forget an operator? or used \"fun\" instead of \"fn\"?".text)

//////////////////////////////////////////
// Expression
//////////////////////////////////////////
type expect
  Generalized(b: bool)
  Instantiated

fun expect/(==)(e1: expect, e2: expect): bool
  match (e1, e2)
    (Generalized(b1), Generalized(b2)) -> b1 == b2
    (Instantiated, Instantiated) -> True
    _ -> False
fun expect/show(e: expect): string
  match e
    Generalized(b) -> "Generalized(" ++ b.show ++ ")"
    Instantiated -> "Instantiated"

pub fun remove-local-effect(ftp: ktype)
  match ftp.split-fun-scheme
    Just((foralls, args, eff, resTp)) -> 
      val (ls, tl) = eff.extract-ordered-effect
      quantify-type(foralls, TFun(args, ls.filter(_.label-name != nameTpLocal).foldr(tl, effect-extend), resTp))
    _ -> fail("type/infer/remove-local-effect: unexpected type: " ++ ftp.show)


//////////////////////////////////////////
// Infer Effect Handlers
//////////////////////////////////////////

///////////////////////////////////////////////////////////
// Infer Applications and Resolve Overloaded Identifiers
//////////////////////////////////////////////////////////

//////////////////////////////////////////
// Infer Lambda
//////////////////////////////////////////


//////////////////////////////////////////
// Infer Variables
//////////////////////////////////////////


//////////////////////////////////////////
// infer match, branches and patterns
//////////////////////////////////////////

type pattern-kind
  PatternOutermost(is-lazy: bool)
  PatternNested







fun checkFun(rng: range) 
  Check("function type does not match the argument types", rng)
fun checkMatch(rng: range) 
  Check("branch has not the same type as previous branches", rng)
fun checkAnn(rng: range) 
  Check("type cannot be instantiated to match the annotation", rng)
fun checkRec(rng: range) 
  Check("recursive invocations do not match the assumed type; add a type annotation?", rng)
fun checkGuardTotal(rng: range) 
  Check("guard expressions must be total", rng)
fun checkGuardBool(rng: range) 
  Check("guard expressions must be of a boolean type", rng)
fun checkConMatch(rng: range) 
  Check("constructor must have the same the type as the matched term", rng)
fun checkLitMatch(rng: range) 
  Check("literal pattern does not match the type of the matched term", rng)
fun checkConTotal(rng: range) 
  Check("constructor in a pattern must have a total effect type", rng)
fun checkLit(rng: range)      
  Check("literal does not match the expected type", rng)
fun checkOptional(rng: range) 
  Check("default value does not match the parameter type", rng)
fun checkOptionalTotal(rng: range) 
  Check("default value expression must be total", rng)
fun checkInject(rng: range) 
  Check("inject expects a parameter-less function argument", rng)
val checkEffect = Infer
fun checkEffectSubsume(rng: range) 
  Check("effect cannot be subsumed", rng)
fun checkReturnResult(rng: range) 
  Check("function returns values of different types", rng)
fun checkReturn(rng: range)        
  Check("return type does not match an earlier return type", rng)
fun checkOp(rng: range)         
  Check("operator type does not match the parameter types", rng)
fun checkMakeHandler(rng: range) 
  Check("handler types do not match the handler maker; please report this as a bug!", rng)
fun checkMakeHandlerBranch(rng: range) 
  Check("handle branch types do not match the handler branch maker; please report this as a bug!", rng)
fun checkEffectTp(rng: range)   
  Check("operator type does not match the effect type", rng)
fun checkLocalScope(rng: range) 
  Check("a reference to a local variable escapes it's scope", rng)

//////////////////////////////////////////
// infer arguments
//////////////////////////////////////////





// Match given fixed arguments and named arguments with a function type.
// some fixed arguments may already have been inferred (`fresolved`).
// also returns a list of implicit arguments that need to be resolved.
// returns:
// - iargs: a list of indexed argument terms, either user expressions, already resolved (from `fresolved`), or implicit names
//          the indices indicate the required evaluation order (due to named arguments).
// - pars: list of the full function parameters (name,type)
// - effect of the function
// - the result type of the function
// - a core transformer that modifies the application appropriately (for constructor copy)
type arg-expr
  ArgExpr(e: syntax/syntax/expr<ktype>, hide-range-info: bool)
  ArgCore(arg: fixed-arg)
  ArgImplicit(name: name, app-range: range, name-range: range)

fun pp-arg-expr(ae: arg-expr): _ doc
  match ae
    ArgExpr(e, _) -> "ArgExpr".text |+| e.pretty
    ArgCore((_, tp, _, _)) -> "ArgCore".text |+| tp.pp-type
    ArgImplicit(n, _, _) -> "ArgImplicit".text |+| n.pp-name



// Try to match the propagated type with a function type,
// returning the propagated argument, effect, and result type, and the expected instantiation of the result
type fun-match-result
  FunMatchResult(
    mb-args: list<maybe<(name, ktype)>>,
    mb-eff: maybe<(ktype, range)>,
    mb-body: maybe<(ktype, range)>,
    mb-skolems: list<type-var>,
    expect: expect
  )
type fun-match-type-args
  FunMatchTypeArgs(
    mb-args: list<(int, arg-expr)>,
    mb-named: list<(name, ktype)>,
    eff: keffect,
    res: ktype,
    fcore: (core/core/expr, list<core/core/expr>) -> core/core/expr
  )

fun wrap-delay(e: syntax/syntax/expr<ktype>, r): _ syntax/syntax/expr<ktype>
  fun is-delayed(expr: syntax/syntax/expr<ktype>): _ bool
    match expr
      Lam([]) -> True
      Var(n) -> 
        match lookup-name-ctx(is-info-val-fun-ext, n, CtxFunArgs(False, 0, [], Nothing), expr.range)
          [(_, info)] -> info.scheme.is-delayed-type
          _ -> False
      _ -> False
  if is-delayed(e) then e
  else Lam([], e, False, e.range)

fun extract(name: name, acc: list<(int, (name, ktype))>, args: list<(int, (name, ktype))>): maybe<(int, ktype, list<(int, (name, ktype))>)>
  match args
    [] -> Nothing
    Cons(par as (i, (n, tp)), rest) -> 
      if n == name || name == n.split-implicit-param-name.fst then Just((i, tp, acc.reverse ++ rest))
      else extract(name, Cons(par, acc), rest)

fun match-fun-type-args(ctx-range: range, f: syntax/syntax/expr<ktype>, tp: ktype, fresolved: list<(int, fixed-arg)>, fixed: list<syntax/syntax/expr<ktype>>, named-args: list<((name, range), syntax/syntax/expr<ktype>)>): _ fun-match-type-args
  val rng = f.range
  fun report-non-callable()
    fun shadow-hint((nm: name, name-info: assumption/name-info))
      [("hint".text, nm.pp-name |+| "at position".text |+| name-info.range.show.text |+| "might be shadowing another function".text)]
    val hints = 
      match f
        Var(name) ->
          match lookup-local-name(is-infoVal, name)
            Right((nm, nm-info)) -> shadow-hint((nm, nm-info))
            Left(results) -> results.flatmap(shadow-hint) //  Multiple locals with the same name?
        _ -> []
    type-error(ctx-range, rng, "only functions or types with a copy constructor can be applied".text, tp, hints)
    FunMatchTypeArgs((fixed ++ named-args.map(snd)).map-indexed(fn(i, x) (i, ArgExpr(x, True))), [], typeTotal, typeUnit, core/core/App)
  fun match-fixed(pars, fixed, fresolved)
    match (pars, fixed)
      (pars, []) -> (pars, [])
      (Cons((name, tp), pars'), Cons((i, arg), fixed')) -> 
        match fresolved.lookup(i)
          Just((crng, ctp, ceff, carg)) -> 
            val (newtp, newarg) = 
                  if tp.is-optional then (ctp.make-optional-type, ctp.wrap-optional(carg))
                  else (ctp, carg)
            val (prest, rest) = match-fixed(pars', fixed', fresolved)
            (prest, Cons((i, ArgCore((crng, newtp, ceff, newarg))), rest))
          Nothing -> 
            val newarg = if tp.is-optional then wrap-optional(arg) elif tp.is-delay then arg.wrap-delay else arg
            val (prest, rest) = match-fixed(pars', fixed', fresolved)
            (prest, Cons((i, ArgExpr(newarg, False)), rest))
      _ -> 
        type-error(ctx-range, rng, "function is applied to too many arguments".text, tp, [])
        ([], [])
  // in the result, the first int is position of the parameter `j`, the second int `i` is the original position of
  // the argument (so we can evaluate in argument order)
  fun match-named(pars, named-args)
    match (pars, named-args)
      ([], []) -> []
      ([], Cons()) -> 
        type-error(ctx-range, rng, "function is applied to too many arguments".text, tp, [])
        []
      (_, Cons((i, ((name, rng), arg)), named-rest)) -> 
        match extract(name, [], pars)
          Just((j, tp, pars-rest)) -> 
            val newarg = if tp.is-optional then wrap-optional(arg) elif tp.is-delay then arg.wrap-delay else arg
            Cons((j, (i, ArgExpr(newarg, rng.is-null))), match-named(pars-rest, named-rest))
          Nothing -> 
            type-error(ctx-range, rng, "there is no parameter with name".text |+| name.pp-name, tp, [])
            match-named(pars, named-rest)
      (_, []) -> 
        if pars.all(_.snd.is-optional-or-implicit) then 
          val (optionals, implicits) = pars.span(_.snd.snd.is-optional)
          val ops = zip(list(fixed.length + named-args.length, pars.length), optionals) // TODO Fix the list()
            .map fn(i, (j, (n, tpar)))
            (j, (i, ArgExpr(make-optional-none(True))))
          val imps = zip(list(fixed.length + named-args.length + ops.length, pars.length), implicits)
            .map fn(i, (j, (n, tpar)))
            (j, (i, ArgImplicit(n, rng, rng)))
          ops ++ imps
        else 
          val hints = match f.root-expr
            Var(name, is-op, nm-range) | name == "resume".new-name ->
              [("hint".text, "cannot use \"resume\" inside a val/fun/except clause")]
            _ -> []
          type-error(ctx-range, rng, "function does not have enough arguments".text, tp, hints)
          [] 
  fun match-parameters(pars)
    val (pars1, args1) = match-fixed(pars, fixed.indexed, fresolved)
    val indexed = list(fixed.length, fixed.length + pars1.length)
    val iargs2 = match-named(zip(indexed, pars1), zip(indexed, named-args))
    args1 ++ iargs2.sort(fn((i1, _), (i2, _)) cmp(i1, i2).lt).map(snd)
  match tp
    TFun(pars, eff, res) -> 
      val iargs = match-parameters(pars)
      FunMatchTypeArgs(iargs, pars, eff, res, core/core/App)
    TSyn(_, _, t) -> match-fun-type-args(ctx-range, f, t, fresolved, fixed, named-args)
    TVar(tv) -> 
      if !named-args.is-empty then // TODO: take fresolved into account
        inf-error(rng, "cannot use named arguments on an inferred function".text |-| 
                        " hint: annotate the parameters".text)
      val targs = fixed.map(fn(_) (nil, fresh-star())) ++ named-args.map(fn(n) (n.fst, fresh-star()))
      val teff = fresh-effect()
      val tres = fresh-star()
      extend-sub([tv, TFun(targs, teff, tres)].single)
      FunMatchTypeArgs((fixed ++ named-args.map(snd)).map-indexed(fn(i, x) (i, ArgExpr(x, False))), targs, teff, tres, core/core/App)
    _ -> 
      // apply the copy constructor if we can find it
      val matches = lookup-name-ctx(is-info-val-fun-ext, nameCopy, CtxFunTypes(True, [tp], [], Nothing), rng)
      match matches
        [(qname, info)] ->
          val (contp, _, coreInst) = info.scheme.instantiate-ex(rng)
          val FunMatchTypeArgs(iargs, pars, eff, res, _) = match-fun-type-args(ctx-range, f, contp, fresolved, Cons(f, fixed), named-args)
          FunMatchTypeArgs(iargs, pars, eff, res, fn(c, cargs) core/core/App(coreInst(info.core-expr(qname)), cargs))
        _ -> report-non-callable()

fun match-fun(nargs: int, mb-type: maybe<(ktype, range)>): _ fun-match-result
  match mb-type
    Nothing -> FunMatchResult(Nothing.replicate(nargs), Nothing, Nothing, [], Instantiated)
    Just((tp, rng)) -> 
      val (skolems, rho, _) = tp.skolemize-ex(rng)
      match rho.split-fun-type
        Nothing -> FunMatchResult(Nothing.replicate(nargs), Nothing, Nothing, skolems, Instantiated)
        Just((args, eff, res)) -> 
          val m = args.length 
          // can happen: see test/type/wrong/hm4 and hm4a
          FunMatchResult((args.map(Just) ++ Nothing.replicate(nargs - m)).take(nargs), 
                          Just((eff, rng)), Just((res, rng)), skolems, 
                          if res.is-rho then Instantiated else Generalized(False))




//////////////////////////////////////////
// Helpers
//////////////////////////////////////////
fun instantiate-binder(b: value-binder<maybe<ktype>, e>): _ value-binder<ktype, e>
  match b
    ValueBinder(name, Just(tp), e, nrng, rng) -> ValueBinder(name, tp, e, nrng, rng)
    ValueBinder(name, Nothing, e, nrng, rng) -> ValueBinder(name, fresh-star(), e, nrng, rng)

// Maybe generalize. The effect is the current effect context and should not be generalized over.
fun maybe-generalize(ctx-range: range, rng: range, expect: expect, f: () -> _ (ktype, keffect, core/core/expr)): _ (scheme, keffect, core/core/expr)
  match expect
    Instantiated -> f()
    Generalized(close) -> generalize(ctx-range, rng, close, f) 

fun maybe-instantiate(rng: range, expect: expect, tp: scheme): _ (rho, core/core/expr -> core/core/expr)
  match expect
    Generalized() -> (tp, id)
    Instantiated -> 
      val (rho, _, coref) = tp.infer-effect/instantiate(rng)
      (rho, coref)

fun maybe-instantiate-or-generalize(ctx-range: range, rng: range, expect: expect, f: () -> (ktype, keffect, core/core/expr)): _ (ktype, keffect, core/core/expr)
  match expect
    Generalized(close) -> generalize(ctx-range, rng, close, f)
    Instantiated -> 
      val (tp, eff, core) = f()
      val (itp, _, icore) = tp.infer-effect/instantiate(rng)
      (itp, eff, icore(core))

fun core-vector(cs: list<core/core/expr>, tp: ktype): _ core/core/expr
  val (vecName, _, vecInfo) = resolve-fun-name(nameVector, CtxFunArgs(False, 0, ["xs".new-name], Nothing), null, null) // TODO: lookup vector less fragile?
  val vecx = TypeApp(vecInfo.core-expr(vecName), [tp])
  core/core/App(vecx, [cs.core-list(tp)])

fun core-list(cs: list<core/core/expr>, tp: ktype): _ core/core/expr 
  val (consName, consTp, consRepr, _) = resolve-con-name(nameCons, Nothing, null)
  val (nilName, nilTp, nilRepr, _) = resolve-con-name(nameListNil, Nothing, null)
  val consx = TypeApp(core/core/Con(TName(consName, consTp), consRepr), [tp])
  val nil = TypeApp(core/core/Con(TName(nilName, nilTp), nilRepr), [tp])
  cs.foldr(nil) fn(c, acc)
    core/core/App(consx, [c, acc])