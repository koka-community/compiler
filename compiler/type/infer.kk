module compiler/type/infer
// Updated as of 7/23/26: Commit 9bc234e

import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/error
import compiler/common/failure
import compiler/common/unique
import compiler/common/nice
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
import compiler/core/corevar
import compiler/core/analysis-match
import compiler/core/analysis-cctx
import compiler/core/binding-groups
import compiler/core/divergent
import compiler/lib/pprint
import std/num/float64
import std/data/rb-set
import std/data/sort
import std/core/undiv
import std/core/unsafe
import compiler/type/infer-effect
import compiler/type/infer-support
import compiler/type/infer-helpers
import std/data/rb-map

fun infer-assign(prop, expect, assign: syntax/syntax/expr<ktype>, arng: range, lhs: (maybe<(name, range)>, syntax/syntax/expr<ktype>), rhs: (maybe<(name, range)>, syntax/syntax/expr<ktype>), rng: range): _ (ktype, keffect, core/core/expr)
  fun fresh-ref-type()
    val hvar = fresh-tvar(kindHeap, Meta)
    val xvar = operations/fresh-star()
    TApp(typeRef, [hvar, xvar])
  match lhs.snd
    App(fun0, args, lrng) -> // array[i] := e
      val xargs = match args
        Cons((mbName, arg as Var(target, _, vrng)), rest) -> // var_vec[i] := e   TODO: perhaps unsafe for general use?
          val (_, gtp, _) = resolve-name(target, Nothing, vrng)
          val (_, tp, _) = instantiate-noex(gtp, vrng)
          if tp.is-type-local-var
            then Cons((mbName, App(Var(nameByref, False, vrng), [(Nothing, arg)], lrng)), rest)
            else args
        _ -> args
      expr/infer(prop, expect, App(fun0, xargs ++ [(Nothing, rhs.snd)], rng))
    Var(target, _, lrng) ->
      val (_, gtp, _) = resolve-name(target, Nothing, lrng)
      val (_, tp, _) = instantiate-ex(gtp, lrng)
      val nameSet =
        if tp.is-type-local-var then nameLocalSet
        else
          val r = fresh-ref-type()
          val _ =
            with val ctxt = Check("an assignable identifier must have a reference type", rng)
            infer-unify(lrng, r, tp)
          nameRefSet
      expr/infer(prop, expect,
        App(Var(nameSet, False, arng), [(Nothing, App(Var(nameByref, False, lrng.before), [lhs], lrng)), rhs], rng))
    _ ->
      context-error(rng, lhs.snd.range, "not an assignable expression".text,
        [("because".text, "an assignable expression must be an application, index expression, or variable".text)])
      (typeUnit, typeTotal, core/core/Con(TName(name-tuple(0), typeUnit), ConEnum(nameTpUnit, DataEnum, valuerepr/zero, 0)))

// effect injection: `mask<l>(e)`

fun infer-inject(prop: maybe<(ktype, range)>, label: ktype, expr0: syntax/syntax/expr<ktype>, behind: bool, rng: range): _ (ktype, keffect, core/core/expr)
  val eff0 = operations/fresh-effect()
  val eff = if !behind then eff0 else effect-extend(label, eff0)
  fun tfun(r) TFun([], eff, r)
  val prop2 = match prop
    Nothing -> Nothing
    Just((ptp, prng)) ->
      val (foralls, rho) = ptp.split-type-scheme
      Just((quantify-type(foralls, tfun(rho)), prng))
  val (mbHandled, effName) = effect-name-core(label, rng)
  val (exprTp, exprEff, exprCore) =
    if effName == nameTpLocal
      then with-no-local-scope({expr/infer(prop2, Instantiated, expr0)})
      else expr/infer(prop2, Instantiated, expr0)
  val res = operations/fresh-star()
  val fullRng = combine([rng, expr0.range])
  val _ =
    with val ctxt = checkInject(fullRng)
    infer-unify(expr0.range, tfun(res), exprTp)
    infer-unify(expr0.range, eff, exprEff)
  val resTp = res.subst
  val effTo = effect-extend(label, eff).subst
  val coreLevel = if behind then exprTrue else exprFalse
  val core = match mbHandled
    // general handled effects use "@inject-effect"
    Just(coreHTag) ->
      val (maskQName, _maskTp, maskInfo) = resolve-fun-name(nameMaskAt, CtxFunArgs(False, 3, [], Nothing), rng, rng)
      val (evvIndexQName, _evvIndexTp, evvIndexInfo) = resolve-fun-name(nameEvvIndex, CtxFunArgs(False, 1, [], Nothing), rng, rng)
      val coreMask = maskInfo.core-expr(maskQName)
      val coreIndex = core/core/App(TypeApp(evvIndexInfo.core-expr(evvIndexQName), [effTo]), [coreHTag])
      core/core/App(TypeApp(coreMask, [resTp, eff, effTo]), [coreIndex, coreLevel, exprCore])
    Nothing ->
      val (maskQName, _maskTp, maskInfo) = resolve-fun-name(nameMaskBuiltin, CtxFunArgs(False, 1, [], Nothing), rng, rng)
      val coreMask = maskInfo.core-expr(maskQName)
      core/core/App(TypeApp(coreMask, [resTp, eff, effTo]), [exprCore])
  (resTp, effTo, core)

// does the expression use any of the given local variables? (for automatic masking of applied handlers)

val checkEffect = Infer
// the full effect row of expression inference (the `infer` alias plus error
// reporting and compiler flags) -- used to tie the recursive knot.
// `pure` is NOT re-listed: `infer` already carries it transitively via
// `pretty-eff` (type/pretty.kk), and listing it again duplicated `exn` and
// `div` in every row that mentions `infer-eff-full` -- exactly the same
// mistake, and the same fix, as the `colors`/`comp-flags` note on
// `infer-full` itself (type/infer-effect.kk).

//////////////////////////////////////////
// The central inference dispatcher:
// takes a propagated type hint, whether the result should be generalized or
// instantiated, and the expression; returns its type, effect, and core expression.
//////////////////////////////////////////
fun expr/infer(prop: maybe<(ktype, range)>, expect: expect, ex: syntax/syntax/expr<ktype>): infer-eff-full (ktype, keffect, core/core/expr)
  match ex
    Lam(binders, body, toplevel, rng) ->
      infer-lam(toplevel, prop, expect, binders, body, rng)
    Let(defgroup, body, _rng) ->
      val (cgroups, (tp, eff, core)) = infer-def-group(False, defgroup, {expr/infer(prop, expect, body)})
      (tp, eff, make-let(cgroups, core))
    Bind(def, body, rng) ->
      val (_tp1, eff1, coreDef) = infer-bind-def(def)
      val cgroup = core/core/DefNonRec(coreDef)
      val (tp, eff2, coreBody) =
        // (perf) no trace-indent handler in the hot path -- see infer-effect.kk note
        with extend-inf-gamma-core(False, [cgroup])
        expr/infer(prop, expect, body)
      val _ =
        with val ctxt = checkEffect(rng)
        infer-unify(rng, eff1, eff2)
      val topEff = eff2.subst
      (tp, topEff, make-let([cgroup], coreBody))
    // return expressions
    App(Var(name, _, nameRng), [(_, expr0)], rng) | name == nameReturn ->
      match lookup-inf-name(nameReturn)
        Nothing ->
          inf-error(rng, "illegal context for a return statement".text)
          expr/infer(prop, expect, expr0)
        Just((_, retTp)) ->
          val (tp, eff, core) = expr/infer(Just((retTp, nameRng)), expect, expr0)
          val _ =
            with val ctxt = checkReturn(rng)
            infer-unify(expr0.range, retTp, tp)
          val resTp = operations/fresh-star()
          val typeReturn = TFun([(name/nil, tp)], typeTotal, resTp)
          add-range-info(nameRng, RIId("return".new-name, NIValue("expr", tp, "", False), [], False))
          (resTp, eff, core/core/App(core/core/Var(TName(nameReturn, typeReturn), InfoExternal("return #1")), [core])) // TODO: fragile
    // assign expressions
    App(assign as Var(name, _, arng), [lhs, rhs], rng) | name == nameAssign ->
      infer-assign(prop, expect, assign, arng, lhs, rhs, rng)
    // applied handlers are treated specially by allowing automatic masking of local effects
    App(Handler(hsort, hscope, hover, Nothing, mbEff, pars, reinit, ret, hfinal, branches, hrng, hrng2), [action], rng) ->
      val lvars = get-local-vars()
      val allow = !uses-locals(lvars.map(fst), action.snd)
      val h = Handler(hsort, hscope, hover, Just(allow), mbEff, pars, reinit, ret, hfinal, branches, hrng, hrng2)
      expr/infer(prop, expect, App(h, [action], rng))
    // byref expressions
    App(Var(byref, _, _), [(_, Var(name, _, rng))], _) | byref == nameByref ->
      infer-var(prop, expect, name, rng, False)
    // hole expressions
    App(fun0 as Var(hname, _, nameRng), [], rng) | hname == nameCCtxHoleCreate ->
      val ok = hole-allowed()
      use-hole()
      if !ok then
        context-error(rng, rng, "ill-formed constructor context".text,
          [("because".text, "there can be only one hole, and it must occur under a constructor context 'ctx'".text)])
      val (tp, eff, core) = infer-app(prop, expect, fun0, [], rng)
      add-range-info(nameRng, RIId("hole".new-name, NIValue("expr", tp, "", False), [], False))
      (tp, eff, core)
    // context expressions
    App(Var(ctxname, _, nameRng), [(_, expr0)], rng) | ctxname == nameCCtxCreate ->
      val tpv = operations/fresh-star()
      val holetp = operations/fresh-star()
      val ctxTp = TApp(typeCCtxx, [tpv, holetp])
      val prop2 = match prop
        Nothing -> Nothing
        Just((ctp, crng)) ->
          val _ =
            with val ctxt = checkMatch(crng)
            infer-unify(nameRng, ctp, ctxTp)
          Just((tpv.subst, rng))
      val ((tp, eff, core), has-hole) = allow-hole({expr/infer(prop2, Instantiated, expr0)})
      val _ =
        with val ctxt = Infer(rng)
        infer-unify(nameRng, tp, tpv)
      if !has-hole then
        context-error(rng, rng, "ill-formed constructor context".text,
          [("because".text, "the context has no hole".text),
           ("hint".text, "perhaps you used an underscore instead of the \"hole\" keyword?".text)])
      val score = core.subst
      val (ccore, errs) = analyze(rng, score, get-target-platform())
      errs.foreach(fn(err) inf-error(rng, err))
      val ctp = ccore.type-of
      add-range-info(nameRng, RIId("ctx".new-name, NIValue("expr", ctp, "", False), [], False))
      (ctp, eff, ccore)
    // application nodes: inference is complicated here since we need to disambiguate overloaded identifiers
    App(fun0, nargs, rng) ->
      infer-app(prop, expect, fun0, nargs, rng)
    Ann(expr0, annTp0, rng) ->
      // match with propagated type first
      val annTp = match prop
        Just((propAnn, propRng)) ->
          val _ =
            with val ctxt = checkAnn(propRng)
            infer-unify(rng, propAnn, annTp0)
          annTp0.subst
        Nothing -> annTp0
      val (tp, eff, core) = expr/infer(Just((annTp, rng.hide)), if annTp.is-rho then Instantiated else Generalized(False), expr0)
      val sannTp = annTp.subst
      val stp = tp.subst
      val (resTp0, coref) =
        with val ctxt = checkAnn(rng)
        infer-subsume(expr0.range, sannTp, stp)
      (resTp0.subst, eff.subst, coref(core).subst)
    Handler(handlerSort, scoped, HandlerNoOverride, mbAllowMask, mbEff, pars, reinit, ret, hfinal, branches, hrng, rng) ->
      val allowMask = match mbAllowMask
        Just(True) -> True
        _ -> False
      infer-handler(prop, expect, handlerSort, scoped, allowMask, mbEff, pars, reinit, ret, hfinal, branches, hrng, rng)
    Handler(handlerSort, scoped, HandlerOverride, mbAllowMask, mbEff, pars, reinit, ret, hfinal, branches, hrng, rng) ->
      val heff = infer-handled-effect(hrng, handlerSort, mbEff, branches)
      val h = Handler(handlerSort, scoped, HandlerNoOverride, mbAllowMask, mbEff, pars, reinit, ret, hfinal, branches, hrng, rng)
      val actionName = "override-action".new-hidden-name
      val actionVar : syntax/syntax/expr<ktype> = Var(actionName, False, rng)
      val actionBind = ValueBinder(actionName, Nothing, Nothing, rng, rng)
      val mask-lam =
        if handlerSort.is-handlerInstance then
          val instName = "override-inst".new-hidden-name
          val instBind = ValueBinder(instName, Nothing, Nothing, rng, rng)
          val instVar : syntax/syntax/expr<ktype> = Var(instName, False, rng)
          val instLam = Lam([], App(actionVar, [(Nothing, instVar)], rng), False, rng)
          Lam([instBind], Inject(heff, instLam, True, rng), False, rng) // mask behind
        else
          Lam([], Inject(heff, actionVar, True, rng), False, rng) // mask behind
      val lam = Lam([actionBind], App(h, [(Nothing, mask-lam)], rng), False, rng)
      expr/infer(prop, expect, lam)
    Case(expr0, branches, isLazyMatch, rng) ->
      infer-case(prop, expect, expr0, branches, isLazyMatch, rng)
    Var(name, _, rng) ->
      infer-var(prop, expect, name, rng, True)
    Literal(lit) ->
      infer-lit(lit)
    Parens(expr0, name, pre, rng) ->
      val (tp, eff, core) = expr/infer(prop, expect, expr0)
      if !name.is-nil then
        add-range-info(rng, RIId(name, NIValue(if pre == "" then "expr" else pre, tp, "", False), [], False))
      (tp, eff, core)
    Inject(label, expr0, behind, rng) ->
      infer-inject(prop, label, expr0, behind, rng)

// show an unsigned integer `x` in binary, left-padded with zeros to `width` bits
// (upstream `showBinary`; no stdlib equivalent for int)
fun uses-locals(lvars: list<name>, ex: syntax/syntax/expr<ktype>): div bool
  fun uses-def(d: syntax/syntax/def<ktype>): div bool
    uses-locals(lvars, d.binder.expr)
  fun uses-mb(mb: maybe<syntax/syntax/expr<ktype>>): div bool
    mb.map(fn(e) uses-locals(lvars, e)).default(False)
  match ex
    App(Var(newLocal, False, _), [_, (_, Parens(Lam([ValueBinder(name)], body), _, _, _))], _) | newLocal == nameLocalVar ->
      uses-locals(lvars.filter(fn(n) !(n == name)), body) // fragile: expects this form from the parser
    Lam(_, body) -> uses-locals(lvars, body)
    Let(defs, body) ->
      val ds = match defs
        DefRec(defs') -> defs'
        DefNonRec(d) -> [d]
      ds.any(uses-def) || uses-locals(lvars, body)
    Bind(def, body) -> uses-def(def) || uses-locals(lvars, body)
    App(fun0, nargs) -> Cons(fun0, nargs.map(snd)).any(fn(e) uses-locals(lvars, e))
    Ann(e) -> uses-locals(lvars, e)
    Case(e, brs) -> uses-locals(lvars, e) || brs.any fn(Branch(_, gs))
      gs.any(fn(Guard(t, e')) uses-locals(lvars, t) || uses-locals(lvars, e'))
    Parens(e) -> uses-locals(lvars, e)
    Handler(initially = reinit, hReturn = ret, finally = hfinal, branches = ops) ->
      uses-mb(reinit) || uses-mb(ret) || uses-mb(hfinal) ||
        ops.any(fn(op) uses-locals(lvars, op.branchExpr))
    Inject(_, e) -> uses-locals(lvars, e)
    Var(name) -> lvars.any(fn(n) n == name)
    _ -> False

// infer a `Bind` definition (a monomorphic non-generalized local definition)
fun infer-bind-def(def: syntax/syntax/def<ktype>): _ (ktype, keffect, core/core/def)
  val Def(ValueBinder(name, _, expr, nameRng, _vrng), rng, vis, sort, inl, doc) = def
  with with-def-name(name)
  with with-scope
  with disallow-hole
  val (tp, eff, coreExpr) =
    // (perf) no trace-indent handler in the hot path -- see infer-effect.kk note
    expr/infer(Nothing, Instantiated, expr)
  val stp = tp.subst
  val seff = eff.subst
  // check for polymorphic values with an effect
  if !stp.is-rho then
    val _ =
      with val ctxt = checkPolyValue(rng)
      infer-unify(nameRng, typeTotal, seff)
    ()
  val coreDef =
    if !sort.is-defVar then core/core/Def(name, stp, coreExpr, vis, sort, inl, nameRng, doc)
    else
      val hp = fresh-tvar(kindHeap, Meta)
      val (qrefName, _, info) = resolve-name(nameRef, Nothing, rng)
      val refTp = TApp(typeRef, [hp, stp])
      val refVar = info.core-expr(qrefName)
      val refExpr = core/core/App(TypeApp(refVar, [hp, stp]), [coreExpr]) // TODO: fragile: depends on order of quantifiers of the ref function!
      core/core/Def(name, refTp, refExpr, vis, sort, inl, nameRng, doc)
  if !name.is-wildcard then
    val sortDoc = if defIsVal(def) then "val" else "fun"
    add-range-info(nameRng, RIId(name, NIValue(sortDoc, coreDef.ktype, doc, expr.is-annot), [], True))
  elif coreDef.ktype.is-type-unit then ()
  else
    // NOTE (shared bug with upstream, do not fix here unilaterally): this
    // check is ORDER-SENSITIVE for recursive groups -- if a val member is
    // inferred before a fun member, the group's shared effect meta collapses
    // to total and this warns spuriously (upstream reproduces: rename
    // `recursive` to `zzz` in test/type/wrong/div1). Any effect-dependent
    // diagnostic here runs before divergence insertion; the principled fix
    // (tracked in TODO_porting.md) is to defer intra-group val-totality
    // constraints (or re-check diagnostics) until after `add-divergent-effect`
    // -- in BOTH compilers, with regenerated expectations.
    val (ls, tl) = seff.extract-effect-extend
    match (ls, tl)
      ([], tl') | tl'.is-type-total -> unused-warning(rng)
      ([], TVar(tv)) ->
        val occ = occurs-in-context(tv, stp.free-type-vars)
        if !occ then unused-warning(rng)
      _ -> ()
  (stp, seff, coreDef)

// infer a single definition
fun infer-def(topLevel: bool, expect: expect, def: syntax/syntax/def<ktype>): _ core/core/def
  val Def(ValueBinder(name, _, expr, nameRng, vrng), rng, vis, sort, inl, doc) = def
  with with-def-name(name)
  with with-scope
  with disallow-hole
  with scope-implicit-constraints
  with fn(act)
    if !sort.is-fun || name.is-nil then act() else allow-return(act)
  val (resTp, _eff, resCore) =
    with maybe-generalize(rng, nameRng, expect)
    // (perf) no trace-indent handler in the hot path -- see infer-effect.kk note
    val (resTp0, eff0, resCore0) = expr/infer(Nothing, expect, expr)
    val _ =
      with val ctxt = checkValue(rng)
      infer-unify(nameRng, typeTotal, eff0)
    (resTp0.subst, eff0.subst, resCore0.subst)
  if sort.is-fun then
    match resTp.split-fun-scheme
      Just((_, _, effTp, resultTp)) ->
        val tp = make-value-operation(effTp, resultTp) // pretty prints nicely as `-> eff res`
        add-range-info(vrng.end-of-range, RIId("result".new-name, NIValue("expr", tp, "", False), [], True))
      _ -> ()
  def/substitute(get-subst(), core/core/Def(name, resTp, resCore, vis, sort, inl, nameRng, doc)) // must subst since the total unification can cause substitution (see test/type/hr1a)

// infer a definition group and continue with `cont` in the extended environment
// (upstream `inferDefGroup`; the recursive case is a first pass without
// divergence re-analysis or canonical-name fixups -- TODO)
fun infer-def-group(topLevel: bool, defgroup: syntax/syntax/def-group<ktype>, cont: () -> _ a): _ (list<core/core/def-group>, a)
  match defgroup
    DefNonRec(def) ->
      // Only the local qualifier
      // is checked there, but upstream also infers a "wrong*"-stemmed def
      // normally (under `ignoreErrors`) rather than skipping it outright; a
      // type error is what triggers the skip-and-cont fallback (residue
      // Infer.hs/InferMonad.hs). Keep the existing wrong-namespace check as an
      // extra disjunct (the port's tests may rely on it).
      val stem = def.binder.name.unqualify.nameStem
      val wrong-stem = stem.starts-with("wrong").bool && stem != "wrong"
      val wrong-pred = topLevel && (wrong-stem || def.binder.name.is-in-wrong-namespace)
      fun normal-infer()
        val core = infer-def(topLevel, Generalized(True), def)
        val (x, core1) =
          if topLevel then
            val core0 = core(def-name = qualify(infer-env.contxt, core.def-name))
            with extend-gamma-core(False, [core/core/DefNonRec(core0)])
            val coreDef = fix-canonical-name(False, core0)
            (cont(), coreDef)
          else
            val x = extend-inf-gamma-core(topLevel, [core/core/DefNonRec(core)], cont)
            (x, core)
        add-range-info-core-def(topLevel, infer-env.contxt, def, core1)
        ([core/core/DefNonRec(core1)], x)
      if wrong-pred then
        ignore-errors({ val x = cont(); ([], x) }, normal-infer)
      else
        normal-infer()
    DefRec(defs0) ->
      if topLevel && defs0.all(fn(d) d.binder.name.is-in-wrong-namespace) then
        val x = cont()
        ([], x)
      else
        val sd = infer-effect/scope-depth
        val (gamma, infgamma, defs) = create-gammas(topLevel, sd, [], [], defs0)
        val (coreDefsX, assumed) =
          with extend-gamma(False, gamma)
          with extend-inf-gamma-ex(topLevel, [], infgamma)
          val assumed = defs.map(fn(d) lookup-inf-name(d.binder.name))
          val coreDefs0 = defs.map(fn(d) infer-def(topLevel, Instantiated, d))
          val coreDefs1 = coreDefs0.map(fn(cd) fix-canonical-name(True, cd))
          (coreDefs1, assumed)
        // re-analyze the mutual recursive groups
        val scoreDefsX = coreDefsX.map(fn(cd) def/substitute(get-subst(), cd))
        val coreGroups0 = regroup(scoreDefsX)
        if topLevel then coreGroups0.foreach(check-rec-val)
        // analyze divergence
        val analyzed = coreGroups0.map fn(cgroup)
          match cgroup
            core/core/DefRec(cdefs) ->
              if analyze-divergence(cdefs) then
                val cdefs' = cdefs.map(add-divergent-effect)
                (core/core/DefRec(cdefs'), cdefs'.map(defTName))
              else (cgroup, [])
            _ -> (cgroup, [])
        val (coreGroups1, divTNamess) = analyzed.unzip
        val divTNames = divTNamess.concat
        // check assumed types against inferred types
        val coreMap = defs.zip(assumed)
        fun lookup-orig(cdef: core/core/def): _ (syntax/syntax/def<ktype>, maybe<(name, ktype)>)
          match coreMap.find(fn((d, _)) d.binder.name == cdef.def-name.unqualify || d.binder.name == cdef.def-name)
            Just(r) -> r
            Nothing -> failure/fail("type/infer/infer-def-group: cannot find original definition for " ++ cdef.def-name.show)
        val coreGroups2 = coreGroups1.map fn(cgroup)
          match cgroup
            core/core/DefRec(cdefs) -> core/core/DefRec(cdefs.map(fn(cd) infer-rec-def2(topLevel, cd, divTNames.any(fn(tn) tn == cd.defTName), lookup-orig(cd))))
            core/core/DefNonRec(cd) -> core/core/DefNonRec(infer-rec-def2(topLevel, cd, divTNames.any(fn(tn) tn == cd.defTName), lookup-orig(cd)))
        // add range info (for documentation)
        fun group-defs(cgroup: core/core/def-group): list<core/core/def>
          match cgroup
            core/core/DefRec(cdefs) -> cdefs
            core/core/DefNonRec(cd) -> [cd]
        coreGroups2.foreach fn(cgroup)
          cgroup.group-defs.foreach(fn(cd) add-range-info-core-def(topLevel, infer-env.contxt, lookup-orig(cd).fst, cd))
        // fix local info in the core
        val sub = coreGroups2.map(group-defs).concat.map fn(cdef)
          val tname = cdef.defTName
          val nameInfo = create-name-infoX(Public, cdef.def-name, sd, cdef.sort, cdef.nameRange, cdef.ktype, cdef.doc)
          (tname, core/core/Var(tname, nameInfo.core-var-info))
        val coreGroups3 = coreGroups2.map(fn(cg) sub.dg/(|->)(cg))
        val x = (if topLevel then extend-gamma-core(True, coreGroups3, cont) else extend-inf-gamma-core(False, coreGroups3, cont))
        (coreGroups3, x)

// split annotated toplevel definitions into gamma, others into infgamma with assumed types
// also annotates unannotated definitions with their assumed type
fun infer-handler(propagated: maybe<(ktype, range)>, expect: expect, handlerSort: handler-sort, 
                  handlerScoped: handler-scope, allowMask: bool, mbeff: maybe<keffect>, 
                  localPars: list<value-binder<maybe<ktype>, ()>>, 
                  initially: maybe<(syntax/syntax/expr<ktype>)>, ret: maybe<(syntax/syntax/expr<ktype>)>, 
                  finally: maybe<(syntax/syntax/expr<ktype>)>, branches: list<handler-branch<ktype>>, hrng: range, rng: range): _ (ktype, keffect, core/core/expr)
  // Regular handler
  match localPars
    Cons -> 
      context-error(hrng, rng, "text \"Type.Infer.inferHandler: TODO: not supporting local parameters\"".text, [])
      failure/fail("abort")
    Nil -> 
      // get the handled effect
      val heff = infer-handled-effect(hrng, handlerSort, mbeff, branches)
      val isInstance = handlerSort.is-handlerInstance
      val effectName = heff.effect-name-from-label
      val handlerConName = effectName.to-handler-con-name
      check-coverage(rng, heff, handlerConName, branches)
      // find the result type of the return clause (if given) to propagate the operation types
      val res = match (propagated, ret)
        (Nothing, Just(rexpr)) ->
          val (rtp, _, _) = expr/infer(propagated, Instantiated, rexpr)
          match rtp.split-fun-scheme
            Just((_, _, _, retTp)) -> retTp
            _ -> fresh-star()
        (Just((retTp, _)), _) -> retTp
        _ -> fresh-star()
      val eff = operations/fresh-effect()
      val resumeArgs = branches.map(fn(_) fresh-star()) // TODO: get operation result types to improve inference
      // create expressions for each clause
      fun lt-op(b1: handler-branch<ktype>, b2: handler-branch<ktype>): bool
        b1.branchName.unqualify.show < b2.branchName.unqualify.show
      fun clause((HandlerBranch(opName, pars, body, opSort, nameRng, patRng), resumeArg): (handler-branch<ktype>, ktype)): _ (maybe<(name, range)>, syntax/syntax/expr<ktype>)
        with with-scope
        val (clauseName, cparams) = match opSort
          OpVal -> (name-clause("tail", pars.length), pars)
          OpFun -> (name-clause("tail", pars.length), pars)
          OpExcept -> (name-clause("never", pars.length), pars)
          OpControl ->
            val resumeTp = TFun([(nil, resumeArg)], eff, res)
            (name-clause("control", pars.length),
             pars ++ [ValueBinder("resume".new-name, Just(resumeTp), (), nameRng.hide, nameRng)])
          OpControlRaw ->
            val eff0 = effect-extend(heff, eff)
            val resumeContextTp = type-resume-context(resumeArg, eff, eff0, res)
            (name-clause("control-raw", pars.length),
             pars ++ [ValueBinder("rcontext".new-name, Just(resumeContextTp), (), hrng.hide, patRng)])
          OpControlErr ->
            failure/fail("type/infer/infer-handler: using a bare operation is deprecated.\n  hint: start with 'val', 'fun', 'brk', or 'ctl' instead.")
        val qopname = if opName.is-qualified then opName else qualify(effectName.qualifier, opName)
        val (_, gtp, _) = resolve-fun-name(qopname, CtxFunArgs(False, pars.length + (if isInstance then 1 else 0), [], Nothing), patRng, nameRng)
        val (_, tp, _) = instantiate-ex(gtp, nameRng)
        val parTps = match tp.split-fun-type
          Just((tpars0, _, _)) ->
            val tpars1 = if isInstance then tpars0.drop(1) else tpars0 // drop the instance name parameter
            tpars1.map(fn((_, t)) Just(t)) ++ cparams.map(fn(_) Nothing) // pad with Nothing
          _ -> failure/fail("type/infer/infer-handler: bad operation type: " ++ opName.show)
        val cparamsx = cparams.zip(parTps).map fn((b, mbtp))
          match b
            ValueBinder(bname, Nothing, _, bnameRng, brng) -> ValueBinder(bname, mbtp, Nothing, bnameRng, brng)
            ValueBinder(bname, annTp, _, bnameRng, brng) -> ValueBinder(bname, annTp, Nothing, bnameRng, brng)
        val frng = nameRng.combine(body.range)
        val cname = match opSort
          OpVal -> opName.from-value-operation-name
          _ -> opName
        val opPrefix = match opSort
          OpVal -> "val"
          OpFun -> "fun"
          OpExcept -> "final ctl"
          OpControl -> "ctl"
          _ -> "raw ctl"
        val capp = App(Var(clauseName, False, hrng.hide),
                       [(Nothing, Parens(Lam(cparamsx, body, False, body.range), cname, opPrefix, nameRng))], frng)
        (Nothing, capp)
      val clauses = branches.sort(?(<) = lt-op).zip(resumeArgs).map(clause)
      val grng = range/null
      // control-flow-context of the handler: 0 = none, 1 = linear, 2 = at most once, 3 = multi
      fun cfc-lub(x: int, y: int): int
        if (x == 0 && y == 1) || (x == 1 && y == 0) then 2 else max(x, y)
      fun hbranch-cfc(b: handler-branch<ktype>): int
        match b.branchSort // todo: more refined analysis
          OpVal -> 1
          OpFun -> 1
          OpExcept -> 0
          _ -> 3 // multi/wild
      val handlerCfc = match branches.map(hbranch-cfc)
        Nil -> 1 // linear
        Cons(c, cs) -> cs.foldl(c, cfc-lub)
      val handlerCon = App(Var(handlerConName, False, hrng),
                           Cons((Nothing, Literal(syntax/syntax/LitInt(handlerCfc, grng))), clauses), rng)
      val actionName = "action".new-hidden-name
      val handleName = effectName.to-handle-name
      val handleRet = match ret // todo: optimize return by using maybe<a->b> value in case no clause was given?
        Nothing ->
          val argName = "res".new-hidden-name
          Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], Var(argName, False, rng), False, hrng) // don't pass `id` as it needs to be opened
        Just(rexpr) -> rexpr
      fun handle-expr(action: syntax/syntax/expr<ktype>): syntax/syntax/expr<ktype>
        App(Var(handleName, False, rng),
            [(Nothing, handlerCon), (Nothing, handleRet), (Nothing, action)], hrng)
      val (_, handleTp, _) = resolve-fun-name(handleName, CtxNone, rng, rng)
      val (_, handleRho, _) = instantiate-ex(handleTp, rng)
      val actionTp = match handleRho.split-fun-type
        Just(([_, _, actionTp0], _, _)) -> actionTp0.snd.subst
        _ -> failure/fail("type/infer/infer-handler: unexpected handler type")
      val handlerExpr = Parens(Lam([ValueBinder(actionName, Just(actionTp), Nothing, rng, rng)],
                                   handle-expr(Var(actionName, False, rng)), False, hrng), "handler".new-name, "expr", rng)
      val hres = expr/infer(propagated, expect, handlerExpr)
      val htp = hres.fst.subst
      val heffect = match htp.split-fun-scheme
        Just((_, [_], heff2, _)) -> heff2
        _ -> failure/fail("type/infer/infer-handler: unexpected inferred handler type")
      if heff.label-is-linear then check-linearity(effectName, heffect, branches, hrng, rng) else ()
      hres

// inferHandler :: Maybe (Type,Range) -> Expect -> HandlerSort -> HandlerScope -> Bool
//                       -> Maybe Effect
//                       -> [ValueBinder (Maybe Type) ()] -> Maybe (Expr Type) -> Maybe (Expr Type) -> Maybe (Expr Type)
//                       -> [HandlerBranch Type] -> Range -> Range -> Inf (Type,Effect,Core.Expr)
// -- Regular handler
// inferHandler propagated expect handlerSort handlerScoped allowMask
//              mbEffect (_:localPars) initially ret finally branches hrng rng
//   = do contextError hrng rng (text "Type.Infer.inferHandler: TODO: not supporting local parameters") []
//        failure "abort"
// inferHandler propagated expect handlerSort handlerScoped allowMask
//              mbEffect [] initially ret finally branches hrng rng
//   = do -- get the handled effect
//        heff <- inferHandledEffect hrng handlerSort mbEffect branches
//        let isInstance = isHandlerInstance handlerSort
//            effectName = effectNameFromLabel heff
//            handlerConName = toHandlerConName effectName
//        -- check operations
//        checkCoverage rng heff handlerConName branches

//        -- infer the result type to improve inference
//        res  <- case (propagated,ret) of
//                 (Nothing,Just expr) -> do (tp,_,_) <- inferExpr propagated Instantiated expr
//                                           case splitFunScheme tp of
//                                             Just (_,_,_,retTp) -> return retTp
//                                             _ -> Op.freshStar
//                 (Just (retTp,_),_) -> return retTp
//                 _ -> Op.freshStar
//        eff  <- Op.freshEffect
//        resumeArgs <- mapM (\_ -> Op.freshStar) branches  -- TODO: get operation result types to improve inference

//        -- construct the handler
//        let -- create expressions for each clause
//            opName b1 b2 = compare (show (unqualify (hbranchName b1))) (show (unqualify (hbranchName b2)))
//            clause (HandlerBranch opName pars body opSort nameRng patRng, resumeArg)
//             = withScope $
//               do (clauseName, cparams, prefix) <- case opSort of
//                           OpVal        -> return (nameClause "tail" (length pars), pars, "val")
//                           OpFun        -> return (nameClause "tail" (length pars), pars, "fun")
//                           OpExcept     -> return (nameClause "never" (length pars), pars, "final ctl")
//                           -- don't optimize ctl to exc since exc runs the finalizers before the clause (unlike ctl)
//                           -- OpControl    | not (hasFreeVar body (newName "resume"))
//                           --             -> (nameClause "never" (length pars), pars)  -- except
//                           OpControl    -> do let resumeTp = TFun [(nameNil,resumeArg)] eff res
//                                                  resumeDoc shorten = if shorten then text "resume" else empty
//                                              addRangeInfo nameRng (RM.Implicits resumeDoc)
//                                              return (nameClause "control" (length pars),
//                                                      pars ++ [ValueBinder (newName "resume") (Just resumeTp) () (rangeHide nameRng) nameRng],
//                                                      "ctl")
//                           OpControlRaw -> do let eff0 = effectExtend heff eff
//                                                  resumeContextTp = typeResumeContext resumeArg eff eff0 res
//                                                  resumeDoc shorten = if shorten then text "rcontext" else empty
//                                              addRangeInfo nameRng (RM.Implicits resumeDoc)
//                                              return (nameClause "control-raw" (length pars),
//                                                      pars ++ [ValueBinder (newName "rcontext") (Just resumeContextTp) () (rangeHide hrng) patRng],
//                                                      "raw ctl")
//                           OpControlErr -> failure "Type.Infer.inferHandler: using a bare operation is deprecated.\n  hint: start with 'val', 'fun', 'brk', or 'ctl' instead."
//                           -- _            -> failure $ "Type.Infer.inferHandler: unexpected resume kind: " ++ show rkind

//                  let qopname = if isQualified opName then opName else qualify (qualifier effectName) opName
//                  (_,gtp,_) <- resolveFunName qopname (CtxFunArgs False (length pars + (if isInstance then 1 else 0)) [] Nothing) patRng nameRng -- todo: resolve more specific with known types?
//                  (tp,_,_)  <- instantiateEx nameRng gtp
//                  let parTps = case splitFunType tp of
//                                 Just (tpars,_,_) -> (if (isInstance) then tail else id) $ -- drop the first parameter of an op for an instance (as it is the instance name)
//                                                     map (Just . snd) tpars ++ repeat Nothing  -- TODO: propagate result type as well?
//                                 _ -> failure $ "Type.Infer.inferHandler: bad operation type: " ++ show opName ++ ": " ++ show (pretty gtp)
//                      cparamsx = map (\(b,mbtp) -> case b of
//                                                     ValueBinder name Nothing _ nameRng rng -> ValueBinder name mbtp Nothing nameRng rng
//                                                     ValueBinder name annTp _ nameRng rng   -> ValueBinder name annTp Nothing nameRng rng)
//                                 $ zip (cparams :: [ValueBinder (Maybe Type) ()]) (parTps)
//                      frng = combineRanged nameRng body
//                      cname = case opSort of
//                                OpVal -> fromValueOperationsName opName
//                                _     -> opName
//                      capp  = App (Var clauseName False (rangeHide hrng))
//                                  [(Nothing,Parens (Lam cparamsx body False (getRange body)) cname prefix nameRng)] frng
//                  -- addRangeInfo nameRng (RM.Id cname (RM.NIValue "fun" gtp "" False) [] False)
//                  return (Nothing, capp)

//        clauses <- mapM clause (zip (sortBy opName branches) resumeArgs)

//        let grng = rangeNull
//        let handlerCon = let hcon = Var handlerConName False hrng
//                         in App hcon ([(Nothing,Lit (LitInt handlerCfc grng))] ++ clauses) rng
//            handlerCfc = -- (\i -> App (Var nameInternalInt32 False grng) [(Nothing,Lit (LitInt i grng))] grng) $
//                         if (null branches) then 1 --linear
//                                            else foldr1 cfcLub (map hbranchCfc branches)
//                       where
//                         cfcLub x y   = if ((x==0&&y==1)||(x==1&&y==0)) then 2 else max x y
//                         hbranchCfc b = case hbranchSort b of -- todo: more refined analysis
//                                         OpVal    -> 1
//                                         OpFun    -> 1
//                                         OpExcept -> 0
//                                         _        -> 3 --multi/wild
//            -- create handler expression
//            actionName = newHiddenName "action"
//            handleName = toHandleName effectName
//            handleRet  = case ret of -- todo: optimize return by using maybe<a->b> value in case no clause was given?
//                           Nothing -> let argName = (newHiddenName "res")
//                                      in Lam [ValueBinder argName Nothing Nothing rng rng] (Var argName False rng) False hrng -- don't pass `id` as it needs to be opened
//                           Just expr -> expr
//            handleExpr action = App (Var handleName False rng)
//                                 [{-(Nothing,handlerCfc),-}(Nothing,handlerCon),(Nothing,handleRet),(Nothing,action)] hrng



//        -- extract the action type for the case where it is higher-ranked (for scoped effects)
//        -- this way we can annotate the action parameter with a higher-rank type if needed
//        -- so it is propagated automatically.
//        penv <- getPrettyEnv
//        (_,handleTp,_)  <- resolveFunName handleName CtxNone rng rng
//        (handleRho,_,_) <- instantiateEx rng handleTp
//        actionTp <- case splitFunType handleRho of
//                         Just ([_,_,actionTp],_,_)
//                           -> subst (snd actionTp)
//                         _ -> failure ("Type.Infer: unexpected handler type: " ++ show (ppType penv handleRho))
//        let handlerExpr = Parens (Lam [ValueBinder actionName (Just actionTp) Nothing rng rng]
//                                      (handleExpr (Var actionName False rng)) False hrng) (newName "handler") "expr" rng

//        -- and check the handle expression
//        hres@(xhtp,_,_) <- inferExpr propagated expect handlerExpr
//        htp <- subst xhtp

//        -- extract handler effect
//        let (actionTp1,heffect) = case splitFunScheme(htp) of
//                         Just (_,[arg],heff,hresTp) -> (snd arg,heff)
//                         _ -> failure $ "Type.Infer.inferHandler: unexpected handler type: " ++ show (ppType penv htp)

//        if (not (labelIsLinear heff))
//         then return ()
//         else checkLinearity effectName heffect branches hrng rng

//        -- insert a mask<local> over the action?
//        if True -- (not (containsLocalEffect heffect) || not allowMask)
//          then return hres
//          else do
//                  hp <- Op.freshTVar kindHeap Meta
//                  let actionTp2  = removeLocalEffect penv actionTp1
//                      handlerExprMask
//                         = if isInstance
//                            then let instName   = newHiddenName "hname"
//                                 in Lam [ValueBinder actionName (Just actionTp2) Nothing rng rng]
//                                     (handleExpr (Lam [ValueBinder instName Nothing Nothing rng rng]
//                                                    (Inject (TApp typeLocal [hp])
//                                                       (Lam [] (App (Var actionName False rng) [(Nothing,Var instName False rng)] rng) False rng)
//                                                       False hrng) False hrng)) False hrng
//                            else Lam [ValueBinder actionName (Just actionTp2) Nothing rng rng]
//                                   (handleExpr (Lam [] (Inject (TApp typeLocal [hp]) (Var actionName False rng) False hrng) False hrng)) False hrng
//                  inferExpr propagated expect handlerExprMask  -- and re-infer :-)



fun infer-app-fun-first(propagated: maybe<(ktype, range)>, prop, fexpr, fresolved, fixed0, named0, implicits0: list<((name, range), syntax/syntax/expr<ktype>, bool -> _ doc)>, rng, origFun: syntax/syntax/expr<_>, expect)
  with maybe-instantiate-or-generalize(rng, origFun.range, expect)
  // infer type of function
  val fprop = match (prop, fexpr)
    (Nothing, syntax/syntax/Var(name)) | !name.is-constructor-name ->
      val (_, ptp, info) = resolve-name(name, prop, rng)
      match (ptp, info.allow-implicit-mask)
        (TVar(), True) -> 
          // we propagate a function type (for example to mask<local> for function parameters)
          val teff = operations/fresh-effect()
          val tres = fresh-star() 
          val tpars = list(1, fixed0.list/length + named0.list/length + implicits0.list/length).map(fn(_) fresh-star())
          val ftp = TFun(tpars.map((nil, _)), teff, tres)
          Just((ftp, rng))
        _ -> prop
    _ -> prop
  val (ftp, eff1, fcore) = 
    with no-allow-return
    infer(fprop, Instantiated, fexpr)
  // we allow passing implicit parameters as a fixed argument: here we name those explicitly based on the type
  // todo: for now disallow implicit parameters as fixed ones as it can lead to long inference times?
  val allow-implicits-as-fixed = True
  val (fixed, named1) =  
    match ftp.split-fun-type
      Just((pars, _, _)) | allow-implicits-as-fixed -> 
        val (tfixed, toptionals, timplicits) = split-optional-implicit(pars)
        val (fixed1, fixed-implicit-args) = fixed0.split(tfixed.length + toptionals.length)
        if fixed-implicit-args.is-empty || fixed-implicit-args.length > timplicits.length then // too many arguments? see `test/static/wrong/rec1`
          (fixed0, named0)
        else 
          val fixed-implicits = timplicits.zipwith(fixed-implicit-args, fn((name, _), expr: syntax/syntax/expr<_>) ((name, expr.range), expr))
          (fixed1, fixed-implicits ++ named0)
      _ -> (fixed0, named0)
  // only add resolved implicits that were not already named
  val already-given = named1.map(_.fst.fst)
  val rimplicits = implicits0.filter(fn(((name,_), _, _)) !already-given.contains(name))
  val named' = named1 ++ rimplicits.map(fn(((name, _), expr, _)) ((name, range/null), expr)) // so no range info is emitted when checking 
  rimplicits.foreach fn((_, _, doc)) 
    add-range-info(fexpr.range, RIImplicits(doc))
  
  // match the type with a function type, wrap optional arguments, and order named arguments
  val FunMatchTypeArgs(iargs, pars0, fun-eff0, fun-tp0, core-app) = match-fun-type-args(rng, fexpr, ftp, fresolved, fixed, named')
  
  // match propagated type with the function result type
  // note: we may disable this in the future?
  val (pars, fun-eff, fun-tp) = 
    match propagated
      Just((pres, prng)) -> 
        val _ = 
          with val ctxt = checkAnn(prng)
          infer-subsume(rng, fun-tp0, pres)
        (pars0.subst, fun-eff0.subst, fun-tp0.subst)
      Nothing -> (pars0, fun-eff0, fun-tp0)
  
  // infer the argument expressions and subsume the type
  val sftp = ftp.subst
  val unused = fresh-name("unused")
  val sd = infer-effect/scope-depth
  val (eff-args, core-args) = 
    with extend-inf-gamma([(unused, InfoVal(Public, unused, sftp, sd, rng, False, False, ""))]) // don't generalize over free propagated types
    val free = free-in-gamma() 
    val par-args = pars.map(snd).zip(iargs.map(snd))
    match origFun
      Var(name, _, _) | name == nameRunLocal -> 
        with with-local-scope
        with val ctxt = checkLocalScope(rng)
        infer-argsN(rng, par-args)
      _ ->
        // upstream: `inferArgsN (Infer rng) rng parArgs` -- the app range is
        // the error context for argument subsumption (not the ambient ctxt)
        with val ctxt = Infer(rng)
        infer-argsN(rng, par-args)
  
  // ensure arguments are evaluated in the declaration order
  val core = 
    match short-circuit(fcore, core-args)
      Just(c) -> c
      Nothing -> 
        // ensure named arguments are evaluated in the correct order
        if iargs.map(fst).monotonic || core-args.all(is-total) then 
          core-app(fcore, core-args)
        else 
          // let bind in evaluation order
          val vars = iargs.map(fn(_) unique-name("arg"))
          val vargs = zip(vars, core-args.zipwith(iargs, fn(carg, (i, _)) (i, carg)))
          val eargs: list<(name,(int,core/core/expr))> = vargs.sort(fn((_: name, (i: int, _)), (_: name, (j: int, _))) i < j)
          val defs = eargs.map fn((v, (_, arg)))
            DefNonRec(Def(v, arg.type-of, arg, Private, DefVal, InlineAuto, null, ""))
          val cargs = vargs.map fn((v, (_, arg)))
            Var(TName(v, arg.type-of), InfoNone)
          if fcore.is-total then 
            make-let(defs, core-app(fcore, cargs))
          else
            val fname = "fct".unique-name
            val fdef = DefNonRec(Def(fname, ftp, fcore, Private, DefFun([]) /* all own, TODO: maintain borrow annotations? */, InlineAuto, null, ""))
            val fvar = Var(TName(fname, ftp), InfoNone)
            Let(Cons(fdef, defs), core-app(fvar, cargs))
  
  // take top effect
  // todo: sub effecting should add core terms
  val top-eff = 
    with val ctxt = checkEffect(rng)
    infer-unifies(Cons((origFun.range, eff1), zip(iargs.map(_.snd.range), eff-args)))
  val _ = 
    with val ctxt = checkEffectSubsume(rng)
    // upstream passes `getRange fun` (the FUNCTION subexpression) as the
    // unify range, so error output's `term:` line shows just the function
    // (e.g. `get()`), not the whole application (`get()(i)`)
    infer-unify(origFun.range, fun-eff, top-eff)
  
  // instantiate or generalize result type
  (fun-tp.subst, top-eff.subst, core)

// inferAppFirst <guessed fixed arg types> <priority order fixed args> <fixed args> <named args>
fun infer-app-args-first(fresolved, funExpr, args, fixed, named0, rng, expect, prop)
  match args
    Nil -> // we inferred all fixed arguments
      // this always fails since we have not been able to resolve the function name
      infer-app-fun-first(prop, Nothing, funExpr, fresolved, fixed, named0, [], rng, funExpr, expect)
    Cons((idx,fix: syntax/syntax/expr<_>), fixs) -> 
      // try to improve our guess
      val (tp-arg, eff-arg, core-arg) = 
        with no-allow-return 
        infer(Nothing, Instantiated, fix)
      val fresolved' = fresolved ++ [(idx, (fix.range, tp-arg, eff-arg, core-arg))]
      val amb = 
        match funExpr.root-expr
          Var(name, _, name-range) ->
            val sctx = fixed-context(prop, fresolved', fixed.length, named0.map(_.fst.fst))
            match lookup-app-name(fixs.is-empty /* allow disambiguate */, name, sctx, rng, name-range)
              Right((itp, fexpr, implicits: list<((name,range), syntax/syntax/expr<ktype>, bool -> pretty-eff doc)>)) -> Just(((itp,rng), fexpr, implicits))
              Left() -> Nothing
          _ -> Nothing
      match amb
        Just((prop-tp, fexpr, implicits)) -> infer-app-fun-first(prop, Just(prop-tp), fexpr, fresolved', fixed, named0, implicits, rng, funExpr, expect) 
        Nothing -> infer-app-args-first(fresolved', funExpr, fixs, fixed, named0, rng, expect, prop)
  
fun infer-app(prop: maybe<(ktype, range)>, expect: expect, funExpr: syntax/syntax/expr<ktype>, nargs: list<(maybe<(name,range)>, syntax/syntax/expr<ktype>)>, rng: range): _ (ktype, keffect, core/core/expr)
  // we cannot resolve an overloaded function name: infer types of arguments without propagation first.
  // The code handles inferring arguments in any order by keeping track of the index, but at the moment
  // we always infer from left to right until we can resolve the function type and then propagate argument types. 
  fun infer-app-from-args(fixed, named0)
    match fixed
      Nil -> 
        // there are no fixed arguments, use fun first anyways (and error..)
        infer-app-fun-first(prop, Nothing, funExpr, [], [], named0, [], rng, funExpr, expect)
      _ -> infer-app-args-first([], funExpr, fixed.indexed, fixed, named0, rng, expect, prop)

  val (fixed, named-args) = nargs.split-named-args
  val amb = 
    match funExpr.root-expr
      Var(name, _, name-range) ->
        val sctx = fixed-count-context(prop, fixed.length, named-args.map(_.fst.fst))
        match lookup-app-name(False, name, sctx, rng, name-range)
          Right((tp, fexpr, implicits)) -> Just((Just((tp, rng)), fexpr, implicits)) // known type, propagate the function type into the parameters
          Left(_) -> Nothing // many matches, start with argument inference and try to resolve the function type
          // Note: lookup-app-name never unifies type variables so we should not emit errors on `Left()`
          // for example in `fn(f) f()` the `f` has a type `_a` and will not match `sctx`
      _ -> Just((Nothing, funExpr, [])) // Function expression first
  match amb
    Just((prop-tp, fexpr, implicits)) -> infer-app-fun-first(prop, prop-tp, fexpr, [], fixed, named-args, implicits, rng, funExpr, expect)
    _ -> infer-app-from-args(fixed, named-args)

//////////////////////////////////////////
// Infer Lambda
//////////////////////////////////////////

fun infer-lam(top: bool, prop: maybe<(ktype, range)>, expect: expect, bindersl: list<value-binder<maybe<ktype>, maybe<syntax/syntax/expr<ktype>>>>, body0: syntax/syntax/expr<ktype>, rng: range)
  with is-named <- is-named-lam
  with with-scope
  with disallow-hole
  fun inf-body()
    val FunMatchResult(prop-args, prop-eff, prop-body, skolems, expect-body) = match-fun(bindersl.length, prop)
    // fill in propagated parameter types FIRST so implicit-parameter unpacking
    // (`.?name : tp`) can find the struct via the parameter's type
    val bindersP = bindersl.zipwith(prop-args) fn(binder, mb-prop)
      match binder.binderType
        Nothing -> ValueBinder(binder.name, mb-prop.map(snd), binder.expr, binder.name-range, binder.range)
        Just(_) -> binder
    val (binders0, unpack-implicitss) = bindersP.map(infer-implicit-param).unzip
    val body = unpack-implicitss.foldr(body0, fn(f, x) f(x))
    val binders1 = binders0.map(instantiate-binder)
    val eff = 
      match prop-eff
        Nothing -> operations/fresh-effect() 
        Just((eff, _)) -> eff
    val ldepth = infer-effect/local-depth
    val (infgamma, sub, defs) = infer-optionals(ldepth == 0, eff, [], binders1)
    fun coref(c) make-let(defs.map(DefNonRec), sub |-> c)
    val return-tp = 
      match prop-body
        Nothing -> fresh-star()
        Just((tp, _)) -> tp
    // nice names for eta-expanded expressions for in the IDE 
    val eta-expanded = !binders0.is-empty && binders0.all(_.name.hidden/starts-with("eta"))
    fun create-eta(name: name, n: int) 
      match "xyz".list.drop(n)
        Cons(c, _) -> c.char
        Nil -> pretty(n+1)
    fun nice-eta(act)
      if eta-expanded then
        with docs <- with-nice-names(create-eta, binders0.map(name))
        add-range-info(make-range(rng.start, rng.start), RIInlayHint(False /* append before */, "fn".text |.| parens(docs.map("_".text |.| _).intersperse(comma).hcat) |.| " ".text))
        act()
      else act()
    val (tp, eff1, core) = 
      // (perf) no trace-indent handler in the hot path -- see infer-effect.kk note
      with with-scope
      with extend-inf-gamma(infgamma)
      with extend-inf-gamma([(nameReturn, create-name-infoX(Public, nameReturn, ldepth, DefVal, body.range, return-tp, ""))])
      with nice-eta
      if is-named then infer-isolated(rng, body.range, body, {expr/infer(prop-body, expect-body, body)})
      else infer(prop-body, expect-body, body)
    val _ = 
      with val ctxt = checkReturnResult(rng)
      infer-unify(body.range, return-tp, tp)
    val _ = 
      with val ctxt = Infer(rng)
      infer-unify(body.range, eff, eff1)
    val top-eff = 
      match prop-eff
        Nothing -> eff.subst
        Just((top-eff, r)) -> 
          val _ = 
            with val ctxt = checkEffectSubsume(rng)
            infer-unify(r, eff, top-eff)
          top-eff.subst
    val opt-pars = binders1.map(fn(b) (b.name, b.binderType.subst))
    val body-core1 = add-lambdas(opt-pars, top-eff, Lam([], top-eff, coref(core)))
    val body-core2 = body-core1.subst
    val pars = opt-pars
    val sftp0 = TFun(pars, top-eff, tp).subst
    // check skolem escape (should this be after generalize?)
    if !top then 
      check-skolem-escape(rng, sftp0, Nothing, skolems, tvs/empty) // TODO: not having this check improves error messages but is it really safe?
    
    // substitute back skolems to meta variables
    val (_sktvars, sksubs) = fresh-sub(Meta, skolems)
    val sftp1 = sksubs |-> sftp0
    val body-core3 = sksubs |-> body-core2
    subst-iconstraints(sksubs)

    // check for polymorphic parameters
    val unannot-binders = binders0.zip(binders1).filter(fn((b0, _)) b0.binderType.is-nothing).map fn((_, b1))
      b1(binderType = b1.binderType.subst)
    val poly-binders = unannot-binders.filter(fn(b) !b.binderType.is-tau)
    match poly-binders
      Cons(b) ->
        type-error(rng, b.range, "unannotated parameters cannot be polymorphic".text, b.binderType, [("hint".text, "annotate the parameter with a polymorphic type".text)])
      Nil -> ()

    // add range info for each parameter
    if !eta-expanded then
      val par-types2 = binders1.map(fn(b) b.binderType.subst)
      val _ = binders0.zipwith(par-types2) fn(binder, tp)
        val annotated =
          match (prop, binder.binderType)
            (Just((_, prng)), Just(_)) | prng.hidden -> True // there was an actual annotation
            _ -> False
        add-range-info(binder.name-range, RIId(binder.name, NIValue("val", tp, "", annotated), [], True))
      ()
    (sftp1, typeTotal, body-core3)
  val (ftp, _, fcore) = maybe-generalize(rng, body0.range, expect, inf-body)
  val eff = operations/fresh-effect()
  (ftp, eff, fcore)

//////////////////////////////////////////
// Infer Variables
//////////////////////////////////////////

fun infer-var(prop: maybe<(ktype, range)>, expect, name, rng, is-rhs)
  if name.is-constructor-name then 
    // constructor
    val (qname1, tp1, con-repr, con-info) = resolve-con-name(name, prop.map(tuple2/fst), rng)
    val info1 = InfoCon(Public, tp1, con-repr, con-info, rng, con-info.doc)
    val (qname, tp, info) = 
      val def-name: name = current-def-name()
      val creator-name: name = qname1.new-creator-name
      if def-name != creator-name.unqualify && def-name != nameCopy then 
        // a bit hacky, but ensure we don't call the creator function inside itself or the copy function
        match lookup-fun-name(creator-name, prop, rng)
          Just((qname', tp', info')) -> (qname', tp', info')
          Nothing -> (qname1, tp1, info1)
      else (qname1, tp1, info1)
    val core-var = info.core-expr(qname)
    add-range-info(rng, RIId(info1.canonical-name(qname1), NICon(tp, info1.doc), [], False))
    val (itp, coref) = maybe-instantiate(rng, expect, tp)
    (itp, fresh-effect(), coref(core-var))
  else 
    // variable
    // we cannot directly "resolveName" with a propagated type
    // as sometimes the types do not match and need to coerce due to local variables or references on the right-hand-side
    val vinfo =
      match prop
        Just(p) | is-rhs -> resolve-rhs-name(name, p, rng)
        _ -> resolve-name(name, prop, rng)
    infer-var-name(prop, expect, name, rng, is-rhs, vinfo)

fun infer-var-name(prop: maybe<(ktype, range)>, expect, name: name, rng: range, is-rhs: bool, (qname: name, tp: ktype, info: assumption/name-info))
  if tp.is-type-local-var && is-rhs then 
    val irng = rng.range/extend(-1)
    val (tp1, eff1, core1) = expr/infer(prop, expect, Parens(App(Var(nameLocalGet, False, irng), [(Nothing, App(Var(nameByref, False, irng), [(Nothing, Var(name, False, irng))], irng))], irng), name, "var", rng))
    add-range-info(rng, RIId(qname, NIValue(info.sort, tp1, info.doc, False), [], False))
    (tp1, eff1, core1)
  else 
    match info
      InfoVal(isVar=isVar) | isVar && is-rhs -> // is it a right hand side variable?
        val (tp1, eff1, core1) = expr/infer(prop, expect, App(Var(nameDeref, False, rng), [(Nothing, App(Var(nameByref, False, rng), [(Nothing, Var(name, False, rng))], rng))], rng))
        add-range-info(rng, RIId(qname, NIValue(info.sort, tp1, info.doc, False), [], False))
        (tp1, eff1, core1)
      InfoVal() | tp.is-value-operation ->
        add-range-info(rng, RIId(qname, NIValue(info.sort, tp, info.doc, False), [], False))
        expr/infer(prop, expect, App(Var(qname.to-value-operation-name, False, null), [], null))
      _ -> 
        val eff = fresh-effect()
        match compilation-constants.lookup(_ == qname)
          Just((tp', fcore)) -> (tp', eff, fcore(module-name(), rng))
          Nothing -> 
            val core-var = info.core-expr(qname)
            val fixed-effect = match tp.split-fun-scheme
              Just((_, _, eff', _)) -> eff'.is-effect-fixed
              _ -> False
            val (itp, coref) = maybe-instantiate(rng, expect, tp)
            val sitp = itp.subst
            val (rm-name, rm-doc) =
              if qname.hidden/starts-with("eta") then 
                match qname.lookup-nice-name
                  Nothing -> ()
                  Just(nice) -> add-range-info(rng.end-of-range, RIInlayHint(True, nice))
                (new-name("_"), "eta-expanded parameter")
              else (info.canonical-name(qname), info.doc)
            add-range-info(rng, RIId(rm-name, NIValue(info.sort, sitp, rm-doc, False), [], False))
            val depth = local-depth
            fun inject-local(n)
              val hp = fresh-tvar(kindHeap, Meta)
              val local-tp = TApp(typeLocal, [hp])
              val mask-expr = eta-expand(n, rng, fn(apply) Inject(local-tp, Lam([], apply(Var(qname, False, rng)), False, rng), False, rng))
              val (tp', eff', core) = 
                with with-no-local-scope
                expr/infer(Nothing /* do not propagate as the effect is different */, Instantiated, mask-expr)
              (tp', eff', core)
            match (itp.expand-syn, prop)
              (TFun(pars), _) | !fixed-effect && info.allow-implicit-mask && !qname.is-hidden-name && depth > 0 ->
                inject-local(pars.length)
              (_, Just((TFun(pars, _, _), _))) | !fixed-effect && info.allow-implicit-mask && !qname.is-hidden-name && depth > 0 -> 
                inject-local(pars.length)
              _ -> (sitp, eff, coref(core-var))

val compilation-constants = 
  [
   // for now, use the module name to not leak info of a dev system
   (nameCoreFileFile, (typeString, fn(mod, rng) ELit(LitString(mod.show-plain ++ ".kk")))), 
   (nameCoreFileLine, (typeInt, fn(mod, rng) ELit(LitInt(rng.start.line)))),
   (nameCoreFileModule, (typeString, fn(mod, rng) ELit(LitString(mod.show-plain))))
  ]

//////////////////////////////////////////
// infer match, branches and patterns
//////////////////////////////////////////


fun infer-case(prop: maybe<(ktype, range)>, expect: expect, expr: syntax/syntax/expr<ktype>, 
              branches: list<syntax/syntax/branch<ktype>>, is-lazy-match: bool, rng: range): infer-eff-full (ktype, keffect, core/core/expr)
  with maybe-instantiate-or-generalize(rng, branches.range, expect)
  val (ctp, ceff, ccore0) =
    with no-allow-return
    with disallow-hole
    infer(Nothing, Instantiated, expr)
  // infer branches
  val matched-names = expr.extract-matched-names
  val pat-kind = PatternOutermost(is-lazy-match)
  val bress = 
    with disallow-hole
    with with-scope
    match (prop, branches)
      (Nothing, Cons(b, bs)) -> // propagate the type of the first branch
        val (tpeffs, br) = infer-branch(pat-kind, prop, ctp, expr.range, matched-names, b)
        val tp = 
          match tpeffs
            Cons((tp, _), _) -> tp
            _ -> failure/fail("type/infer/infer-case: branch without guard")
        val bress = bs.map(infer-branch(pat-kind, Just((tp, b.range)), ctp, expr.range, matched-names, _))
        Cons((tpeffs, br), bress)
      _ -> branches.map(infer-branch(pat-kind, prop, ctp, expr.range, matched-names, _))
  val (tpeffss, bcores) = bress.unzip
  val (tps, effs) = unzip(tpeffss.concat)
  // ensure branches match 
  val rngs = branches.map(_.branchGuard.range)
  val brngs = branches.map(range)
  fun recur(tpsx: list<(ktype, (range, range))>)
    match tpsx
      // NOTE: the 2+-element case MUST come first -- `Cons((tp, _))` leaves the
      // tail as a wildcard and would match ANY non-empty list, silently skipping
      // the cross-branch unification entirely (this bug made `if c then x else y`
      // never unify x with y!)
      Cons((tp1, r), Cons((tp2, (ctx2, rng2)), tps')) ->
        val _ =
          with val ctxt = checkMatch(ctx2)
          infer-unify(rng2, tp1, tp2)
        recur(Cons((tp1,r), tps'))
      Cons((tp, _), Nil) -> tp.subst
      Nil -> failure/fail("type/infer/infer-case: no branches to unify")
  val res-tp = recur(zip(tps, zip(brngs, rngs)))
  val res-eff = fresh-effect()
  val _ = 
    with val ctxt = checkEffectSubsume(rng)
    Cons(expr.range, rngs).zipwith(Cons(ceff,effs)) fn(r, eff) 
      infer-unify(r, eff, res-eff)
  // check scrutinee type
  val stp = ctp.subst
  if stp.type-is-case-legal then ()
  else type-error(rng, expr.range, "can only match on literals or data types".text, stp, [])
  // get data info and analyze branches
  val data-info = stp.get-type-name.find-data-info
  val def-name = current-def-name()
  val sbcores : list<core/core/branch> = bcores.subst
  // TODO: Analysis match 
  val (is-total, cbranches) = branches/analyze(def-name, rng, sbcores, [stp], [data-info], is-lazy-match)
  val cbranches' = 
    if is-total then cbranches
    else 
      val mod-name = module-name()
      // upstream: `show moduleName ++ show rng` where Haskell's derived `Show
      // Range` is the TERSE `show p1` = "(line,col)" -- NOT the driver's full
      // path+line+col error-message format (range/show); using the wrong show
      // here breaks the uncaught-pattern-match-error message at runtime
      val lit-pos = Literal(syntax/syntax/LitString(mod-name.show ++ rng.start.pos/show, rng))
      val lit-def = Literal(syntax/syntax/LitString(def-name.show, rng))
      val exn-branch = Branch(PatWild(rng), [Guard(guardTrue, App(Var(namePatternMatchError, False, rng), [(Nothing, lit-pos), (Nothing, lit-def)], rng))])
      val cexn-branch = infer-branch(pat-kind, Just((res-tp, rng)), ctp, expr.range, matched-names, exn-branch)
      match cexn-branch 
        (Cons((_, eff)), cbranch) -> // already propagated
          with val ctxt = checkEffectSubsume(rng)
          infer-unify(rng, eff, res-eff)
          cbranches ++ [cbranch]
        _ -> failure/fail("type/infer/infer-case: should never, happen, cexn-branch always contains a guard")
  // add lazy force
  // todo: warning if lazy match on regular datatype?
  val ccore1 = 
    if !is-lazy-match && data-info.di/is-lazy then 
      val forceName = data-info.lazy-name("force")
      val (force, force-tp, force-info) = resolve-fun-name(forceName, CtxFunArgs(False, 1, [], Nothing), rng, expr.range)
      val cforce = force-info.core-expr(force)
      match ccore0
        core/core/App(Var(fname), [_]) | force == fname.get-name -> ccore0 // don't duplicate as force(force(expr)) -- this can happen in kind/infer where force is explicitly inserted sometimes
        _ -> 
          val (ftp, _, coref) = infer-effect/instantiate(force-tp, rng) 
          match ftp.split-fun-type
            Just((_, eff, rtp)) -> 
              val _ = 
                with val ctxt = Infer(rng)
                infer-unify(expr.range, ctp, rtp)
              val _ = 
                with val ctxt = checkEffectSubsume(rng)
                infer-unify(expr.range, eff, res-eff)
              App(coref(cforce), [ccore0])
    else ccore0
  val core = get-subst() |-> Case([ccore1], cbranches')
  val sres-eff = res-eff.subst
  (res-tp, sres-eff, core)  

fun infer-branch(pat-kind, prop, match-type, match-range, matched-names, branch): infer-eff-full (list<(ktype, keffect)>, core/core/branch)
  match branch
    syntax/syntax/Branch(pattern, guards) -> 
      infer-pattern(pat-kind, match-type, branch.range, pattern, fn(pcore, gcores: list<core/core/guard>) {
          if pattern.range != range/null then  
            // check for unused pattern bindings 
            val defined = pcore.pat/bound-vars
            val free = rb-set/from-list(gcores.free-vars.list.map(get-name))
            // upstream reports only the FIRST unused name (in sorted
            // `tnamesList` order), with singular wording
            match defined.filter(fn(tn) !free.member(tn.get-name)).list.sort(?(<) = fn(a: tName, b: tName) a.get-name.name/cmp(b.get-name).is-lt)
              [] -> ()
              Cons(name, _) ->
                inf-warning(pattern.range, "pattern variable".text |+| name.get-name.pp-name |+| "is unused (or a wrongly spelled constructor?)".text |-|
                  " hint: start with an underscore to make it a wildcard pattern".text)
          core/core/Branch([pcore], gcores)
        }, 
        fn(inf-gamma) {
            extend-inf-gamma-ex(False, matched-names, inf-gamma, {guards.map(infer-guard(prop, branch.range, _)).unzip})
        })

fun infer-guard(prop: maybe<(ktype,range)>, branch-range: range, Guard(test, expr): syntax/syntax/guard<ktype>)
  val (gtp, geff, gcore) = 
    with no-allow-return 
    infer(Just((typeBool, test.range)), Instantiated, test)
  val _ = 
    with val ctxt = checkGuardTotal(branch-range)
    infer-unify(test.range, typeTotal, geff)
  val _ = 
    with val ctxt = checkGuardBool(branch-range)
    infer-unify(test.range, typeBool, gtp)
  // check branch expression
  val (btp, beff, bcore) = infer(prop, Instantiated, expr)
  ((btp, beff), get-subst() |-> core/core/Guard(gcore, bcore))

fun infer-binders(inf-gamma, binders: list<value-binder<_, _>>)
  match binders
    [] -> inf-gamma
    Cons(par, pars) -> 
      val info = (par.name, create-name-infoX(Public, par.name, infer-effect/scope-depth, DefVal, par.range, par.binderType, ""))
      infer-binders(inf-gamma ++ [info], pars)

// infer implicit parameter declaration:
// check if the expression is a single identifier and possibly generate unpacking of fields
fun infer-optionals(allow-implicit-mask: bool, eff : keffect, inf-gamma: list<(name, assumption/name-info)>, params: list<value-binder<ktype, maybe<syntax/syntax/expr<ktype>>>>): _ (list<(name, assumption/name-info)>, list<(tName, core/core/expr)>, list<core/core/def>)
  match params 
    [] -> (inf-gamma, [], [])
    Cons(par: value-binder<ktype, maybe<syntax/syntax/expr<ktype>>>, pars) -> 
      match par.expr
        Nothing -> infer-optionals(allow-implicit-mask, eff, inf-gamma ++ [(par.name, create-name-infoEX(Public, par.name, infer-effect/scope-depth, DefVal, allow-implicit-mask, par.range, par.binderType, ""))], pars)
        Just(def-expr) -> // default value 
          val def-range = def-expr.range
          val full-range = par.range.combine(def-range)
          val opt-tp = par.binderType
          // infer parameter type from optional
          val tvar = fresh-star()
          val _ = 
            with val ctxt = Infer(full-range)
            infer-unify(par.range, opt-tp, tvar.make-optional)
          val partp = tvar.subst
          // infer expression
          val (expr-tp, expr-eff: ktype, core-expr) = 
            extend-inf-gamma(inf-gamma) 
              infer(Just((partp, par.range)), if partp.is-rho then Instantiated else Generalized(False), def-expr)
          val _ = 
            with val ctxt = checkOptional(full-range)
            infer-unify(def-range, partp, expr-tp)
          
          // check optional expressions; avoid unifying with `eff` type if possible
          match expr-eff.subst
            TVar(_) -> 
              with val ctxt = checkOptionalTotal(full-range)
              infer-unify(def-range, eff, expr-eff)
            _ -> if expr-eff.is-type-total then () else 
              with val ctxt = Infer(full-range)
              infer-unify(def-range, eff, expr-eff)
          
          val tp = partp.subst
          val infgamma' = inf-gamma ++ [(par.name, create-name-infoEX(Public, par.name, infer-effect/scope-depth, DefVal, allow-implicit-mask, par.range, tp, ""))]

          // build up core to get the optional value
          val local = par.name.unique-name-from
          val temp = par.name.unique-name-from
          val di = find-data-info(nameTpOptional)
          val (core-name-opt, core-tp-opt, core-repr-opt, con-info-opt) = resolve-con-name(nameOptional, Nothing, full-range)
          val (core-name-opt-none, core-tp-opt-none, core-repr-opt-none, con-info-opt-none) = resolve-con-name(nameOptionalNone, Nothing, full-range)
          val temp-name = TName(temp, tp)
          val par-name = TName(par.name, opt-tp)
          val core-par = Var(par-name, InfoNone) 
          val core-res-tp = TApp(TCon(TypeCon(di.name, di.kind)), [tp])
          val init = core/core/Case([core-par], 
               [Branch([
                  PatCon(TName(core-name-opt, core-tp-opt), [PatVar(temp-name, PatWild)], core-repr-opt, [tp], [], core-res-tp, con-info-opt, False
                    )], [core/core/Guard(exprTrue, Var(temp-name, InfoNone))]),
                Branch([
                  PatCon(TName(core-name-opt-none, core-tp-opt-none), [], core-repr-opt-none, [], [], core-res-tp, con-info-opt-none, True // Skip test
                    )], [core/core/Guard(exprTrue, core-expr)])
              ])
          val def = Def(local, partp, init, Private, DefVal, InlineNever, par.name-range, "")
          val sub = [(TName(par.name, tp), Var(TName(local, partp), InfoNone))]
          // infer the rest
          val (infgamma2, sub2, defs2) = infer-optionals(allow-implicit-mask, eff, infgamma', pars)
          (infgamma2, sub ++ sub2, Cons(def, sub |-> defs2))


//////////////////////////////////////////
// infer arguments
//////////////////////////////////////////

// infer the types of argument expressions, some of which may have already been inferred (`:FixedArg`).
fun infer-argsN(rng: range, par-args: list<(ktype, arg-expr)>): infer-eff-full (list<keffect>, list<core/core/expr>)
  fun infer-arg-expr(tp: ktype, arg-expr: _, hidden: bool) // TODO: Add context for better error messages for implicit parameters?
    with (if hidden then no-range-info else fn(f) f())
    with allow-return 
    val eta-arg = eta-expand-var-arg(tp, arg-expr)
    infer(Just((tp, arg-expr.range)), if tp.is-rho then Instantiated else Generalized(False), eta-arg)
  fun infer-arg(acc, args)
    match args 
      [] -> acc.reverse
      Cons((tpar: ktype, arg: arg-expr), args) ->
        val tpar0 = tpar.subst
        fun subsume-arg((targ, teff: ktype, core))
          val tpar1 = tpar0.subst
          val (_, coref) = infer-subsume(arg.range, tpar1, targ)
          (teff.subst, coref(core))
        val (eff, core) = match arg
          ArgExpr(arg-expr, hidden) -> subsume-arg(infer-arg-expr(tpar0, arg-expr, hidden))
          ArgCore((_, ctp, ceff, carg)) -> 
            val res = if tpar0.is-rho then (ctp, ceff, carg)
                      else generalize(rng, rng, False, {(ctp, ceff, carg)}) // TODO: is this ok?
            subsume-arg(res)
          ArgImplicit(name, r, _) ->
            val (arg-expr, term-info) = resolve-implicit-name(name, tpar0, r, r.end-of-range)
            // for any errors in `rng` we can show a nice representation as `termInfo` since
            // the `argExpr` is generated by implicit name resolving
            with hidden-term-doc(rng, term-info)
            subsume-arg(infer-arg-expr(tpar0, arg-expr, True))
        infer-arg(Cons((eff, core), acc), args)
  // (perf) no trace-indent handler in the hot path -- see infer-effect.kk note
  infer-arg([], par-args).unzip
 


fun infer-def-groups(topLevel: bool, dgroups: list<syntax/syntax/def-group<ktype>>): infer-eff-full list<core/core/def-group>
  match dgroups
    Nil -> []
    Cons(dg, rest) ->
      val (cgroups, crest) = infer-def-group(topLevel, dg) fn()
        infer-def-groups(topLevel, rest)
      // Zap the substitution after each top-level
      // def group completes (including all groups that follow it, since
      // `cont` already ran inside `infer-def-group`)
      if topLevel then zap-subst()
      cgroups ++ crest

// For std/core, move the key definitions (`ref`, `set`, `!`) to the front so
// their types are assumed before use in divergence checking
pub fun run-infer(tpl: target-platform, uniq0: int, imports: import-map, gamma0: gamma, modName: name,
                  syns: synonyms, newtps: newtypes, action: () -> infer-eff-full a): _ (a, range-map)
  with val current-error-kind = ErrType
  with nice-env
  with default-doc-env
  with default-pp-env
  with val pp-prec = precTopTop
  with default-indent
  with handler
    val ranked = rankedDefault
    val moduleContext = modName
    val importsMap = imports
  with build-range-map
  with run-unique(uniq0)
  with with-synonyms(syns)
  with withNewtypes(newtps)
  // the persistent global substitution (upstream: the `St` state)
  var subst := sub/null
  with handler
    final ctl unify-error(err) failure/fail("type/infer/run-infer: unexpected unification error: " ++ err.show)
    fun extend-sub(tv, tp) subst := subst.extend(tv, tp)
    fun add-sub(s) subst := s.compose(subst)
    fun get-subst() subst
    // Substitute the accumulated
    // range map with the current substitution, then clear it (called once per
    // top-level def group, see infer-def-groups)
    fun zap-subst()
      set-range-map(subst |-> get-range-map())
      subst := sub/null
    fun set-subst(s) subst := s
  with val infer-env = InferEnv(modName, [], False, False, False, Nothing, 0, False, rb-map/empty(), imports, inf-gamma/empty, gamma0, tpl)
  with val ctxt = Infer(range/null)
  with val scope-depth = 0
  with val local-depth = 0
  var holeAllowed := False
  with handler
    fun hole-allowed() holeAllowed
    fun use-hole() holeAllowed := False
  with handle-infer-eff
  with handle-iconstraints
  val x = action()
  // Apply the final substitution to the range map before
  // returning it ((sub st) |-> mbRangeMap st)
  (x, subst |-> get-range-map())

// Type inference for a module's definition groups
pub fun infer-types(tpl: target-platform, uniq0: int, imports: import-map, gamma0: gamma, modName: name,
                    syns: synonyms, newtps: newtypes, dgroups: list<syntax/syntax/def-group<ktype>>): _ (list<core/core/def-group>, range-map)
  with run-infer(tpl, uniq0, imports, gamma0, modName, syns, newtps)
  // upstream zaps the substitution after each top-level def group (see
  // infer-def-groups / zap-subst) instead of applying it once here at the
  // end; individual defs are already substituted as they are produced (see
  // infer-def) so no final pass over cgroups is needed
  infer-def-groups(True, arrange(dgroups))



