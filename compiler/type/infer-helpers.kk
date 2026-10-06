module compiler/type/infer-helpers
// Split out of compiler/type/infer (2026-09-11).
//
// These definitions never reference infer's mutually-recursive core -- the 19
// functions around `infer`/`infer-app`/`infer-lam`/`infer-handler` that have to
// stay in one module -- so they can live BELOW it and be compiled separately.
//
// Why: `compiler/type/infer.kk` was the most expensive module in the tree to
// rebuild (131.7s warm: 58.9s of it type checking alone, then 41.4s of clang on
// its 15.9MB object), which is the cost of every iteration on the type checker.
// Its interface is 14.8MB, 21% of all interface bytes in the compiler.

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
import std/data/rb-map

// used by definitions on both sides of the split
pub alias infer-eff-full = infer-full

pub type pattern-kind
  PatternOutermost(is-lazy: bool)
  PatternNested
pub fun show-binary(x: int, width: int): string
  fun bits(n: int)
    if n <= 0 then "" else bits(pretend-decreasing(n / 2)) ++ (n % 2).show
  // Padding written out rather than via `pad-left`. Upstream's simplifier had a
  // name-capture bug (fixed in Core/Simplify.hs: `uniqueTNameAvoiding`) that
  // miscompiled the inlined `pad-left` here, returning the fill instead of the
  // padded string. Building this repo with a compiler that predates that fix
  // would reintroduce it, so the dependency is avoided outright.
  val digits = if x <= 0 then "0" else bits(x)
  val fill = width - digits.count
  if fill <= 0 then digits else "0".repeat(fill) ++ digits

pub fun infer-lit(lit: syntax/syntax/lit): _ (ktype, keffect, core/core/expr)
  val (tp, core, rng, docs) = match lit
    LitInt(i, r) ->
      val decDoc = "dec  = " ++ i.show
      val hexDocs =
        if i < -0x8000000000000000 || i > 0x7FFFFFFFFFFFFFFF then []
        else
          val x = if i >= 0 then i
                  elif i >= -0x80 then 0x100 + i
                  elif i >= -0x8000 then 0x10000 + i
                  elif i >= -0x80000000 then 0x100000000 + i
                  else 0x10000000000000000 + i
          if x < 0 then []
          elif x <= 0x7F || (i < 0 && x <= 0xFF) then ["hex8 = 0x" ++ show-hex(x,2,pre=""), "bit8 = 0b" ++ show-binary(x,8)]
          elif x <= 0x7FFF || (i < 0 && x <= 0xFFFF) then ["hex16= 0x" ++ show-hex(x,4,pre=""), "bit16= 0b" ++ show-binary(x,16)]
          elif x <= 0x7FFFFFFF || (i < 0 && x <= 0xFFFFFFFF) then ["hex32= 0x" ++ show-hex(x,8,pre=""), "bit32= 0b" ++ show-binary(x,32)]
          else ["hex64= 0x" ++ show-hex(x,16,pre=""), "bit64= 0b" ++ show-binary(x,64)]
      (typeInt, core/core/ELit(core/core/LitInt(i)), r, [decDoc] ++ hexDocs)
    LitChar(c, r) ->
      val i = c.list.head.default(' ').char/int
      val udoc = if i < 0 || i > 0xFFFFF then (i.show ++ " (out of range)")
                 elif i <= 0xFFFF then "u" ++ show-hex(i,4,pre="")
                 else "U" ++ show-hex(i,6,pre="")
      (typeChar, core/core/ELit(core/core/LitChar(c)), r, ["unicode= " ++ udoc])
    LitFloat(f, r) -> (typeFloat, core/core/ELit(core/core/LitFloat(f)), r, ["hex64= " ++ std/num/float64/show-hex(f)])
    LitString(s, r) -> (typeString, core/core/ELit(core/core/LitString(s)), r, ["count= " ++ s.count.show])
  add-range-info(rng, RIId("literal".new-name, NIValue("expr", tp, "", False), docs.map(fn(d) d.text), False))
  val eff = operations/fresh-effect()
  (tp, eff, core)

// assignment: `x := e`, `arr[i] := e`

pub fun create-gammas(topLevel: bool, sd: int, gamma: list<(name, assumption/name-info)>, infgamma: list<(name, assumption/name-info)>, defs: list<syntax/syntax/def<ktype>>): _ (list<(name, assumption/name-info)>, list<(name, assumption/name-info)>, list<syntax/syntax/def<ktype>>)
  match defs
    Nil -> (gamma.reverse, infgamma.reverse, [])
    Cons(def, rest) ->
      val Def(binder as ValueBinder(name, _, expr, nameRng, _), _rng, _vis, sort, _inl, doc) = def
      if infgamma.any(fn((nm, _)) nm == name) then
        if topLevel
          then inf-error(nameRng, "recursive functions with the same overloaded name must all have a full type signature".text |-|
                                  " hint: give a type annotation for each function (including the effect type).".text)
          else inf-error(nameRng, "recursive functions with the same overloaded name cannot be defined as local definitions".text |-|
                                  " hint: use different names for each function.".text)
        val (g, ig, ds) = create-gammas(topLevel, sd, gamma, infgamma, rest)
        (g, ig, Cons(def, ds))
      else
        val mb-closed-ann = match expr
          Ann(_, tp, _) -> if topLevel && tp.free-type-vars.list.is-empty then Just(tp) else Nothing
          _ -> Nothing
        match mb-closed-ann
          Just(tp) ->
            val qname = qualify(infer-env.contxt, name)
            val nameInfo = create-name-infoX(Public, qname, sd, sort, nameRng, tp, doc)
            val (g, ig, ds) = create-gammas(topLevel, sd, Cons((qname, nameInfo), gamma), infgamma, rest)
            (g, ig, Cons(def, ds))
          Nothing ->
            if gamma.any(fn((nm, _)) nm.unqualify == name) then
              inf-error(nameRng, "recursive functions with the same overloaded name must have a full type signature".text)
            val qname = if topLevel then qualify(infer-env.contxt, name) else name
            match expr
              Ann(_, tp, _) ->
                val info = create-name-infoX(Public, qname, sd, sort, nameRng, tp, doc) // may be off due to incomplete type: fixed later in infer-rec-def2
                val (g, ig, ds) = create-gammas(topLevel, sd, gamma, Cons((qname, info), infgamma), rest)
                (g, ig, Cons(def, ds))
              _ ->
                val info = match expr
                  Lam(pars, _, _, _) ->
                    val tpars = pars.map fn(ValueBinder(bname, btp))
                      val t = match btp
                        Just(tp) -> tp
                        _ -> operations/fresh-star()
                      (bname, t)
                    val teff = operations/fresh-effect()
                    val tres = operations/fresh-star()
                    create-name-infoX(Public, qname, sd, DefVal, nameRng, TFun(tpars, teff, tres), doc)
                  _ ->
                    create-name-infoX(Public, qname, sd, DefVal, nameRng, operations/fresh-star(), doc) // must assume Val for now: fixed later in infer-rec-def2
                val def' = def(binder = binder(expr = Ann(expr, info.scheme, expr.range)))
                val (g, ig, ds) = create-gammas(topLevel, sd, gamma, Cons((qname, info), infgamma), rest)
                (g, ig, Cons(def', ds))

pub fun check-rec-val(cgroup: core/core/def-group): _ ()
  match cgroup
    core/core/DefNonRec -> ()
    core/core/DefRec(defs) ->
      defs.foreach fn(def)
        if !def.sort.is-fun then
          inf-error(def.nameRange, ("value definition is recursive.\n  recursive group: " ++ defs.map(def-name).show-list(show)).text)

pub fun fix-canonical-name(isRec: bool, def: core/core/def): _ core/core/def
  // first look in the inf gamma for recursive definitions (since they may not resolve unambiguously)
  val mbAssumedType = if isRec then lookup-inf-name(def.def-name) else Nothing
  match mbAssumedType
    Just((qname, _)) -> def(def-name = qname)
    // gamma fallback: resolve normally and take the info's canonical name --
    // this QUALIFIES the def name (upstream infoCanonicalName returns the
    // resolved infoCName); createCanonicalName's @N suffixing is disabled
    // upstream but the qualification is real work
    _ ->
      val (_, _, info) = resolve-name(def.def-name, Just((def.ktype, def.nameRange)), def.nameRange) // should never fail
      def(def-name = info.canonical-name(def.def-name))

// add the divergent effect to the type of a recursive core definition

pub fun add-divergent-effect(def: core/core/def): _ core/core/def
  val rng = def.nameRange
  val (_, tp0, coref) = instantiate-noex(def.ktype, rng)
  match tp0.split-fun-type
    Nothing -> def // can happen if a value contains a data structure containing recursive functions that refer to the value
    Just((targs, teff, tres)) ->

      val tv = operations/fresh-effect()
      val newEff = effect-extend(typeDivergent, tv)
      val _ =
        with val ctxt = checkEffectSubsume(rng)
        infer-unify(rng, newEff, teff)
      val snewEff = newEff.subst
      val (resTp, _, resCore) =
        with generalize(rng, rng, True)
        (TFun(targs, snewEff, tres), typeTotal, coref(def.defExpr))
      val _ =
        with val ctxt = checkEffectSubsume(rng)
        infer-subsume(rng, def.ktype, resTp)
      def(ktype = resTp, defExpr = resCore)

// check the assumed type of a recursive definition against its inferred type and
// generalize; fix up recursive occurrences that refer to the assumed (mono) type

pub fun infer-rec-def2(topLevel: bool, coreDef: core/core/def, divergent: bool, (def, mbAssumed): (syntax/syntax/def<ktype>, maybe<(name, ktype)>)): _ core/core/def
  val rng = def.range
  val nameRng = def.binder.name-range
  val (resTp0, assumedTp, coref0) = match mbAssumed
    Nothing -> (coreDef.ktype, coreDef.ktype, fn(e: core/core/expr) e)
    Just((_qname, assumed)) ->
      val assumedTp = assumed.subst
      val (resTp, coref) =
        with val ctxt = checkRec(rng)
        infer-subsume(nameRng, assumedTp, coreDef.ktype)
      (resTp.subst, assumedTp.subst, coref)
  val resTpX = if topLevel then unskolemize(resTp0) else resTp0
  val (resTp1, _, resCore1) =
    with generalize(rng, nameRng, True)
    (resTpX, typeTotal, coref0(coreDef.defExpr)) // typeTotal is ok since only functions are recursive (?)
  val sassumedTp = assumedTp.subst
  val sd = infer-effect/scope-depth
  val name = coreDef.def-name
  val csort = if topLevel || coreDef.is-top-level then coreDef.sort else DefVal
  val info = create-name-infoX(Public, name, sd, csort, def.range, resTp1, def.doc).core-var-info
  val (resTp2, coreExpr) = match resCore1
    TypeLam(tvars, expr) | sassumedTp.is-rho -> // we assumed a monomorphic type, but generalized eventually
      // fix it up by adding the polymorphic type application
      val assumedTpX = normalize(True, sassumedTp)
      val coreX = expr.subst
      val (mvars, msub) = fresh-sub(Bound, tvars)
      val resCoreX = replace-rec-calls(name, resTp1, info, msub |-> coreX)
      val resCoreY = add-type-lambdas(mvars, resCoreX)
      (resTp1, resCoreY)
    _ | divergent -> // we added a divergent effect, fix up the occurrences of the assumed type
      val assumedTpX = normalize(True, assumedTp).subst
      val coreX = resCore1.subst
      val resCoreX = replace-rec-calls(name, resTp1, info, coreX)
      (resTp1, resCoreX)
    _ -> // ensure we insert the right info (test: static/div2-ack)
      val assumedTpX = normalize(True, assumedTp).subst
      val coreX = resCore1.subst
      val resCoreX = replace-rec-calls(name, resTp1, info, coreX)
      (resTp1, resCoreX)
  def/substitute(get-subst(), core/core/Def(name, resTp2, coreExpr, coreDef.vis, csort, coreDef.kinline, coreDef.nameRange, coreDef.doc))

// Replace the references in `ex` to `name`, a member of a recursive group, by
// references at its generalized type `tp`. The group was checked with `name` at the
// type `occTp`: its annotation, or the monomorphic type assumed for it. A reference's
// type arguments instantiate `occTp`, and are mapped to the ones that instantiate
// `tp` at the same type (see `instance-type-args`). They cannot be reused as they are,
// since an annotation can quantify in another order than `tp` (tests
// cgen/rec-annot-order, cgen/rec-mutual-order), nor dropped, since a polymorphic
// recursive call has arguments of its own (test cgen/rec-polytargs).
pub fun replace-rec-calls(name: name, tp: ktype, info: var-info, ex: core/core/expr): _ core/core/expr
  match ex.free-vars.list.find(fn(TName(n, _)) n == name)
    Nothing -> ex
    Just(TName(_, occTp)) ->
      val to-tp-args = instance-type-args(name, occTp, tp)
      fun type-args-of(occurrence: core/core/expr): list<ktype>
        match occurrence
          core/core/TypeApp(_, targs) -> targs
          _ -> []
      fun call(occurrence: core/core/expr): div core/core/expr
        make-type-app(core/core/Var(TName(name, tp), info), to-tp-args(occurrence.type-args-of))
      [(TName(name, occTp), call)].expr/subst-occurrences(ex)

// Given the type `occTp` that the body of `name` was checked at, and its generalized
// type `tp`, map the type arguments of an instance of `occTp` to those of the same
// instance of `tp`; every instance of `occTp` is one of `tp`. The two can differ in
// the order of their quantifiers, `tp` can close an effect row that `occTp`
// quantifies over, and `tp` can quantify a variable that is free in `occTp` (the
// wildcard in `act : () -> _ a`). Unifying their bodies, with the quantifiers of both
// as unknowns, expresses each quantifier of `tp` in those of `occTp`. The unknowns
// are meta variables. A variable free in a body and not quantified by its own scheme
// must stay as it is, so it is a skolem during the unification: a meta variable can
// be bound to a skolem, but not to a bound variable.
fun instance-type-args(name: name, occTp: ktype, tp: ktype): _ ((list<ktype>) -> div list<ktype>)
  val (occVars, occRho) = occTp.split-type-scheme
  val (tpVars, tpRho) = tp.split-type-scheme
  val fixed = ((occRho.free-type-vars - occVars) + (tpRho.free-type-vars - tpVars)).list
  val (occMetas, occSub) = fresh-sub(Meta, occVars)
  val (tpMetas, tpSub) = fresh-sub(Meta, tpVars)
  val (skolems, toSkolem) = fresh-sub(Skolem, fixed)
  match run-unify({ unify(toSkolem |-> (tpSub |-> tpRho), toSkolem |-> (occSub |-> occRho)) })
    (Left(_), _) -> failure/fail("type/infer-helpers/instance-type-args: the type the body was checked at is not an instance of the generalized type: " ++ name.show)
    (Right(_), usub) ->
      val fromSkolem = skolems.zip(fixed.map(TVar)).sub
      fn(targs)
        if targs.length != occMetas.length then
          unsafe-total({ failure/fail("type/infer-helpers/instance-type-args: type arguments of " ++ name.show) })
        else
          // after unification, a quantifier of `occTp` is a variable, or a type where `tp` closed it
          fun arg-binding((occMeta, targ))
            match usub |-> TVar(occMeta)
              TVar(tv) -> [(tv, targ)]
              _ -> []
          val argSub = occMetas.zip(targs).flatmap(arg-binding).sub
          tpMetas.map(fn(tpMeta) fromSkolem |-> (argSub |-> (usub |-> TVar(tpMeta))))

pub fun add-range-info-core-def(topLevel: bool, mod: name, def: syntax/syntax/def<ktype>, coreDef: core/core/def): _ ()
  val qname =
    if topLevel && !coreDef.def-name.is-qualified
      then qualify(mod, coreDef.def-name)
      else coreDef.def-name
  val sortDoc = if defIsVal(def) then "val" else "fun"
  add-range-info(coreDef.nameRange, RIId(qname, NIValue(sortDoc, coreDef.ktype, def.doc, True), [], True))
  add-range-info(def.range, RIDecl(sortDoc, qname, qname.mangle(coreDef.ktype), Just(coreDef.ktype)))

// Infer the type of an expression while isolating its effect (e.g. for named handler bodies);
// also checks that local variables do not escape their lexical scope.

pub fun infer-isolated(context-range: range, rng: range, body: syntax/syntax/expr<ktype>, inf: () -> _ (ktype, keffect, core/core/expr)): _ (ktype, keffect, core/core/expr)
  fun has-var-decl(e: syntax/syntax/expr<ktype>): div maybe<range>
    match e
      Parens(x) -> x.pretend-decreasing.has-var-decl
      Let(_, x) -> x.pretend-decreasing.has-var-decl
      Bind(_, x) -> x.pretend-decreasing.has-var-decl
      Ann(x) -> x.pretend-decreasing.has-var-decl
      Inject(_, x) -> x.pretend-decreasing.has-var-decl
      App(Var(name, _, vrng)) | name == nameLocalNew -> Just(vrng)
      _ -> Nothing
  // only discharge constraints arising in the body; leftovers float up on scope exit
  val (tp, eff, core) =
    with scope-implicit-constraints
    inf()
  val (itp, ieff, coref) = improve(context-range, rng, True, eff, tp)
  match body.has-var-decl
    Nothing -> (itp, ieff, coref(core))
    Just(vrng) ->
      val sieff = ieff.subst
      val (ls, _) = sieff.extract-ordered-effect
      if ls.filter(fn(l) l.label-name == nameTpLocal).is-cons then
        type-error(context-range, vrng, "reference to a local variable escapes its lexical scope".text, sieff, [])
      (itp, sieff, coref(core))
//////////////////////////////////////////
// Infer Types
//////////////////////////////////////////


//////////////////////////////////////////
// Definition Groups
//////////////////////////////////////////


//////////////////////////////////////////
// Definition
//////////////////////////////////////////

pub fun check-linearity(effectName: name, heffect: ktype, branches: list<handler-branch<ktype>>, hrng: range, rng: range)
  fun check-linear-clauses()
    fun check(hbranch)
      if hbranch.branchSort <= OpFun then ()
      else context-error(rng, hbranch.branchPatRange, 
        "operation".text |+| hbranch.branchName.pp-name |+| 
        "needs to be linear but is handled in a non-linear way (as '".text |.| hbranch.branchSort.show.text |.| "')".text, 
        [("hint".text, "use a 'val' or 'fun' operation clause instead".text)])
    branches.map(check)
  fun check-linear-effect()
    val (effs, _tl) = heffect.extract-effect-extend
    match effs.drop-while(_.label-is-linear)
      Cons(e) -> 
        context-error(rng, hrng, 
          "handler for".text |+| pp-name(effectName) |+| 
          "needs to be linear but uses a non-linear effect:".text |+| e.pp-type, 
          [("hint".text, "ensure only linear effects are used in a handler".text)])
      [] -> ()
  check-linear-clauses()
  check-linear-effect()

// Infer the handled effect from looking at the operation clauses

pub fun infer-handled-effect(rng: range, handlerSort: handler-sort, mbeff: maybe<keffect>, ops: list<handler-branch<ktype>>): _ keffect
  match mbeff
    Just(eff) -> eff
    Nothing -> 
      match ops
        Cons(HandlerBranch(name, pars, _expr, _opSort, nameRng, rng), _) ->
          // TODO: handle errors if we find a non-operator
          val isInst = handlerSort.is-handlerInstance
          val (qname, tp, _info) = resolve-fun-name(name, CtxFunArgs(False, pars.length + (if isInst then 1 else 0), [], Nothing), rng, nameRng)
          val (_, rho, _) = instantiate-ex(tp, nameRng)
          match rho.split-fun-type
            Just((Cons((op-name, rtp)), _, _)) | isInst && op-name == new-hidden-name("hname") ->
              match rtp
                TApp(TCon(ev), [teff]) | ev.type-con/name == nameTpEv ->
                  val dataInfo = find-data-info(teff.get-type-name)
                  wrap-handled-from-data-effect(dataInfo.dEffect, teff)
                _ -> inf-error(rng, "Type.Infer.inferHandledEffect: illegal named effect type in operation?".text)
            Just((_, eff, _)) | !handlerSort.is-handlerInstance -> 
              match eff.extract-effect-extend
                (ls, _) ->
                  match ls.filter(_.is-handled-effect)
                    Cons(l, _) -> l // TODO: can we assume the effect comes first?
                    Nil -> inf-error(rng, "Type.Infer.inferHandledEffect: not an effect operation:".text |+| qname.pp-name |.| ".".text |-| " hint: maybe wrong number of parameters?".text)
            _ -> inf-error(rng, "Type.Infer.inferHandledEffect: unable to determine the handled effect.".text |-| " hint: use a `handler<eff>` declaration?".text)

// Check coverage is not needed for type inference but gives nicer error messages

pub fun check-coverage(rng: range, eff: ktype, handler-con-name: name, branches: list<handler-branch<ktype>>)
  val mod-name = handler-con-name.qualifier
  fun field-to-op-name(fname: name)
    val (pre, post) = fname.nameStem.list.span(_ != '-')
    val (op-sort, op-name) = 
      match (read-op-sort(pre.drop(1).string), pre.take(1), post) 
        (Just(op-sort), ['@'], Cons(_, op-name)) -> (op-sort, op-name.string)
        _ -> failure/fail("Type.Infer.checkCoverage: illegal operation field name: " ++ fname.show ++ " in " ++ handler-con-name.show)
    (mod-name.qualify(new-qualified(fname.nameModule, op-name)), op-sort)
  fun branch-to-op-name(hbranch: handler-branch<ktype>)
    val nm = 
      if is-value-operation-name(hbranch.branchName) then // .val-<op>
        from-value-operation-name(hbranch.branchName) 
      else hbranch.branchName
    (mod-name.qualify(nm.unqualify), hbranch.branchSort)
  fun check-coverage-of(all-op-names: list<name>, op-names: list<(name, operation-sort)>, branch-names: list<(name, operation-sort)>)
    match op-names 
      [] ->
        if branch-names.is-empty then () 
          // should not occur if branches typechecked previously
        else match branch-names.filter(fn((bname, _)) !all-op-names.contains(bname))
          Cons((bname, _), _) -> term-error(rng, "operator".text |+| bname.pp-name |+| "is not part of the handled effect".text, eff, [])
          Nil -> inf-error(rng, "some operators are handled multiple times for effect".text |+| eff.pretty)
      Cons((op-name, op-sort),op-names') ->
        val (matches, branch-names') = branch-names.partition(fn((bname, _)) bname == op-name)
        match matches
          [(_bname, bsort)] ->
            if bsort != op-sort && op-sort == OpVal then
              inf-error(rng, "cannot handle a 'val' operation".text |+| op-name.pp-name |+| "with".text |+| squotes(bsort.show.text))
            elif bsort > op-sort then
              // upstream joins the sort names with `<.>` (no surrounding spaces)
              inf-warning(rng, "operation".text |+| op-name.pp-name |+| "is declared as '".text |.| op-sort.show.text |.| "' but handled here using '".text |.| bsort.show.text |.| "'".text)
            else ()
          [] -> inf-error(rng, "operator".text |+| op-name.pp-name |+| "is not handled".text)
          _ -> inf-error(rng, "operator".text |+| op-name.pp-name |+| "is handled multiple times".text)
        // upstream recurses over the REMAINING operations (`checkCoverageOf
        // rng allOpNames opNames' branchNames'`); without this only the first
        // operation was ever checked (algeff/wrong/ops1, ops4)
        check-coverage-of(all-op-names, op-names'.pretend-decreasing, branch-names')
  val (_, _, _, con-info) = resolve-con-name(handler-con-name, Nothing, rng)
  val op-names = con-info.params.drop(1).map(fn((fname, _)) field-to-op-name(fname)) // Drop (cfc) parameter
  val branch-names = branches.map(_.branch-to-op-name)
  check-coverage-of(op-names.map(fst), op-names, branch-names)

// resolve the effect tag core expression for handled effects.

pub fun effect-name-core(eff: keffect, rng: range): _ (maybe<core/core/expr>, name)
  match eff.expand-syn
    // handled effects (from an `effect` declaration)
    TApp(TCon(tc), [hx])
      | tc.name == nameTpHandled || tc.name == nameTpHandled1 || tc.name == nameTpNHandled || tc.name == nameTpNHandled1 ->
        val eff-name = hx.effect-name-from-label
        val (tag-qname, _, tag-info) = resolve-name(eff-name.to-effect-tag-name, Nothing, rng)
        (Just(tag-info.core-expr(tag-qname)), eff-name)
    // builtin effect
    _ ->
      (Nothing, eff.effect-name-from-label)

///////////////////////////////////////////////////////////
// Infer Applications and Resolve Overloaded Identifiers
//////////////////////////////////////////////////////////

pub fun infer-pattern-nested(pat-kind: pattern-kind, match-type: ktype, branch-range: range, pattern: syntax/syntax/pattern<ktype>): _ (core/core/pattern, list<(name, assumption/name-info)>)
  val (_, res) = infer-pattern(pat-kind, match-type, branch-range, pattern, fn(pcore, inf-gamma) (pcore, inf-gamma)) fn(inf-gamma)
    val smatch-type = match-type.subst
    ([(smatch-type, typeTotal)], inf-gamma)
  res

pub fun use-skolemized-con(con-info: con-info, gcon-tp: ktype, range, name-range: range, cont)
  if con-info.existentials.is-empty then 
    val (conRho, _, _) = gcon-tp.infer-effect/instantiate(name-range)
    val (res, _) = cont(conRho, [])
    res
  else 
    val con-res-tp = fresh-star()
    val con-exists-tp = TForAll(con-info.existentials, if con-info.params.is-empty then con-res-tp else TFun(con-info.params, typeTotal, con-res-tp))
    with-skolemized(range, con-exists-tp, Nothing) fn(conXRho0, xvars)
      val conXRho = operations/instantiate(TForAll(con-info.foralls, conXRho0), name-range)
      val (iconRho, _, _) = gcon-tp.infer-effect/instantiate(name-range)
      val _ =
        with val ctxt = checkOp(range)
        infer-unify(name-range, conXRho, iconRho)
      cont(iconRho.subst, xvars)

pub fun infer-pattern(pat-kind: pattern-kind, match-type: ktype, branch-range: range, 
    pat: syntax/syntax/pattern<ktype>, 
    with-pattern: (core/core/pattern, a) -> infer-eff-full b,
    infer-part: (list<(name,assumption/name-info)> -> infer-eff-full (list<(ktype, keffect)>, a)),
    ?(|->): (sub, a) -> infer-eff-full a): infer-eff-full (list<(ktype, keffect)>, b)
  match pat 
    PatCon(name, patterns0, name-range, range) -> 
      val (qname, gcon-tp, repr, con-info) = resolve-con-pattern-name(name, match-type, patterns0.length, range)
      add-range-info(name-range, RIId(qname, NiCon(gcon-tp, con-info.doc), [], False))
      use-skolemized-con(con-info, gcon-tp, branch-range, range) fn(con-rho, xvars)
        val (con-par-tps, con-eff-tp, con-res-tp) = con-rho.split-con-tp
        val _ =
          with val ctxt = checkConTotal(range)
          infer-unify(name-range, con-eff-tp, typeTotal)
        val _ = 
          with val ctxt = checkConMatch(range)
          infer-unify(name-range, con-res-tp, match-type)
        // check valid lazy constructors
        val data-info = find-data-info(con-res-tp.get-type-name)
        if data-info.di/is-lazy then 
          match pat-kind
            PatternOutermost(is-lazy-match) -> 
              if con-info.coninfo/is-lazy && !is-lazy-match then 
                inf-error(name-range, qname.pp-name |.| ": lazy constructors are not allowed in a (non lazy) match".text)
            PatternNested -> 
              inf-error(name-range, qname.pp-name |.| ": constructors of a lazy type cannot be matched in a nested pattern (but must always be matched as an outermost pattern)".text)
        val patterns = match-patterns(range, name-range, con-rho, con-par-tps, patterns0)
        val (cpatterns, inf-gammas) = con-par-tps.map(snd).zipwith(patterns, fn(par-tp, p) infer-pattern-nested(PatternNested, par-tp.subst, branch-range, p)).unzip
        val inf-gamma = inf-gammas.concat
        val (btpeffs: list<(ktype, keffect)>, core-guards0) = infer-part(inf-gamma) // infer-guards
        val (pcore, core-guards) = 
          if xvars.is-empty then (PatCon(TName(qname, con-rho), cpatterns, repr, con-par-tps.map(snd), [], con-res-tp, con-info, False), core-guards0)
          else 
            val (bind-exists, sub-exists: sub) = fresh-sub(Bound, xvars)
            val pcore = PatCon(TName(qname, con-rho), sub-exists |-> cpatterns, repr, sub-exists |-> con-par-tps.map(snd), bind-exists, con-res-tp, con-info, False)
            (pcore, sub-exists |-> core-guards0)
        ((btpeffs, with-pattern(pcore, core-guards)), btpeffs.free-type-vars)
    PatVar(binder) -> 
      add-range-info(binder.name-range, RIId(binder.name, NIValue("val", match-type, "", binder.is-annotated), [], True))
      match binder.binderType
        Just(tp) -> 
          with val ctxt = checkAnn(binder.range)
          infer-unify(binder.name-range, match-type, tp)
        Nothing -> ()
      val (cpat, infgamma0) = infer-pattern-nested(pat-kind, match-type, branch-range, binder.expr)
      val infgamma = [(binder.name, create-name-infoX(Public, binder.name, infer-effect/scope-depth, DefVal, binder.name-range, match-type, ""))] ++ infgamma0
      val (btpeffs, x) = infer-part(infgamma)
      (btpeffs, with-pattern(PatVar(TName(binder.name, match-type), cpat), x))
    PatWild() ->
      val (btpeffs, x) = infer-part([])
      (btpeffs, with-pattern(PatWild, x))
    PatAnn(pat, tp, rng) -> 
      infer-pattern(pat-kind, tp, rng, pat, with-pattern) fn(infgamma)
        val _ = 
          with val ctxt = checkAnn(rng)
          infer-unify(pat.pattern/range, match-type, tp) // TODO: improve error message
        infer-part(infgamma)
    PatParens(pat) -> infer-pattern(pat-kind, match-type, branch-range, pat, with-pattern, infer-part)
    PatLit(lit) -> 
      val (pat', tp) = match lit 
        LitInt(i, _) -> (PatLit(LitInt(i)), typeInt)
        LitChar(c, _) -> (PatLit(LitChar(c)), typeChar)
        LitFloat(f, _) -> (PatLit(LitFloat(f)), typeFloat)
        LitString(s, _) -> (PatLit(LitString(s)), typeString)
      val _  = 
        with val ctxt = checkLitMatch(lit.range)
        infer-unify(branch-range, tp, match-type)
      val (btpeffs,x) = infer-part([])
      (btpeffs, with-pattern(pat', x))

pub fun infer-implicit-param(par: value-binder<maybe<ktype>, maybe<syntax/syntax/expr<t2>>>): _ (value-binder<maybe<ktype>, maybe<syntax/syntax/expr<t2>>>, syntax/syntax/expr<ktype> -> syntax/syntax/expr<ktype>)
  if par.name.is-implicit-param-name then
    val unpack =
      match par.expr
        Just(Parens(Var(qname, _, rng))) -> // encoded in the parser as a default expression
          infer-implicit-unpack(par.range.hide, rng.hide, par.name, qname, par.binderType)
        Nothing -> id
        Just(expr) ->
          context-error(par.range, expr.range, "the value of an implicit parameter must be a single identifier".text, [])
          id
    // leave the binder name locally qualified as `@implicit/name` -- binderName = pname,
    (ValueBinder(par.name, par.binderType, Nothing, par.name-range, par.range), unpack)
  else (par, id)

// the type annotation (`.?key : child`) takes precedence over the
// parameter name: it is the declared type of the parameter

pub fun type-con-name-of(tp: ktype): div maybe<name>
  match tp.expand-syn
    TCon(tcon) -> Just(tcon.name)
    TApp(t, _) -> t.type-con-name-of
    TForAll(_, t) -> t.type-con-name-of
    _ -> Nothing

pub fun infer-implicit-unpack(rng: range, nrng: range, pname: name, qname: name, mb-par-tp: maybe<ktype>): _ (syntax/syntax/expr<ktype> -> syntax/syntax/expr<ktype>)
  val mb-annot-info = match mb-par-tp.map(type-con-name-of)
    Just(Just(tcname)) -> newtypes-lookup-any(tcname)
    _ -> Nothing
  val mb-name-info = newtypes-lookup-any(qname)
  val mb-info = match mb-annot-info
    Just(_) -> mb-annot-info
    Nothing -> mb-name-info
  match mb-info
    Just(DataInfo(sort=Inductive, constrs=[conInfo], def=ddef)) | !ddef.is-open -> 
      // struct unpack the fields
      val pats = conInfo.params.map(fst).filter(!_.is-nil).map(fn(fname) PatVar(ValueBinder(pname.qualify-unpacked(fname), Nothing, PatWild(nrng), nrng, rng)))
      val pat = PatCon(conInfo.name, pats.map(fn(p) (Nothing, p)), nrng, null) // no warnings for unused pattern variables by using a null range
      fun unpack(body)
        Case(Var(pname, False, nrng), [Branch(pat, [Guard(guardTrue, body)])], False, rng)
      fun extract-struct-type(tp)
        match tp.expand-syn
          TApp(TCon(tcon), _) -> [tcon.name]
          TCon(tcon) -> [tcon.name]
          _ -> []
      val bases = conInfo.params.filter(fn((fname, _)) fname.name/starts-with("base")).flatmap(fn((fname, ftp)) ftp.extract-struct-type.map((fname, _)))
      fun compose(l, e) 
        match l
          Nil -> e
          Cons(f, fs) -> f(compose(fs, e))
      val unpackBases = bases.map fn((fname, fqname))
        infer-implicit-unpack(rng, nrng, pname.qualify-unpacked(fname), fqname, Nothing)
      fn(e) compose(Cons(unpack, unpackBases), e)
    _ -> id

// Infer automatic unwrapping for parameters with default values, and adjust their type from optional<a> to a
// Takes an accumulated InfGamma (initially empty), a list of parameters (as value binders) and returns
// the new InfGamma and a substitution from optional parameter names to the local unique names (of type a)
// and a list of core (non-recursive) bindings (where the substitution has already been applied)

pub fun match-fun-type-args(ctx-range: range, f: syntax/syntax/expr<ktype>, tp: ktype, fresolved: list<(int, fixed-arg)>, fixed: list<syntax/syntax/expr<ktype>>, named-args: list<((name, range), syntax/syntax/expr<ktype>)>): _ fun-match-type-args
  val rng = f.range
  val fixed-length = fixed.length
  val named-length = named-args.length
  fun report-non-callable()
    fun shadow-hint((nm: name, name-info: assumption/name-info))
      // Show Range is the start pos `(line, col)` only
      [("hint".text, nm.pp-name |+| "at position".text |+| name-info.range.start.pos/show.text |+| "might be shadowing another function".text)]
    val hints = 
      match f
        Var(name) ->
          match lookup-local-name(is-infoVal, name)
            Right((nm, nm-info)) -> shadow-hint((nm, nm-info))
            Left(results) -> results.flatmap(shadow-hint) //  Multiple locals with the same name?
        _ -> []
    type-error(ctx-range, rng, "only functions or types with a copy constructor can be applied".text, tp, hints)
    FunMatchTypeArgs((fixed ++ named-args.map(snd)).map-indexed(fn(i, x) (i, ArgExpr(x, True))), [], typeTotal, typeUnit, core/core/App)
  fun arg-wrap-tp(argtp: ktype, arg)
    if argtp.is-optional then arg.wrap-optional
    elif argtp.is-delay then arg.wrap-delay
    else arg
  fun match-fixed(pars: list<(int, (name, ktype))>, fixedx)
    match (pars, fixedx)
      (pars', []) -> (pars', [])
      (Cons((j, (_, tp')), pars'), Cons((i: int, arg), fixed')) ->
        match fresolved.lookup(_ == i)
          Just((crng, ctp, ceff, carg)) ->
            val (newtp, newarg) =
                  if tp'.is-optional then (ctp.make-optional, ctp.wrap-optional(carg))
                  else (ctp, carg)
            val (prest, rest) = match-fixed(pars', fixed')
            (prest, Cons((j, (i, ArgCore((crng, newtp, ceff, newarg)))), rest))
          Nothing ->
            val (prest, rest) = match-fixed(pars', fixed')
            (prest, Cons((j, (i, ArgExpr(arg-wrap-tp(tp', arg), False))), rest))
      ([], _) ->
        type-error(ctx-range, rng, "function is applied to too many arguments".text, tp, [])
        ([], [])
  // in the result, the first int is position of the parameter `j`, the second int `i` is the original position of
  // the argument (so we can evaluate in argument order)
  fun match-named(pars: list<(int, (name, ktype))>, named-argsx: list<(int, ((name, range), syntax/syntax/expr<ktype>))>)
    match (pars, named-argsx)
      ([], []) -> ([], [])
      ([], Cons()) ->
        type-error(ctx-range, rng, "function is applied to too many arguments".text, tp, [])
        ([], [])
      (_, Cons((i, ((name, r), arg)), named-rest)) ->
        match extract(name, [], pars)
          Just((j, tp', pars-rest)) ->
            val (prest, rest) = match-named(pars-rest, named-rest)
            (prest, Cons((j, (i, ArgExpr(arg-wrap-tp(tp', arg), r.range/is-null))), rest))
          Nothing ->
            type-error(ctx-range, rng, "there is no parameter with name".text |+| name.pp-name, tp, [])
            match-named(pars, named-rest)
      (_, []) -> (pars, [])
  // remaining parameters: missing required arguments are reported here
  fun match-rest(pars: list<(int, (name, ktype))>)
    if pars.all(_.snd.is-optional-or-implicit) then
      val (optionals, implicits) = pars.span(_.snd.snd.is-optional)
      // synthetic `i` values continue after the user-provided arguments
      val ops = optionals.map-indexed fn(k, (j, _))
        (j, (fixed-length + named-length + k, ArgExpr(optionalNone, True)))
      val imps = implicits.map-indexed fn(k, (j, (n, _)))
        (j, (fixed-length + named-length + optionals.length + k, ArgImplicit(n.split-implicit-param-name.snd, rng, rng)))
      ops ++ imps
    else
      val hints = match f.root-expr
        Var(name, _, _) | name == "resume".new-name ->
          [("hint".text, "cannot use \"resume\" inside a val/fun/except clause".text)]
        _ -> []
      type-error(ctx-range, rng, "function has not enough arguments".text, tp, hints)
      []
  fun match-parameters(pars)
    // Numbering model:
    // j = declaration slot of the formal parameter (used to bind expected types to arguments)
    // i = source argument order (used later to preserve evaluation order for side effects)
    // Match named arguments first so positional arguments cannot consume their parameter slots.
    val (pars1, iargs-named) = match-named(pars.indexed, named-args.indexed.map(fn((k, na)) (k + fixed-length, na)))
    val (pars2, iargs-fixed) = match-fixed(pars1, fixed.indexed)
    val iargs-rest = match-rest(pars2)
    (iargs-fixed ++ iargs-named ++ iargs-rest).sort(fn((j1, _), (j2, _)) cmp(j1, j2).is-lt).map(snd)
  match tp
    TFun(pars, eff, res) -> 
      val iargs = match-parameters(pars)
      FunMatchTypeArgs(iargs, pars, eff, res, core/core/App)
    TSyn(_, _, t) -> match-fun-type-args(ctx-range, f, t, fresolved, fixed, named-args)
    TVar(tv) -> 
      if !named-args.is-empty then // TODO: take fresolved into account
        inf-error(rng, "cannot use named arguments on an inferred function".text |-| 
                        " hint: annotate the parameters".text)
      val targs = fixed.map(fn(_) (nil, fresh-star())) ++ named-args.map(fn((n, _)) (n.fst, fresh-star()))
      val teff = fresh-effect()
      val tres = fresh-star()
      add-sub(sub/single(tv, TFun(targs, teff, tres)))
      FunMatchTypeArgs((fixed ++ named-args.map(snd)).map-indexed(fn(i, x) (i, ArgExpr(x, False))), targs, teff, tres, core/core/App)
    _ -> 
      // apply the copy constructor if we can find it
      val matches = lookup-name-ctx(is-info-val-fun-ext, nameCopy, CtxFunTypes(True, [tp], [], Nothing), rng)
      match matches 
        [(qname, info)] ->
          val (_, contp, coreInst) = info.scheme.instantiate-ex(rng)
          val FunMatchTypeArgs(iargs, pars, eff, res, _) = match-fun-type-args(ctx-range, f, contp, fresolved, Cons(f, fixed), named-args)
          FunMatchTypeArgs(iargs, pars, eff, res, fn(c, cargs) core/core/App(coreInst(info.core-expr(qname)), cargs))
        _ -> report-non-callable()

pub fun match-fun(nargs: int, mb-type: maybe<(ktype, range)>): _ fun-match-result
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
// Module-level inference (upstream `inferTypes` / `runInfer`)
//////////////////////////////////////////

// Infer types for a list of definition groups in sequence, each group
// extending the environment for the next

pub fun arrange(dgroups: list<syntax/syntax/def-group<ktype>>): _ list<syntax/syntax/def-group<ktype>>
  if module-name() != nameSystemCore then dgroups
  else
    val keyDefNames = [nameRef, nameRefSet, nameDeref]
    fun is-key(dg: syntax/syntax/def-group<ktype>): bool
      match dg
        DefNonRec(def) -> keyDefNames.any(fn(nm) nm.unqualify == def.binder.name.unqualify)
        _ -> False
    val (key, rest) = dgroups.partition(is-key)
    key ++ rest

// Install the full `infer-full` handler stack and run `action`;
// returns the action's result together with the collected range map.
