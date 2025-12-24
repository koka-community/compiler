module compiler/type/infer-effect

import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/failure
import compiler/common/unique
import compiler/platform/config
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
import compiler/syntax/range-map
import compiler/core/core
import compiler/lib/pprint
import std/data/linearmap
import std/data/linearset
import std/core/undiv
import std/core/unsafe

pub type variance
  Negative
  Invariant
  Positive

fun flip(v : variance)
  match v 
    Negative -> Positive
    Positive -> Negative
    Invariant -> Invariant

pub fun normalize(close: bool, tp: rho): <infer|e> rho
  val free = free-in-gamma()
  normalizeX(close, free, tp)

pub fun normalizeX(close: bool, free: tvs, tp: rho): <infer|e> rho
  match tp
    TForAll([], t) -> normalizeX(close, free, t)
    TSyn(syn, targs, t) ->
      TSyn(syn, targs, normalizeX(close, free, t))
    TFun(args, eff, res) ->
      val (ls, tl) = nofail-unify(fn() eff.extract-normalize-effect)
      val eff' = // remove tail variables in the result type
        match tl.expand-syn
          TVar(tv) | pretend-no-div{ close && tv.is-meta && !free.member(tv) && !(Cons(res, args.map(snd))).free-type-vars.member(tv)} ->
            nofail-unify(fn() unify(typeTotal, tl))
            eff.subst
          _ ->
            val ls' = ls.map(normalizex2(Positive, _))
            val tl' = normalizex2(Positive, tl)
            effect-extends(ls', tl')
      
      val args' = args.map fn((nm, arg))
        (nm, normalizex2(Negative, arg))
      val res' = normalizex2(Positive, res)
      val nice-eff = nicefy-effect(eff')
      TFun(args', nice-eff, res')
    _ -> normalizex2(Positive, tp)

fun normalizex2(v: variance, tp: rho): <infer|e> rho
  match v
    Invariant -> tp
    _ -> match tp
      TFun(args, eff, res) ->
        val (ls, tl) = nofail-unify(fn() eff.extract-normalize-effect)
        // we can only do this if 'tl' does not also occur anywhere else without
        // the same label present...
        // see 'catch' and 'run' for example
        val eff' = 
          val ls' = ls.map(fn(l) normalizex2(v, l))
          val tl' = normalizex2(v, tl)
          effect-extends(ls', tl')
        val args' = args.map fn((nm, arg))
          (nm, normalizex2(v.flip, arg))
        val res' = normalizex2(v, res)
        val nice-eff = nicefy-effect(eff')
        TFun(args', nice-eff, res')
      TForAll(vars, t) ->
        TForAll(vars, normalizex2(v, t))
      TApp(t, args) ->
        TApp(normalizex2(v, t), args)
      TSyn(syn, args, t) ->
        TSyn(syn, args, normalizex2(v, t))
      _ -> tp

pub fun nicefy-effect(eff: keffect): <infer|e> keffect
  fun try-alias(ls: list<tau>, nm: name): <infer|e> (list<tau>, list<tau>)
    if ls.is-nil then ([], [])
    else
      match synonyms-lookup(nm)
        Nothing -> ([], ls)
        Just(syn) ->
          val (ls2, tl2) = syn.t.extract-ordered-effect
          if ls2.is-nil || !tl2.is-effect-empty then ([], ls)
          else
            val (sls, insts) = find-insts(syn.syn-info/params, ls2, ls)
            match is-subset([], sls, ls)
              Just(rest) ->
                ([TSyn(TypeSyn(nm, syn.syn-info/kind, syn.syn-info/rank, Just(syn)), insts, effect-fixed(sls))], rest)
              _ -> ([], ls)
  fun match-aliases(names: list<name>, ls: list<tau>): <infer|e> list<tau>
    match names
      Nil -> ls
      Cons(nm, ns) ->
        val (pre, post) = try-alias(ls, nm)
        val post' = match-aliases(ns, post)
        pre ++ post'
  val (ls, tl) = eff.extract-ordered-effect
  val ls' = match-aliases([nameTpIO, nameTpST, nameTpPure, nameTpAsyncX], ls)
  ls'.foldr(tl, fn(l, t) TApp(TCon(tconEffectExtend), [l, t]))


fun find-insts(params: list<type-var>, ls1: list<tau>, ls2: list<tau>): pure (list<tau>, list<tau>)
  if params.is-nil then (ls1, [])
  else
    fun match-params(tp)
      match tp
        TApp(_, args) -> eq-types(params.map(TVar), args)
        _ -> False
    match ls1.filter(match-params)
      Nil -> (ls1, params.map(TVar))
      Cons(tp, _) ->
        val nm = tp.label-name
        match ls2.filter(fn(t) t.label-name == nm)
          Cons(TApp(_, args), _) | args.length == params.length ->
            (sub(params.zip(args)) |-> ls1, args)
          _ -> (ls1, params.map(TVar))

fun is-subset(acc: list<tau>, ls1: list<tau>, ls2: list<tau>): pure maybe<list<tau>>
  match (ls1, ls2)
    (Nil, Nil) -> Just(acc.reverse)
    (Nil, Cons()) -> Just(acc.reverse ++ ls2)
    (Cons(), Nil) -> Nothing
    (Cons(l1, ll1), Cons(l2, ll2)) ->
      val cmp = name/cmp
      if l1.label-name < l2.label-name then Nothing
      else if l1.label-name > l2.label-name then is-subset(Cons(l2, acc), ls1, ll2)
      else if eq-type(l1, l2) then is-subset(acc, ll1, ll2)
      else Nothing

pub fun split-effect(eff: keffect): <infer|e> (list<tau>, keffect)
  nofail-unify(fn() eff.extract-normalize-effect)

fun nofail-unify(action: () -> <infer,unify|e> a, ?kk-file-line: string): <infer|e> a
  match run-unify(action)
    (Right(v), sub) -> 
      add-sub(sub)
      v
    (Left(err), sub) -> 
      add-sub(sub)
      fail("should never fail!: " ++ err.show ++ " " ++ kk-file-line)

type infer-context
  Check(message: string, range: range)
  Infer(range: range)

/////////////////////////////////////
// Implicit arguments
/////////////////////////////////////

// A resolved implicit argument is always a name together with a list of further
// implicit arguments (in case it is a function itself)
type implicit-arg
  ImplicitArg(
    name: name, 
    info: assumption/name-info, 
    typ: rho, // instantiated type
    implicit-args: list<(name, implicit-arg)>
    )

alias typed-arg = (name, assumption/name-info, rho)

// special empty implicit arg for display purposes (as "...")
pub val empty-implicit-arg = 
  ImplicitArg(nil, InfoVal(Private, nil, typeUnit, 0, null, True, False, ""), typeUnit, [])

pub fun pp-implicit-arg(iarg: implicit-arg): <pretty-eff> doc
  if iarg.name.is-nil then "...".text
  else
    val docargs = iarg.implicit-args.map fn((pname, arg))
      pp-implicit-assign("", pname, arg, True)
    
    val fcount = match iarg.typ.split-fun-type
      Just((ipars, _, _)) -> 
        val (fixed, _, _) = ipars.split-optional-implicit
        fixed.length
      _ -> 0 // should never happen?
    
    val docfixed = list(1, fcount, fn(_) -> "_".text)
    
    iarg.name.pp-name-plain.color(colors.colorImplicitExpr) |.|
      (if iarg.implicit-args.is-nil then pprint/empty
       else (docfixed ++ docargs).intersperse(comma).hcat.parens)

pub fun pp-implicit-assign(pfx: string, pname: name, iarg: implicit-arg, shorten: bool): <pretty-eff> doc
  val pardoc = pname.pp-name-plain.color(colors.colorImplicitParameter) |.| "=".text
  if (pname == iarg.name && iarg.implicit-args.is-nil) || pname.from-implicit-param-name == iarg.name.unqualify-full || iarg.name.is-nil then
    (if shorten then pprint/empty else pardoc) |.| iarg.pp-implicit-arg
  else
    pardoc |.| iarg.pp-implicit-arg

pub fun iarg-scope-depth(nm: name, info: assumption/name-info): int
  if nm.is-implicit-constraint-evidence then -2 // never prefer compiler generated constraints
  else info.scope-depth

pub fun ia-scope-depth(iarg: implicit-arg): int
  iarg-scope-depth(iarg.name, iarg.info)

// Convert an implicit argument to an expression (that is supplied as the argument)
pub fun to-implicit-arg-expr(xrange: range, iarg: implicit-arg): <unique,pure> user-expr
  val range = xrange.hide // don't add things in the expression to the rangemap
  match iarg.implicit-args
    Nil -> syntax/Var(iarg.name, False, range)
    _ -> match iarg.typ.split-fun-type
      Just((ipars, _, _)) | ipars.any(is-optional-or-implicit) -> // eta-expansion needed?
        // eta-expand and resolve further implicit parameters
        // todo: eta-expansion may become part of subsumption?
        val (fixed, _, _) = ipars.split-optional-implicit
        // assertion "Type.InferMonad.toImplicitAppExpr" (implicits.length == iarg.implicit-args.length)
        val name-fixed = fixed.map-indexed fn(i, _)
          make-hidden-name("arg", new-name("x" ++ (i + 1).show))
        val args-fixed = name-fixed.map fn(nm)
          (Nothing, syntax/Var(nm, False, range))
        val args-implicit = iarg.implicit-args.map fn((pname, arg))
          (Just((pname, range)), to-implicit-arg-expr(range.end-of-range, arg))
        
        val body = App(syntax/Var(iarg.name, False, range), args-fixed ++ args-implicit, range)
        if name-fixed.is-nil then body
        else
          val binders = name-fixed.map fn(nm)
            ValueBinder(nm, Nothing, Nothing, range, range)
          Lam(binders, body, False, range)
      _ -> fail("compiler/type/infer-effect: to-implicit-arg-expr: illegal type for implicit? " ++ range.show ++ ", " ++ iarg.name.show)

pub fun pp-typed-arg(targ: typed-arg): <pretty-eff> doc
  val (nm, _, tp) = targ
  pp-param((nm, tp))

pub fun to-implicit-arg(iargs: list<(name, implicit-arg)>, targ: typed-arg): implicit-arg
  val (nm, info, rho) = targ
  ImplicitArg(nm, info, rho, iargs)

// We can find a unique solution, or none, or surely ambiguous.
// The `Infty` tracks infinite chains, while `Amb` ambigious ones. 
// Both are for error messages only.
type implicit-select
  None                           // no solution
  Found(arg: implicit-arg)       // unique solution
  Amb(args: list<implicit-arg>)  // multiple solutions (failure)
  Infty(arg: implicit-arg)       // infinite chain (failure)

pub val resolve-max-chain-depth = 32
pub val decreasing-within = 4

fun all-candidates(sel: implicit-select): list<implicit-arg>
  match sel
    None -> []
    Found(arg) -> [arg]
    Amb(args) -> args
    Infty(arg) -> [arg]

fun map(sel: implicit-select, f: (implicit-arg) -> implicit-arg): implicit-select
  match sel
    None -> None
    Found(arg) -> Found(f(arg))
    Amb(args) -> Amb(args.map(f))
    Infty(arg) -> Infty(f(arg))

fun merge(sel1: implicit-select, sel2: implicit-select): implicit-select
  match (sel1, sel2)
    (None, s) -> s
    (s, None) -> s
    // Any other combination becomes ambiguous
    // in particular Infty + Found must be treated as ambiguous to be sound
    _ -> Amb(sel1.all-candidates ++ sel2.all-candidates)

fun pp-select(sel: implicit-select): <pretty-eff> doc
  match sel
    None -> "None".text
    Found(iarg) -> "Found".text |+| iarg.pp-implicit-arg
    Infty(iarg) -> "Infty".text |+| iarg.pp-implicit-arg
    Amb(xs) -> "Amb".text |+| xs.map(pp-implicit-arg).list

/////////////////////////////////////
// Name Context
/////////////////////////////////////

pub type name-context
  CtxNone // Just a name
  CtxType(tp: ktype) // A name that can appear in a context with this type
  CtxFunArgs(
    matchSome: bool, // Only some arguments supplied?
    fixed: int, // `n` fixed (given without name) arguments
    names: list<name>, // given named arguments
    mbResTp: maybe<ktype>)  // possible result type
  CtxFunTypes(
    matchSome: bool, // Only some arguments supplied?
    fixedTypes: list<ktype>,  // `n` fixed (given without name) argument types
    namedTypes: list<(name, ktype)>, // given named argument types
    mbResTp: maybe<ktype>) // possible result type

pub fun pp-name-context(nctx: name-context): <pretty-eff> doc
  match nctx
    CtxNone -> "_".text
    CtxType(tp) -> tp.pp-type
    CtxFunArgs(matchSome, n, names, mbResTp) ->
      val args = list(1, n, fn(_) -> "?".text) ++ names.map(fn(nm) nm.pp-name |.| ": ?".text) ++ (if matchSome then ["...".text] else [])
      args.tupled |+| "->".text |+| mbResTp.map(pp-type).default("_".text)
    CtxFunTypes(matchSome, fixed, namedArgs, mbResTp) ->
      val args = fixed.map(pp-type) ++ namedArgs.map(pp-param) ++ (if matchSome then ["...".text] else [])
      args.tupled |+| "->".text |+| mbResTp.map(pp-type).default("_".text)

pub fun pp-name-ctx(nm: name, nctx: name-context): <pretty-eff> doc
  nm.pp-name |+| ":".text |+| pp-name-context(nctx)


// A fixed argument that has been inferred
alias fixed-arg = (range, ktype, keffect, core/core/expr)

pub fun pure-match-shape-name-ctx(ctx1 : name-context, ctx2 : name-context) : <pure,unique> bool
  match (ctx1, ctx2)
    (CtxType(tp1), CtxType(tp2)) -> pure-match-shape(tp1, tp2)
    (CtxFunTypes(some1, fixed1, named1, mbResTp1), CtxFunTypes(some2, fixed2, named2, mbResTp2)) ->
      if (some1 == some2) && fixed1.zipwith(fixed2, pure-match-shape).all(id) && named1.is-nil && named2.is-nil then
        match (mbResTp1, mbResTp2)
          (Nothing, Nothing) -> True
          (Just(tp1), Just(tp2)) -> pure-match-shape(tp1, tp2)
          _ -> False
      else False
    _ -> False

// Create a name context where the argument count is known (and perhaps some named arguments)
pub fun fixed-count-context(propagated : maybe<(ktype, range)>, fixed-count : int, namedArgs : list<name>) : name-context
  CtxFunArgs(False, fixed-count, namedArgs, propagated.map(fst))


pub fun pp-tvs(tvs: tvs): <pretty-eff> doc
  tvs.list.map(pp-type-var).list

pub fun implicit-type-context(tp : ktype) : name-context
  match tp.split-fun-type
    Just((ppars, _, prestp)) -> CtxFunTypes(False, ppars.map(snd), [], Just(prestp)) // can handle further implicits better
    _ -> CtxType(tp)

pub fun maybe-to-context(mb-type : maybe<ktype>) : name-context
  match mb-type
    Just(tp) -> CtxType(tp)
    Nothing -> CtxNone

pub fun maybe-r-to-context(mb-type-range : maybe<(ktype, range)>) : name-context
  maybe-to-context(mb-type-range.map(fst))



/////////////////////////////////////
// Implicit Constraints
/////////////////////////////////////
pub div type implicit-constraint
  ImplicitConstraint(
    name: name, // name of the implicit constraint (e.g. @hdiv)
    typ: ktype,
    evidence: name, // fresh name for the evidence
    contxt: range,
    range: range,
    canSolve: (tvs, implicit-constraint) -> infer bool,
    solve: (tvs, implicit-constraint) -> infer (core/core/expr, ktype)
  )

fun show(ic: implicit-constraint): string
  ic.name.show

fun ic/substitute(sub: sub, ic: implicit-constraint)
  ic(typ = ktype/substitute(sub, ic.typ))
fun ic/free-type-vars(ic: implicit-constraint): div tvs
  ic.typ.free-type-vars
fun ic/free-type-constructors(ic: implicit-constraint): div type-cons
  ic.typ.free-type-constructors


// implicit constraint evidence name?
fun is-implicit-constraint-evidence(name: name): bool
  name.name/starts-with("iev@")

fun pp-constraint(ic: implicit-constraint): <pretty-eff> doc 
  pp-name(ic.evidence) |.| "=".text |+| pp-param((ic.name, ic.typ))

fun pp-constraints(ics: list<implicit-constraint>): <pretty-eff> doc
  ics.map(pp-constraint).list

/////////////////////////////
// Error Helpers
/////////////////////////////

// Casing checks
pub fun case-overlaps(nm: name, qname: name, info: assumption/name-info): maybe<name>
  val qname1 = match info
    InfoImport(_, _, infoAlias, _, _) -> infoAlias
    _ -> qname
  
  if !qname.is-locally-qualified && // TODO: fix casing check for internally qualified names
     name-case-overlap(if nm.is-qualified then qname1 else qname1.unqualify, nm) 
  then Just(qname1)
  else Nothing

pub fun check-casing-overlap(rng: range, nm: name, qname: name, info: assumption/name-info): <infer> ()
  match case-overlaps(nm, qname, info)
    Just(qname1) ->
      val env = infer-env
      inf-error(rng, info.element.text |+| nm.unqualify.pp-name |+| "is already in scope with a different casing as".text |+| env.importsMap.get-alias(qname1).pp-name)
    Nothing -> ()

pub fun check-casing(rng: range, nm: name, qname: name, info: assumption/name-info): <infer> ()
  match case-overlaps(nm, qname, info)
    Just(qname1) ->
      val env = infer-env
      inf-error(rng, info.element.text |+| nm.unqualify.pp-name |+| "should be cased as".text |+| env.importsMap.get-alias(qname1).pp-name)
    Nothing -> ()


pub fun pp-ambiguous(hint: string, infos: list<(name, assumption/name-info)>): <pretty-eff> doc
  vcat([". Possible candidates: ".text, pp-candidates(infos)] ++
       (if hint.is-empty then [] else ["hint: ".text |+| hint.text]))


pub fun pp-candidates(nameInfos: list<(name, assumption/name-info)>): <pretty-eff> doc
  val env = infer-env
  val modName = env.contxt
  val n = 10
  val sorted = nameInfos.sort-by fn((nm1, info1), (nm2, info2))
    if nm1.qualifier == modName && nm2.qualifier != modName then Lt
    else if nm1.qualifier != modName && nm2.qualifier == modName then Gt
    else cmp(!info1.info-type.is-rho, !info2.info-type.is-rho)
  
  val (defs, rest) = sorted.split(n)
  val rows = defs.map fn((nm, info)) pp-name-info(nm, info)
  val finalRows = 
    if rest.is-nil then rows
    else rows ++ [("...".text, "or".text |+| rest.length.show.text |+| "other definitions".text)]
  finalRows.table.align

pub fun pp-implicits-hint(nameInfos: list<(name, assumption/name-info)>): <pretty-eff> list<(doc, doc)>
  val candidateMissingImplicits = nameInfos.map fn((_, info))
    info.info-type.requires-implicits.map(fst)
  
  val allMissingImplicits = candidateMissingImplicits.concat.linearset
  val allRequiredMissingImplicits = allMissingImplicits.list.filter fn(imp)
    candidateMissingImplicits.all(fn(missing) missing.any(fn(m) m == imp))
  
  match allRequiredMissingImplicits
    Nil -> []
    _ -> [("missing implicits".text, allRequiredMissingImplicits.map(pp-name).hsep),
          ("hint".text, "ensure implicit functions are defined prior to functions that require them".text)]

pub fun pp-name-info(nm: name, info: assumption/name-info): <pretty-eff> (doc, doc)
  val env = infer-env
  (env.importsMap.get-alias(nm).pp-name, info.info-type.pp-type)

pub fun pp-or(names : list<name>) : <pretty-eff> doc
  match names
    Nil -> pprint/empty
    Cons(name, Nil) -> pp-name(name)
    _ -> 
      match names.reverse
        Cons(last, rest) -> 
          hcat(rest.reverse.map(pp-name(_) |.| ", ".text)) |+| "or".text |+| pp-name(last)
        Nil -> pprint/empty




/////////////////////////////////////
// Inference Effect
/////////////////////////////////////
pub struct inferEnv
  contxt: name
  currentDefs: list<name>
  namedLam: bool
  holeAllowed: bool
  returnAllowed: bool
  inLhs: bool
  hiddenTermDoc: maybe<(range, doc)>
  localDepth: int
  allowInfiniteChains: bool
  niceNames: name-map<doc>
  importsMap: import-map

pub effect val scope-depth: int
pub effect val local-depth: int

pub alias infer = <pretty-eff, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, inf-gamma-eff, synonyms-eff, newtypes-eff, unify, unique>;

fun free-in-gamma()
  (sub/(|->)(get-subst(), inf-gamma-list().map(snd))).free-type-vars

div type ic-params 
  ICParams(
    nm: name,
    tp: ktype,
    can-solve: (tvs, implicit-constraint) -> infer bool,
    solve: (tvs, implicit-constraint) -> infer (core/core/expr, ktype),
    rngCtx: range,
    rng: range
  )

pub div effect def-infer-effect
  fun get-iconstraints(): list<implicit-constraint>
  // add a new implicit constraint with a fresh name (to be solved at generalization time)
  fun add-iconstraint(ic: ic-params): (name, assumption/name-info, ktype)
  fun solve-iconstraint(nm : name, tp : ktype): ()

// TODO: incorporate generalization into here?
fun with-def(action)
  var iconstraints : list<implicit-constraint> := []
  var iconstraints-gamma := inf-gamma/empty
  with override
    fun get-iconstraints() iconstraints.subst
    fun add-iconstraint(ic: ic-params) 
      val evName = fresh-name("iev")
      val icx = ImplicitConstraint(ic.nm, ic.tp, evName, ic.rngCtx, ic.rng, ic.can-solve, ic.solve)
      val icNameInfo = create-name-infoX(Public, evName, 2, DefVal, ic.rng, ic.tp, "")
      val iarg = (evName, icNameInfo, ic.tp)
      iconstraints := iconstraints ++ [icx]
      iconstraints-gamma := iconstraints-gamma.extend(evName, icNameInfo)
      iarg
    fun solve-iconstraint(nm : name, tp : ktype)
      iconstraints := iconstraints.remove(fn(ic) ic.name == nm)
  action()

fun with-hole-allowed(allowed: bool, action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(holeAllowed = allowed)
  action()
pub fun with-context(nm: name, action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(contxt = nm)
  action()
pub fun with-lhs(action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(inLhs = True)
  action()
pub fun with-return-allowed(allowed: bool, action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(returnAllowed = allowed)
  action()
pub fun with-scope(action: () -> <infer|e> a): <infer|e> a
  with override val scope-depth = infer-effect/scope-depth + 1
  action()
pub fun with-local-scope(action: () -> <infer|e> a): <infer|e> a
  with override val local-depth = local-depth + 1
  action()
pub fun with-no-local-scope(action: () -> <infer|e> a): <infer|e> a
  with override val local-depth = 0
  action()

pub effect val infer-env: inferEnv

pub effect infer-eff 
  fun inf-error(rng: range, msg: doc): ()
  fun inf-warning(rng: range, msg: doc): ()