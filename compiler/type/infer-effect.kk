module compiler/type/infer-effect

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
import compiler/type/operations
import compiler/type/unify
import compiler/type/pretty
import compiler/syntax/syntax
import compiler/syntax/range-map
import compiler/core/core
import compiler/lib/pprint
import std/data/linear-map
import std/data/linear-set
import std/data/sort
import std/core/undiv
import std/core/unsafe
import compiler/lib/core

pub type variance
  Negative
  Invariant
  Positive

fun flip(v : variance)
  match v 
    Negative -> Positive
    Positive -> Negative
    Invariant -> Invariant

pub fun normalize(close: bool, tp: rho): _ rho
  val free = free-in-gamma()
  normalizeX(close, free, tp)

pub fun normalizeX(close: bool, free: tvs, tp: rho): _ rho
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

fun normalizex2(v: variance, tp: rho): _ rho
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

pub fun nicefy-effect(eff: keffect): _ keffect
  fun try-alias(ls: list<tau>, nm: name): _ (list<tau>, list<tau>)
    if ls.is-nil then ([], [])
    else
      match synonyms-lookup(nm)
        Nothing -> ([], ls)
        Just(syn) ->
          val (ls2, tl2) = syn.tp.extract-ordered-effect
          if ls2.is-nil || !tl2.is-effect-empty then ([], ls)
          else
            val (sls, insts) = find-insts(syn.syn-info/params, ls2, ls)
            match is-subset([], sls, ls)
              Just(rest) ->
                ([TSyn(TypeSyn(nm, syn.syn-info/kind, syn.syn-info/rank, Just(syn)), insts, effect-fixed(sls))], rest)
              _ -> ([], ls)
  fun match-aliases(names: list<name>, ls: list<tau>): _ list<tau>
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

pub fun split-effect(eff: keffect): _ (list<tau>, keffect)
  nofail-unify(fn() eff.extract-normalize-effect)

//////////////////////////////////////
// Generalization
//////////////////////////////////////

pub fun generalize(contextRng: range, rng: range, close: bool, f: () -> _ (rho,keffect,core/core/expr)): _ (rho, keffect, core/core/expr)
  fun generalizeX(tp: ktype, eff0: keffect, core0: core/core/expr)
    match tp 
      TForAll(_, _) ->
        val stp = tp.subst
        val seff = eff0.subst
        if stp.fuv.is-empty then (tp, seff, core0)
        else 
          val (rho, _, icore) = instantiate-no-ex(stp, rng) // instantiate first
          generalizeX(rho, seff, icore(core0))
      _ ->
        if close then 
          // check that the computation is total
          with val ctxt = Check("Generalized values cannot have an effect", contextRng)
          infer-unify(rng, typeTotal, eff0)
        else ()
        // Solve implicit constraints
        val seff0 = eff0.subst
        val free0 = free-in-gamma()
        val free1 = free0.union(seff0.fuv)
        val iccore = try-resolve-implicit-constraints(close, free1)
        val bodycore1 = iccore(core0)

        // Normalize type
        val seff = eff0.subst
        val srho = tp.subst
        val free = free0.union(seff.fuv)
        val nrho = normalizeX(close, free, srho)

        // Generalized type variables
        val tvars = nrho.ofuv.filter(!free.member(_))
        if tvars.is-empty then (nrho, seff, bodycore1)
        else
          // Create free type variables for the bounds
          // Important to avoid duplicate names (`test/algeff/exn3`)
          val (bvars, bsub) = fresh-sub(Bound, tvars)
          val TForAll([], rho5) = bsub |-> (TForAll([], nrho))
          // Core 
          val corePre = bsub |-> bodycore1
          val core1 = bvars.add-type-lambdas(corePre)
          val resTp = bvars.quantify-type(rho5)
          (resTp, seff, core1)
  if close then 
    val (tp, eff, core) = f()
    generalizeX(tp, eff, core)
  else
    with scope-implicit-constraints
    val (tp, eff, core) = f()
    generalizeX(tp, eff, core)


// TODO: improve / isolate


pub fun instantiate(tp: ktype, rng: range): _ (ktype, list<type-var>, core/core/expr -> core/core/expr)
  if tp.is-rho then 
    val (rho, coref) = tp.extend
    (rho, [], coref)
  else 
    val (tvars, rho, coref) = tp.instantiate-ex(rng)
    (rho, tvars, coref)

pub fun instantiate-no-ex(tp: ktype, rng: range): _ (ktype, list<type-var>, core/core/expr -> core/core/expr)
  if tp.is-rho then 
    (tp, [], id)
  else 
    val (tvars, rho, coref) = tp.instantiate-noex(rng)
    (rho, tvars, coref)

pub type infer-context
  Check(message: string, range: range)
  Infer(range: range)

/////////////////////////////////////
// Resolve Names
/////////////////////////////////////

// Lookup a name with a certain type and return the fully qualified name and its type
pub fun resolve-name(name: name, mb-type: maybe<(ktype, range)>, rng: range): _ (name, ktype, assumption/name-info)
  match mb-type
    Just((tp, ctx-range)) -> resolve-name-ex(is-info-val-fun-ext, Just(fn(x) !x.is-infoImport), name, CtxType(tp), ctx-range, rng)
    Nothing -> resolve-name-ex(is-info-val-fun-ext, Just(fn(x) !x.is-infoImport), name, CtxNone, rng, rng)

// Lookup a name with a certain type and return the fully qualified name and its type
// because of local variables and references a typed lookup may fail as we need to
// dereference first. So we do a typed lookup first and fall back to untyped lookup
pub fun resolve-rhs-name(name: name, (tp, ctx-range): (ktype, range), rng: range): _ (name, ktype, assumption/name-info)
  val candidates = lookup-name-ctx(is-info-val-fun-ext, name, CtxType(tp), rng)
  match candidates
    [(qname, info)] -> // unambiguous and matched
      check-casing(rng, name, qname, info)
      return (qname, info.scheme, info)
    [] -> // not found; this may be due to needing a coercion term
      resolve-name(name, Nothing, rng) // try again without type info
    _ -> // still ambiguous (even with a type), call regular lookup to throw an error
      resolve-name(name, Just((tp, ctx-range)), rng)

// Lookup a name with a number of arguments and return the fully qualified name and its type
pub fun resolve-fun-name(name: name, ctx-name: name-context, ctx-range: range, rng: range)
  resolve-name-ex(is-info-val-fun-ext, Just(fn(x) !x.is-infoImport), name, ctx-name, ctx-range, rng)

pub fun resolve-con-name(name: name, mb-type: maybe<ktype>, rng: range): _ (name, ktype, con-repr, con-info)
  val (qname, tp, InfoCon(_, _, repr, info)) = resolve-name-ex(is-infoCon, Nothing, name, maybe-to-context(mb-type), rng, rng)
  (qname, tp, repr, info)

pub fun resolve-con-pattern-name(name: name, match-type: ktype, pattern-count: int, rng: range): _ (name, ktype, con-repr, con-info)
  val (qname, tp, InfoCon(_, _, repr, info)) = resolve-name-ex(is-infoCon, Nothing, name, CtxFunArgs(True /* partial */, pattern-count, [], Just(match-type)), rng, rng)
  (qname, tp, repr, info)

fun resolve-name-ex(info-filter: (assumption/name-info -> bool), mb-info-filter-amb: maybe<(assumption/name-info -> bool)>, name: name, ctx-name: name-context, ctx-range: range, rng: range)
  match lookup-name-ctx(info-filter, name, ctx-name, rng)
    Nil -> 
      val amb = match ctx-name
        CtxNone -> []
        _ -> lookup-name-ctx(info-filter, name, CtxNone, rng)
      val ctx-term = [("context".text, doc-from-range(ctx-range)), 
                      ("term".text, doc-from-range(rng))]
      match (ctx-name, amb)
        (CtxType(tp), [(_, info)]) -> 
          val [nice1, nice2] = nice-types([tp, info.scheme])
          inf-error(rng, name.pp-name |+| "does not match the argument types".text |-| 
            table(ctx-term ++ 
              [("inferred type".text, nice2), 
              ("expected type".text, nice1)]))
        (CtxType(tp), Cons()) -> 
          val nice1 = nice-types([tp]).head.unjust
          inf-error(rng, "identifier".text |+| name.pp-name |+| "has no matching definition".text |-| 
            table(ctx-term ++ 
              [("inferred type".text, nice-type(tp)),
              ("candidates".text, pp-candidates(amb))] ++ pp-implicits-hint(amb)))
        (CtxFunArgs(_, fixed, namedArgs, Just(res-tp)), Cons()) ->
          val message = "with " ++ (fixed + namedArgs.length).show ++ " argument(s) matches the result type"
          inf-error(rng, "no function".text |+| name.pp-name |+| message.text |+|
            nice-type(res-tp) |.| pp-ambiguous("", amb))
        (CtxFunArgs(_, fixed, namedArgs, Nothing), Cons()) ->
          val message = "takes " ++ (fixed + namedArgs.length).show ++ " argument(s)" ++ 
                        (if namedArgs.is-nil then "" else " with those parameter names")
          inf-error(rng, "no function".text |+| name.pp-name |+| message.text |.| pp-ambiguous("", amb))
        (CtxFunTypes(partial, fixed, namedArgs, _), Cons()) -> 
          val docs = (fixed ++ namedArgs.map(snd)).nice-types
          val fdocs = docs.take(fixed.length)
          val ndocs = namedArgs.zipwith(docs.drop(fixed.length)) fn((_, n), tpdoc)
            (n.pretty |+| ":".text).color(colors.colorParameter) |+| tpdoc
          val pdocs = if partial then ["...".text] else []
          val argsDoc = parens(hsep((fdocs ++ ndocs ++ pdocs).punctuate(comma))) |+| "-> ...".text // TODO: Show nice mbResTp if present
          inf-error(rng, "no function".text |+| name.pp-name |+| "is defined that matches the argument types".text |-| 
            table(ctx-term ++ 
              [("inferred type".text, argsDoc),
              ("candidates".text, pp-candidates(amb))] ++ 
              pp-implicits-hint(amb) ++ 
              (if name == new-name("+") then [("hint".text, "did you mean to use append (++)? (instead of addition (+))".text)] else [])))
        _ -> 
          val amb2 = mb-info-filter-amb.map(fn(filter) lookup-name-ctx(filter, name, ctx-name, rng)).default([])
          match amb2
            Cons() -> inf-error(rng, "identifier".text |+| name.pp-name |+| "cannot be found".text |-|
              "perhaps you meant:".text |+| pp-or(amb2.map(fst)))
            _ | is-eta-hole(name) -> 
              val in-ctx = hole-allowed()
              val header = "eta-expansion of \"_\" is not allowed for top-level expressions".text
              val message = if in-ctx then header |-| "hint: perhaps you meant to use the \"hole\" keyword to denote the hole in a constructor context?".text 
                          else header
              inf-error(rng, message)
            _ -> 
              inf-error(rng, "identifier".text |+| name.pp-name |+| "cannot be found".text)
    [(qname, info)] -> // umambiguous
      check-casing(rng, name, qname, info)
      (qname, info.scheme, info)
    matches -> 
      val (term, term-info) = get-term-doc("context", ctx-range)
      inf-error(rng, "identifier".text |+| name.pp-name |+| "cannot be resolved.".text |-|
        table([(term, term-info), 
              ("inferred type".text, pp-name-context(ctx-name)), 
              ("candidates".text, pp-candidates(matches)), 
              ("hint".text, "give a type annotation or qualify the name?".text)
              ] ++ pp-implicits-hint(matches)))   
       

/////////////////////////////////////
// Resolving of implicit expressions
/////////////////////////////////////

// lookup an application name `f(...)` where the name context usually contains (partially) inferred
// argument types. We reuse the lookup for implicit arguments as it works the same
// (except that for implicit arguments we allow value types to be resolved with unit functions (for conversions))
fun lookup-app-name(allow-disambiguate : bool, name: name, name-ctx: name-context, ctx-range: range, rng: range): _ either<list<doc>, (ktype, syntax/syntax/expr<ktype>, list<((name, range), syntax/syntax/expr<ktype>, bool -> pretty-eff doc)>)>
  val roots = 
    if !name.is-constructor-name then // normal identifiers
      [(is-info-val-fun-ext, name)]
    else // constructor application: we need to consider creator functions too (for default fields)
      val cname = name.new-creator-name
      val def-name = current-def-name()
      if cname.unqualify == def-name || def-name == nameCopy then // a bit hacky, but ensure we don't call the creator function inside itself or the copy function
        [(is-infoCon, name)]
      else [(is-infoFun, cname), (is-infoCon, name)]
  // try to find a unique solution
  val res = resolve-implicit-arg(allow-disambiguate, !allow-disambiguate, /* allow unitFunVal: at first, when allowDisambiguate is False, we like to see all possible instantiations */
                                 name-ctx, rng, roots)
  match res
    Right(ImplicitArg(qname, _, rho, iargs)) ->
      val implicits = iargs.map fn((pname, iarg'))
        ((pname, rng), iarg'.to-implicit-arg-expr(rng.end-of-range), fn(b) pp-implicit-assign("", pname, iarg', b)) 
      Right((rho, Var(qname, False, rng), implicits))
    Left(docs) ->
      if allow-disambiguate && !docs.is-empty then 
        val term-doc = get-term-doc("context", ctx-range)
        inf-error(rng, "identifier".text |+| name.pp-name |+| "cannot be resolved".text |-|
          table([term-doc, 
                ("inferred type".text, pp-name-context(name-ctx)),
                ("candidates".text, pp-amb-docs(docs)),
                ("hint".text, "qualify the name?".text)]))
        Left(docs)
      else
        Left(docs)

// resolve an implicit argument name to an expression
pub fun resolve-implicit-name(name: name, tp: ktype, ctx-range: range, rng: range): _ (syntax/syntax/expr<ktype>,doc)
  val res = resolve-implicit-arg(True /* disambiguate */, True /* allow unit fun val for conversions */, 
       tp.implicit-type-context, rng, [(is-info-val-fun-ext, name)])
  match res
    Right(iarg) -> // TODO: Trace
      (iarg.to-implicit-arg-expr(rng), pp-implicit-arg(iarg))
    Left(docs) -> 
      val ctx-term = get-term-doc("context", ctx-range)
      inf-error(rng, "cannot resolve implicit parameter".text |-|
        table([ctx-term, 
              ("parameter".text, "?".text |.| (name,tp).pp-name-type),
              ("candidates".text, pp-amb-docs(docs)),
              ("hint".text, "add a (implicit) parameter to the function signature?".text)]))

/////////////////////////////////////
// Resolving implicit names
/////////////////////////////////////

// Resolve an implicit argument fully
fun resolve-implicit-arg(allow-disambiguate: bool, allow-unit-fun-val: bool, ctx-name: name-context, rng: range, roots: list<(assumption/name-info -> bool, name)>): _ either<list<doc>, implicit-arg>
  val sel = resolve-implicit-arg-ex(allow-disambiguate, allow-unit-fun-val, [], ctx-name, rng, roots)
  match sel
    Found(iarg) -> Right(iarg)
    _ -> Left(sel.all-candidates.map(pp-implicit-arg))

// always prefer a creator definition over a plain constructor if it exists
fun exists-con-creator(candidates: list<typed-arg>, (name, info, _): typed-arg): bool
  val cname = name.new-creator-name
  info.is-infoCon && candidates.any(fn((iargName, _, _)) iargName == cname)


// Resolve an implicit argument fully. This is recursively used with the `chain` of previously resolved implicit names
fun resolve-implicit-arg-ex(allow-disambiguate: bool, allow-unit-fun-val: bool, chain: list<typed-arg>, ctx-name: name-context, rng: range, roots: list<(assumption/name-info -> bool, name)>): _ implicit-select
  val candidates = roots.flatmap(fn((filter, name)) lookup-implicit-arg(allow-unit-fun-val, filter, name, ctx-name, rng))
  val candidates2 = candidates.filter(!candidates.exists-con-creator(_))
  fun sort-candidates(unsorted: list<typed-arg>)
    // find for each candidate which further implicits need to be resolved
    val icandidates = unsorted.map(implicits-to-resolve(ctx-name, _))
    // now we can sort them according to their cost 
    fun cost(((name, info, _), iargs))
      (0 - (iarg-scope-depth(name, info)), // inner scopes first
        iargs.list/length) // least further implicits arguments first
    icandidates.sort(fn(x, y) x.cost.cmp(y.cost).is-lt)
  val sorted = candidates2.sort-candidates
  resolve-uniquely(allow-disambiguate, chain, ctx-name, rng, None, sorted)

// Resolve the best candidate for an implicit parameter
fun resolve-uniquely(allow-disambiguate: bool, chain: list<typed-arg>, ctx-name: name-context, rng: range, current: implicit-select, others: list<(typed-arg, list<(name, ktype)>)>): _ implicit-select
  match (current, others) 
    (_, []) -> current // nothing further to explore
    (Amb(ambs as Cons(_, Cons(_, _))), _) -> //once we are ambiguous with 2 or more (possible) solutions, we don't need to explore further options
      val extra = others.map(_.fst.to-implicit-arg([])) // include all remaining potential candidates in the error message?
      Amb(ambs ++ extra)
    (Found(found), Cons(((qname, info, _), _))) | allow-disambiguate && found.ia-scope-depth > iarg-scope-depth(qname, info) ->
      // if we can disambiguate, the inner scope is always preferred (assuming sorted candidates)
      Found(found)
    (_, Cons(next as ((qname, _, rho), ipars), candidates)) ->
      if !infer-env.allowInfiniteChains && !is-decreasing-chain(chain, ctx-name, qname, rho) then
        val iarg = next.fst.to-implicit-arg(ipars.map(fn((pname, _)) (pname, empty-implicit-arg)))
        val sel = Infty(iarg)
        resolve-uniquely(allow-disambiguate, chain, ctx-name, rng, current.merge(sel), candidates)
      elif chain.length > resolve-max-chain-depth then 
        // TODO: Trace
        val sels = candidates.map(fn(c) Infty(c.fst.to-implicit-arg([])))
        sels.foldr(None, merge)
      else
        val sel = resolve-implicit-parameters(allow-disambiguate, chain, rng, next)
        resolve-uniquely(allow-disambiguate, chain, ctx-name, rng, current.merge(sel), candidates)

// Resolve recursively any further required implicit parameters
fun resolve-implicit-parameters(allow-disambiguate: bool, chain: list<typed-arg>, rng: range, current as ((name, info, rho), ipars): (typed-arg, list<(name, ktype)>)): _ implicit-select
  val new-chain = Cons(current.fst, chain)
  fun resolve(acc: list<(name, implicit-arg)>, pars: list<(name, ktype)>): _ implicit-select
    match pars
      [] -> Found(ImplicitArg(name, info, rho, acc.reverse))
      Cons(par, pars') -> 
        val sel = resolve-implicit-parameter(allow-disambiguate, new-chain, rng, par)
        match sel 
          Found(iarg) -> // keep resolving
            resolve(Cons((par.fst, iarg), acc), pars')
          _ -> // give up early if we cannot resolve a parameter
            sel.map fn(iarg)
              ImplicitArg(name, info, rho, acc.reverse ++ [(par.fst, iarg)] ++ pars.map(fn((pname, _)) (pname, empty-implicit-arg)))
  resolve([], ipars)

// recursively resolve an implicit parameter
fun resolve-implicit-parameter(allow-disambiguate: bool, chain: list<typed-arg>, rng: range, (pname, ptp): (name, ktype)): _ implicit-select
  // recursively resolve an implicit parameter
  val (_, pname-expr) = pname.split-implicit-param-name
  val newctx = ptp.implicit-type-context
  resolve-implicit-arg-ex(allow-disambiguate, True, // allow unit val
                   chain, newctx, rng.end-of-range, // use end of range to deprioritize with hover info
                   [(is-info-val-fun-ext, pname-expr)])

// Find for an typed argument if it needs further implicits to be solved
fun implicits-to-resolve(ctx-name: name-context, targ as (_, _, rho): typed-arg): _ (typed-arg, list<(name, ktype)>)
  match split-fun-scheme(rho)
    Just((_, pars, _, _)) -> 
      fun implicits-of(ipars: list<(name, ktype)>): list<(name, ktype)>
        // only return implicits that were not already given explicitly by the user (in `named`)
        val (fixed, optional, implicits) = ipars.split-optional-implicit
        val already-given = match ctx-name
          CtxFunTypes(_, fixedArgs, namedArgs, _) -> 
            val namedAsFixed = implicits.take(fixedArgs.length - fixed.length - optional.length).map(fst) 
            namedAsFixed ++ namedArgs.map(fst)
          CtxFunArgs(_, n, namedArgs, _) ->
            val namedAsFixed = implicits.take(n - fixed.length - optional.length).map(fst)
            namedAsFixed ++ namedArgs
          _ -> []
        implicits.filter fn((iname, _))
          val (pname, _) = iname.split-implicit-param-name
          !already-given.any(_ == pname)
      if pars.any(is-optional-or-implicit) then // recursively resolve further required implicits
        (targ, implicits-of(pars))
      else
        (targ, [])
    _ -> (targ, [])

// Have we previously tried to derive this parameter?
fun is-decreasing-chain(chain: list<typed-arg>, ctx-name: name-context, qname: name, tp: ktype)
  // Note: pname and qname are fully qualified resolved names with their instantiated types
  //   pname=qname : forall as. t           e.g. list/show : (xs : list<a>, ?show : a -> string ) : string
  //
  // This means ptp and tp are instantiations of the same type scheme (and only differ in substitution):
  //   ptp = t[as:=ts1]  tp = t[as:=ts2]
  //
  // We can now put a decreasing measure on those types to see if the instantiation is getting smaller
  // which ensures termination (but also prevents some programs to be accepted even though finite derivations exist (see `test/overload/wrong/blowup6.kk`))
  // Our current measure is the number of constructors in the types of the implicit parameters.
  // (and an even more precise one would be the size of each instantiated type variable used in implicits in a particular lexical order)
  match filter(chain, fn((pname, _, _)) pname == qname) // find only matching definition in the chain
    [] -> True // never visited before
    prevtps -> 
      if prevtps.length < decreasing-within then True // Not enough to decide yet (we want to be able to grow a bit at the beginning)
      else 
        val limited = prevtps.take(decreasing-within) // the last *k* elements in the same partition.
        tp.weight < limited.map(fn((_, _, t)) t.weight).maximum(0) // we want the instantiated type to "smaller" than any previous one (i.e. at least smaller than the maximum)
  
fun weight(tp: ktype): div int 
  match split-fun-scheme(tp)
    Just((_, pars, _, _)) -> 
      val (_, _, implicits) = pars.split-optional-implicit
      implicits.weight-params
    _ -> 0

fun weight-type(tp: ktype): div int 
  match tp
    TForAll(_, t) -> t.weight-type
    TFun(tpars, teff, tres) -> tpars.weight-params + teff.weight-type + tres.weight-type
    TApp(t, args) -> t.weight-type + args.map(weight-type).sum
    TSyn(_, _, t) -> t.weight-type
    TCon() -> 1
    _ -> 0

fun weight-params(pars: list<(name, ktype)>): div int
  pars.map(_.snd.weight-type).sum

///////////////////////////////////////////////////////////
// Looking up application names and implicit names
///////////////////////////////////////////////////////////

fun lookup-implicit-arg(allow-unit-fun-val: bool, info-filter: (assumption/name-info -> bool), name: name, ctx-name: name-context, rng: range): _ list<typed-arg>
  val candidates0 = lookup-names(info-filter, name, ctx-name, rng)
  val candidates = match ctx-name
        // for implicits we also allow conversion unit functions for values
        // if `expect` is a type variable we may need to remove duplicate candidates here.
        CtxType(expect) | allow-unit-fun-val && !expect.is-fun ->
          val candidates1 = lookup-names(info-filter, name, CtxFunTypes(False, [], [], Just(expect)), rng)
          (candidates0 ++ candidates1).nub-by(fn((_, info1, _), (_, info2, _)) info1.cname == info2.cname)
        _ -> candidates0
  // add implicit constraints
  val iargs = match ctx-name
    CtxType(expect) -> 
      val mbiarg = check-implicit-constraint(name, expect, rng, rng)
      match mbiarg
        Just(iarg) -> [iarg]
        Nothing -> []
    _ -> []
  candidates ++ iargs

///////////////////////////////////////////////////////////
// Lookup names
///////////////////////////////////////////////////////////

pub fun lookup-fun-name(name: name, mb-type: maybe<(ktype, range)>, rng: range)
  match lookup-name-ctx(is-infoFun, name, maybe-r-to-context(mb-type), rng)
    Nil -> Nothing
    [(qname, info)] -> Just((qname, info.scheme, info))
    amb -> 
      inf-error(rng, "identifier".text |+| name.pp-name |+| "cannot be resolved".text
       |.| pp-ambiguous("qualify the name to disambiguate it", amb))

fun cmp-scope-depth((_, info1): (name, assumption/name-info), (_, info2): (name, assumption/name-info)): order
  cmp(info1.scope-depth, info2.scope-depth)    

pub fun lookup-name-ctx(info-filter: (assumption/name-info -> bool), name: name, ctx-name: name-context, rng: range): _ list<(name, assumption/name-info)>
  val candidates0 = lookup-names(info-filter, name, ctx-name, rng)
  val candidates = candidates0.map(fn((qname, info, _)) (qname, info))
  fun filter-inner-scopes(cands: list<(name, assumption/name-info)>): list<(name, assumption/name-info)>
    fun filter(x, acc, xs)
      match xs
        [] -> Cons(x, filter-inner-scopes(acc.reverse.pretend-decreasing))
        Cons(y, ys) -> 
          match cmp-scope-depth(x, y)
            Lt -> filter(y, [], ys) // continue with y, drop x and acc 
            Eq -> filter(x, acc, ys) // drop y
            Gt -> filter(x, Cons(y, acc), ys)
    match cands
      Cons(x, xs) -> filter(x, [], xs)
      [] -> []
  match candidates
    [] -> candidates
    [_] -> candidates
    _ -> 
      match filter-inner-scopes(candidates)
        [candidate] -> [candidate]
        _ -> candidates

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

pub fun pp-implicit-arg(iarg: implicit-arg): _ doc
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

pub fun pp-implicit-assign(pfx: string, pname: name, iarg: implicit-arg, shorten: bool): _ doc
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
pub fun to-implicit-arg-expr(iarg: implicit-arg, xrange: range): _ syntax/syntax/expr<ktype>
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
          (Just((pname, range)), to-implicit-arg-expr(arg, range.end-of-range))
        
        val body = App(syntax/Var(iarg.name, False, range), args-fixed ++ args-implicit, range)
        if name-fixed.is-nil then body
        else
          val binders = name-fixed.map fn(nm)
            ValueBinder(nm, Nothing, Nothing, range, range)
          Lam(binders, body, False, range)
      _ -> failure/fail("compiler/type/infer-effect: to-implicit-arg-expr: illegal type for implicit? " ++ range.show ++ ", " ++ iarg.name.show)

pub fun pp-typed-arg(targ: typed-arg): _ doc
  val (nm, _, tp) = targ
  pp-param((nm, tp))

pub fun to-implicit-arg(targ: typed-arg, iargs: list<(name, implicit-arg)>): implicit-arg
  val (nm, info, rho) = targ
  ImplicitArg(nm, info, rho, iargs)

// We can find a unique solution, or none, or surely ambiguous.
// The `Infty` tracks infinite chains, while `Amb` ambiguous ones. 
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

fun pp-select(sel: implicit-select): _ doc
  match sel
    None -> "None".text
    Found(iarg) -> "Found".text |+| iarg.pp-implicit-arg
    Infty(iarg) -> "Infty".text |+| iarg.pp-implicit-arg
    Amb(xs) -> "Amb".text |+| xs.map(pp-implicit-arg).list

/////////////////////////////////////
// Variable Name Resolution
/////////////////////////////////////

// lookup names in the local and global scope that match the given name context
// Returns also an instantiated rho required to match the name context
fun lookup-names(info-filter: (assumption/name-info) -> bool, name: name, nctx: name-context, rng: range): _ list<(name, assumption/name-info, rho)>
  val matches = 
    match lookup-local-name(info-filter, name)
      Right(local) -> [local] // a local name that matches exactly was found; use it always
      Left(locals) -> 
        // otherwise consider globals as well besides the locally qualified locals that matched
        // todo: should we prioritize local locally qualified names when disambiguating?
        val globals = lookup-global-name(info-filter, name) 
        locals ++ globals
  filter-match-name-context-ex(matches, nctx, rng)

pub fun lookup-local-name(info-filter: (assumption/name-info) -> bool, name: name): _ either<list<(name, assumption/name-info)>, (name, assumption/name-info)>
  if name.is-implicit-constraint-evidence then 
    get-iconstraints-gamma().inf-gamma/lookup(name)
  else 
    match infer-env.inf-gamma.lookup-ex(info-filter, name)
      Left(all) -> Left(all.subst)
      Right((n, ni)) -> Right((n, ni.subst))

fun lookup-global-name(info-filter: (assumption/name-info) -> bool, name: name): _ list<(name, assumption/name-info)>
  val find = fn(nm) gamma-lookup(infer-env.gamma, nm).filter(fn((_, info)) info-filter(info))
  match infer-env.importsMap.expand(name)
    Right((name', _)) -> 
      match find(name') // First look by aliased import name
        Nil -> find(name) // If not found, look by original import name
        ni -> ni
    Left([]) -> find(name) // If no import alias, look by original name
    Left() -> 
      // If multiple aliases match, ideally we look through all of them
      // However, that runs into issue #719 where the original module name is not included in `names`
      find(name)

fun filter-match-name-context(matches: list<(name, assumption/name-info)>, nctx: name-context, rng: range): _ list<(name, assumption/name-info)>
  filter-match-name-context-ex(matches, nctx, rng).map(fn((nm, info, _)) (nm, info))

fun filter-match-name-context-ex(matches: list<(name, assumption/name-info)>, nctx: name-context, rng: range): _ list<(name, assumption/name-info, rho)>
  fun match-type(ex: ktype, (nm, info): (name, assumption/name-info)): _ list<(name, assumption/name-info, rho)>
    val free = free-in-gamma()
    match run-unify({subsume(rng, free, ex, info.typ)})
      (Right((rho, _, _)), _) -> [(nm, info, rho)]
      _ -> []
  fun match-named-args(matchSome: bool, n: int, namedPars: list<name>, mbResTp: maybe<ktype>, (nm, info): (name, assumption/name-info)): _ list<(name, assumption/name-info, rho)>
    val free = free-in-gamma()
    match run-unify({match-named(matchSome, rng, free, info.typ, n, namedPars, mbResTp)})
      (Right(rho), _) -> [(nm, info, rho)]
      _ -> []
  fun match-args(matchSome: bool, fixedTypes: list<ktype>, namedPars: list<(name, ktype)>, mbResTp: maybe<ktype>, (nm, info): (name, assumption/name-info)): _ list<(name, assumption/name-info, rho)>
    val free = free-in-gamma()
    match run-unify({match-arguments(matchSome, rng, free, info.typ, fixedTypes, namedPars, mbResTp)})
      (Right(rho), _) -> [(nm, info, rho)]
      _ -> []
  
  match nctx 
    CtxNone -> matches.map(fn((nm, info: assumption/name-info)) (nm, info, info.typ))
    CtxType(expect) -> matches.map(match-type(expect, _)).concat
    CtxFunArgs(partial, n, namedPars, mbResTp) -> 
      val mss1 = matches.map(match-named-args(partial, n, namedPars, mbResTp, _)).concat
      val mss2 = match mbResTp
        Just(tp) | partial && n == 0 -> matches.map(match-type(tp, _)) // for partial constructor like `Nil`
        _ -> []
      (mss1 ++ mss2.concat)
    CtxFunTypes(partial, fixed, namedPars, mbResTp) -> 
      matches.map(match-args(partial, fixed, namedPars, mbResTp, _)).concat

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

// A context where some fixed arguments have been inferred
pub fun fixed-context(propagated: maybe<(ktype, range)>, fixed-resolved: list<(int, fixed-arg)>, fixed-count: int, namedArgs: list<name>): _ name-context
  fun tvars(i: int)
    list(1, i).map(fn(_) fresh-star())
  fun fill(j, l: list<(int, fixed-arg)>)
    match l
      [] -> tvars(fixed-count - j)
      Cons((i,(_, tp, _, _)), rst) -> 
        val post = fill(i + 1, rst)
        val pre = tvars(i - j)
        val stp = tp.subst()
        (pre ++ [stp] ++ post)
  val fargs = fill(0, fixed-resolved.sort(fn((i1, _), (i2, _)) i1 < i2))
  val nargs = namedArgs.map(fn(nm) (nm, fresh-star()))
  CtxFunTypes(fixed-count > fixed-resolved.length, fargs, nargs, propagated.map(fst))

    
  

pub fun pp-name-context(nctx: name-context): _ doc
  match nctx
    CtxNone -> "_".text
    CtxType(tp) -> tp.pp-type
    CtxFunArgs(matchSome, n, names, mbResTp) ->
      val args = list(1, n, fn(_) -> "?".text) ++ names.map(fn(nm) nm.pp-name |.| ": ?".text) ++ (if matchSome then ["...".text] else [])
      args.tupled |+| "->".text |+| mbResTp.map(pp-type).default("_".text)
    CtxFunTypes(matchSome, fixed, namedArgs, mbResTp) ->
      val args = fixed.map(pp-type) ++ namedArgs.map(pp-param) ++ (if matchSome then ["...".text] else [])
      args.tupled |+| "->".text |+| mbResTp.map(pp-type).default("_".text)

pub fun pp-name-ctx(nm: name, nctx: name-context): _ doc
  nm.pp-name |+| ":".text |+| pp-name-context(nctx)


// A fixed argument that has been inferred
pub alias fixed-arg = (range, ktype, keffect, core/core/expr)

pub fun pure-match-shape-name-ctx(ctx1 : name-context, ctx2 : name-context) : _ bool
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


pub fun pp-tvs(tvs: tvs): _ doc
  tvs.list.map(pp-typevar).list

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

pub fun check-casing-overlap(rng: range, nm: name, qname: name, info: assumption/name-info): _ ()
  match case-overlaps(nm, qname, info)
    Just(qname1) ->
      val env = infer-env
      inf-error(rng, info.element.text |+| nm.unqualify.pp-name |+| "is already in scope with a different casing as".text |+| env.importsMap.get-alias(qname1).pp-name)
    Nothing -> ()

pub fun check-casing(rng: range, nm: name, qname: name, info: assumption/name-info): _ ()
  match case-overlaps(nm, qname, info)
    Just(qname1) ->
      val env = infer-env
      inf-error(rng, info.element.text |+| nm.unqualify.pp-name |+| "should be cased as".text |+| env.importsMap.get-alias(qname1).pp-name)
    Nothing -> ()

pub fun pp-amb-docs(docs: list<doc>)
  match docs
    Nil -> "...".text
    _ -> 
      val cut = docs.take(10) ++ (if docs.length > 10 then ["...".text] else [])
      align(vcat(cut))

pub fun pp-ambiguous(hint: string, infos: list<(name, assumption/name-info)>): _ doc
  vcat([". Possible candidates: ".text, pp-candidates(infos)] ++
       (if hint.is-empty then [] else ["hint: ".text |+| hint.text]))


pub fun pp-candidates(nameInfos: list<(name, assumption/name-info)>): _ doc
  val env = infer-env
  val modName = env.contxt
  val n = 10
  val sorted = nameInfos.sort fn((nm1, info1), (nm2, info2))
    if nm1.qualifier == modName && nm2.qualifier != modName then True
    else if nm1.qualifier != modName && nm2.qualifier == modName then False
    else cmp(!info1.scheme.is-rho, !info2.scheme.is-rho).is-lt
  
  val (defs, rest) = sorted.split(n)
  val rows = defs.map fn((nm, info)) pp-name-info(nm, info)
  val finalRows = 
    if rest.is-nil then rows
    else rows ++ [("...".text, "or".text |+| rest.length.show.text |+| "other definitions".text)]
  finalRows.table.align

pub fun pp-implicits-hint(nameInfos: list<(name, assumption/name-info)>): _ list<(doc, doc)>
  val candidateMissingImplicits = nameInfos.map fn((_, info))
    info.scheme.requires-implicits.map(fst)
  
  val allMissingImplicits = candidateMissingImplicits.concat.linear-set
  val allRequiredMissingImplicits = allMissingImplicits.list.filter fn(imp)
    candidateMissingImplicits.all(fn(missing) missing.any(fn(m) m == imp))
  
  match allRequiredMissingImplicits
    Nil -> []
    _ -> [("missing implicits".text, allRequiredMissingImplicits.map(pp-name).hsep),
          ("hint".text, "ensure implicit functions are defined prior to functions that require them".text)]

pub fun pp-name-info(nm: name, info: assumption/name-info): _ (doc, doc)
  val env = infer-env
  (env.importsMap.get-alias(nm).pp-name, info.scheme.pp-type)

pub fun pp-or(names : list<name>) : _ doc
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
  contxt: name // module name
  currentDefNames: list<name>
  namedLam: bool
  returnAllowed: bool
  inLhs: bool
  hiddenTermDoc: maybe<(range, doc)>
  localDepth: int
  allowInfiniteChains: bool
  niceNames: name-map<doc>
  importsMap: import-map
  inf-gamma: inf-gamma
  gamma: gamma

pub fun current-def-name()
  match infer-env.currentDefNames
    Cons(n, _) -> n
    Nil -> nil

pub effect infer-state
  fun hole-allowed(): bool
  fun use-hole(): ()

pub fun module-name()
  infer-env.contxt

fun in-hidden-term-doc(): infer-env bool
  infer-env.hiddenTermDoc.is-just

fun qualify-name(nm: name)
  qualify(module-name(), nm)
pub fun find-data-info(nm: name): _ data-info
  newtypes-lookup-any(nm).expect("type/infer-effect/find-data-info: unknown type: " ++ nm.show ++ "\nin: " ++ newtypes-list().show)
fun lookup-inf-name(nm: name)
  match infer-env.inf-gamma.inf-gamma/lookup(nm.unqualify) 
    Right((qname, info)) -> Just((qname, info.scheme))
    Left([]) -> Nothing
    Left(infos) -> failure/fail("infer-effect/lookup-inf-name: ambiguous local? " ++ current-def-name().show ++ ": " ++ nm.show ++ ":\n" ++ infos.show)
// TODO: Remove, not needed anymore
fun create-canonical-name(nm-ctx: name, gamma: gamma, qname: name)
  qname

fun get-local-vars(): _ list<(name, ktype)>
  infer-env.inf-gamma.inf-gamma/list.filter(fn((_, info)) info.is-type-local-var)

pub effect val scope-depth: int
pub effect val local-depth: int

pub effect val ctxt : infer-context
pub alias infer = <pretty-eff, ctxt, infer-state, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, synonyms-eff, newtypes-eff, unify, unique>;

fun free-in-gamma()
  (sub/(|->)(get-subst(), infer-env.inf-gamma.inf-gamma/list.map(snd))).free-type-vars

fun with-hole-allowed(allowed0: bool, action: () -> _ a): _ a
  var allowed := allowed0
  with override 
    fun hole-allowed() allowed
    fun use-hole() allowed := False
  action()

pub fun hidden-term-doc(rng: range, doc: doc, action: () -> _ a): _ a
  with override val infer-env = infer-env(hiddenTermDoc = Just((rng, doc)))
  action()
pub fun disallow-hole(action: () -> _ a): _ a
  with-hole-allowed(False, action)
// Returns the value of the action and whether a hole was used
pub fun allow-hole(action: () -> _ a): _ (a, bool)
  with-hole-allowed(True, {(action(), !hole-allowed())})
pub fun with-context(nm: name, action: () -> _ a): _ a
  with override val infer-env = infer-env(contxt = nm)
  action()
pub fun with-lhs(action: () -> _ a): _ a
  with override val infer-env = infer-env(inLhs = True)
  action()
pub fun return-allowed(allowed: bool, action: () -> _ a): _ a
  with override val infer-env = infer-env(returnAllowed = allowed)
  action()
pub fun allow-return(action: () -> _ a): _ a
  return-allowed(True, action)
pub fun no-allow-return(action: () -> _ a): _ a
  return-allowed(False, action)
pub fun with-scope(action: () -> _ a): _ a
  with override val scope-depth = infer-effect/scope-depth + 1
  action()
pub fun with-local-scope(action: () -> _ a): _ a
  with override val local-depth = local-depth + 1
  action()
pub fun with-no-local-scope(action: () -> _ a): _ a
  with override val local-depth = 0
  action()
pub fun with-def-name(nm: name, action: () -> _ a): _ a
  with override val infer-env = infer-env(currentDefNames = Cons(nm, infer-env.currentDefNames), namedLam = !(nm.is-nil || nm.is-wildcard) )
  action()

pub effect val infer-env: inferEnv
pub fun with-env(env: inferEnv, action: () -> _ a): _ a
  with override val infer-env = env
  action()

pub fun infer-eff(action)
  with override
    fun inf-error(rng: range, msg: doc)
      add-range-info(rng, RIError(msg))
      failure/fail(msg.show ++ " at " ++ rng.show)
    fun inf-warning(rng: range, msg: doc)
      add-range-info(rng, RIWarning(msg))
      ()
  action()

pub fun no-range-info(f)
  with override 
    fun get-range-map() get-range-map()
    fun add-range-info(rng: range, ri: range-info) ()
  f()

pub effect infer-eff 
  fun inf-error(rng: range, msg: doc): a
  fun inf-warning(rng: range, msg: doc): ()

fun trace-def-doc(f: () -> _ doc): _ ()
  val names = infer-env.currentDefNames
  with trace-doc 
  hcat(intersperse(names.map(pp-name), ".".text)) |+| ":".text |+| f()


//////////////////////////////////////
// Unify helpers
//////////////////////////////////////

fun nofail-unify(action: () -> _ a, ?kk-file-line: string): _ a
  match run-unify(action)
    (Right(v), sub) -> 
      add-sub(sub)
      v
    (Left(err), sub) -> 
      add-sub(sub)
      failure/fail("should never fail!: " ++ err.show ++ " " ++ kk-file-line)

fun do-unify(action)
  match run-unify(action)
    (Right(x), sub) -> 
      add-sub(sub)
      Right(x)
    (Left(err), sub) -> 
      add-sub(sub)
      Left(err)

pub fun infer-unify(rng: range, expected: ktype, tp: ktype): _ ()
  val (sexp, stp) = (expected.subst, tp.subst)
  match do-unify({ unify(expected, tp) })
    Left(err) -> infer-unify-error(rng, err, sexp, stp)
    Right(_) -> ()

pub fun infer-unifies(tps: list<(range, ktype)>): _ ktype
  match tps
    Cons((_, tp), Nil) -> tp
    Cons((rng1, tp1), Cons((rng2, tp2), rst)) -> 
      val r = rng1.combine(rng2)
      infer-unify(r, tp1, tp2)
      val tp = tp1.subst
      infer-unifies(Cons((r, tp), rst))

pub fun infer-subsume(rng: range, expected: ktype, tp: ktype): _ (ktype, core/core/expr -> pure core/core/expr)
  val free = free-in-gamma()
  val (sexp, stp) = (expected.subst, tp.subst)
  match do-unify({ subsume(rng, free, sexp, stp) })
    Left(err) -> 
      infer-unify-error(rng, err, sexp, stp)
      (expected, fn(e) e) // never reached
    Right((t, _, coref)) -> (t, coref)

pub fun check-skolem-escape(rng: range, tp: ktype, mhint: maybe<doc>, skolems: list<type-var>, extra-free: tvs): _ ()
  match skolems
    Nil -> ()
    _ -> 
      val free = free-in-gamma() + extra-free
      if free.disjoint(skolems.linear-set) then
        val stp = tp.subst
        val escaped = skolems.filter(fn(skm) free.member(skm))
        val hintDocs = match mhint
          Just(h) -> [("hint".text, h)]
          Nothing -> [("hint".text, "give a higher-rank type annotation to a function parameter?".text)]
        term-error(rng, "abstract type(s) escape(s) into the context".text, stp, hintDocs)

pub fun with-skolemized(rng: range, tp: ktype, mhint: maybe<doc>, action: (ktype, list<type-var>) -> infer (a, tvs)): _ a
  val (xvars, xrho, _) = skolemize-ex(tp, rng)
  val (x, extra-free) = action(xrho, xvars)
  check-skolem-escape(rng, tp, mhint, xvars, extra-free)
  x

pub fun occurs-in-context(tv: type-var, extraFree: tvs): _ bool
  val free = free-in-gamma() + extraFree
  free.member(tv)



//////////////////////////////////////
// Unification Errors
//////////////////////////////////////

fun get-term-doc(term: string, rng: range): _ (doc, doc)
  val env = infer-env
  match env.hiddenTermDoc
    Just((_, doc)) -> 
      ("implicit".text |+| term.text, doc)
    Nothing -> 
      (term.text, doc-from-range(rng))

fun infer-unify-error(rng: range, err: unify-error, xtp1: ktype, xtp2: ktype): _ ()
  match err
    NoMatchEffect(eff1, eff2) ->
      infer-unify-error(rng, NoMatchType, eff2, eff1)
    _ ->
      val free = free-in-gamma()
      val tp1: ktype = normalizeX(False, free, xtp1.subst)
      val tp2: ktype = normalizeX(False, free, xtp2.subst)
      with no-full-names
      with val pp-env = if err.is-noMatchKind then pp-env(showKinds=True) else pp-env

      // Get context range and extra info
      val (rangeContext, extra) = match ctxt
        Check(msg, rng2) -> (rng2, [("because".text, msg.text)])
        Infer(rng2) -> (rng2, [])
      
      // Get term documentation
      val termInfo = get-term-doc("term", rng)
      // Pretty print the types
      val [nice1, nice2]= nice-types([tp1, tp2])
      
      
      // Determine if we're dealing with effects or types
      val name-type = if tp1.kind == kindEffect then "effect" else "type"
       
      // Determine match messages
      val nomatch = match err
        NoSubsume -> [("is less general than".text, nice1)]
        NoArgMatch(_, _) -> []
        _ -> [("expected ".text |.| name-type.text, nice1)]
      
      // Determine main message and hints
      val (message, hint) = match err
        NoMatchType -> (name-type ++ "s do not match", [])
        NoMatchKind -> ("kinds do not match", [])
        NoMatchSkolem(kind) ->
          if extra.is-empty then
            ("abstract types do not match", 
              [("hint".text, if kind == kindHeap || kind == kindScope 
                then "a local variable or reference escapes its scope?".text
                else "an higher-rank type escapes its scope?".text)])
          else
            ("abstract types do not match", [])
        NoSubsume -> 
          ("type is not polymorphic enough", 
            [("hint".text, "give a higher-rank type annotation to a function parameter?".text)])
        Infinite ->
          ("types do not match (due to an infinite type)",
            [("hint".text, "give a type to the function definition?".text)])
        NoMatchEffect(_, _) -> ("effects do not match", [])
        NoArgMatch(n, m) ->
          if m < 0 then
            ("only functions can be applied", [])
          else
            val exp-str = (if n > m then "few" else "many")
            val arg-str = if n == 1 then "argument" else "arguments"
            val hint-msg = "expecting " ++ n.show ++ " " ++ arg-str ++ " but has been given " ++ m.show
            ("application has too " ++ exp-str ++ " arguments",
              [("hint".text, hint-msg.text)])
      
      // Build the error message table
      val rows = 
        [("context".text, doc-from-range(rangeContext)),
         termInfo,
         ("inferred ".text |.| name-type.text, nice2)]
        ++ nomatch ++ extra ++ hint
      
      // Report the error
      inf-error(rng, message.text |-| table(rows))


pub fun type-error(ctxRng: range, rng: range, message: doc, xtp: ktype, extra: list<(doc,doc)>): _ ()
  val free = free-in-gamma()
  val tp: ktype = normalizeX(False, free, xtp.subst)
  val termInfo = get-term-doc("term", rng)
  val rows = 
    [("context".text, doc-from-range(ctxRng)),
     termInfo,
     ("inferred type".text, nice-type(tp))]
    ++ extra
  inf-error(rng, message |-| table(rows))

pub fun context-error(ctxRng: range, rng: range, message: doc, extra: list<(doc,doc)>): _ ()
  val termInfo = get-term-doc("term", rng)
  val rows = 
    [("context".text, doc-from-range(ctxRng)),
     termInfo]
    ++ extra
  inf-error(rng, message |-| table(rows))

pub fun term-error(rng: range, message: doc, tp: ktype, extra: list<(doc,doc)>): _ ()
  val termInfo = get-term-doc("term", rng)
  val rows = 
    [termInfo,
     ("inferred type".text, nice-type(tp))]
    ++ extra
  inf-error(rng, message |-| table(rows))


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

alias can-resolve-constraint = (tvs, implicit-constraint) -> <pretty-eff, ctxt, infer-state, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, synonyms-eff, newtypes-eff, unify, unique> bool
alias resolve-constraint = (tvs, implicit-constraint) -> <pretty-eff, ctxt, infer-state, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, synonyms-eff, newtypes-eff, unify, unique> (core/core/expr, ktype)
alias check-constraint = (name, ktype) -> maybe<(can-resolve-constraint, resolve-constraint)>

div type ic-params 
  ICParams(
    nm: name,
    tp: ktype,
    rngCtx: range,
    rng: range
  )

pub div effect def-infer-effect
  fun get-iconstraints(): list<implicit-constraint>
  fun get-iconstraints-gamma(): inf-gamma
  // add a new implicit constraint with a fresh name (to be solved at generalization time)
  fun add-iconstraint(ic: ic-params, 
       can-solve: (tvs, implicit-constraint) -> <pretty-eff, ctxt, infer-state, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, synonyms-eff, newtypes-eff, unify, unique> bool, 
       resolve: (tvs, implicit-constraint) -> <pretty-eff, ctxt, infer-state, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, synonyms-eff, newtypes-eff, unify, unique> (core/core/expr, ktype)): (name, assumption/name-info, ktype)
  fun solve-iconstraint(nm : name, tp : ktype): ()

fun implicit-constraint-type(ic: implicit-constraint): infer ktype
  val ig = infer-env.inf-gamma
  match ig.inf-gamma/lookup(ic.evidence) 
    Right((_, nameInfo)) -> 
      nameInfo.scheme.subst // unlike icType, this may have substituted skolems
    _ -> failure/fail("type/infer-monad/implicit-constraint-type: unknown constraint " ++ ic.evidence.show)

fun check-heap-div-constraint(nm: name, tp: ktype): maybe<(can-resolve-constraint, resolve-constraint)>
  match tp.expand-syn
    TApp(TCon(tc), [_, _, _]) | tc.name == nameTypeHeapDiv ->
      Just((can-resolve-heap-div-constraint, resolve-heap-div-constraint))
    _ -> Nothing

fun can-resolve-heap-div-constraint(free: tvs, ic: implicit-constraint): infer bool
  val icTp = implicit-constraint-type(ic)
  match icTp.expand-syn //  expand here again (should never fail!) so we get skolem substitutions
    TApp(TCon(_), [tpHeap, tpVal, _tpEff]) ->
      val never = heap-never-contained-in(free, tpHeap, tpVal)
      val always = heap-always-contained-in(free, tpHeap, tpVal)
      never || always
    _ -> False

fun resolve-heap-div-constraint(free: tvs, ic: implicit-constraint): infer (core/core/expr, ktype)
  // val sic = ic.subst // TODO: This isn't used?
  val tp = implicit-constraint-type(ic)
  match tp.expand-syn // expand here again (should never fail!) so we get skolem substitutions
    TApp(TCon(_), [tpHeap, tpVal, tpEff]) ->
       val maydiv = if heap-never-contained-in(free, tpHeap, tpVal) then False // not (tvsIsEmpty (ftv stp)))) -- conservative guess...
                    else
                      // add div effect to tpEff
                      val tv = fresh-effect() 
                      val divEff = effect-extend(typeDivergent, tv)
                      with val ctxt = Infer(ic.contxt)
                      infer-unify(ic.range, tpEff, divEff)
                      True
       val nameToFind = if maydiv then nameEvHeapDiv else nameEvHeapNoDiv
       val (cname, _, cinfo) = resolve-name-ex(is-infoCon, Nothing, if maydiv then nameEvHeapDiv else nameEvHeapNoDiv, CtxNone, ic.contxt, ic.range)
       val seff = tpEff.subst
       val stp = tp.subst
       val ev = TypeApp(cinfo.core-expr(cname), [tpHeap, tpVal, seff])
       (ev, stp)
    _ -> failure/fail("resolve-heap-div-constraint: invalid type")


val implicit-constraints : list<(name, check-constraint)> = [(nameHeapDiv, check-heap-div-constraint)]

fun check-implicit-constraint(name: name, tp: ktype, ctx-range: range, rng: range): _ maybe<typed-arg>
  match implicit-constraints.lookup(name)
    Just(check) -> match check(name, tp)
      Just((can-resolve, resolve)) -> 
        val iarg = add-iconstraint(ICParams(name, tp, ctx-range, rng), can-resolve, resolve)
        Just(iarg)
      Nothing -> Nothing
    Nothing -> Nothing

// TODO: incorporate generalization into here?
// This is essentially scope-implicit-constraints
fun scope-implicit-constraints(action: () -> _ a): _ a
  var iconstraints : list<implicit-constraint> := []
  var iconstraints-gamma := inf-gamma/empty
  with override
    return(x) if iconstraints.is-empty then x else throw("unresolved implicit constraints: " ++ pp-constraints(iconstraints).show)
    fun get-iconstraints() iconstraints.subst(list/substitute) 
    fun get-iconstraints-gamma() iconstraints-gamma.subst // apply skolem substitution to unresolved implicit constraints
    fun add-iconstraint(ic: ic-params, canSolve, solve) 
      val ICParams(nm, tp, rngCtx, rng) = ic
      val evName = fresh-name("iev")
      val icx = ImplicitConstraint(nm, tp, evName, rngCtx, rng, canSolve : can-resolve-constraint, solve)
      val icNameInfo = create-name-infoX(Public, evName, 2, DefVal, rng, tp, "")
      val iarg = (evName, icNameInfo, tp)
      iconstraints := iconstraints ++ [icx]
      iconstraints-gamma := iconstraints-gamma.extend(evName, icNameInfo)
      iarg
    fun solve-iconstraint(nm : name, tp : ktype)
      iconstraints := iconstraints.remove(fn(ic) ic.name == nm)
  trace-indent(action) 

fun show(ic: implicit-constraint): string
  ic.name.show

fun ic/substitute(sub: sub, ic: implicit-constraint): _ implicit-constraint
  ic(typ = ktype/substitute(sub, ic.typ))
fun ic/free-type-vars(ic: implicit-constraint): div tvs
  ic.typ.free-type-vars
fun ic/free-type-constructors(ic: implicit-constraint): div type-cons
  ic.typ.free-type-constructors


// implicit constraint evidence name?
fun is-implicit-constraint-evidence(name: name): bool
  name.name/starts-with("iev@")

fun pp-constraint(ic: implicit-constraint): _ doc 
  pp-name(ic.evidence) |.| "=".text |+| pp-param((ic.name, ic.typ))

fun pp-constraints(ics: list<implicit-constraint>): _ doc
  ics.map(pp-constraint).list

fun resolve-implicit-constraints(free: tvs, ics : list<implicit-constraint>): infer (core/core/expr -> core/core/expr)
  if ics.is-nil then return id
  val defs = ics.map(_.resolve-one(free))
  fn(core) make-defs-let(defs, core)

fun resolve-one(ic: implicit-constraint, free: tvs): infer core/core/def
  val (ev, tp) = ic.solve.(free, ic)
  solve-iconstraint(ic.evidence, tp)
  make-tdef(TName(ic.evidence, tp), ev)

fun try-resolve-implicit-constraints(close: bool, free: tvs): _ (core/core/expr -> core/core/expr)
  val ics = get-iconstraints()
  fun try-resolve-loop(ics': list<implicit-constraint>, defs: list<core/core/def>): _ (core/core/expr -> core/core/expr)
    match ics'
      Nil -> 
        if defs.is-nil then id 
        else fn(core) make-defs-let(defs.reverse, core)
      Cons(ic, ics-next) ->
        val determined = ic.canSolve.(free, ic)
        val freeTv = ic.fuv.list
        val force = freeTv.is-nil || freeTv.any(fn(tv) !free.member(tv))
        if determined || force || close then
          val (ev, tp) = ic.solve.(free, ic)
          solve-iconstraint(ic.evidence, tp)
          val def = make-tdef(TName(ic.evidence, tp), ev)
          try-resolve-loop(ics-next, Cons(def, defs))
        else
          try-resolve-loop(ics-next, defs)
  try-resolve-loop(ics, [])

fun improve(ctx-range: range, rng: range, close: bool, eff0: keffect, rho0: rho): _ (keffect, rho, core/core/expr -> core/core/expr)
  val seff = eff0.subst
  val srho = rho0.subst
  val free0 = free-in-gamma()
  val (eff1, coref) = 
    // TODO: We need to scope implicit constraints?
    val free = free0.union(srho.free-type-vars)
    val (_, eff1, coref) = isolate(ctx-range, close, free, get-iconstraints(), seff)
    (eff1, coref)
  val nrho = normalizeX(close, free0, srho) // use free0 or otherwise function results are not closed, see `test/type/talpin-jouvelot1/#t1`
  (nrho, eff1, coref)

// Automatically remove heap effects when safe to do so
fun isolate(rng: range, close: bool, free: tvs, ics: list<implicit-constraint>, eff: keffect): _ (list<implicit-constraint>, keffect, core/core/expr -> core/core/expr)
  val (ls, _) = eff.extract-ordered-effect
  match ls.filter(fn(l) [nameTpLocal, nameTpRead, nameTpWrite].any(_ == l.label-name))
    Cons(lab as TApp(_, [TVar(h)])) -> 
      // has heap variable 'h' in it's effect
      val (poly-ics, ics1) = split-hdiv(h, ics)
      val is-local = lab.label-name == nameTpLocal
      if !free.member(h) then 
        // we can isolate, and discharge the poly-ics hdiv predicates
        val tv = fresh-effect()
        if is-local then 
          if infer-effect/scope-depth == 0 then nofail-unify({unify(effect-extend(lab, tv), eff)})
          else ()
        else 
          val syn = synonyms-lookup(nameTpST).unjust
          val bvar = syn.syn-info/params.head.unjust
          val st = new/sub([(bvar, TVar(h))]) |-> syn.tp
          nofail-unify({unify(effect-extend(lab, st), eff)})
        val coref = resolve-implicit-constraints(free,poly-ics)
        val new-eff = tv.subst
        val sics = ics1.subst
        // and try again
        val (ics', eff', coref') = isolate(rng, close, free, sics, new-eff)
        (ics', eff', fn(x) coref'(coref(x)))
      else 
        val coref = try-resolve-implicit-constraints(close,free)
        (ics, eff, coref)
      
    Cons(TApp(_, [TCon(_global)])) -> 
      // maybe has global heap effect 
      val coref = try-resolve-implicit-constraints(close, free)
      (ics, eff, coref)
    _ -> (ics, eff, id) 

// split-hdiv(h,ics') splits constraints 'ics'. Constraints of the form hdiv<h,tp,e> where tp does
// not contain h are returned as the first element, all others as the second. This includes
// constraints where hdiv<h,a,e> for example where a is polymorphic. Normally, we need to assume
// divergence conservatively in such case; however, when we isolate, we know it cannot be instatiated
// to contain a reference to h and it is safe to discharge them during isolation without implying
// divergence. See test\type\talpin-jouvelot1 for an example: fun rid(x) { val r = ref(x) in !r }
fun split-hdiv(htv: type-var, ics: list<implicit-constraint>): _ (list<implicit-constraint>, list<implicit-constraint>)
  match ics 
    Nil -> (Nil, Nil)
    Cons(ic, rest) -> 
      val (ics1, ics2) = split-hdiv(htv, rest)
      val default-res = (ics1, Cons(ic, ics2))
      match ic.typ.expand-syn
        TApp(TCon(tc), [htp, _, _]) | tc.name == nameTypeHeapDiv ->
          match htp.subst.expand-syn
            TVar(tv) | tv == htv -> (Cons(ic, ics1), ics2)
            _ -> default-res
        _ -> default-res

/////////////////////////////////////
// Helpers for gamma
/////////////////////////////////////

fun extend-gamma-core(is-already-canonical: bool, defs: list<core/core/def-group>, act: () -> _ a): _ a
  match defs
    Nil -> act()
    Cons(dg, rest) -> 
      val depth = infer-effect/scope-depth
      val to-add = match dg
        DefRec(dfs) -> dfs.map(_.core-def-infoX(depth))
        DefNonRec(def) -> [def.core-def-infoX(depth)]
      extend-gamma(is-already-canonical, to-add, fn() extend-gamma-core(is-already-canonical, rest, act))

// Specialized for recursive defs where we sometimes get InfoVal even though we want InfoFun? is this correct for the csharp backend?
fun core-def-infoX(def : core/core/def, scope-depth: int)
  match def 
    Def(name, tp, _, _, sort, _, rng, doc) -> 
     (name, create-name-infoX(Public, name, scope-depth, sort, rng, tp, doc))

// extend gamma with qualified names
pub fun extend-gamma(is-already-canonical: bool, defs: list<(name, assumption/name-info)>, act: () -> _ a): _ a
  val e = infer-env
  fun extend(ctxt: name, to-add: list<(name, assumption/name-info)>, gamma: gamma): _ gamma
    match to-add
      Nil -> gamma
      Cons((name, info), rest) -> 
        val matches = gamma.gamma-lookup(name)
        val local-matches = matches.list/filter fn((qname, qinfo))
          !qinfo.is-infoImport && (qname.qualifier == ctxt || qname.qualifier == nil) && name.unqualify == qname.unqualify && is-same-namespace(qname, name)
        match local-matches
          Cons((_, qinfo), _) -> 
            inf-error(info.range, "definition".text |+| name.pp-name |+| "is already defined in this module, at".text |+| qinfo.range.start.show.text 
              |-| " hint: use a local qualifier".text)
          Nil -> ()
        extend(ctxt, rest, gamma.assumption/extend(name, info))
  val gamma' = extend(e.contxt, defs, e.gamma)
  with-env(infer-env(gamma=gamma'), act)
            
fun extend-inf-gamma-core(top-level: bool, defs: list<core/core/def-group>, act: () -> _ a): _ a
  match defs
    Nil -> act()
    Cons(dg, rest) -> 
      val depth = infer-effect/scope-depth
      val to-add = match dg
        DefRec(dfs) -> dfs.map(_.core-def-info(depth))
        DefNonRec(def) -> [def.core-def-info(depth)]
      extend-inf-gamma-ex(top-level, [], to-add, fn() extend-inf-gamma-core(top-level, rest, act))

pub fun extend-inf-gamma(tnames: list<(name, assumption/name-info)>, act: () -> _ a): _ a
  extend-inf-gamma-ex(False, [], tnames, act)

pub fun extend-inf-gamma-ex(top-level: bool, ignores: list<name>, tnames: list<(name, assumption/name-info)>, act: () -> _ a): _ a
  val e = infer-env
  fun extend(ctxt: name, gamma: gamma, seen: list<(name, assumption/name-info)>, to-add: list<(name, assumption/name-info)>, inf-gamma: inf-gamma): _ inf-gamma
    match to-add
      Nil -> inf-gamma
      Cons(x as (name, info), rest) -> 
        val qname = info.canonical-name(name)
        val rng = info.range
        val tp = info.scheme
        match seen.lookup(name)
          Just(info2) -> 
            check-casing-overlap(rng, name, info2.canonical-name(name), info2)
            inf-error(rng, name.pp-name |+| "is already defined at".text |+| info2.range.show.text |-| 
             " hint: if these are potentially recursive definitions, give them a full type signature to disambiguate.".text )
          Nothing -> 
            match inf-gamma.inf-gamma/lookup(name)
              Right((cname, info2)) | cname != nameReturn -> // TODO: Adapt to multiple matches?
                check-casing-overlap(rng, name, cname, info2)
                if !name.is-hidden-name && name.show != "resume" && name.show != "resume-shallow" && !ignores.any(_ == name) then 
                  inf-warning(rng, name.pp-name |+| "shadows an earlier local definition or parameter".text)
              _ -> ()
        extend(ctxt, gamma, Cons(x, seen), rest, inf-gamma.inf-gamma/extend(qname, info.update-canonical-name(qname)))
  val inf-gamma' = extend(e.contxt, e.gamma, [], tnames.filter(!_.fst.is-wildcard).map(fn((nm, info)) (nm.unqualify, info)), e.inf-gamma)
  with-env(infer-env(inf-gamma=inf-gamma'), act)
