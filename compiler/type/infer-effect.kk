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
import compiler/type/unify
import compiler/type/pretty
import compiler/type/operations
import compiler/syntax/syntax
import compiler/syntax/range-map
import compiler/core/core
import compiler/lib/pprint
import std/data/linearmap
import std/data/linearset
import std/data/sort
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

//////////////////////////////////////
// Generalization
//////////////////////////////////////

pub fun instantiate(tp: ktype, rng: range)
  if tp.is-rho then 
    val (rho, coref) = tp.extend
    (rho, [], coref)
  else 
    val (tvars, rho, coref) = tp.instantiate-ex(rng)
    (rho, tvars, coref)

pub fun instantiate-no-ex(tp: ktype, rng: range)
  if tp.is-rho then 
    (tp, [], id)
  else 
    val (tvars, rho, coref) = tp.instantiate-noex(rng)
    (rho, tvars, coref)

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

fun pp-select(sel: implicit-select): <pretty-eff> doc
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
fun lookup-names(info-filter: (assumption/name-info) -> bool, name: name, nctx: name-context, rng: range): infer list<(name, assumption/name-info, rho)>
  val matches = 
    match lookup-local-name(info-filter, name)
      Right(local) -> [local] // a local name that matches exactly was found; use it always
      Left(locals) -> 
        // otherwise consider globals as well besides the locally qualified locals that matched
        // todo: should we prioritize local locally qualified names when disambiguating?
        val globals = lookup-global-name(info-filter, name) 
        locals ++ globals
  filter-match-name-context-ex(matches, nctx, rng)

fun name-info/subst(ni: assumption/name-info)
  update-type(ni, ni.typ.subst)

fun lookup-local-name(info-filter: (assumption/name-info) -> bool, name: name): infer either<list<(name, assumption/name-info)>, (name, assumption/name-info)>
  if name.is-implicit-constraint-evidence then 
    get-iconstraints-gamma().inf-gamma/lookup(name)
  else 
    match gamma-lookup-ex(info-filter, name)
      Left(all) -> Left(all.map(fn((n, ni: assumption/name-info)) (n, ni.subst)))
      Right((n, ni)) -> Right((n, ni.subst))

fun lookup-global-name(info-filter: (assumption/name-info) -> bool, name: name): infer list<(name, assumption/name-info)>
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

fun filter-match-name-context(matches: list<(name, assumption/name-info)>, nctx: name-context, rng: range): infer list<(name, assumption/name-info)>
  filter-match-name-context-ex(matches, nctx, rng).map(fn((nm, info, _)) (nm, info))

fun filter-match-name-context-ex(matches: list<(name, assumption/name-info)>, nctx: name-context, rng: range): infer list<(name, assumption/name-info, rho)>
  fun match-type(ex: ktype, (nm, info): (name, assumption/name-info)): infer list<(name, assumption/name-info, rho)>
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
pub fun fixed-context(propagated: maybe<(ktype, range)>, fixed-resolved: list<(int, fixed-arg)>, fixed-count: int, namedArgs: list<name>): infer name-context
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


pub fun pp-ambiguous(hint: string, infos: list<(name, assumption/name-info)>): infer doc
  vcat([". Possible candidates: ".text, pp-candidates(infos)] ++
       (if hint.is-empty then [] else ["hint: ".text |+| hint.text]))


pub fun pp-candidates(nameInfos: list<(name, assumption/name-info)>): infer doc
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

pub fun pp-implicits-hint(nameInfos: list<(name, assumption/name-info)>): infer list<(doc, doc)>
  val candidateMissingImplicits = nameInfos.map fn((_, info))
    info.scheme.requires-implicits.map(fst)
  
  val allMissingImplicits = candidateMissingImplicits.concat.linear-set
  val allRequiredMissingImplicits = allMissingImplicits.list.filter fn(imp)
    candidateMissingImplicits.all(fn(missing) missing.any(fn(m) m == imp))
  
  match allRequiredMissingImplicits
    Nil -> []
    _ -> [("missing implicits".text, allRequiredMissingImplicits.map(pp-name).hsep),
          ("hint".text, "ensure implicit functions are defined prior to functions that require them".text)]

pub fun pp-name-info(nm: name, info: assumption/name-info): infer (doc, doc)
  val env = infer-env
  (env.importsMap.get-alias(nm).pp-name, info.scheme.pp-type)

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
  contxt: name // module name
  currentDefs: list<name>
  namedLam: bool
  returnAllowed: bool
  inLhs: bool
  hiddenTermDoc: maybe<(range, doc)>
  localDepth: int
  allowInfiniteChains: bool
  niceNames: name-map<doc>
  importsMap: import-map
  gamma: gamma

pub effect infer-state
  fun hole-allowed(): bool
  fun use-hole(): ()

fun module-name()
  infer-env.contxt

fun with-hidden-term-doc(rng: range, doc: doc, action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(hiddenTermDoc = Just((rng, doc)))
  action()

fun in-hidden-term-doc(): infer-env bool
  infer-env.hiddenTermDoc.is-just

fun qualify-name(nm: name)
  qualify(module-name(), nm)

pub effect val scope-depth: int
pub effect val local-depth: int

pub alias infer = <pretty-eff, infer-state, infer-eff, range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, inf-gamma-eff, synonyms-eff, newtypes-eff, unify, unique>;

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
  fun get-iconstraints-gamma(): inf-gamma
  // add a new implicit constraint with a fresh name (to be solved at generalization time)
  fun add-iconstraint(ic: ic-params): (name, assumption/name-info, ktype)
  fun solve-iconstraint(nm : name, tp : ktype): ()

// TODO: incorporate generalization into here?
fun with-def(def-name,action)
  var iconstraints : list<implicit-constraint> := []
  var iconstraints-gamma := inf-gamma/empty
  with override
    fun get-iconstraints() iconstraints.subst
    fun get-iconstraints-gamma() iconstraints-gamma
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

fun with-hole-allowed(allowed0: bool, action: () -> <infer|e> a): <infer|e> a
  var allowed := allowed0
  with override 
    fun hole-allowed() allowed
    fun use-hole() allowed := False
  action()
pub fun disallow-hole(action: () -> <infer|e> a): <infer|e> a
  with-hole-allowed(False, action)
// Returns the value of the action and whether a hole was used
pub fun allow-hole(action: () -> <infer|e> a): <infer|e> (a, bool)
  with-hole-allowed(True, {(action(), !hole-allowed())})
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

pub fun infer-eff(action)
  with override
    fun inf-error(rng: range, msg: doc)
      add-range-info(rng, RIError(msg))
      fail(msg.show ++ " at " ++ rng.show)
    fun inf-warning(rng: range, msg: doc)
      add-range-info(rng, RIWarning(msg))
      ()
  action()

pub effect infer-eff 
  fun inf-error(rng: range, msg: doc): ()
  fun inf-warning(rng: range, msg: doc): ()


//////////////////////////////////////
// Unify helpers
//////////////////////////////////////

fun nofail-unify(action: () -> <infer,unify|e> a, ?kk-file-line: string): <infer|e> a
  match run-unify(action)
    (Right(v), sub) -> 
      add-sub(sub)
      v
    (Left(err), sub) -> 
      add-sub(sub)
      fail("should never fail!: " ++ err.show ++ " " ++ kk-file-line)

fun do-unify(action)
  match run-unify(action)
    (Right(x), sub) -> 
      add-sub(sub)
      Right(x)
    (Left(err), sub) -> 
      add-sub(sub)
      Left(err)

pub fun infer-unify(ctxt: infer-context, rng: range, expected: ktype, tp: ktype): infer ()
  val (sexp, stp) = (expected.subst, tp.subst)
  match do-unify({ unify(expected, tp) })
    Left(err) -> infer-unify-error(ctxt, rng, err, sexp, stp)
    Right(_) -> ()

pub fun infer-unifies(ctxt: infer-context, tps: list<(range, ktype)>): infer ktype
  match tps
    Cons((_, tp), Nil) -> tp
    Cons((rng1, tp1), Cons((rng2, tp2), rst)) -> 
      val r = rng1.combine(rng2)
      infer-unify(ctxt, r, tp1, tp2)
      val tp = tp1.subst
      infer-unifies(ctxt, Cons((r, tp), rst))

pub fun infer-subsume(ctxt: infer-context, rng: range, expected: ktype, tp: ktype): infer (ktype, core/core/expr -> pure core/core/expr)
  val free = free-in-gamma()
  val (sexp, stp) = (expected.subst, tp.subst)
  match do-unify({ subsume(rng, free, sexp, stp) })
    Left(err) -> 
      infer-unify-error(ctxt, rng, err, sexp, stp)
      (expected, fn(e) e) // never reached
    Right((t, _, coref)) -> (t, coref)

pub fun check-skolem-escape(rng: range, tp: ktype, mhint: maybe<doc>, skolems: list<type-var>, extra-free: tvs): infer ()
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

pub fun with-skolemized(rng: range, tp: ktype, mhint: maybe<doc>, action: (ktype, list<type-var>) -> infer (a, tvs)): infer a
  val (xvars, xrho, _) = skolemize-ex(tp, rng)
  val (x, extra-free) = action(xrho, xvars)
  check-skolem-escape(rng, tp, mhint, xvars, extra-free)
  x

pub fun occurs-in-context(tv: type-var, extraFree: tvs): infer bool
  val free = free-in-gamma() + extraFree
  free.member(tv)


//////////////////////////////////////
// Unification Errors
//////////////////////////////////////

fun get-term-doc(term: string, rng: range): <infer-env,colors,exn> (doc, doc)
  val env = infer-env
  match env.hiddenTermDoc
    Just((_, doc)) -> 
      ("implicit".text |+| term.text, doc)
    Nothing -> 
      (term.text, doc-from-range(rng))

fun infer-unify-error(ctxt: infer-context, rng: range, err: unify-error, xtp1: ktype, xtp2: ktype): infer ()
  match err
    NoMatchEffect(eff1, eff2) ->
      infer-unify-error(ctxt, rng, NoMatchType, eff2, eff1)
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


pub fun type-error(ctxRng: range, rng: range, message: doc, xtp: ktype, extra: list<(doc,doc)>): infer ()
  val free = free-in-gamma()
  val tp: ktype = normalizeX(False, free, xtp.subst)
  val termInfo = get-term-doc("term", rng)
  val rows = 
    [("context".text, doc-from-range(ctxRng)),
     termInfo,
     ("inferred type".text, nice-type(tp))]
    ++ extra
  inf-error(rng, message |-| table(rows))

pub fun context-error(ctxRng: range, rng: range, message: doc, extra: list<(doc,doc)>): infer ()
  val termInfo = get-term-doc("term", rng)
  val rows = 
    [("context".text, doc-from-range(ctxRng)),
     termInfo]
    ++ extra
  inf-error(rng, message |-| table(rows))

pub fun term-error(rng: range, message: doc, tp: ktype, extra: list<(doc,doc)>): infer ()
  val termInfo = get-term-doc("term", rng)
  val rows = 
    [termInfo,
     ("inferred type".text, nice-type(tp))]
    ++ extra
  inf-error(rng, message |-| table(rows))