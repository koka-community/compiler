module compiler/type/infer-effect

import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/syntax
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
import compiler/syntax/range-map
import compiler/core/core
import compiler/lib/pprint
import std/data/linearmap

pub type variance
  Negative
  Invariant
  Positive

fun flip(v : variance)
  match v 
    Negative -> Positive
    Positive -> Negative
    Invariant -> Invariant

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




pub fun implicit-type-context(tp : ktype) : name-context
  match tp.split-fun-type
    Just((ppars, peff, prestp)) -> CtxFunTypes(False, ppars.map(snd), [], Just(prestp)) // can handle further implicits better
    _ -> CtxType(tp)

pub fun maybe-to-context(mb-type : maybe<ktype>) : name-context
  match mb-type
    Just(tp) -> CtxType(tp)
    Nothing -> CtxNone

pub fun maybe-r-to-context(mb-type-range : maybe<(ktype, range)>) : name-context
  maybe-to-context(mb-type-range.map(fst))



// Error Helpers


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
    solve: (tvs, implicit-constraint) -> infer (expr, ktype)
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

pub effect val scope-depth: int
pub effect val local-depth: int

pub alias infer = <range-map-eff, local-depth, scope-depth, def-infer-effect, infer-env, inf-gamma-eff, synonyms-eff, newtypes-eff, unify, unique>;

div type ic-params 
  ICParams(
    nm: name,
    tp: ktype,
    can-solve: (tvs, implicit-constraint) -> infer bool,
    solve: (tvs, implicit-constraint) -> infer (expr, ktype),
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
