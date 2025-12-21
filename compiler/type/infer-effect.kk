module compiler/type/infer-effect

import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/failure
import compiler/common/unique
import compiler/platform/config
import compiler/type/type
import compiler/type/typevar
import compiler/type/assumption
import compiler/type/infgamma
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/import-map
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
  scopeNestingDepth: int
  allowInfiniteChains: bool
  niceNames: name-map<doc>

pub alias infer = <range-map-eff, def-infer-effect, infer-env, infGammaEff, synonymsEff, newtypes-eff, unify>

pub effect def-infer-effect
  fun get-iconstraints(): list<implicit-constraint>
  fun add-iconstraint(ic: implicit-constraint): ()

fun with-hole-allowed(allowed: bool, action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(holeAllowed = allowed)
  action()
pub fun with-context(nm: name, action: () -> <infer|e> a): <infer|e> a
  with override val infer-env = infer-env(contxt = nm)
  action()

pub effect val infer-env: inferEnv
