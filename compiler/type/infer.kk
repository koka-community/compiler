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






//////////////////////////////////////////
// Helpers
//////////////////////////////////////////

