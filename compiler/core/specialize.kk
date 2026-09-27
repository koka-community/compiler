// Port of Core/Specialize.hs (499 lines): the specializer pass.
// Ported as of 2026-08-01; approx upstream baseline of src/Core/Specialize.hs.
//
// Suppose a function is recursive and passes a function to itself unchanged,
// e.g. `map` takes a function `f` which does not change during recursive
// calls. If we call `map` with a known function argument (e.g. `inc` or
// `fn(x) x + x`) then we generate a new 'specialized' definition at this call
// site which always has the same value for this parameter:
//
//   map(inc, list(1, 10))   becomes
//
//   val spec-map = fn(xs)
//     val f = inc
//     match xs
//       Nil -> Nil
//       Cons(x, xx) -> Cons(f(x), xx.spec-map())
//   spec-map(list(1, 10))
//
// and the simplifier later inlines the only occurrence of `f`.
//
// Port notes (vs upstream Core/Specialize.hs):
//  - upstream `specialize :: Inlines -> Env -> CorePhase b ()` carries a
//    `Pretty.Env` that is tracing-only; like ctail.kk and optimize.kk this
//    port drops all Pretty.Env parameters.
//  - the `SpecM` monad (UniqueT over Reader Inlines) becomes the ambient
//    `unique` effect plus a single reader `effect val spec-inlines` (house
//    style: effects, not monad emulation).
//  - upstream's generic `foldMapExpr`/`rewriteTopDownM` from Core/Core.hs are
//    not present in this port's core.kk, so faithful local copies are defined
//    here (`spec-fold-map`, `spec-rewrite-top-down`).
//  - `filterMaybe`/`whenJust` maybe-monad plumbing is inlined into direct
//    `match`/early-`return` control flow.
//  - `uniqueSimplify defaultEnv False False 1 10` maps to one pass of
//    simplify.kk's `expr/simplify` under `Simp-settings(False, False, 10)`.
//  - `usedInThisDef` is defined-but-unused upstream and is ported as such.

module compiler/core/specialize

import compiler/common/failure
import std/data/rb-map
import compiler/common/name
import compiler/common/name-collections
import compiler/common/range
import compiler/common/syntax
import compiler/common/unique
import compiler/platform/config
import compiler/type/type
import compiler/type/typevar
import compiler/core/core
import compiler/core/corevar
import compiler/core/pretty
import compiler/core/inlines
import compiler/core/simplify
import compiler/core/uniquefy
import std/core/undiv
import std/data/rb-set

//--------------------------------------------------------------------------
// Specialization "monad": reader-only inlines + ambient unique
//--------------------------------------------------------------------------

effect val spec-inlines: inlines

// upstream PR koka-lang/koka#906: minimum instantiation weight per function
// in the current specialization ancestry (Reader-local `specStack`): an
// ancestor is only specialized again at a STRICTLY SMALLER weight, so
// mutually recursive specializable groups terminate after one round.
effect val spec-stack: name-map<int>

// Whether to write the provenance comment into the interface. OFF by default:
// it is documentation nothing reads back -- the lexer scans every byte and
// discards it -- and it was ~30% of interface bytes. Interface text is what an
// LSP pays at startup, so the default matters most there. `--coreprovenance`
// turns it back on when you need to see WHY something specialized.
effect val spec-provenance: bool

alias spec-eff = <spec-inlines, spec-stack, spec-provenance, unique, pure, comp-flags>

//--------------------------------------------------------------------------
// Entry point
//--------------------------------------------------------------------------

pub fun specialize(spec-env: inlines, provenance: bool = False): _ ()
  with val spec-inlines = spec-env
  with val spec-provenance = provenance
  with val spec-stack = rb-map/empty()
  // upstream: runSpecM (uniq+100) ... TODO (also upstream): use the unique int
  // to generate names and remove the call to uniquefyDefGroups?
  set-unique(get-unique() + 100)
  val defs' = get-core-defs().map(spec-one-def-group)
  set-core-defs(dgs/uniquefy(defs'))

// Only specialize-eligible inline defs count
fun spec-lookup(nm: name): spec-eff maybe<inline-def>
  match spec-inlines.lookup(nm)
    Just(idef) | idef.isSpecialize -> Just(idef)
    _ -> Nothing

fun spec-one-def-group(dg: def-group): spec-eff def-group
  match dg
    DefNonRec(d) -> DefNonRec(d.spec-one-def)
    DefRec(ds) -> DefRec(ds.map(spec-one-def))

fun spec-one-def(d: def): spec-eff def
  d(defExpr = spec-one-expr(d.def-name, d.defExpr))

// instantiation weight of a call: constructor count of its type arguments
// (TVar counts 0); mirrors `weight` in Type/InferMonad.hs (PR #906)
fun spec-weight(tps: list<ktype>): pure int
  fun weight-type(tp: ktype): pure int
    match tp
      TForAll(_, t) -> weight-type(t.pretend-decreasing)
      TFun(tpars, teff, tres) -> tpars.map(fn((_, t)) weight-type(t.pretend-decreasing)).sum + weight-type(teff.pretend-decreasing) + weight-type(tres.pretend-decreasing)
      TApp(t, targs) -> weight-type(t.pretend-decreasing) + targs.map(fn(t2) weight-type(t2.pretend-decreasing)).sum
      TSyn(_, _, t) -> weight-type(t.pretend-decreasing)
      TCon(_) -> 1
      TVar(_) -> 0
  tps.map(weight-type).sum

// Own recursion
// instead of rewriteTopDownM so the ancestry stack scopes over the descent
// into freshly created specialization bodies
fun spec-one-expr(this-def-name: name, e0: expr): spec-eff expr
  spec-descend(this-def-name, e0)

fun spec-descend(this-def-name: name, e: expr): spec-eff expr
  match e
    App(Var(v, _), _) -> spec-go(this-def-name, v.get-name, [], e)
    App(TypeApp(Var(v, _), typeArgs), _) -> spec-go(this-def-name, v.get-name, typeArgs, e)
    _ -> spec-descend-children(this-def-name, e)

fun spec-descend-children(this-def-name: name, e: expr): spec-eff expr
  match e
    Lam(params, eff, body) -> Lam(params, eff, spec-descend(this-def-name, body))
    Var -> e
    App(f, xs) -> App(spec-descend(this-def-name, f), xs.map(fn(x) spec-descend(this-def-name, x)))
    TypeLam(tpars, body) -> TypeLam(tpars, spec-descend(this-def-name, body))
    TypeApp(body, targs) -> TypeApp(spec-descend(this-def-name, body), targs)
    Con -> e
    ELit -> e
    Let(binders, body) ->
      val binders' = binders.map fn(b)
        match b
          DefNonRec(d) -> DefNonRec(d(defExpr = spec-descend(this-def-name, d.defExpr)))
          DefRec(ds) -> DefRec(ds.map(fn(d) d(defExpr = spec-descend(this-def-name, d.defExpr))))
      Let(binders', spec-descend(this-def-name, body))
    Case(exprs, branches) ->
      val branches' = branches.map fn(b)
        Branch(b.patterns, b.guards.map(fn(g) Guard(spec-descend(this-def-name, g.test), spec-descend(this-def-name, g.body))))
      Case(exprs.map(fn(x) spec-descend(this-def-name, x)), branches')

// upstream local `go` in specOneExpr (PRs #906 + #899)
fun spec-go(this-def-name: name, nm: name, typeArgs: list<ktype>, e: expr): spec-eff expr
  match spec-lookup(nm)
    Nothing -> spec-descend-children(this-def-name, e)
    Just(idef) ->
      val w = spec-weight(typeArgs)
      val decreasing = match spec-stack.lookup(nm)
        Nothing -> True     // not an ancestor
        Just(w0) -> w < w0  // ancestors only at strictly smaller instantiation
      if idef.def-name != this-def-name && decreasing then
        val e' = spec-one-call(idef, e)
        // M.insertWith min: keep the smaller weight for repeated ancestors
        with override val spec-stack = spec-stack.update(idef.def-name, w, fn(w0: int, w1: int) if w0 < w1 then w0 else w1)
        spec-descend-children(this-def-name, e')
      else
        spec-descend-children(this-def-name, e)

//--------------------------------------------------------------------------
// Bool-list helpers
//--------------------------------------------------------------------------

fun filter-bools(bools: list<bool>, xs: list<a>): list<a>
  bools.zip(xs).filter(fst).map(snd)

// (falses, trues)
fun partition-bools(bools: list<bool>, xs: list<a>): (list<a>, list<a>)
  bools.zip(xs).foldr(([], [])) fn(bx, acc)
    val (b, x) = bx
    val (falses, trues) = acc
    if b then (falses, Cons(x, trues)) else (Cons(x, falses), trues)

//--------------------------------------------------------------------------
// Specialize a single call site
//--------------------------------------------------------------------------

fun spec-one-call(idef: inline-def, e: expr): spec-eff expr
  match e
    App(Var(_, _), args) ->
      val gargs = good-args(idef.paramSpecialize, args)
      if gargs.any(is-just)
        then replace-call(idef.def-name, idef.expr, idef.sort, idef.paramSpecialize, new-args(gargs, args), Nothing).default(e)
        else e
    App(TypeApp(Var(_, _), typeArgs), args) ->
      val gargs = good-args(idef.paramSpecialize, args)
      if gargs.any(is-just)
        then replace-call(idef.def-name, idef.expr, idef.sort, idef.paramSpecialize, new-args(gargs, args), Just(typeArgs)).default(e)
        else e
    _ -> e

fun new-args(gargs: list<maybe<expr>>, args: list<expr>): list<expr>
  args.zipwith(gargs, fn(arg, g) g.default(arg))

fun good-args(bools: list<bool>, exprs: list<expr>): _ list<maybe<expr>>
  bools.zipwith(exprs, fn(b, e) if b && e.good-arg then Just(e) else Nothing)

fun good-arg(e: expr): _ bool
  match e
    Lam -> True
    TypeLam(_, body) -> body.good-arg
    TypeApp(body, _) -> body.good-arg
    App(f, _) -> f.good-arg  // ?? for open(f) calls
    Var(_, info) -> match info
      InfoNone -> False
      _ -> True
    _ -> False

//--------------------------------------------------------------------------
// Capture-avoiding rewrite of all recursive calls to the specialized name
// the context record replaces the Haskell
// closure over `from`/`to`/`isSpecParam`/`specParamNames`.
//--------------------------------------------------------------------------

struct sic
  sic-from: tName
  sic-to: tName
  sic-spec: list<bool>          // which params are specialized away
  sic-spec-names: list<tName>   // the specialized parameter names

fun spec-inner-calls(from: tName, to: tName, isSpecParam: list<bool>, specParamNames: list<tName>, e: expr): _ expr
  sic-expr(Sic(from, to, isSpecParam, specParamNames), e)

// `Var to (InfoArity 0 arityTo)` where arityTo counts the *kept* parameters
fun sic-var-to(s: sic): expr
  Var(s.sic-to, InfoArity(0, s.sic-spec.filter(fn(b) !b).length))

fun sic-match-spec-param-names(s: sic, args: list<expr>): _ bool
  args.length == s.sic-spec-names.length && s.sic-spec-names.zip(args).all(sic-eq-var)

fun sic-eq-var(pa: (tName, expr)): _ bool
  val (nm, arg) = pa
  match arg
    Var(v, _) -> nm == v
    // upstream PR #899 removed the trace here (it pretty-printed the FULL
    // core argument on every mismatch -- 215MB of stderr on a looping
    // module): the recursive call does not pass the specialized parameter
    // unchanged; leave it (and decline to specialize in replace-call)
    _ -> False

// rewritten recursive call: drop the specialized arguments
fun sic-app-to(s: sic, args: list<expr>): _ expr
  App(sic-var-to(s), filter-bools(s.sic-spec.map(fn(b) !b), args).map(fn(a) sic-expr(s, a)))

fun sic-expr(s: sic, e: expr): _ expr
  match e
    App(g, args) -> sic-app(s, g, args)
    Lam(params, eff, body) ->
      // avoid capture
      if params.any(fn(p) p == s.sic-from) then e else Lam(params, eff, sic-expr(s, body))
    TypeLam(tpars, body) -> TypeLam(tpars, sic-expr(s, body))
    TypeApp(body, targs) -> TypeApp(sic-expr(s, body), targs)
    Let(dgs, body) -> sic-let(s, dgs, body)
    Case(exprs, branches) -> Case(exprs.map(fn(x) sic-expr(s, x)), branches.map(fn(b) sic-branch(s, b)))
    _ -> e

// rewrite recursive calls (the specialized result is always monomorphic, so a
// `TypeApp` head is dropped; the TypeLam was applied to the call-site types)
fun sic-app(s: sic, g: expr, args: list<expr>): _ expr
  fun generic()
    App(sic-expr(s, g), args.map(fn(a) sic-expr(s, a)))
  match g
    Var(v, _) | v == s.sic-from ->
      if sic-match-spec-param-names(s, filter-bools(s.sic-spec, args)) then sic-app-to(s, args) else generic()
    TypeApp(Var(v, _), _) | v == s.sic-from ->
      if sic-match-spec-param-names(s, filter-bools(s.sic-spec, args)) then sic-app-to(s, args) else generic()
    _ -> generic()

// capture-avoiding rewrite over let bindings
fun sic-let(s: sic, dgs: list<def-group>, body: expr): _ expr
  match dgs
    Nil -> sic-expr(s, body)
    Cons(DefNonRec(d), rest) ->
      if defTName(d) == s.sic-from
        then make-let(Cons(DefNonRec(sic-def(s, d)), rest), body)
        else make-let([DefNonRec(sic-def(s, d))], sic-let(s, rest, body))
    Cons(DefRec(rdefs), rest) ->
      if rdefs.any(fn(d) defTName(d) == s.sic-from)
        then make-let(Cons(DefRec(rdefs), rest), body)
        else make-let([DefRec(rdefs.map(fn(d) sic-def(s, d)))], sic-let(s, rest, body))

// capture-avoiding rewrite over branches
fun sic-branch(s: sic, b: branch): _ branch
  match b
    Branch(patterns, guards) ->
      if patterns.any(fn(p) p.bound-vars.member(s.sic-from))
        then b
        else Branch(patterns, guards.map(fn(g) sic-guard(s, g)))

fun sic-guard(s: sic, g: guard): _ guard
  Guard(sic-expr(s, g.test), sic-expr(s, g.body))

fun sic-def(s: sic, d: def): _ def
  d(defExpr = sic-expr(s, d.defExpr))

//--------------------------------------------------------------------------
// Replace a specializable call
//
// At this point we've identified a call to a specializable function with a
// 'known' argument passed for all specializable parameters. A couple of steps
// here to avoid looping when getting the type of the specialized def:
//  1. build the body of spec-f, e.g. `val y = yexpr; ...body of f...`
//  2. get the type of this body
//  3. only then replace the recursive calls to f in the body (spec-inner-calls)
// It is important not to get the type of the body at the same time as
// replacing the recursive calls, since the type of the body depends on the
// type of the functions it calls and vice versa.
//--------------------------------------------------------------------------

fun replace-call(nm: name, expr0: expr, dsort: def-sort, bools: list<bool>, args: list<expr>, mb-type-args: maybe<list<ktype>>): spec-eff maybe<expr>
  val (uexpr, _) = uniquefyExprU(expr0)

  // extract the specialized parameters
  val (newPairs, speccedPairs) = partition-bools(bools, fn-params(uexpr).zip(args))
  val newParams = newPairs.map(fst)
  val newArgs = newPairs.map(snd)
  val speccedParams = speccedPairs.map(fst)
  val speccedArgs = speccedPairs.map(snd)

  // create a new (recursive) specialized body where the specialized
  // parameters become local definitions
  val specLets = speccedPairs.map fn(pa)
    val (p, arg) = pa
    DefNonRec(Def(p.get-name, p.type-of, arg, Private, DefVal, InlineAuto, range/null, ""))
  val body1 = Lam(newParams, fn-effect(uexpr), Let(specLets, fn-body(uexpr)))
  val specBody0 = match mb-type-args
    Nothing -> body1
    Just(typeArgs) -> new/sub(fn-type-params(uexpr).zip(typeArgs)).expr/substitute(body1)

  // substitute self-recursive calls to call our new specialized definition
  // (without the specialized arguments!)
  val specName = unique-name("spec")
  val specType = specBody0.type-of
  val specTName = TName(specName, specType)
  val (specBody, specInnerBody) = match specBody0
    Lam(largs, leff, Let(specDgs, sbody)) ->
      val inner = spec-inner-calls(TName(nm, uexpr.type-of), specTName, bools, speccedParams, sbody)
      (Lam(largs, leff, Let(specDgs, inner)), inner)
    _ -> failure/fail("core/specialize replace-call: unexpected output from specialize pass")

  // upstream PR koka-lang/koka#899: a residual recursive call to the ORIGINAL
  // definition (one spec-inner-calls could not rewrite) that is ITSELF
  // specializable would be re-specialized by the top-down rewrite descending
  // into this body, recreating the same residual from the same inline def
  // inside yet another specialized def, forever. Decline to specialize.
  if has-spec-residual(nm, bools, specInnerBody) then Nothing
  else
    // simplify so the new specialized arguments are potentially inlined,
    // unlocking potential further specialization
    val sspecBody = spec-simplify(specBody)
    // the ARGUMENT renders with the pretty printer, not `show`: upstream's
    // `show` for an `Expr` IS `prettyExpr` (Core/Pretty.hs), and this comment
    // is written verbatim into the interface of every module with a
    // specialization. A structural dump here was 913 bytes where upstream's
    // rendering is 68.
    val doc = if !spec-provenance then "" else
              "// specialized: " ++ nm.show ++ ", on parameters " ++ speccedParams.map(show).join(", ") ++ ", using:\n" ++
              spec-comment(speccedPairs.map(fn((p, a)) p.show ++ " = " ++ a.pretty-show).join("\n"))
    // The specialized parameters are GONE from the new definition, so their
    // parameter infos must go too. Reusing `dsort` as-is (upstream does, Core/
    // Specialize.hs:435) shifts a `Borrow` onto whichever parameter now sits in
    // that slot: for `map(xs, ^f)` specialized on `f`, TRMC then appends `_acc`
    // into the borrowed slot. A borrowed accumulator is dup'ed (so every extend
    // COPIES the context -- quadratic) and dropped after the recursive call (so
    // no tail call -- O(n) C stack). `list(1, 200000).map(fn(x) x + 1)` segfaulted.
    val specSort = match dsort
      DefFun(pinfos, fip) -> DefFun(partition-bools(bools, pinfos).fst, fip)
      _ -> dsort
    val specDef = Def(specName, specType, sspecBody, Private, specSort, InlineAuto, range/null, doc)
    Just(Let([DefRec([specDef])], App(Var(defTName(specDef), InfoNone), newArgs)))

fun has-spec-residual(nm: name, bools: list<bool>, e0: expr): pure bool
  fun is-residual(g: expr, rargs: list<expr>): pure bool
    match g
      Var(v, _) | v.get-name == nm -> good-args(bools, rargs).any(is-just)
      TypeApp(Var(v, _), _) | v.get-name == nm -> good-args(bools, rargs).any(is-just)
      _ -> False
  fun go(e: expr): pure bool
    match e
      App(g, rargs) -> is-residual(g, rargs) || go(g.pretend-decreasing) || rargs.any(fn(x) go(x.pretend-decreasing))
      Lam(_, _, body) -> go(body.pretend-decreasing)
      TypeLam(_, body) -> go(body.pretend-decreasing)
      TypeApp(body, _) -> go(body.pretend-decreasing)
      Let(dgs, body) -> dgs.any(fn(dg) dg.flatten.any(fn(d) go(d.defExpr.pretend-decreasing))) || go(body.pretend-decreasing)
      Case(exprs, branches) ->
        exprs.any(fn(x) go(x.pretend-decreasing)) ||
        branches.any(fn(b) b.guards.any(fn(g) go(g.test.pretend-decreasing) || go(g.body.pretend-decreasing)))
      _ -> False
  go(e0)

// One simplification
// pass, unsafe=False, ndebug=False, duplication max 10 (Pretty.Env dropped)
fun spec-simplify(e: expr): <unique, pure, comp-flags> expr
  with val simp-env = Simp-settings(False, False, 10)
  e.expr/simplify

// Prefix every line with "// "
fun spec-comment(s: string): string
  s.lines.map(fn(l) "// " ++ l).join("\n") ++ "\n"

//--------------------------------------------------------------------------
// Function shape accessors (upstream fnTypeParams/fnParams/fnEffect/fnBody)
//--------------------------------------------------------------------------

fun fn-type-params(e: expr): _ list<type-var>
  match e
    TypeLam(typeParams, _) -> typeParams
    _ -> failure/fail("core/specialize fn-type-params: not a function: " ++ e.show)

fun fn-params(e: expr): _ list<tName>
  match e
    Lam(params, _, _) -> params
    TypeLam(_, Lam(params, _, _)) -> params
    _ -> failure/fail("core/specialize fn-params: not a function: " ++ e.show)

fun fn-effect(e: expr): _ keffect
  match e
    Lam(_, eff, _) -> eff
    TypeLam(_, Lam(_, eff, _)) -> eff
    _ -> failure/fail("core/specialize fn-effect: not a function: " ++ e.show)

fun fn-body(e: expr): _ expr
  match e
    Lam(_, _, body) -> body
    TypeLam(_, Lam(_, _, body)) -> body
    _ -> failure/fail("core/specialize fn-body: not a function: " ++ e.show)

//--------------------------------------------------------------------------
// Extract definitions that should be specialized
//--------------------------------------------------------------------------

pub fun extract-specialize-defs(loaded-inlines: inlines, dgs: def-groups): _ list<inline-def>
  val initial = inlines(dgs.filter(is-recursive-def-group).flatten
                           .filter(fn(d) d.ktype.spec-is-fun)
                           .map(make-specialize).concat-maybe)
  multi-step-inlines(loaded-inlines, initial, dgs.flatten).values

fun is-recursive-def-group(dg: def-group): bool
  match dg
    DefRec([_]) -> True
    _ -> False

// restriction: all recursive calls pass the specialized parameters unchanged,
// and all recursive calls use the exact same type arguments (this rules out
// polymorphic recursion, so the specialized definition is monomorphic).
fun make-specialize(d: def): _ maybe<inline-def>
  val (mbTypes, recArgs) = recursive-calls(d)
  val typesOk = match mbTypes
    Nothing -> True
    Just(tss) -> all-eq(tss)
  if !typesOk then return Nothing
  // defensive (not upstream-faithful by omission, not by contradiction):
  // upstream's `isFun . defType` pre-filter checks the def's DECLARED type,
  // which doesn't rule out a zero-parameter recursive thunk that an earlier
  // simplify/inline pass eta-reduced down to a bare alias (`foo = bar`,
  // wrapped in a TypeLam) -- `defExpr` is then not `Lam`-shaped even though
  // `defType` is still a function type. Upstream's `fnParams` has the same
  // partial match and would crash too if it ever saw this shape; skip
  // specialization for such a def instead of hard-failing the whole compile
  // (worst case: a missed specialization opportunity, never a correctness
  // issue -- `d.defExpr` is used as-is, unmodified, everywhere else).
  val mbParams = match d.defExpr
    Lam(pars) -> Just(pars)
    TypeLam(_, Lam(pars)) -> Just(pars)
    _ -> Nothing
  val params = match mbParams
    Just(pars) -> pars
    Nothing -> return Nothing
  val specializableParams = all-passed-in-same-order(params, recArgs).map(keep-fun-param)
  if !specializableParams.any(is-just) then return Nothing
  Just(InlineDef(d.def-name, d.defExpr, True, InlineAuto, d.cost, d.sort, specializableParams.map(is-just)))

fun keep-fun-param(mb: maybe<tName>): _ maybe<tName>
  match mb
    Just(tn) -> if tn.type-of.spec-is-fun then Just(tn) else Nothing
    Nothing -> Nothing

fun all-passed-in-same-order(params: list<tName>, calls: list<list<expr>>): _ list<maybe<tName>>
  calls.map(fn(c) passed-in-same-order(params, c)).spec-transpose.map(same-order-column)

// `fmap head . sequence`: Just the (shared) param name when every call passes
// it in place (head is safe upstream since transposed sublists are non-empty;
// here the impossible empty case simply yields Nothing)
fun same-order-column(col: list<maybe<tName>>): maybe<tName>
  match col.sequence-maybes
    Just(Cons(x, _)) -> Just(x)
    _ -> Nothing

fun passed-in-same-order(params: list<tName>, args: list<expr>): list<maybe<tName>>
  params.zipwith(args, same-order-arg)

fun same-order-arg(param: tName, arg: expr): maybe<tName>
  match arg
    Var(v, _) | v == param -> Just(v)
    _ -> Nothing

fun spec-is-fun(tp: ktype): bool
  tp.split-fun-scheme.is-just

fun used-in-this-def(d: def): _ name-set
  rb-set/from-list(d.defExpr.spec-fold-map(used-var).map(get-name))

fun used-var(e: expr): list<tName>
  match e
    Var(v, _) -> [v]
    _ -> []

fun all-eq(xss: list<list<ktype>>): _ bool
  match xss
    Nil -> True
    Cons(x, rest) -> rest.all(fn(y) eq-types(x, y))

// list of all argument lists of recursive calls; includes the type arguments
// when the call is a TypeApp. ASSUMED: either all recursive applications are
// TypeApps or none are -- hence the `sequence`
fun recursive-calls(d: def): _ (maybe<list<list<ktype>>>, list<list<expr>>)
  val body = match d.defExpr
    Lam(_, _, b) -> b
    TypeLam(_, Lam(_, _, b)) -> b
    _ -> failure/fail("core/specialize recursive-calls: not a function: " ++ d.def-name.show)
  val pairs = body.spec-fold-map(fn(e) rec-call-hit(d.def-name, e))
  val (types, argss) = pairs.unzip
  (types.sequence-maybes, argss)

fun rec-call-hit(dname: name, e: expr): list<(maybe<list<ktype>>, list<expr>)>
  match e
    App(Var(v, _), args) | v.get-name == dname -> [(Nothing, args)]
    App(TypeApp(Var(v, _), types), args) | v.get-name == dname -> [(Just(types), args)]
    _ -> []

//--------------------------------------------------------------------------
// Multi-step specialization: a definition that
// passes one of its own (function) parameters to a specializable function
// becomes specializable itself.
//--------------------------------------------------------------------------

fun multi-step-inlines(loaded-inlines: inlines, inls: inlines, defs: list<def>): _ inlines
  defs.foldl((inls.merge(loaded-inlines), inls), multi-step).snd

fun multi-step(acc: (inlines, inlines), d: def): _ (inlines, inlines)
  val (allInlines, newInlines) = acc
  if d.is-val || d.kinline.is-inlineNever then return acc
  match calls-specializable(allInlines, d)
    Nothing -> acc
    Just(specArgs) ->
      // inlineCost = 1 here since kki complains about inline + specialize
      val new = InlineDef(d.def-name, d.defExpr, False, InlineAuto, 1, d.sort, specArgs)
      (allInlines.extend(new), newInlines.extend(new))

// look for calls to specializable functions where we don't know the RHS of an
// argument; references that aren't calls aren't eligible for multi-step
// specialization (we don't have the specializable args anyway). Returns the
// first hit.
fun calls-specializable(inls: inlines, d: def): _ maybe<list<bool>>
  // runs over EVERY def in the module (not just specialize candidates), so
  // a non-`Lam`-shaped def (any plain value/alias def with a function TYPE
  // but no literal Lam, e.g. an eta-reduced alias) must be skipped rather
  // than crash `fn-params` -- see the identical guard in `make-specialize`
  match d.defExpr
    Lam -> calls-specializable-params(inls, d, fn-params(d.defExpr))
    TypeLam(_, Lam) -> calls-specializable-params(inls, d, fn-params(d.defExpr))
    _ -> Nothing

fun calls-specializable-params(inls: inlines, d: def, params: list<tName>): _ maybe<list<bool>>
  val hits = d.defExpr.spec-fold-map(fn(e) specializable-call(inls, d.def-name, params, e))
  match hits
    Cons(x, _) -> Just(x)
    Nil -> Nothing

fun specializable-call(inls: inlines, dname: name, params: list<tName>, e: expr): _ list<list<bool>>
  match e
    App(Var(v, _), args) -> spec-call-overlap(inls, dname, params, v.get-name, args)
    App(TypeApp(Var(v, _), _), args) -> spec-call-overlap(inls, dname, params, v.get-name, args)
    _ -> []

fun spec-call-overlap(inls: inlines, dname: name, params: list<tName>, nm: name, args: list<expr>): _ list<list<bool>>
  match inls.lookup(nm)
    Nothing -> []
    Just(idef) ->
      if nm == dname then return []
      val spArgs = filter-bools(idef.paramSpecialize, args)
      val argVars = spArgs.map(spec-vars).concat
      val overlap = params.map(fn(p) argVars.any(fn(v) v == p))
      if overlap.any(id) then [overlap] else []

fun spec-vars(e: expr): _ list<tName>
  e.spec-fold-map(used-var)

//--------------------------------------------------------------------------
// Generic traversals (faithful local copies of upstream Core/Core.hs
// `foldMapExpr` (with the list monoid) and `rewriteTopDownM`, which this
// port's core.kk does not provide)
//--------------------------------------------------------------------------

fun spec-fold-map(e: expr, f: (expr) -> <div|e> list<a>): <div|e> list<a>
  match e
    Lam(_, _, body) -> f(e) ++ body.spec-fold-map(f)
    Var -> f(e)
    App(g, xs) -> f(e) ++ g.spec-fold-map(f) ++ xs.map(fn(x) x.spec-fold-map(f)).concat
    TypeLam(_, body) -> f(e) ++ body.spec-fold-map(f)
    TypeApp(body, _) -> f(e) ++ body.spec-fold-map(f)
    Con -> f(e)
    ELit -> f(e)
    Let(binders, body) ->
      f(e) ++ binders.flatten.map(fn(d) d.defExpr.spec-fold-map(f)).concat ++ body.spec-fold-map(f)
    Case(cases, branches) ->
      f(e) ++ cases.map(fn(c) c.spec-fold-map(f)).concat ++
        branches.map(fn(b) b.guards.map(fn(g) g.test.spec-fold-map(f) ++ g.body.spec-fold-map(f)).concat).concat

fun spec-rewrite-top-down(e0: expr, f: (expr) -> spec-eff expr): spec-eff expr
  val e = f(e0)
  match e
    Lam(params, eff, body) -> Lam(params, eff, spec-rewrite-top-down(body, f))
    App(g, xs) -> App(spec-rewrite-top-down(g, f), xs.map(fn(x) spec-rewrite-top-down(x, f)))
    TypeLam(tpars, body) -> TypeLam(tpars, spec-rewrite-top-down(body, f))
    TypeApp(body, targs) -> TypeApp(spec-rewrite-top-down(body, f), targs)
    Let(binders, body) ->
      Let(binders.map(fn(b) spec-rewrite-dg(b, f)), spec-rewrite-top-down(body, f))
    Case(cases, branches) ->
      Case(cases.map(fn(c) spec-rewrite-top-down(c, f)), branches.map(fn(b) spec-rewrite-branch(b, f)))
    _ -> e

fun spec-rewrite-dg(dg: def-group, f: (expr) -> spec-eff expr): spec-eff def-group
  match dg
    DefNonRec(d) -> DefNonRec(spec-rewrite-def(d, f))
    DefRec(ds) -> DefRec(ds.map(fn(d) spec-rewrite-def(d, f)))

// note: the def's type is updated to the type of the rewritten expression
fun spec-rewrite-def(d: def, f: (expr) -> spec-eff expr): spec-eff def
  val fexpr = spec-rewrite-top-down(d.defExpr, f)
  d(defExpr = fexpr, ktype = fexpr.type-of)

fun spec-rewrite-branch(b: branch, f: (expr) -> spec-eff expr): spec-eff branch
  match b
    Branch(patterns, guards) ->
      Branch(patterns, guards.map(fn(g) Guard(spec-rewrite-top-down(g.test, f), spec-rewrite-top-down(g.body, f))))

//--------------------------------------------------------------------------
// Small list utilities (upstream: Data.List transpose / Prelude sequence)
//--------------------------------------------------------------------------

// upstream `Data.List.transpose` silently SKIPS any row that has already run
// out of elements (`[h | (h:_) <- xss]`), so ragged input (rows of differing
// length) doesn't crash. The previous version assumed every row in `xss'`
// still had a head once the first row was non-empty (`fn(Cons(hd, tl)) ...`
// has no `Nil` arm) -- currently unreachable here since every caller only
// ever feeds rows of equal length (Core's "App is always fully applied"
// invariant), but ragged-unsafe by construction; filter to match upstream.
fun spec-transpose(xss: list<list<a>>): _ list<list<a>>
  match xss
    Nil -> Nil
    Cons(Nil, xss') -> spec-transpose(xss')
    Cons(Cons(x, xs), xss') ->
      val (hds, tls) = xss'.flatmap(fn(row) match row { Cons(hd, tl) -> [(hd, tl)]; Nil -> [] }).unzip
      Cons(Cons(x, hds), spec-transpose(Cons(xs, tls)))

fun sequence-maybes(xs: list<maybe<a>>): maybe<list<a>>
  match xs
    Nil -> Just([])
    Cons(Nothing, _) -> Nothing
    Cons(Just(x), rest) -> match rest.sequence-maybes
      Just(r) -> Just(Cons(x, r))
      Nothing -> Nothing
