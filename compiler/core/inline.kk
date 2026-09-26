// Ported from Core/Inline.hs (291 lines)
//
// Inline top-level functions (across modules)
// Does not inline recursive top-level functions, that is done by specialization
// (See Core/Specialize).
module compiler/core/inline

import compiler/core/core
import std/data/rb-map
import compiler/common/name-collections
import compiler/core/corevar
import compiler/core/inlines
import compiler/core/uniquefy
import compiler/core/simplify
import compiler/common/name
import compiler/common/name-prim
import compiler/common/syntax
import compiler/platform/config
import std/data/rb-set

// The public entry point.
// Operates on the current core-phase definitions, replacing call sites of
// registered inline definitions with their (shared) bodies, then running a
// small local simplification pass to beta-reduce/expose further candidates,
// and then inlining once more -- mirroring upstream's:
//   defs1 <- fmap uniquefyDefGroups $ inlDefGroups defs
//   defs2 <- liftUnique (uniqueSimplify penv False True 3 0 defs1)
//   fmap uniquefyDefGroups $ inlDefGroups defs2
pub fun inline-defs(inline-max: int, inls0: inlines): _ ()
  set-core-defs(get-core-defs().run-inline-defs(inline-max, inls0))

fun run-inline-defs(defs: def-groups, inline-max: int, inls0: inlines): _ def-groups
  val defs1 = dgs/uniquefy(inl-def-groups(defs, inline-max, inls0))
  val defs2 = defs1.local-simplify
  dgs/uniquefy(inl-def-groups(defs2, inline-max, inls0))

// A small, fixed local
// simplification (beta-reduction etc.) run between the two inlining passes so
// that inlined applications can reduce and expose further inline candidates.
fun local-simplify(defs1: def-groups): _ def-groups
  with val simp-env = Simp-settings(False, True, 0)
  simplifyN(3, defs1)

// transform definition groups

fun inl-def-groups(dgs: def-groups, inline-max: int, inls: inlines): _ def-groups
  match dgs
    Nil -> Nil
    Cons(dg, rest) ->
      val (dg', inls') = inl-def-group(dg, inline-max, inls)
      Cons(dg', inl-def-groups(rest, inline-max, inls'))

fun inl-def-group(dg: def-group, inline-max: int, inls: inlines): _ (def-group, inlines)
  match dg
    DefRec(defs) ->
      val defs' = defs.map(fn(d) inl-def(d, inline-max, inls))
      (DefRec(defs'), inl-extend(True, defs', inline-max, inls))
    DefNonRec(d) ->
      val d' = inl-def(d, inline-max, inls)
      (DefNonRec(d'), inl-extend(False, [d'], inline-max, inls))

// local (`let`) definition groups are transformed but never registered as
// inline candidates for their siblings
fun inl-local-def-groups(dgs: def-groups, inline-max: int, inls: inlines): _ def-groups
  dgs.map(fn(dg) inl-local-def-group(dg, inline-max, inls))

fun inl-local-def-group(dg: def-group, inline-max: int, inls: inlines): _ def-group
  match dg
    DefRec(defs) -> DefRec(defs.map(fn(d) inl-def(d, inline-max, inls)))
    DefNonRec(d) -> DefNonRec(inl-def(d, inline-max, inls))

fun inl-def(d: def, inline-max: int, inls: inlines): _ def
  d(defExpr = inl-expr(d.defExpr, inline-max, inls))

fun inl-expr(expr0: expr, inline-max: int, inls: inlines): _ expr
  match expr0
    // Applications
    App(TypeApp(f, targs), args) ->
      val f0 = inl-expr(f, inline-max, inls)
      val args' = args.map(fn(a) inl-expr(a, inline-max, inls))
      val f' = inl-app-expr(f0, targs.length, args.length, args.args-only-zero-cost, inline-max, inls)
      App(TypeApp(f', targs), args')

    App(f, args) ->
      val f0 = inl-expr(f, inline-max, inls)
      val args' = args.map(fn(a) inl-expr(a, inline-max, inls))
      val f' = inl-app-expr(f0, 0, args.length, args.args-only-zero-cost, inline-max, inls)
      App(f', args')

    // regular cases
    Lam(pars, eff, body) ->
      Lam(pars, eff, inl-expr(body, inline-max, inls))

    Let(defgs, body) ->
      Let(inl-local-def-groups(defgs, inline-max, inls), inl-expr(body, inline-max, inls))

    Case(exprs, bs) ->
      Case(exprs.map(fn(x) inl-expr(x, inline-max, inls)), bs.map(fn(b) inl-branch(b, inline-max, inls)))

    // type application and abstraction
    TypeLam(tvars, body) ->
      TypeLam(tvars, inl-expr(body, inline-max, inls))

    TypeApp(body, tps) ->
      TypeApp(inl-app-expr(body, tps.length, 0, False, inline-max, inls), tps)

    // the rest
    _ -> inl-app-expr(expr0, 0, 0, False, inline-max, inls)

// prevent inlining of functions applied only to variable arguments unless the
// inline is cheap or forced (`InlineAlways`)
fun args-only-zero-cost(args: list<expr>): bool
  args.all(is-var-expr)

fun is-var-expr(e: expr): bool
  match e
    Var(_, _) -> True
    _ -> False

fun inl-app-expr(expr0: expr, m: int, n: int, only-zero-cost: bool, inline-max: int, inls: inlines): _ expr
  match expr0
    Var(tname, _) ->
      match inl-lookup(tname.get-name, inls)
        Just((info, m', n')) ->
          if !info.is-rec && m >= m' && n >= n' &&
             (!only-zero-cost || info.kind.is-inlineAlways || info.cost <= 4)
            then info.expr
            else expr0
        Nothing -> expr0

    // handle .open(f) calls
    // can happen if it is inside an open as:  .open<..>(f<..>)  (test: cgen/inline4)
    TypeApp(f, targs) | m == 0 ->
      TypeApp(inl-app-expr(f, targs.length, n, only-zero-cost, inline-max, inls), targs)

    App(TypeApp(Var(open-tn, open-info), targs), [f]) | open-tn.get-name == nameEffectOpen ->
      App(TypeApp(Var(open-tn, open-info), targs), [inl-app-expr(f, m, n, only-zero-cost, inline-max, inls)])

    _ -> expr0  // no inlining

fun inl-branch(b: branch, inline-max: int, inls: inlines): _ branch
  Branch(b.patterns, b.guards.map(fn(g) inl-guard(g, inline-max, inls)))

fun inl-guard(g: guard, inline-max: int, inls: inlines): _ guard
  Guard(inl-expr(g.test, inline-max, inls), inl-expr(g.body, inline-max, inls))

// inline environment lookups and extension

// Look up a name and return its (uniquefied-later)
// inline expression together with its type/value arity, skipping
// specialize-only definitions.
fun inl-lookup(nm: name, inls: inlines): _ maybe<(inline-def, int, int)>
  match rb-map/lookup(inls, nm)
    Just(idef) ->
      if idef.isSpecialize then Nothing
      else
        val (m, n) = idef.expr.inline-arity
        Just((idef, m, n))
    Nothing -> Nothing

// arity (type parameters, value parameters) of an inline candidate's body
fun inline-arity(e: expr): _ (int, int)
  match e
    TypeLam(tpars, Lam(pars, _, _)) -> (tpars.length, pars.length)
    TypeLam(tpars, _) -> (tpars.length, 0)
    Lam(pars, _, _) -> (0, pars.length)
    _ -> (0, 0)

// Register the (already-inlined) defs of a just-processed
// definition group as inline candidates for the remainder of the program.
fun inl-extend(is-rec: bool, defs: list<def>, inline-max: int, inls: inlines): _ inlines
  inls.extends(extract-inline-defs(inline-max, is-rec, defs))

// Not exposed by the already-ported
// compiler/core/inlines.kk (which only extracts from whole def-groups / a
// single non-recursive def), so the recursive-group variant is reproduced
// here to stay faithful to Inline.hs's use of `inlExtend`.
fun extract-inline-defs(cost-max: int, is-rec: bool, defs: list<def>): _ list<inline-def>
  if is-rec then
    match defs
      [_] -> []  // self-recursive singleton: never inline
      _ -> defs.map(fn(d) extract-inline-def-rec(d, cost-max)).concat-maybe
  else
    defs.map(fn(d) d.extract-inlines(cost-max, False)).concat-maybe

// A definition from a (mutually) recursive
// group is only considered for inlining if it does not call itself directly;
// note it is still registered with `isRec = False`: mutual (but not self)
// recursion is not detected here.
fun extract-inline-def-rec(d: def, cost-max: int): _ maybe<inline-def>
  if d.defExpr.free-vars.member(TName(d.def-name, d.ktype)) then Nothing
  else d.extract-inlines(cost-max, False)
