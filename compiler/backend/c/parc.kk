// Port of Backend/C/Parc.hs (Perceus precise reference counting pass)
//
// Notes:
// - The live variable set is state; the borrowed/owned (multi-set) environment
//   and the shape map behave like a Reader that is dynamically scoped: they are
//   restored after the sub-computation that extended them returns (see
//   `with-owned`/`extend-owned`/`extend-shapes`/`scoped` below, which mirror
//   `localized` in compiler/core/uniquefy.kk).
// - To calculate the live variables we visit the expression tree _in reverse_
//   (see `reverse-map`, used for let-bindings and application arguments).
// - `platform`/`newtypes`/`borrowed`/`enable-specialize` never change during a
//   run and are exposed as a single immutable `val` effect operation
//   (`parc-config`), matching how compiler/platform/config.kk's `comp-flags`
//   and compiler/core/simplify.kk's `simp-env` expose read-only pass settings.
//
// TODO(parc): upstream's `currentDef`/`prettyEnv` reader fields and
// `parcTrace`/`parcTraceDoc` are omitted -- they only fed debug trace
// messages (guarded by GHC's `trace`, off in normal builds) and are not
// otherwise observable in the transformation itself.
module compiler/backend/c/parc

import compiler/core/core
import compiler/core/corevar
import compiler/core/borrowed
import compiler/common/name
import compiler/common/name-prim
import compiler/common/unique
import compiler/common/syntax
import compiler/common/failure
import compiler/type/type
import compiler/kind/newtypes
import std/data/rb-set
import std/data/sort
import std/core/undiv
import std/data/rb-map
import compiler/common/name-collections

//--------------------------------------------------------------------------
// Parc effect: read-only settings as a single `val` op; live/owned/shapes as
// var-backed `fun` ops, installed once at the pass entry point (`parc-core`).
//--------------------------------------------------------------------------

// Iterates in name order, which decides the
// emitted dup/drop order and which drop `optimize-disjoint` specializes first
alias tnameset = rbset<tName>
alias tnamedups = tnameset
alias tnamedrops = tnameset

// maps a name to its (known) children/constructor-repr/scan-field-count
alias shape-map = rbmap<tName, shape-info>
struct shape-info
  m-children: maybe<tnameset>          // if known, Just of children
  m-con-repr: maybe<(con-repr, name)>  // if known, conRepr; may be Just while m-children is Nothing in case there is just one constructor (like a tuple)
  scan-fields: maybe<int>

val shape-info/empty: shape-info = Shape-info(Nothing, Nothing, Nothing)

struct parc-settings
  platform: platform
  newtypes: newtypes
  borrowed: borrowed
  enable-specialize: bool

effect parc-eff
  val parc-config: parc-settings
  fun get-owned(): tnameset
  fun set-owned(o: tnameset): ()
  fun get-shapes(): shape-map
  fun set-shapes(m: shape-map): ()
  fun get-live(): tnameset
  fun set-live(l: tnameset): ()
  // Pattern variables of an ENCLOSING match whose dups were deferred, to be
  // emitted by the guards of the immediately nested match instead. See
  // `parc-guard`/`deferrable-into`.
  fun get-pending(): tnameset
  fun set-pending(p: tnameset): ()

alias parc-effs = <parc-eff,unique,exn,div>

// closures returned from the two-phase branch/guard analysis (see `parc-branches`)
alias branch-fn = (tnameset) -> parc-effs branch
alias guard-fn = (tnameset) -> parc-effs guard

//--------------------------------------------------------------------------
// Reference count transformation: entry point
//--------------------------------------------------------------------------

pub fun parc-core(platform: platform, newtypes: newtypes, borrowed: borrowed, enable-specialize: bool, c: core): <unique,exn,div> core
  var owned-v := tnames/empty
  var shapes-v := rb-map/empty()
  var live-v := tnames/empty
  var pending-v := tnames/empty
  with handler
    val parc-config = Parc-settings(platform, newtypes, borrowed, enable-specialize)
    fun get-owned() owned-v
    fun set-owned(o) owned-v := o
    fun get-shapes() shapes-v
    fun set-shapes(m) shapes-v := m
    fun get-live() live-v
    fun set-live(l) live-v := l
    fun get-pending() pending-v
    fun set-pending(p) pending-v := p
  c(defs = parc-def-groups(True, c.defs))

//--------------------------------------------------------------------------
// Definition groups
//--------------------------------------------------------------------------

fun parc-def-groups(top-level: bool, dgs: def-groups): parc-effs def-groups
  dgs.reverse-map(fn(dg) parc-def-group(top-level, dg))

fun parc-def-group(top-level: bool, dg: def-group): parc-effs def-group
  match dg
    DefRec(defs) -> DefRec(defs.reverse-map(fn(d) parc-def(top-level, d)))
    DefNonRec(def) -> DefNonRec(parc-def(top-level, def))

// todo: should inline definitions use borrowing as well?
fun parc-def(top-level: bool, def: def): parc-effs def
  fun body()
    // a deferred dup may only be claimed by the nested match itself
    with with-pending(tnames/empty)
    val expr = if top-level then parc-top-level-expr(def.sort, def.defExpr) else def.defExpr.parc-expr
    def(defExpr = expr)
  if top-level then isolated_(body) else body()

//--------------------------------------------------------------------------
// Main PARC algorithm
//--------------------------------------------------------------------------

fun parc-top-level-expr(ds: def-sort, expr: expr): parc-effs expr
  match ds
    DefFun(bs, _) ->
      match expr
        TypeLam(tpars, body) -> TypeLam(tpars, parc-top-level-expr(ds, body))
        Lam(pars, eff, body) ->
          val pars-bs = zip-own(pars, bs)
          val pars-set = tnames(pars-bs.filter(fn((_, pi)) pi == Own).map(fst))
          val (dups, body') = parc-lam(expr, pars-set, body)
          maybe-stats(dups, Lam(pars, eff, body'))
        _ -> expr.parc-expr
    _ -> expr.parc-expr

fun parc-expr(expr: expr): parc-effs expr
  match expr
    // memoize markers are opaque to parc: left untouched
    App(Var(name, _), _) | name.get-name == nameLazyMemoizeTarget -> expr

    TypeLam(tpars, body) -> TypeLam(tpars, body.parc-expr)
    TypeApp(body, targs) -> TypeApp(body.parc-expr, targs)

    Lam(pars, eff, body) ->
      val pars-set = tnames(pars)
      val (dups, body') = parc-lam(expr, pars-set, body)
      maybe-stats(dups, Lam(pars, eff, body'))

    Var(tname, info) | info.isRefCounted ->
      use-tname(tname).default(expr)

    // Functions/Externals are not reference-counted, but they need to be
    // wrapped if they appear outside of an application.
    Var(tname, info) ->
      val bs = get-param-infos(tname.get-name)
      if !bs.any(fn(b) b == Borrow) then expr
      else match expr.type-of.split-fun-scheme
        Just((ts, pars2, eff, _)) ->
          parc-expr(add-type-lambdas(ts,
            list2/add-lambdas(pars2, eff,
              add-apps(pars2.map(fn((n, t)) Var(TName(n, t), InfoNone)),
                core/add-type-apps(ts, Var(tname, info))))))
        Nothing -> expr

    // If the function is refcounted, it may need to be dupped. On the other
    // hand, we want to avoid infinite recursion with the wrapping above if it
    // is not ref-counted.
    App(inner as Var(tname, info), args) ->
      val inner' = if info.isRefCounted then inner.parc-expr else inner
      parc-borrow-app(tname, args, inner')
    App(inner as TypeApp(Var(tname, info), _targs), args) ->
      val inner' = if info.isRefCounted then inner.parc-expr else inner
      parc-borrow-app(tname, args, inner')
    App(f, args) ->
      val args' = args.reverse-map(parc-expr)
      val f' = f.parc-expr
      App(f', args')

    ELit(_) -> expr
    Con(_, _) -> expr

    Let([], body) -> body.parc-expr
    Let(Cons(DefNonRec(def), dgs), body) ->
      // check if we need to name a result in case it will be dropped
      val def1 = def.name-result-if-dropped
      val body1 = owned-in-scope(tnames([def1.defTName]), fn() Let(dgs, body).parc-expr)
      val def2 = parc-def(False, def1)
      make-let([DefNonRec(def2)], body1)
    Let(Cons(DefRec(_), _), _) ->
      failure/fail("Backend.C.Parc.parcExpr: Recursive definition in let")

    Case(vars, brs) | case-is-normalized(vars, brs) ->
      Case(vars, parc-branches(var-names(vars), brs))
    Case(_, _) ->
      expr.normalize-case.parc-expr

// name a `let`-bound result if it would otherwise be silently dropped
// (upstream inlines this check at the top of the `Let` case)
fun name-result-if-dropped(def: def): parc-effs def
  if !def.def-name.is-nil then def
  else match def.defTName.gen-drop
    Just(_) -> def(def-name = unique-name("res"))
    Nothing -> def

// todo: this is a whole second pass. is there any way around this?
// maybe we should track a borrowed set and presume owned, instead of the
// other way around?
fun parc-lam(expr: expr, pars-set: tnameset, body: expr): parc-effs (list<maybe<expr>>, expr)
  val caps = expr.free-locals
  fun action(): parc-effs expr
    with with-owned(tnames/empty)
    // a deferred dup may only be claimed by the nested match itself
    with with-pending(tnames/empty)
    owned-in-scope(caps.union(pars-set), fn() body.parc-expr)
  val (body', _) = isolate-with(tnames/empty, action)
  val dups = caps.list.map(use-tname)
  (dups, body')

fun parc-borrow-app(tname: tName, args: list<expr>, expr: expr): parc-effs expr
  val bs = get-param-infos(tname.get-name)
  if !bs.any(fn(b) b == Borrow) then App(expr, args.reverse-map(parc-expr))
  else
    val args-bs = zip-own(args, bs)
    val triples = args-bs.reverse-map(fn((a, pi)) parc-borrow-arg(a, pi))
    val lets = triples.map(fn((l, _, _)) l).concat
    val drops = triples.map(fn((_, d, _)) d)
    val args' = triples.map(fn((_, _, a)) a)
    val expr' = match drops.concat-maybe
      [] -> App(expr, args')
      _ ->
        val app-name = unique-name("brw")
        val def = make-def(app-name, App(expr, args'))
        make-let([DefNonRec(def)], maybe-stats(drops, Var(def.defTName, InfoNone)))
    make-let(lets, expr')

// Let-float borrowed arguments to the top so that we can drop them after the
// function call. We also let-float owned arguments so that the order of
// evaluation is unchanged. We make the result prettier by not floating
// variables and owned total expressions.
fun parc-borrow-arg(expr: expr, par-info: param-info): parc-effs (list<def-group>, maybe<expr>, expr)
  match (expr, par-info)
    (_, Own) ->
      if expr.is-total then ([], Nothing, expr.parc-expr)
      else
        val arg-name = unique-name("own")
        val expr' = expr.parc-expr
        val def = make-def(arg-name, expr')
        ([DefNonRec(def)], Nothing, Var(def.defTName, InfoNone))
    (Var(tname, info), Borrow) ->
      if info.isRefCounted then
        val d = use-tname-borrowed(tname)
        ([], d, expr)
      else ([], Nothing, expr)
    (_, Borrow) ->
      val expr' = expr.parc-expr
      val not-refcounted = expr.expr-is-not-refcounted
      if not-refcounted then ([], Nothing, expr')
      else
        val arg-name = unique-name("brw")
        val def = make-def(arg-name, expr')
        val drop = extend-owned(tnames([def.defTName]), fn() def.defTName.gen-drop)
        ([DefNonRec(def)], drop, Var(def.defTName, InfoNone))

fun var-names(exprs: list<expr>): list<tName>
  match exprs
    Cons(Var(tn, _), rest) -> Cons(tn, var-names(rest))
    Cons(_, rest) -> var-names(rest)
    Nil -> Nil

fun parc-branches(scrutinees: list<tName>, brs: list<branch>): parc-effs list<branch>
  val live = get-live()
  val branch-fns = brs.reverse-map(fn(b) parc-branch(scrutinees, live, b))
  val owned-scrutinees = scrutinees.filter(is-owned)
  mark-lives(owned-scrutinees)
  val live' = get-live()
  branch-fns.map(fn(bf) bf(live'))

fun parc-branch(scrutinees: list<tName>, live: tnameset, b: branch): parc-effs branch-fn
  match b
    Branch(pats, guards) ->
      val guard-fns = guards.reverse-map(fn(g) parc-guard(scrutinees, pats, live, g))
      fn(c: tnameset) Branch(pats, guard-fns.map(fn(gf) gf(c)))

fun parc-guard(scrutinees: list<tName>, pats: list<pattern>, live: tnameset, g: guard): parc-effs guard-fn
  match g
    Guard(test, body) ->
      val owned-pats = scrutinees.zip(pats).filter(fn((s, _)) is-owned(s)).map(snd)
      val owned-pvs = bv(owned-pats)
      val pvs = bv(pats)
      // Dups this guard INHERITED from an enclosing match (see `get-pending`):
      // pattern variables of the enclosing pattern whose dup was deferred down
      // to here so that it meets the drop of the enclosing scrutinee in the SAME
      // `optimize-guard` call and can be cancelled.
      val inherited = get-pending()
      with scoped(pvs)
      with extend-owned(owned-pvs)
      with with-pending(tnames/empty)
      val shapes = infer-shapes(scrutinees, pats)  // create alias map for the pattern
      with extend-shapes(shapes)                   // merge with current alias map
      // Defer this guard's own pattern dups into an immediately nested match
      // when that is safe; otherwise this is empty and everything below behaves
      // exactly as it did before.
      val deferred = deferrable-into(scrutinees, pats, body)
      val (body', live-in-this-branch) = isolate-with(live, fn() with-pending(deferred, fn() body.parc-expr))
      // A guard `test` may reference variables that are not bound by the
      // pattern and not used in the branch body (e.g. `... | info.field ->
      // body` where `body` does not use `info`). Such variables must stay
      // live into the match so they are not dropped before the guard runs
      // (otherwise the guard reads a dropped value -- a use-after-free). They
      // are still dropped after the test via `drops` below, which is
      // computed from the body-only `live-in-this-branch`.
      val test-fvs = test.free-vars.set/(-)(pvs)
      mark-lives(live-in-this-branch.union(test-fvs).list)
      val test' = with-owned(tnames/empty, fn() test.parc-expr)
      fn(live-in-some-branch: tnameset)
        with scoped(pvs)
        with extend-owned(owned-pvs)
        with extend-shapes(shapes)
        // this guard's own pattern dups, MINUS the ones deferred into the nested
        // match, PLUS the ones inherited from the enclosing match.
        val inherited-dups = inherited.intersection(live-in-this-branch)
        val own-dups = owned-pvs.set/(-)(deferred).intersection(live-in-this-branch)
        val dups = own-dups.union(inherited-dups)
        // An INHERITED variable must never be dropped here: this branch did not
        // dup it (only the branches that USE it do, just above), and the
        // enclosing block still owns it -- its release is the enclosing drop of
        // the scrutinee it is a field of. Dropping it here over-releases.
        val drops = live-in-some-branch.set/(-)(live-in-this-branch).set/(-)(inherited).list.filter(is-owned)
        // special case for a lazy match in lazy-eval where we do not dup the
        // children (which is unsafe in general); generated in
        // Kind/Infer/synLazyEval
        val (dups1, drops1) = match scrutinees
          // (inherited dups are NOT the lazy value's children and must survive;
          //  `deferrable-into` refuses to defer into a lazy match, so in practice
          //  `inherited-dups` is empty here.)
          [lazy-name] | lazy-name.get-name.hidden/starts-with("lazy") && drops.is-nil ->
            (inherited-dups, tnames/empty)
          _ -> (dups, tnames(drops))
        Guard(test', parc-guard-rc(dups1, drops1, body'))

// Which of this guard's pattern variables may have their dup DEFERRED into the
// branches of an immediately nested match.
//
// Parc runs bottom-up: a guard PREPENDS its pattern dups to an already-rewritten
// body. So when the enclosing scrutinee's drop ends up inside a nested match --
// the shape of every in-place record update under one more `match` -- the dups
// and that drop never reach the same `optimize-guard` call and cannot be
// cancelled: the code dups every field and then immediately drops them again.
// Deferring the dups into the nested branches puts them in the same call.
//
// The dynamic dup count never goes up: exactly one branch runs, a branch that
// uses the variable dups it there instead of here, and a branch that does not
// use it now dups nothing at all (before, it dup'd here and dropped again
// inside).
//
// Conditions, all for soundness rather than profit:
//
//  * the body is (lets over) a `Case`, whose branches are exactly the guards
//    that will see this pending set (`parc-guard` clears it for everything else,
//    and so do `parc-def`/`parc-lam`), so no other match can claim these dups,
//    every branch that uses one dups it, and exactly one branch runs;
//
//  * THE SCRUTINEE MUST STILL BE LIVE IN THE NESTED BRANCHES. A deferred dup
//    runs later than it used to, so nothing in between may release the field.
//    The one thing that would is the drop of the scrutinee the field belongs to:
//    if the scrutinee dies at THIS guard, this guard drops it, and the drop is
//    specialized to free exactly those children that were not dup'ed here --
//    which would now include the deferred ones, so the nested branch would dup a
//    freed field. Requiring the scrutinee to occur free in the nested branches
//    means it is live all the way into them, so any drop of it happens at or
//    below the guards that emit the deferred dups, never before them. (And that
//    is exactly the case where the optimization is needed: when the scrutinee
//    dies here, dups and drop already meet and already fuse.)
//
//  * a variable used BEFORE the branches (in the lets, or in the nested
//    scrutinees) is not deferrable -- it is needed before any branch is entered;
//
//  * every branch guard is trivially true: a guard TEST is processed with
//    everything borrowed so it dups its own uses, and a failing test falls
//    through to the next guard, so a dup placed in a guard body is not
//    guaranteed to run;
//
//  * neither match is a lazy match: `parc-guard` deliberately DISCARDS the dups
//    of a lazy match's children, so dups deferred into one would be silently
//    lost (a use-after-free), and dups deferred out of one would start dupping
//    children the lazy protocol requires we do not.
fun deferrable-into(scrutinees: list<tName>, pats: list<pattern>, body: expr): parc-effs tnameset
  if scrutinees.any(is-lazy-match-name) then tnames/empty
  else match body.strip-lets
    Just((defs, cscruts, brs)) | !brs.is-nil && brs.all(trivial-guards) && !cscruts.any(is-lazy-match-expr) ->
      val live-into-branches = brs.map(branch/free-vars).unions
      val used-early = cscruts.map(expr/free-vars).unions.union(defs.map(fn(d) d.defExpr.free-vars).unions)
      // keep only the patterns whose scrutinee is owned here (so its children are
      // ours to dup at all) and still live in the nested branches (so its drop
      // cannot precede the deferred dups)
      val keep = scrutinees.zip(pats).filter(fn((sc, _)) is-owned(sc) && live-into-branches.member(sc))
      bv(keep.map(snd)).set/(-)(used-early)
    _ -> tnames/empty

fun is-lazy-match-name(tn: tName): bool
  tn.get-name.hidden/starts-with("lazy")

fun is-lazy-match-expr(e: expr): bool
  match e
    Var(tn) -> tn.is-lazy-match-name
    _ -> False

fun is-expr-true(e: expr): bool
  match e
    Con(TName(nm)) -> nm == nameTrue
    _ -> False

fun trivial-guards(Branch(_, guards): branch): bool
  guards.all(fn(g) g.test.is-expr-true)

// `(lets, scrutinees, branches)` when `body` is a `Case` under zero or more
// `Let`s, which is the only shape dups may be deferred into.
fun strip-lets(e: expr): maybe<(list<def>, list<expr>, list<branch>)>
  match e
    Let(dgs, body) ->
      match body.strip-lets
        Just((defs, cscruts, brs)) -> Just((dgs.map(defs-of).concat ++ defs, cscruts, brs))
        Nothing -> Nothing
    Case(cscruts, brs) -> Just(([], cscruts, brs))
    _ -> Nothing

fun defs-of(dg: def-group): list<def>
  match dg
    DefNonRec(d) -> [d]
    DefRec(ds) -> ds

fun parc-guard-rc(dps: tnamedups, drops: tnamedrops, body: expr): parc-effs expr
  val rc-stats = optimize-guard(parc-config.enable-specialize, dps, drops)
  maybe-stats(rc-stats, body)

fun mchildren-of(shapes: shape-map, x: tName): maybe<tnameset>
  match shapes.lookup(x)
    Just(Shape-info(Just(mc), _, _)) | !mc.is-empty -> Just(mc)
    _ -> Nothing

fun children-of(shapes: shape-map, x: tName): tnameset
  mchildren-of(shapes, x).default(tnames/empty)

fun con-name-of(shapes: shape-map, x: tName): maybe<name>
  match shapes.lookup(x)
    Just(Shape-info(_, Just((_, cname)), _)) -> Just(cname)
    _ -> Nothing

// TODO: interaction with borrowed names
// order invariant:
//  - all dups before drops, and drops before drop-reuses, and,
//  - within drops and dropr-reuses, each are ordered by pattern tree depth: parents must appear before children.
// note: all drops are "tree" disjoint, none is a parent of another.
fun optimize-guard(specialize: bool, dps: tnamedups, rdrops: tnamedrops): parc-effs list<maybe<expr>>
  if !specialize then
    // no optimization on dup/drops
    val xdups = dps.list.map(gen-dup)
    val xdrops = rdrops.list.map(gen-drop)
    xdups ++ xdrops
  else
    optimize-dup-drops(get-shapes(), dps, rdrops)

fun optimize-dup-drops(shapes: shape-map, dups0: tnamedups, drops0: tnamedrops): parc-effs list<maybe<expr>>
  val (fdups, fdrops) = fuse-dup-drops(shapes, dups0, drops0)
  assert("Backend.C.Parc.optimizeDupDrops: intersection not empty",
    fdups.intersection(fdrops).is-empty,
    optimize-disjoint(shapes, fdups, fdrops.list))

fun is-descendent-of(shapes: shape-map, parent: tName, x: tName): div bool
  val ys = children-of(shapes, parent)
  ys.member(x) || ys.list.any(fn(c) is-descendent-of(shapes, c, x).pretend-decreasing)

fun optimize-disjoint(shapes: shape-map, dps: tnamedups, drops: list<tName>): parc-effs list<maybe<expr>>
  match drops
    [] -> dps.list.map(gen-dup)
    Cons(y, rest) ->
      val (y-dups, dups') = dps.list.partition(fn(x) is-descendent-of(shapes, y, x))
      val (y-drops, drops') = rest.partition(fn(x) is-descendent-of(shapes, y, x))
      val r = optimize-disjoint(shapes, tnames(dups'), drops')       // optimize outside the y tree
      val pfx = y-drops.map(gen-drop)                                // todo: these could be decRef as these can never be unique
      val spec = specialize-drop(shapes, tnames(y-dups), y)          // specialize the y tree
      r ++ pfx ++ spec

fun specialize-drop(shapes: shape-map, dps: tnamedups, v: tName): parc-effs list<maybe<expr>>  // dups are descendents of v
  val x-shared = dps.list.map(gen-dup)                                  // for the non-unique branch
  val x-unique = optimize-dup-drops(shapes, dps, children-of(shapes, v))  // drop direct children in unique branch (note: v is not in drops)
  val tp = v.type-of
  val is-value = get-value-form(tp).is-just
  val is-data-as-maybe = get-is-data-as-maybe(tp)
  val has-known-children = mchildren-of(shapes, v).is-just
  val dont-specialize = !has-known-children ||   // or otherwise x-unique is wrong!
                        is-value || tp.is-box-type || tp.is-fun || tp.is-type-int || is-data-as-maybe
  fun no-specialize(y: tName): parc-effs list<maybe<expr>>
    val x-drop = y.gen-drop
    x-shared ++ [x-drop]
  if is-value && children-of(shapes, v).list.all(fn(child) dps.member(child)) then
    // Try to optimize a dropped value type where all fields are dup'd and
    // where the fields are not boxed in a special way (all BoxIdentity). This
    // optimization is important for TRMC for the `ctail` value type.
    match get-field-types(tp, con-name-of(shapes, v))
      Nothing -> no-specialize(v)
      Just(ftps) ->
        val bforms = ftps.map(get-box-form)
        if bforms.all(is-box-identity-or-unknown) then []
        else no-specialize(v)
  elif dont-specialize then
    // don't specialize certain primitives
    no-specialize(v)
  else
    val x-decref = v.gen-dec-ref
    fun maybe-stats-unit(xs: list<maybe<expr>>): <exn,div> expr
      maybe-stats(xs, exprUnit)  // must be a let to match in ParcReuse
    [Just(make-drop-special(v, maybe-stats-unit(x-unique), maybe-stats-unit(x-shared), maybe-stats-unit([x-decref])))]

// Remove dup/drop pairs
fun fuse-dup-drops(shapes: shape-map, dps: tnamedups, drops: tnamedrops): parc-effs (tnamedups, tnamedrops)
  fuse-aliases(shapes, dps.set/(-)(drops), drops.set/(-)(dps))

fun fuse-aliases(shapes: shape-map, dps: tnamedups, drops: tnamedrops): parc-effs (tnamedups, tnamedrops)
  val newtypes = parc-config.newtypes
  val platform = parc-config.platform
  fun fuse-alias((dps1, drops1): (tnamedups, tnamedrops), y: tName): <exn,div> (tnamedups, tnamedrops)
    match forwarding-child(platform, newtypes, shapes, dps1, y)
      Just(child) ->
        if dps1.member(child)
          then (dps1.set/(-)(tnames([child])), drops1)   // fuse the dup with the alias
          else (dps1, drops1 + child)                    // use the alias child as that may reveal more shape info for reuse later on
      Nothing -> (dps1, drops1 + y)
  drops.list.foldl((dps, tnames/empty), fuse-alias)

// Return a dupped name which is a child of the given name if the given name
// will always forward a drop directly to the child (e.g. because the given
// name is a box or a newtype).
fun forwarding-child(platform: platform, newtypes: newtypes, shapes: shape-map, dps: tnamedups, y: tName): <exn,div> maybe<tName>
  fun find-child(x: tName): maybe<tName>
    if dps.member(x) then Just(x) else Nothing
  match children-of(shapes, y).list
    [x] ->
      match get-value-form-x(newtypes, y.type-of)
        Just(ValueOneScan) ->  // for example `value type maybe<a> { Nothing; Just(val:a) }`
          match find-child(x)
            Just(x') -> Just(x')  // y as Just(x)
            Nothing ->
              if x.type-of.is-box-type then
                match children-of(shapes, x).list
                  [x'] -> match get-box-form-x(platform, newtypes, x'.type-of)
                    BoxIdentity -> Just(x')  // y as Just(x as Box(x'))
                    _ -> Nothing
                  _ -> Nothing
              else
                match get-box-form-x(platform, newtypes, x.type-of)
                  BoxIdentity ->
                    match children-of(shapes, x).list
                      [x'] -> Just(x')
                      _ -> Nothing
                  _ -> Nothing
        Just(_) -> Nothing
        Nothing ->
          if y.type-of.is-box-type then
            match get-box-form-x(platform, newtypes, x.type-of)
              BoxIdentity -> Just(x)  // y as Box(x)
              _ -> Nothing
          else Nothing
    _ -> Nothing

fun infer-shapes(scrutinees: list<tName>, pats: list<pattern>): <exn,div> shape-map
  scrutinees.zip(pats).map(fn((s, p)) shapes-of(s, p)).unions-nodup

fun no-dup(s1: shape-info, s2: shape-info): exn shape-info
  failure/fail("Backend.C.Parc.aliasMap.noDup: duplicate pattern names")

fun unions-nodup(ms: list<shape-map>): <exn,div> shape-map
  ms.foldl(rb-map/empty(), fn(acc: shape-map, m: shape-map) acc.union-with(m, no-dup))

fun shapes-of(parent: tName, pat: pattern): <exn,div> shape-map
  match pat
    PatCon(conname, subpats, repr, _, _, _, _, _) ->
      val scan = scan-count(repr)
      val shape = Shape-info(Just(tnames(subpats.map(pat-var-name))), Just((repr, conname.get-name)), Just(scan))
      val child-map = subpats.map(shapes-child).unions-nodup
      child-map.set(parent, shape)
    PatVar(patname, patpattern) ->
      val child-map = shapes-of(patname, patpattern)
      match child-map.lookup(patname)
        Just(shape) -> child-map.set(parent, shape)   // same children as parent == patname
        Nothing -> failure/fail("Backend.C.Parc.aliasMap: unbound alias: " ++ patname.show)
    PatLit(_) -> rb-map/from-list([(parent, Shape-info(Nothing, Nothing, Just(0)))])
    PatWild -> rb-map/from-list([(parent, Shape-info(Nothing, Nothing, Nothing))])

fun shapes-child(pat: pattern): <exn,div> shape-map
  match pat
    PatVar(patname, patpattern) -> shapes-of(patname, patpattern)
    PatCon -> failure/fail("Backend.C.Parc.aliasMap: unnamed nested pattern")
    _ -> rb-map/empty()

fun pat-var-name(p: pattern): <exn> tName
  match p
    PatVar(tn, _) -> tn
    _ -> failure/fail("Backend.C.Parc.aliasMap: unbound alias")

fun merge-shape-info(s1: shape-info, s2: shape-info): shape-info   // prefer most info
  fun merge-maybe(x: maybe<a>, y: maybe<a>): maybe<a>
    match x
      Nothing -> y
      _ -> x
  Shape-info(merge-maybe(s1.m-children, s2.m-children), merge-maybe(s1.m-con-repr, s2.m-con-repr), merge-maybe(s1.scan-fields, s2.scan-fields))

//--------------------------------------------------------------------------
// Case normalization
//--------------------------------------------------------------------------

fun case-is-normalized(exprs: list<expr>, branches: list<branch>): bool
  fun is-expr-var(e: expr): bool
    match e
      Var -> True
      _ -> False
  fun might-alias(b: branch): bool
    match b
      Branch(pats, _) -> pats.any(is-patVar)
  exprs.all(is-expr-var) && branches.all(fn(b) !might-alias(b))

fun normalize-case(expr: expr): parc-effs expr
  match expr
    Case(case-exprs, case-branches) ->
      val pairs = case-exprs.reverse-map(case-expand-expr)
      val vexprs = pairs.map(fst)
      val dgs = pairs.map(snd)
      val brs' = case-branches.map(fn(b) normalize-branch(vexprs, b))
      make-let(dgs.concat-maybe, Case(vexprs, brs'))
    _ -> failure/fail("Backend.C.Parc.normalizeCase")

// Generate variable names for scrutinee expressions
fun case-expand-expr(ex: expr): parc-effs (expr, maybe<def-group>)
  match ex
    Var -> (ex, Nothing)
    _ ->
      val nm = unique-name("match")
      val def = DefNonRec(make-def(nm, ex))
      val v = Var(TName(nm, ex.type-of), InfoNone)
      (v, Just(def))

fun normalize-branch(vexprs: list<expr>, b: branch): div branch
  match b
    Branch(branch-patterns, branch-guards) ->
      fun name-mapping(pat: pattern, new: expr): (maybe<(tName, expr)>, pattern)
        match pat
          PatVar(old, pat') -> (Just((old, new)), pat')
          _ -> (Nothing, pat)
      val mapped = branch-patterns.zip(vexprs).map(fn((p, n)) name-mapping(p, n))
      val new-names = mapped.map(fst).concat-maybe
      val pats' = mapped.map(snd)
      val guards' = new-names |-> branch-guards
      Branch(pats', guards')

//--------------------------------------------------------------------------
// Convenience methods for inserting PARC ops
//--------------------------------------------------------------------------

fun use-tname(tname: tName): parc-effs maybe<expr>
  val live = is-live(tname)
  val is-borr = is-borrowed(tname)
  mark-live(tname)
  if live || is-borr then gen-dup(tname) else Nothing

fun use-tname-borrowed(tname: tName): parc-effs maybe<expr>
  val live = is-live(tname)
  val is-borr = is-borrowed(tname)
  mark-live(tname)
  if !(live || is-borr) then gen-drop(tname) else Nothing

//-----------------------------------------------------------
// Optimize boxed reference counting
//-----------------------------------------------------------

type box-form
  BoxIdentity   // directly in the box itself (`int` or any regular datatype)
  BoxRaw        // (possibly) heap allocated raw bits (`int64`)
  BoxValue      // (possibly) heap allocated value with scan fields (`maybe<int>`)
  BoxUnknown

fun is-box-identity-or-unknown(b: box-form): bool
  match b
    BoxIdentity -> True
    BoxUnknown -> True
    _ -> False

fun get-box-form-x(platform: platform, newtypes: newtypes, tp: ktype): <exn,div> box-form
  match get-data-def-x(newtypes, tp)
    Just(DataDefValue(ValueRepr(m, 0, _))) ->    // 0 scan fields, m is size in bytes of raw fields
      match tp.extract-data-def-type
        Just(nm) | nm == nameTpInt || nm == nameTpFieldAddr ||
                    ([nameTpByte, nameTpInt8, nameTpInt16, nameTpFloat16].any(fn(n) n == nm) && platform.ptrSize > 2) ||
                    ([nameTpChar, nameTpInt32, nameTpMarker, nameTpFloat32].any(fn(n) n == nm) && platform.ptrSize > 4) ->
          BoxIdentity
        _ -> if m < platform.ptrSize then BoxIdentity else BoxRaw  // for example `bool`, but not `int64`
    Just(DataDefValue(_)) -> BoxValue
    Just(_) -> BoxIdentity
    Nothing -> BoxUnknown

fun get-box-form(tp: ktype): parc-effs box-form
  get-box-form-x(parc-config.platform, parc-config.newtypes, tp)

//-----------------------------------------------------------
// Ref-counting helpers
//-----------------------------------------------------------

// Generate a ref-count drop of a constructor
fun gen-dec-ref(tname: tName): parc-effs maybe<expr>
  if !tname.type-of.needs-dup-drop then Nothing
  else
    val fun-tp = TFun([(name/nil, tname.type-of)], typeTotal, typeUnit)
    Just(App(Var(TName(nameDecRef, fun-tp), InfoExternal("decref(#1,current_context())")), [Var(tname, InfoNone)]))

fun needs-dup-drop(tp: ktype): parc-effs bool
  match get-data-info(tp)
    Nothing -> True
    Just(di) -> needs-dup-drop-data(di)

pub fun needs-dup-drop-data(info: data-info): bool
  match info.def
    DataDefValue(vr) | vr.is-raw -> False   // value types with no reference fields don't need a drop
    _ -> match info.constrs
      // structs with no fields (eg. Pad) don't need a drop
      [ConInfo(params = Nil, valueRepr = ValueRepr(0, 0, _))] -> False
      _ -> True

fun is-value-type(tp: ktype): parc-effs bool
  get-data-def(tp).is-dataDefValue

type value-form
  ValueAllRaw   // just bits
  ValueOneScan  // one heap allocated member
  ValueOther

fun get-value-form-x(newtypes: newtypes, tp: ktype): <exn,div> maybe<value-form>
  match get-data-def-x(newtypes, tp)
    Just(DataDefValue(ValueRepr(_, 0, _))) -> Just(ValueAllRaw)
    Just(DataDefValue(ValueRepr(0, 1, _))) -> Just(ValueOneScan)
    Just(DataDefValue(_)) -> Just(ValueOther)
    _ -> Nothing

fun get-value-form(tp: ktype): parc-effs maybe<value-form>
  get-value-form-x(parc-config.newtypes, tp)

fun get-field-types(tp: ktype, mb-con-name: maybe<name>): parc-effs maybe<list<ktype>>
  match mb-con-name
    Nothing -> Nothing
    Just(con-name) -> match get-data-info(tp)
      Just(di) | di.name == nameOptional -> Nothing  // prevent trying to optimize the optional type in specialize above
      Just(di) -> match di.constrs.filter(fn(ci) con-name == ci.name)
        [ci] -> Just(ci.params.map(snd))
        _ -> Nothing
      Nothing -> Nothing

// Generate a dup/drop over a given (locally bound) name.
// May return Nothing if the type never needs a dup/drop (like an `int32` or `bool`)
fun gen-dup-drop(is-dup: bool, tname: tName, mb-con-repr: maybe<(con-repr, name)>, mb-scan-count: maybe<int>): parc-effs maybe<expr>
  match (mb-con-repr, mb-scan-count)
    (Just((cr, _)), Just(0)) | cr.is-conSingleton -> Nothing
    _ ->
      val tp = tname.type-of
      val mb-di = get-data-info(tp)
      val is-borr = is-borrowed(tname)
      if is-borr && !is-dup then Nothing
      else
        val normal = Just(dup-drop-fun(is-dup, tp, mb-con-repr, mb-scan-count, Var(tname, InfoNone)))
        match mb-di
          Just(di) ->
            match (di.def, di.constrs, di.data-repr(data/is-value).snd)
              (ddef, [con-info], [con-repr]) | ddef.is-dataDefNormal ->    // data with just one constructor
                val scan = scan-count(con-repr)
                Just(dup-drop-fun(is-dup, tp, Just((con-repr, con-info.name)), Just(scan), Var(tname, InfoNone)))
              (DataDefValue(vr), _, _) | vr.is-raw -> Nothing   // value with no scan fields
              _ -> normal
          Nothing -> normal

fun gen-dup(tname: tName): parc-effs maybe<expr>
  gen-dup-drop(True, tname, Nothing, Nothing)

fun gen-drop(tname: tName): parc-effs maybe<expr>
  val shape = get-shape-info(tname)
  gen-dup-drop(False, tname, shape.m-con-repr, shape.scan-fields)

// get the dup/drop function
fun dup-drop-fun(is-dup: bool, tp: ktype, mb-con-repr: maybe<(con-repr, name)>, mb-scan-count: maybe<int>, arg: expr): expr
  match (is-dup, mb-con-repr, mb-scan-count)
    (False, Just((cr, _)), Just(sc)) | sc > 0 && !cr.is-value && !cr.is-conAsJust && !tp.is-box-type ->
      // drop with a known number of scan fields
      val coerce-tp = TFun([(name/nil, tp), (name/nil, typeInt32)], typeTotal, typeUnit)
      App(Var(TName(nameDrop, coerce-tp), InfoExternal("dropn(#1,#2)")), [arg, make-int32(sc)])
    _ ->
      val nm = if is-dup then nameDup else nameDrop
      val coerce-tp = TFun([(name/nil, tp)], typeTotal, if is-dup then tp else typeUnit)
      App(Var(TName(nm, coerce-tp), InfoExternal((if is-dup then "dup" else "drop") ++ "(#1)")), [arg])

// is an expression definitely not reference counted?
fun expr-is-not-refcounted(expr: expr): parc-effs bool
  match expr
    ELit(LitInt(i)) -> i >= -8191 && i <= 8191  // 14 bits is safe on every platform
    _ -> !expr.type-of.needs-dup-drop

//--------------------------------------------------------------------------
// Utilities for readability
//--------------------------------------------------------------------------

fun reverse-map(xs: list<a>, f: (a) -> e b): e list<b>
  xs.reverse.map(f).reverse

fun zip-own(xs: list<a>, bs: list<param-info>): <exn,div> list<(a, param-info)>
  match (xs, bs)
    (Cons(x, xs'), Cons(b, bs')) -> Cons((x, b), zip-own(xs', bs'))
    (Cons(x, xs'), Nil) -> Cons((x, Own), zip-own(xs', []))
    (Nil, _) -> Nil

fun bv(pats: list<pattern>): div tnameset
  pats.map(bound-vars).unions

fun mark-lives(tns: list<tName>): parc-effs ()
  tns.foreach(mark-live)

fun maybe-stats(xs: list<maybe<expr>>, expr: expr): <exn,div> expr
  make-stats(xs.concat-maybe ++ [expr])

fun is-box-type(tp: ktype): bool
  match tp
    TCon(TypeCon(nm, _)) -> nm == nameTpBox
    TVar(_) -> True
    TSyn(_, _, t) -> t.is-box-type
    TApp(t, _) -> t.is-box-type
    _ -> False

fun extract-data-def-type(tp: ktype): div maybe<name>
  match tp.expand-syn
    TApp(t, _) -> t.extract-data-def-type
    TForAll(_, t) -> t.extract-data-def-type
    TCon(TypeCon(nm, _)) -> Just(nm)
    _ -> Nothing

//--------------------------------------------------------------------------
// Parc effect: derived accessors
//--------------------------------------------------------------------------

fun get-param-infos(nm: name): parc-effs list<param-info>
  match parc-config.borrowed.lookup(nm)
    Nothing -> []
    Just(pinfos) -> pinfos

//-------------------------------
// owned name abstractions
//-------------------------------

fun is-owned(tn: tName): parc-effs bool
  get-owned().member(tn)

fun is-borrowed(tn: tName): parc-effs bool
  if tn.get-name.is-nil then False
  else !is-owned(tn)

fun with-owned(o: tnameset, f: () -> parc-effs a): parc-effs a
  val saved = get-owned()
  set-owned(o)
  val r = f()
  set-owned(saved)
  r

// Replace (never extend) the deferred set: a variable must never be dup'ed at
// two levels, so only the one nested match we defer into may see it.
fun with-pending(p: tnameset, f: () -> parc-effs a): parc-effs a
  val saved = get-pending()
  set-pending(p)
  val r = f()
  set-pending(saved)
  r

fun extend-owned(o: tnameset, f: () -> parc-effs a): parc-effs a
  with-owned(get-owned().union(o), f)

fun extend-shapes(extend: shape-map, f: () -> parc-effs a): parc-effs a
  val saved = get-shapes()
  set-shapes(extend.union-with(saved, merge-shape-info))   // note: left-biased, prefer extend
  val r = f()
  set-shapes(saved)
  r

fun get-shape-info(tname: tName): parc-effs shape-info
  get-shapes().lookup(tname).default(shape-info/empty)

//-------------------------------
// live set abstractions
//-------------------------------

// Mark a local variable as live.
fun mark-live(tname: tName): parc-effs ()
  if !tname.get-name.is-qualified then set-live(get-live() + tname)

fun forget(tns: tnameset): parc-effs ()
  set-live(get-live().set/(-)(tns))

fun is-live(name: tName): parc-effs bool
  get-live().member(name)

fun isolated(f: () -> parc-effs a): parc-effs (a, tnameset)
  val saved = get-live()
  val x = f()
  val live' = get-live()
  set-live(saved)
  (x, live')

fun isolated_(f: () -> parc-effs a): parc-effs a
  isolated(f).fst

fun isolate-with(l: tnameset, f: () -> parc-effs a): parc-effs (a, tnameset)
  isolated(fn() { set-live(l); f() })

//-------------------------------
// scope abstractions
//-------------------------------

// Remove the variables from the live set after the action.
fun scoped(vars: tnameset, f: () -> parc-effs a): parc-effs a
  val r = f()
  forget(vars)
  r

// Assume the variables as owned in the scope and insert the necessary drops,
// removing them from the live set afterwards.
fun owned-in-scope(vars: tnameset, f: () -> parc-effs expr): parc-effs expr
  with scoped(vars)
  with extend-owned(vars)
  val body = f()
  val live = get-live()
  val drops = vars.set/(-)(live).list.map(gen-drop)
  maybe-stats(drops, body)

//--------------------------------------------------------------------------
// Newtype / data-info lookups
// (upstream exports `getDataDef'`/`getDataInfo'`/`needsDupDropData` for use
// by the reuse-analysis pass; ported here as `pub` for the same reason)
//--------------------------------------------------------------------------

pub fun get-data-info-x(newtypes: newtypes, tp: ktype): <exn,div> maybe<data-info>
  match tp.extract-data-def-type
    Nothing -> Nothing
    Just(nm) | nm == nameTpBox -> Nothing
    Just(nm) -> match newtypes.lookup-any(nm)
      Nothing -> failure/fail("Core.Parc.getDataDefInfo: cannot find type: " ++ nm.show)
      Just(di) -> Just(di)

pub fun get-data-def-x(newtypes: newtypes, tp: ktype): <exn,div> maybe<data-def>
  match get-data-info-x(newtypes, tp)
    Just(di) -> Just(di.def)
    Nothing -> Nothing

fun get-data-info(tp: ktype): parc-effs maybe<data-info>
  get-data-info-x(parc-config.newtypes, tp)

fun get-is-data-as-maybe(tp: ktype): parc-effs bool
  match get-data-info(tp)
    Just(di) -> match di.data-repr(data/is-value).fst
      DataAsMaybe -> True
      _ -> False
    Nothing -> False

fun get-data-def(tp: ktype): parc-effs data-def
  match get-data-def-x(parc-config.newtypes, tp)
    Just(dd) -> dd
    Nothing -> DataDefNormal
