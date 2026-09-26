// Port of Backend/C/ParcReuse.hs (constructor in-place reuse analysis, runs after Parc).
// Not yet wired into compiler/main/driver.kk's run-core-phase -- see report.
//
// Upstream ParcReuse.hs threads a `Reuse` monad (ReaderT Env (State ReuseState)).
// Following house style (compiler/core/simplify.kk's `simp-env`, compiler/core/uniquefy.kk's
// `uniquefy` effect, compiler/core/fun-lift.kk's `currentDef`): the mutable analysis state
// (available-reuse map / deconstructed map / reused set / lazy-con marker) becomes the `reuse`
// effect's `fun` operations, installed ONCE at the pass entry (`with-reuse`) over `var` locals;
// the reader-like context (platform, newtypes, enableReuse, enclosing-def stack) becomes
// `effect val` declarations, matching `simp-env` / `currentDef`. There is no ReaderT/StateT
// emulation: state flows through effect operations, not through threaded/tuple-returned state.
//
// DEPENDENCY: compiler/backend/c/parc-reuse-spec.kk (ported concurrently by another agent).
// This file uses its `ru-match`/`RuMatch`/`RuNoMatch`, `try-match(expr,pat)`, and the three
// `gen-con*-fields-assign` codegen functions. Only `gen-con-tag-scan-fields-assign` is marked
// `pub` there; `ru-match`/`RuMatch`/`RuNoMatch`/`try-match`/`gen-con-tag-fields-assign`/
// `gen-con-fields-assign` are plain (non-`pub`) top-level bindings -- consistent with most
// other files in this port (e.g. compiler/core/simplify.kk's `simplify-defs` callees are not
// `pub` either and are still called cross-module from compiler/main/driver.kk), so this is
// expected to resolve, but flagging it since it was not verified with a build. See the final
// report for the exact names used.
//
// Dead code NOT ported (unused in upstream ParcReuse.hs itself): foldMapM, maybeStats,
// extractCon, the commented-out `pick` con-matching heuristic, isolateAvailable, and
// deconstructedIntersect (upstream `foldl NameMap.intersection NameMap.empty` always yields
// empty from the first step -- looks like a pre-existing upstream bug, moot since unused).
// Also not ported: the large upstream block comment (constructorSizeOf / orderConFieldsEx /
// hasTagField / etc.) -- that code is `{- ... -}`-commented out in the Haskell source itself.
module compiler/backend/c/parc-reuse

import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/failure
import compiler/common/unique
import compiler/common/syntax
import compiler/type/type
import compiler/kind/newtypes
import compiler/core/core
import compiler/backend/c/parc-reuse-spec
import std/data/rb-set
import std/core/undiv
import std/data/rb-map
import std/data/int-map
import std/num/int64

//--------------------------------------------------------------------------
// Reference count / reuse transformation entry point
//--------------------------------------------------------------------------

// Adapted signature: upstream `parcReuseCore :: Pretty.Env -> Bool -> Platform -> Newtypes ->
// Core -> Unique Core`. The port drops the `Pretty.Env` (tracing here uses plain `.show`
// via `trace`, see `rux-trace` below) and reads/writes the pass's def-groups through the
// ambient `core-phase` effect (`get-core-defs`/`set-core-defs`) instead of taking/returning
// a whole `core` value, matching every other pass in this pipeline (simplify-defs,
// lift-functions, mon-transform, open-resolve, monadic-lift in compiler/main/driver.kk).
pub fun parc-reuse-core(enable-reuse: bool, platform: platform, newtypes: newtypes): <core-phase, unique, pure> ()
  with with-reuse(enable-reuse, platform, newtypes)
  set-core-defs(get-core-defs().rux-def-groups)

//--------------------------------------------------------------------------
// Definition groups
//--------------------------------------------------------------------------

fun rux-def-groups(dgs: def-groups): reuse-eff def-groups
  dgs.map(rux-def-group)

fun rux-def-group(dg: def-group): reuse-eff def-group
  match dg
    DefRec(defs) -> DefRec(defs.map(ru-top-level-def))
    DefNonRec(d) -> DefNonRec(d.ru-top-level-def)

fun ru-top-level-def(d: def): reuse-eff def
  with with-current-def(d)
  d(defExpr = d.defExpr.rux-expr)

//--------------------------------------------------------------------------
// Main PARC algorithm
//--------------------------------------------------------------------------

fun get-ru-con-info(data-type: ktype, con-name: name): reuse-eff maybe<con-info>
  match data-type.ru-extract-data-name
    Nothing -> Nothing
    Just(dname) -> match ru-newtypes.lookup-any(dname)
      Nothing -> Nothing
      Just(di) -> match di.constrs.filter(fn(ci) ci.name == con-name)
        Cons(ci, _) -> Just(ci)
        Nil -> Nothing

fun ru-extract-data-name(tp: ktype): div maybe<name>
  match tp.expand-syn
    TForAll(_, t) -> t.ru-extract-data-name
    TFun(_, _, t) -> t.ru-extract-data-name
    TCon(TypeCon(nm, _)) -> Just(nm)
    TApp(t, _) -> t.ru-extract-data-name
    _ -> Nothing

fun rux-to-assign(m: ru-match): reuse-eff (list<def-group>, (expr, bool /* is match? */))
  match m
    RuMatch(pres, arg) -> (pres.map(fn(pre) DefNonRec(make-def(name/nil, pre))), (arg, True))
    RuNoMatch(e) ->
      if e.is-total then ([], (e, False))
      else
        val nm = unique-name("ru-def")
        val d = DefNonRec(make-def(nm, e))
        val v = Var(TName(nm, e.type-of), InfoNone)
        ([d], (v, False))

fun ru-spec-con(reuse-name: tName, con-name: tName, con-repr: con-repr, con-info: con-info,
                 mb-tag-scan: maybe<(int, maybe<int>)>, matches: list<ru-match>): reuse-eff expr
  val assign-results = matches.map(rux-to-assign)
  val (defss, assigns) = assign-results.unzip
  val result-tp = match con-info.typeScheme.split-fun-scheme
    Just((_, _, _, res)) -> res
    Nothing -> ru-error("ruSpecCon': constructor type is not a function: " ++ con-info.typeScheme.show)
  val fields = con-info.params.map(fst)
  val non-matching = fields.zip(assigns).filter(fn((_, (_, is-match))) !is-match).map(fn((nm, (e, _))) (nm, e))
  val reuse-expr = match mb-tag-scan
    Just((tag, Just(scan))) -> gen-con-tag-scan-fields-assign(result-tp, con-name, con-repr, reuse-name, tag, scan, non-matching)
    Just((tag, Nothing)) -> gen-con-tag-fields-assign(result-tp, con-name, con-repr, reuse-name, tag, non-matching)
    Nothing -> gen-con-fields-assign(result-tp, con-name, con-repr, reuse-name, non-matching)
  // upstream also binds an unused `res <- uniqueTName "res" resultType`; kept for parity of the
  // generated-name unique counter (its own `res` binding is dead in the returned expression there too).
  val _res = unique-tname("res", result-tp)
  make-let(defss.concat, reuse-expr)

fun strip-lets(e: expr): div (list<def-group>, expr)
  match e
    Let([], body) -> body.strip-lets
    Let(Cons(DefNonRec(d), dgs), body) ->
      val (dgs1, body1) = body.strip-lets
      (Cons(DefNonRec(d), dgs1 ++ dgs), body1)
    _ -> ([], e)

fun make-lets(dgs: list<def-group>, e: expr): expr
  if dgs.is-nil then e else make-let(dgs, e)

fun rux-expr(e: expr): reuse-eff expr
  match e
    App(Var(name, _), [Var(tname, _), ELit(LitInt(size)), ELit(LitInt(scan))]) | name.get-name == nameLazyMemoizeTarget ->
      tname.register-lazy-con
      add-deconstructed((tname, Nothing, size, scan))
      TName(name/nil, typeReuse).deconstruct-lazy-con
      exprUnit
    App(Var(name, _), [Var(tname, _), con-app]) | name.get-name == nameLazyMemoize ->
      ru-lazy-memoize(tname, con-app)
    App(conx as Con(cname, repr), args) ->
      val args1 = args.map(rux-expr)
      ru-try-reuse-con(cname, repr, App(conx, args1))
    App(ta as TypeApp(Con(cname, repr), _), args) ->
      val args1 = args.map(rux-expr)
      ru-try-reuse-con(cname, repr, App(ta, args1))
    TypeLam(tpars, body) -> TypeLam(tpars, body.rux-expr)
    TypeApp(body, targs) -> TypeApp(body.rux-expr, targs)
    Lam(pars, eff, body) -> ru-lam(pars, eff, body)
    App(f, args) -> App(f.rux-expr, args.map(rux-expr))
    Let([], body) -> body.rux-expr
    Let(Cons(DefNonRec(def), dgs), body) -> ru-let(def, Let(dgs, body))
    Let(_, _) -> ru-error("Backend.C.Reuse.ruExpr: " ++ e.show)
    // Since this runs after Parc: the scrutinees are variables
    Case(scrutinees, branches) ->
      val svars = scrutinees.map fn(s)
        match s
          Var(tn, _) -> tn
          _ -> ru-error("ParcReusePost: scrutinees must be variables! But got " ++ s.show)
      Case(scrutinees, rux-branches(svars, branches))
    // Var, Lit, Con
    _ -> e

fun ru-lam(pars: list<tName>, eff: ktype, body: expr): reuse-eff expr
  val body1 = with-none fn()
    pars.foreach fn(p)
      match p.type-of.get-ru-fixed-data-alloc-size
        Just((size, scan)) -> add-deconstructed((p, Nothing, size, scan))
        Nothing -> ()
    body.rux-expr
  Lam(pars, eff, body1)

// The result of processing one `let`-binding: how many freshly-created reuse tokens it
// contributes (to be dropped if unused) and a continuation prepending its generated code.
// This is genuinely a *deferred* decision -- upstream only knows, once the WHOLE rest of the
// let-chain has been analysed, which reuse tokens created along the way actually got consumed
// (by a later `App(Con ..)` matching their size). It is not state-threading: the mutable
// `reused` effect state is queried once (`get-reused()`, after `expr` has been processed) and
// handed to this pure closure, exactly mirroring upstream's `Reused -> (...)`.
alias let-step = (reused) -> pure (list<tName>, expr -> pure expr)

// identity continuation, typed exactly at `let-step`'s (pure) continuation effect so it
// unifies with the other `let-step`-producing match branches below (which go through
// `make-defs-let` and are themselves inferred `pure`)
fun let-step-id(e: expr): pure expr
  e

// prepend `defs` before the rest of the let-chain; typed exactly at `let-step`'s (pure)
// continuation effect (via this function's own declared return type) so every match branch
// below produces a value of the SAME concrete closure type instead of each anonymous
// `fn(e) make-defs-let(...)` being inferred independently (which produced mismatched
// `total` vs `pure` effects across branches of `ru-let-prime`/`ru-let-expr`).
fun let-step-prepend(defs: list<def>): total (expr -> pure expr)
  fn(e: expr) make-defs-let(defs, e)

fun ru-let(def: def, expr: expr): reuse-eff expr
  val av1 = get-available()
  val fn1 = def.ru-let-prime
  val expr1 = expr.rux-expr
  val av2 = get-available()
  set-available-intersect([av1, av2])
  val reused0 = get-reused()
  val (rus, fe) = fn1(reused0)
  val ds = rus.map(fn(tn) make-tdef(tn, gen-reuse-null()))
  set-reused(reused0 - rus)
  make-defs-let(ds, fe(expr1))

fun ru-let-expr(expr: expr): reuse-eff let-step
  match expr
    Let([], body) -> body.ru-let-expr
    Let(Cons(DefNonRec(def), dgs), body) ->
      val fn1 = def.ru-let-prime
      val fn2 = Let(dgs, body).ru-let-expr
      fn(rd: reused)
        val (ds1, fe1) = fn1(rd)
        val (ds2, fe2) = fn2(rd)
        (ds1 ++ ds2, fn(e: expr) fe1(fe2(e)))
    _ -> fn(_: reused) ([], let-step-id)

fun ru-let-prime(def: def): reuse-eff let-step
  with with-current-def(def)
  match def.defExpr
    App(Var(name, _), Cons(Var(tname, _), _maybe-scan-fields)) | name.get-name == nameDrop ->
      val ru = tname.ru-make-available
      val scan = tname.ru-get-scan
      fn(rd: reused)
        match ru
          Just(runame) | rd.member(runame) ->
            val assign = match scan
              Just(sc) -> gen-drop-reuse(tname, make-int32(sc))
              Nothing -> gen-reuse-address(tname)
            ([runame], let-step-prepend([make-def(name/nil, gen-reuse-assign-with(runame, assign))]))
          _ -> ([], let-step-prepend([def]))
    // See core/core's `make-drop-special`: we assume this always occurs in a definition.
    App(Var(name, _), [Var(y, _), x-unique, r-shared, x-dec-ref]) | name.get-name == nameDropSpecial ->
      val f-unique = x-unique.ru-let-expr
      val reg-lazy-con = get-registered-lazy-con()
      match reg-lazy-con
        Just(reg) | y == reg ->
          val ru = unique-reuse-name(typeReuse)
          ru.deconstruct-lazy-con
          fn(rd: reused)
            val (rus-unique, r-unique-p) = f-unique(rd)
            val r-unique = r-unique-p(exprUnit)
            if rd.member(ru) then
              val r-reuse = gen-reuse-assign-with(ru, gen-reuse-address(y))
              (Cons(ru, rus-unique), let-step-prepend([make-def(name/nil, make-stats([r-unique, r-reuse]))]))
            else
              (rus-unique, let-step-prepend([make-def(name/nil,
                make-if-expr(gen-is-unique(y), make-stats([r-unique, gen-free(y)]), make-stats([r-shared, x-dec-ref])))]))
        _ ->
          val ru = y.ru-make-available
          fn(rd: reused)
            val (rus-unique, r-unique-p) = f-unique(rd)
            val r-unique = r-unique-p(exprUnit)
            match ru
              Just(runame) | rd.member(runame) ->
                val r-reuse = gen-reuse-assign-with(runame, gen-reuse-address(y))
                (Cons(runame, rus-unique), let-step-prepend([make-def(name/nil,
                  make-if-expr(gen-is-unique(y), make-stats([r-unique, r-reuse]), make-stats([r-shared, x-dec-ref])))]))
              _ ->
                (rus-unique, let-step-prepend([make-def(name/nil,
                  make-if-expr(gen-is-unique(y), make-stats([r-unique, gen-free(y)]), make-stats([r-shared, x-dec-ref])))]))
    _ ->
      val de = def.defExpr.rux-expr
      fn(_: reused) ([], let-step-prepend([def(defExpr=de)]))

fun ru-make-available(tname: tName): reuse-eff maybe<tName>
  val ds = get-deconstructed()
  match (ru-enable-reuse, ds.lookup(tname.get-name))
    (True, Just((pat, size, _scan))) ->
      val rname = unique-reuse-name(typeReuse)
      // `insert-with` combines as (new, old), so this prepends the fresh credit
      set-available(get-available().insert-with(size.int64, [Reuse-info(rname, pat)], fn(nw: list<reuse-info>, old: list<reuse-info>) nw.list/(++)(old)))
      Just(rname)
    _ -> Nothing

fun ru-get-scan(tname: tName): reuse-eff maybe<int>
  match get-deconstructed().lookup(tname.get-name)
    Just((_, _, scan)) -> Just(scan)
    _ -> Nothing

fun rux-branches(scrutinees: list<tName>, branches: list<branch>): reuse-eff list<branch>
  val results = branches.map(fn(b) b.rux-branch(scrutinees))
  val (branch-fns, rs, avs) = results.unzip3
  set-available-intersect(avs)
  val rus = rs.reused-union
  set-reused(rus)
  val reuse-drops: rbmap<tName,expr> = rb-map/from-list(rus.list.map(fn(tn) (tn, gen-reuse-drop(tn))))
  branch-fns.map(fn(bf) bf(reuse-drops))

fun rux-branch(b: branch, scrutinees: list<tName>): reuse-eff ((rbmap<tName,expr>) -> pure branch, reused, available)
  val ((bf, rd), av) = isolate-get-available fn()
    isolate-deconstructed fn()
      isolate-get-reused fn()
        val reuses = scrutinees.zipwith(b.patterns, ru-pattern).concat  // must be in depth order, as in Parc
        reuses.foreach(add-deconstructed)
        val gs = b.guards.map(rux-guard)
        val (guards1, avs) = gs.unzip
        set-available-intersect(avs)
        fn(reuse-drops: rbmap<tName,expr>): pure branch
          Branch(b.patterns, guards1.map(fn(gf) gf(reuse-drops)))
  (bf, rd, av)

fun add-deconstructed(entry: (tName, maybe<pattern>, int, int)): reuse-eff ()
  val (tn, pat, size, scan) = entry
  if size > 0 then
    set-deconstructed(rb-map/set(get-deconstructed(), tn.get-name, (pat, size, scan)))

fun ru-pattern(scrutinee: tName, pat: pattern): reuse-eff list<(tName, maybe<pattern>, int, int)>
  match pat
    PatVar(tname, p) -> ru-pattern(tname, p)
    PatCon(pat-con-name, pat-con-patterns, pat-con-repr, _typeArgs, _kexists, _typeRes, _info, _skip) ->
      // NOTE: faithfully preserved from upstream -- the recursive call passes the OUTER
      // `scrutinee`, not each subpattern's own binder, into `mapM (ruPattern varName)
      // patConPatterns`. This only matters when a subpattern is not itself wrapped in a
      // `PatVar` (rare in practice): the `PatVar` clause above ignores the passed-in name
      // and recurses on its own binder instead, which is the common case.
      val reuses = pat-con-patterns.map(fn(p) ru-pattern(scrutinee, p)).concat
      if pat-con-name.get-name == nameBoxCon then reuses  // don't reuse boxes
      else
        // use the constructor's own (uninstantiated) repr to compute the correct size
        val (size, scan) = pat-con-repr.alloc-size-scan(ru-platform)
        if size > 0 then Cons((scrutinee, Just(pat), size, scan), reuses) else reuses
    _ ->
      match scrutinee.type-of.get-ru-fixed-data-alloc-size
        Just((size, scan)) -> [(scrutinee, Nothing, size, scan)]
        Nothing -> []

fun rux-guard(g: guard): reuse-eff ((rbmap<tName,expr>) -> pure guard, available)
  isolate-get-available fn()
    val test1 = with-none( fn() g.test.rux-expr )
    val expr1 = g.body.rux-expr
    val reused-here = get-reused()
    fn(reuse-drops: rbmap<tName,expr>): pure guard
      val drops-here = reuse-drops.filter(fn(k, _v) !reused-here.member(k)).values
      Guard(test1, make-stats(drops-here ++ [expr1]))

pub type reusable
  NotReusable
  ReusableWithSize(size: int)

pub fun ru-is-reusable(repr: con-repr, platform: platform): reusable
  val size = repr.alloc-size(platform)
  // never try to reuse a Just-like constructor; `_noreuse`-suffixed types are a special
  // case to allow benchmarking the effect of reuse analysis; size 0 indicates value types
  if repr.is-con-as-just || repr.n.local.ends-with("_noreuse").bool || size == 0
    then NotReusable
    else ReusableWithSize(size)

fun is-con-as-just(repr: con-repr): bool
  match repr
    ConAsJust -> True
    _ -> False

fun ru-try-reuse-con(cname: tName, repr: con-repr, con-app: expr): reuse-eff expr
  match ru-is-reusable(repr, ru-platform)
    NotReusable -> con-app
    ReusableWithSize(size) ->
      val avail = get-available()
      match avail.lookup(size.int64)
        Just(Cons(rinfo, rinfos)) ->
          set-available(avail.set(size.int64, rinfos))
          mark-reused(rinfo.reuse-name)
          gen-alloc-at(rinfo, con-app, con-app.type-of)
        _ -> con-app
  // upstream keeps a `pick`-a-good-match heuristic here (prefer reusing the same
  // constructor), but it is commented out / disabled there too ("Picking can prevent
  // reuse in FIP programs, disabled for now") -- not ported.

fun ru-lazy-memoize(lazy-tname: tName, arg: expr): reuse-eff expr
  val ds = get-deconstructed()
  lazy-tname.maybe-mark-deconstructed-lazy-con-as-reused
  val reuse-name = unique-reuse-name(typeReuse)
  val (box-defs, tail-arg) = arg.strip-lets
  val box-defs1 = box-defs.map(rux-def-group)

  // Nested helpers are ordered so each only calls ones already defined above it (no forward
  // references needed among these local funs): lazy-reuse, lazy-apply-indirect-con-at,
  // lazy-indirect, update-con.

  // specialized reuse, or a fallback that overwrites all fields
  fun lazy-reuse(lazy-info: (maybe<pattern>, int, int), mci: maybe<con-info>, cname: tName, crepr: con-repr, conx: expr, args1: list<expr>): reuse-eff expr
    match (lazy-info, mci)
      ((Just(PatCon(pat-con-name, pat-con-patterns, _, _, _, _, _, _)), _size, scan), Just(ci)) ->
        val matches = args1.zipwith(pat-con-patterns, try-match)
        val needs-tag = pat-con-name != cname
        val needs-scan = scan != crepr.scan-count
        val mb-tag-scan: maybe<(int, maybe<int>)> =
          if needs-scan then Just((crepr.tag, Just(crepr.scan-count)))
          elif needs-tag then Just((crepr.tag, Nothing))
          else Nothing
        ru-spec-con(reuse-name, cname, crepr, ci, mb-tag-scan, matches)
      ((_, _, _), Just(ci)) ->
        // we cannot use alloc-at since that resets the reference count to 0 (and we need
        // to keep the current ref count)
        val matches = args1.map(RuNoMatch)
        val mb-tag-scan = Just((crepr.tag, Just(crepr.scan-count)))
        ru-spec-con(reuse-name, cname, crepr, ci, mb-tag-scan, matches)
      (_, Nothing) ->
        ru-error("ruLazyMemoize.lazyReuse: missing constructor info for " ++ cname.show)

  fun lazy-apply-indirect-con-at(lazy-info: (maybe<pattern>, int, int), arg1: expr): reuse-eff expr
    match get-lazy-indirect-con(lazy-tname)
      Just((cinfo, crepr)) ->
        val (_, rho) = cinfo.typeScheme.split-type-scheme
        val cname = TName(cinfo.name, rho)
        val conx = Con(cname, crepr)
        lazy-reuse(lazy-info, Just(cinfo), cname, crepr, conx, [arg1])
      Nothing ->
        ru-error("Backend.C.ParcReuse.getLazyIndirectCon: cannot find indirection constructor for " ++ lazy-tname.show)

  // create an indirection
  fun lazy-indirect(lazy-info: (maybe<pattern>, int, int), is-singleton: bool, a: expr): reuse-eff expr
    val arg-name = unique-tname("lazyres", lazy-tname.type-of)
    val arg1 = a.rux-expr
    val arg-var = Var(arg-name, InfoNone)
    val ind-con = lazy-apply-indirect-con-at(lazy-info, arg-var)
    val ind-expr = make-if-expr(gen-is-unique(lazy-tname),
      make-stats([gen-free(lazy-tname), arg-var]),
      make-stats(Cons(ind-con, (if is-singleton then [] else [gen-dup(arg-name)]) ++ [gen-dec-ref(lazy-tname), arg-var])))
    make-defs-let([make-def(arg-name.get-name, arg1)], ind-expr)

  fun update-con(lazy-info: (maybe<pattern>, int, int), cname: tName, crepr: con-repr, conx: expr, args: list<expr>): reuse-eff expr
    val (_pat, lazy-size, _scan) = lazy-info
    val size = crepr.alloc-size(ru-platform)
    if lazy-size < size then
      // the target is too small! (checked already during kind inference upstream)
      lazy-indirect(lazy-info, False, App(conx, args))
    elif size == 0 then
      // singleton
      lazy-indirect(lazy-info, True, App(conx, args))
    else
      // generate alloc-at
      val args1 = args.map(rux-expr)
      val mci = get-ru-con-info(cname.type-of, cname.get-name)
      lazy-reuse(lazy-info, mci, cname, crepr, conx, args1)

  val body = match ds.lookup(lazy-tname.get-name)
    Nothing ->
      ru-warning("cannot find lazy update target " ++ lazy-tname.show ++ ", using indirection instead")
      lazy-indirect((Nothing, 0, 0), False, tail-arg)
    Just(lazy-info) ->
      match tail-arg
        // try to write the constructor in-place on the lazy one
        App(conx as Con(cname, repr), args) -> update-con(lazy-info, cname, repr, conx, args)
        App(conx as TypeApp(Con(cname, repr), _targs), args) -> update-con(lazy-info, cname, repr, conx, args)
        // singleton uses an indirection
        Con -> lazy-indirect(lazy-info, True, tail-arg)
        // otherwise use an indirection (no warning needed -- checked in Kind.Infer upstream)
        _ -> lazy-indirect(lazy-info, False, tail-arg)
  make-lets(box-defs1 ++ [DefNonRec(make-def(reuse-name.get-name, gen-reuse-address(lazy-tname)))], body)

//--------------------------------------------------------------------------
// Codegen helpers for reuse-related primitives
//--------------------------------------------------------------------------

fun gen-dec-ref(tname: tName): expr
  val fun-tp = TFun([(name/nil, tname.type-of)], typeTotal, typeUnit)
  App(Var(TName(nameDecRef, fun-tp), InfoExternal("decref(#1,current_context())")), [Var(tname, InfoNone)])

fun gen-dup(nm: tName): expr
  val tp = nm.type-of
  val coerce-tp = TFun([(name/nil, tp)], typeTotal, tp)
  App(Var(TName(nameDup, coerce-tp), InfoExternal("dup(#1)")), [Var(nm, InfoNone)])

// Generate a reuse-drop of a constructor
fun gen-drop-reuse(tname: tName, scan: expr /* : int32 */): expr
  val fun-tp = TFun([(name/nil, tname.type-of), (name/nil, typeInt32)], typeTotal, typeReuse)
  App(Var(TName(nameDropReuse, fun-tp), InfoExternal("drop_reuse(#1,#2,kk_context())")), [Var(tname, InfoNone), scan])

// Generate allocation-at of a constructor application; `con-app` should have the
// form `App(Con(_,_), conArgs)` with `length conArgs >= 1`.
fun gen-alloc-at(ri: reuse-info, con-app: expr, con-tp: ktype): expr
  val info = match ri.ru-pat
    Just(p) -> InfoReuse(p)
    Nothing -> InfoNone
  val type-alloc-at = TFun([(name/nil, typeReuse), (name/nil, con-tp)], typeTotal, con-tp)
  App(Var(TName(nameAllocAt, type-alloc-at), InfoArity(0, 2)), [Var(ri.reuse-name, info), con-app])

// Generate a test if a (locally bound) name is unique
fun gen-is-unique(tname: tName): expr
  val fun-tp = TFun([(name/nil, tname.type-of)], typeTotal, typeBool)
  App(Var(TName(nameIsUnique, fun-tp), InfoExternal("is_unique(#1)")), [Var(tname, InfoNone)])

// Generate a free of a constructor
fun gen-free(tname: tName): expr
  val fun-tp = TFun([(name/nil, tname.type-of)], typeTotal, typeUnit)
  App(Var(TName(nameFree, fun-tp), InfoExternal("kk_constructor_free(#1,kk_context())")), [Var(tname, InfoNone)])

// Generate a drop of a reuse token
fun gen-reuse-drop(tname: tName): expr
  val fun-tp = TFun([(name/nil, tname.type-of)], typeTotal, typeReuse)
  App(Var(TName(nameReuseDrop, fun-tp), InfoExternal("kk_reuse_drop(#1,kk_context())")), [Var(tname, InfoNone)])

// Get a null token for reuse inlining
fun gen-reuse-null(): expr
  val fun-tp = TFun([], typeTotal, typeReuse)
  App(Var(TName(nameReuseNull, fun-tp), InfoExternal("kk_reuse_null")), [])

// Generate a reuse of a block
fun gen-reuse-address(tname: tName): expr
  val fun-tp = TFun([(name/nil, tname.type-of)], typeTotal, typeReuse)
  App(Var(TName(nameReuse, fun-tp), InfoExternal("reuse_datatype(#1,kk_context())")), [Var(tname, InfoNone)])

fun gen-reuse-assign-with(reuse-name: tName, arg: expr): expr
  val assign = TName(nameAssignReuse, TFun([(name/nil, typeReuse), (name/nil, typeReuse)], typeTotal, typeUnit))
  App(Var(assign, InfoExternal("#1 = #2")), [Var(reuse-name, InfoNone), arg])

//--------------------------------------------------------------------------
// Utilities for readability
//--------------------------------------------------------------------------

// create a unique name specific to this module
fun unique-reuse-name(tp: ktype): reuse-eff tName
  unique-tname("ru", tp)

fun unique-tname(pre: string, tp: ktype): reuse-eff tName
  TName(unique-name(pre), tp)

// `unzip3` is provided by std (`list/unzip3`); no local definition needed.

//--------------------------------------------------------------------------
// Reuse effect: mutable analysis state + reader-like context
//--------------------------------------------------------------------------

// Byte-size -> stack of available reuse credits
// Patricia tree keyed by byte size.
alias available = int-map<list<reuse-info>>
alias deconstructed = name-map<(maybe<pattern>, int, int)>
alias reused = rbset<tName>

struct reuse-info
  reuse-name: tName
  ru-pat: maybe<pattern>

type lazy-con
  NoLazyCon
  KnownLazyCon(tname: tName)
  DeconstructedLazyCon(tname: tName, rname: tName)

// mutable analysis state, installed once at the pass entry (`with-reuse`)
effect reuse
  fun get-available(): available
  fun set-available(av: available): ()
  fun get-deconstructed(): deconstructed
  fun set-deconstructed(ds: deconstructed): ()
  fun get-reused(): reused
  fun set-reused(r: reused): ()
  fun get-lazy-con(): lazy-con
  fun set-lazy-con(lc: lazy-con): ()

// reader-like context; `ru-encl-def` is pushed/popped per top-level def via `with-current-def`
// (mirrors compiler/core/fun-lift.kk's `currentDef`), the others are set once for the whole pass
effect val ru-platform: platform
effect val ru-newtypes: newtypes
effect val ru-enable-reuse: bool
effect val ru-encl-def: list<def>

alias reuse-eff = <reuse, unique, ru-platform, ru-newtypes, ru-enable-reuse, ru-encl-def, pure>

fun with-reuse(enable-reuse: bool, platform: platform, newtypes: newtypes,
                f: () -> <reuse, unique, ru-platform, ru-newtypes, ru-enable-reuse, ru-encl-def|e> a): <unique|e> a
  var available := (int-map/empty() : available)
  var deconstructed := (rb-map/empty() : deconstructed)
  var reused := (rb-set/empty() : reused)
  var lazy-con := NoLazyCon
  with handler
    fun get-available() available
    fun set-available(av) available := av
    fun get-deconstructed() deconstructed
    fun set-deconstructed(ds) deconstructed := ds
    fun get-reused() reused
    fun set-reused(r) reused := r
    fun get-lazy-con() lazy-con
    fun set-lazy-con(lc) lazy-con := lc
  with val ru-platform = platform
  with val ru-newtypes = newtypes
  with val ru-enable-reuse = enable-reuse
  with val ru-encl-def = []
  f()

fun with-current-def(d: def, f)
  with override
    val ru-encl-def = Cons(d, ru-encl-def)
  f()

fun mark-reused(tn: tName): reuse-eff ()
  set-reused(get-reused() + tn)

fun reused-union(rs: list<reused>): reused
  rs.unions

fun set-available-intersect(avs: list<available>): reuse-eff ()
  match avs
    [] -> ()
    _ -> set-available(avs.available-intersect-all)

fun available-intersect-all(avs: list<available>): available
  match avs
    [] -> int-map/empty()
    [a] -> a
    Cons(a, rest) -> a.available-intersect(rest.available-intersect-all)

// upstream: `M.intersectionWith intersect`, where
// `intersect xs ys = [r | r@(ReuseInfo rname _) <- xs, rname `elem` map reuseName ys]`.
// A size present in both is KEPT even when the surviving credit list is empty
// the only consumer matches `Just(Cons(..))`, so an empty entry reads as "no
// credit" exactly like an absent one.
fun available-intersect(a: available, b: available): available
  intersection-with(a, b) fn(xs: list<reuse-info>, ys: list<reuse-info>)
    xs.filter(fn(ri) ys.any(fn(ri2) ri2.reuse-name == ri.reuse-name))

fun register-lazy-con(tname: tName): reuse-eff ()
  set-lazy-con(KnownLazyCon(tname))

fun get-registered-lazy-con(): reuse-eff maybe<tName>
  match get-lazy-con()
    KnownLazyCon(tname) -> Just(tname)
    DeconstructedLazyCon(tname, _) -> Just(tname)
    _ -> Nothing

fun deconstruct-lazy-con(rname: tName): reuse-eff ()
  match get-lazy-con()
    KnownLazyCon(tname) -> set-lazy-con(DeconstructedLazyCon(tname, rname))
    DeconstructedLazyCon(tname, _) -> set-lazy-con(DeconstructedLazyCon(tname, rname))
    NoLazyCon -> ru-error("deconstructLazyCon: not a known lazy con")

// unused upstream too (dead code, kept for parity with the lazy-con state machine)
fun get-deconstructed-lazy-con(): reuse-eff (tName, tName)
  match get-lazy-con()
    DeconstructedLazyCon(tname, rname) -> (tname, rname)
    KnownLazyCon(tname) -> ru-error("getDeconstructedLazyCon: " ++ tname.show ++ " was not deconstructed")
    NoLazyCon -> ru-error("getDeconstructedLazyCon: no known lazy con")

fun maybe-mark-deconstructed-lazy-con-as-reused(_lazy-tname: tName): reuse-eff ()
  match get-lazy-con()
    DeconstructedLazyCon(_, rname) | !rname.get-name.is-nil -> mark-reused(rname)
    _ -> ()

// Execute the action with an empty available/deconstructed state -- used for the body of
// lambdas and the test of guards.
fun with-none(f: () -> reuse-eff a): reuse-eff a
  val av0 = get-available()
  val ds0 = get-deconstructed()
  set-available(int-map/empty())
  set-deconstructed(rb-map/empty())
  val x = f()
  set-available(av0)
  set-deconstructed(ds0)
  x

fun isolate-get-available(f: () -> reuse-eff a): reuse-eff (a, available)
  val av0 = get-available()
  val x = f()
  val av1 = get-available()
  set-available(av0)
  (x, av1)

fun isolate-deconstructed(f: () -> reuse-eff a): reuse-eff a
  val ds0 = get-deconstructed()
  val x = f()
  set-deconstructed(ds0)
  x

fun isolate-get-reused(f: () -> reuse-eff a): reuse-eff (a, reused)
  val rd0 = get-reused()
  val x = f()
  val rd1 = get-reused()
  set-reused(rd0)
  (x, rd1)

//--------------------------------------------------------------------------
// Tracing
//--------------------------------------------------------------------------
// Simplified vs. upstream: upstream formats a colored `Pretty.Env` doc; this port just
// `.show`s the enclosing def names, since tracing here is a debug aid, not observable output.

fun rux-trace(msg: string): reuse-eff ()
  trace("Core.Reuse: " ++ ru-encl-def.map(fn(d) d.def-name.show).show ++ ": " ++ msg)

fun ru-warning(msg: string): reuse-eff ()
  trace("Core.Reuse: " ++ ru-encl-def.map(fn(d) d.def-name.show).show ++ ": warning: " ++ msg)

fun ru-error(msg: string): reuse-eff a
  failure/fail("Core.Reuse: " ++ ru-encl-def.map(fn(d) d.def-name.show).show ++ ": " ++ msg)

//--------------------------------------------------------------------------
// Constructor / data size helpers
//--------------------------------------------------------------------------

fun get-ru-fixed-data-alloc-size(data-type: ktype): reuse-eff maybe<(int, int)>
  get-fixed-data-alloc-size(ru-platform, ru-newtypes, data-type)

// If all constructors of a type have the same shape, return the byte size and number of
// scan fields. A function value has none: its size depends on what the closure
// captures, and `get-data-info` would otherwise answer with the size of its result type.
pub fun get-fixed-data-alloc-size(platform: platform, newtypes: newtypes, data-type: ktype): div maybe<(int, int)>
  if data-type.split-fun-scheme.is-just then Nothing else
    match get-data-info(newtypes, data-type)
      Nothing -> Nothing
      Just((data-name, data-info)) ->
        if data-name.local.ends-with("_noreuse").bool then Nothing
        else if data-info.def.is-value then Nothing
        else
          val size-scans = data-info.constrs.map(fn(ci) platform.scan-size(ci.valueRepr))
          match size-scans
            Cons(ss, rest) | rest.all(fn(s) s.fst == ss.fst && s.snd == ss.snd) -> Just(ss)
            _ -> Nothing

fun get-lazy-indirect-con(lazy-tname: tName): reuse-eff maybe<(con-info, con-repr)>
  match get-data-info(ru-newtypes, lazy-tname.type-of)
    Nothing -> Nothing
    Just((_, data-info)) ->
      match data-info.constrs.filter(fn(ci) ci.name.is-lazy-indirect-con-name)
        [ci] | ci.params.length == 1 -> Just((ci, data-info.con-repr(ci)))
        _ -> Nothing

fun get-data-info(newtypes: newtypes, data-type: ktype): div maybe<(name, data-info)>
  match data-type.ru-extract-data-name
    Nothing -> Nothing
    Just(nm) -> match newtypes.lookup-any(nm)
      Just(di) -> Just((nm, di))
      Nothing -> Nothing
