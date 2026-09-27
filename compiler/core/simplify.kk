// Core simplification (port of Core/Simplify.hs)
// Ported as of 2026-07-25; upstream baseline commit dd91082 of Core/Simplify.hs
module compiler/core/simplify

import compiler/common/failure
import compiler/common/range
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/unique
import compiler/platform/config
import compiler/kind/kind
import compiler/type/type
import compiler/type/kind
import compiler/type/typevar
import compiler/core/core
import compiler/core/corevar
import compiler/core/uniquefy
import std/data/rb-set
import std/core/undiv
import std/data/rb-map
import compiler/common/name-collections

// settings for a simplification run
pub struct simp-settings
  is-unsafe: bool   // remove all `@open` calls (final simplification)
  ndebug: bool      // remove assertions
  dup-max: int      // maximum size of expressions that may be duplicated on inlining

pub effect val simp-env: simp-settings

pub alias simp-eff = <simp-env, unique, pure, comp-flags>

// Simplify the core definitions in the current core phase
pub fun simplify-defs(unsafe0: bool, ndebug: bool, nRuns: int, dupMax: int): _ ()
  with val simp-env = Simp-settings(unsafe0, ndebug, dupMax)
  set-core-defs(simplifyN(nRuns, get-core-defs().uniquefy-def-bodies))

pub fun simplifyN(nRuns: int, dgs: def-groups): simp-eff def-groups
  if nRuns <= 0 then dgs
  else simplifyN(nRuns - 1, dgs.map(dg/simplify))

fun uniquefy-def-bodies(dgs: def-groups): _ def-groups
  dgs.map fn(dg)
    match dg
      DefRec(defs) -> DefRec(defs.map(fn(d) d(defExpr = d.defExpr.expr/uniquefy)))
      DefNonRec(d) -> DefNonRec(d(defExpr = d.defExpr.expr/uniquefy))

//--------------------------------------------------------------------------
// Top-down transformations; these must call simplify recursively when needed
//--------------------------------------------------------------------------

fun top-down(ex: expr): simp-eff expr
  match ex
    Let(dgs, body) -> top-down-let([], [], dgs, body)
    // remove assertions in ndebug mode
    App(assert as Var(nm), [msg, cond]) | nm.get-name == nameAssert ->
      if simp-env.ndebug then exprUnit
      else App(assert, [msg, cond])
    // remove identity open applications; need to be careful about total effects
    App(app as TypeApp(Var(openName), [effFrom, effTo, _tpFrom, _tpTo]), [arg]) | openName.get-name == nameEffectOpen ->
      val (lsFrom, tlFrom) = effFrom.extract-handled-effect
      val (lsTo, tlTo) = effTo.extract-handled-effect
      if arg.has-no-effect-expr ||
         (match-type(tlFrom, tlTo) && lsFrom.length == lsTo.length &&
          lsFrom.zip(lsTo).all(fn((t1, t2)) match-type(t1, t2))) then arg
      // upstream falls THROUGH to the next equation when the identity guard
      // fails: a non-identity open is still removed in the unsafe (final) pass
      elif simp-env.is-unsafe then arg
      else App(app, [arg])
    // remove all open applications (only if all transformations are done)
    App(app as TypeApp(Var(openName)), [arg]) | openName.get-name == nameEffectOpen ->
      if simp-env.is-unsafe then arg else App(app, [arg])
    App(app as TypeApp(Var(_, InfoExternal("#1"))), [arg]) ->
      if simp-env.is-unsafe then arg else App(app, [arg])
    // beta reduction
    App(Lam(pars, _, body), args) | pars.length == args.length ->
      val avoid = body.bound-names
      val newNames = pars.map(fn(p) p.unique-tname-avoiding(avoid))
      val sub = pars.zip(newNames.map(fn(np) Var(np, InfoNone)))
      make-let(newNames.zipwith(args, make-par-def), sub |-> body)
    // beta reduction with type application
    App(TypeApp(TypeLam(tpars, Lam(pars, _, body)), targs), args) | pars.length == args.length && tpars.length == targs.length ->
      val tsub = new/sub(tpars.zip(targs))
      val avoid = body.bound-names
      val newNames = pars.map(fn(TName(nm, tp)) unique-tname-avoiding(TName(nm, tsub |-> tp), avoid))
      val sub = pars.zip(newNames.map(fn(np) Var(np, InfoNone)))
      Let(newNames.zipwith(args, make-par-def), sub |-> expr/substitute(tsub, body))
    // case of let
    Case([Let(dgs, e)], branches) ->
      Let(dgs, Case([e], branches))
    // case of case: push outer branches into the inner case when it does not duplicate
    Case([Case(scruts0, branches0)], branches1) ->
      if !case-of-case-ok(branches0, branches1) then ex
      else
        fun push-case-g(g: guard)
          Guard(g.test, Case([g.body], branches1))
        fun push-case(b: branch)
          Branch(b.patterns, b.guards.map(push-case-g))
        Case(scruts0, branches0.map(push-case))
    // application of a case expression: push the application into the branches
    App(Case(scruts, branches), args) ->
      val (sbinders, bscruts) = bind-exprs(scruts)
      val (binders, bargs) = bind-exprs(args)
      fun make-guard-app(g: guard)
        Guard(g.test, App(g.body, bargs))
      fun make-branch-app(b: branch)
        Branch(b.patterns, b.guards.map(make-guard-app))
      sbinders(binders(Case(bscruts, branches.map(make-branch-app))))
    // float let bindings
    TypeApp(Let(binds, e), targs) ->
      Let(binds, TypeApp(e, targs))
    App(f, args) ->
      val (fbinds, fexpr) = f.float-let
      val (abindss, aexprs) = args.map(float-let).unzip
      make-let(Cons(fbinds, abindss).concat, App(fexpr, aexprs)) // note: assumes unique bindings!
    _ -> ex

fun make-par-def(tn: tName, arg: expr): def-group
  DefNonRec(Def(tn.get-name, tn.type-of, arg, Private, DefVal, InlineAuto, range/null, ""))

fun is-var-named(e: expr, nm: name): bool
  match e
    Var(v) -> v.get-name == nm
    _ -> False

fun float-let(e: expr): (list<def-group>, expr)
  match e
    Let(binds, body) ->
      val (binds', body') = body.float-let
      (binds ++ binds', body')
    _ -> ([], e)

fun has-no-effect-expr(e: expr): bool
  match e
    TypeApp(e') -> e'.has-no-effect-expr
    ELit -> True
    Con -> True
    _ -> False

fun case-of-case-ok(branches0: list<branch>, branches1: list<branch>): simp-eff bool
  fun simplifies-on-e(e: expr): _ bool
    match e
      Let(_, body) -> body.pretend-decreasing.simplifies-on-e
      _ -> kmatch-branches([e], branches1).is-just
  fun simplifies-on(b: branch)
    b.guards.all(fn(g) g.body.simplifies-on-e)
  val single = match branches0
    [Branch(_, [_])] -> True
    _ -> False
  // upstream PR koka-lang/koka#902: each inner branch that does not collapse
  // keeps a FULL COPY of the outer branches (branches1). In an `if/elif`
  // chain whose conditions use `&&` (each `&&` is a nested case in the
  // scrutinee) the outer else-arm is the whole rest of the chain, so the
  // duplication compounds to 2^n core size. Only take the +1 slack when the
  // copied continuation is small.
  fun size-of-branches(bs: list<branch>): _ int
    bs.map(fn(b) b.guards.map(fn(g) g.test.size-of-expr + g.body.size-of-expr).sum).sum
  val maxCaseOfCaseDup = 25
  single || (branches0.filter(simplifies-on).length + 1 >= branches0.length &&
             size-of-branches(branches1) <= maxCaseOfCaseDup)

// let simplification: inline cheap, single-use, or dead bindings
fun top-down-let(sub: list<(tName, expr)>, acc: list<def-group>, dgs0: list<def-group>, body: expr): simp-eff expr
  fun apply-sub(e: expr): _ expr
    if sub.is-empty then e else sub |-> e
  match dgs0
    Nil ->
      match body.apply-sub
        Let(sdgs, sbody) -> top-down-let([], acc, sdgs, sbody) // merge nested lets
        sbody ->
          if acc.is-empty then sbody
          else Let(acc.reverse, sbody)
    [DefNonRec(Def(name, _, e))] | body.is-var-named(name) ->
      top-down-let(sub, acc, [], e)
    Cons(DefNonRec(def as Def(_, _, Let(dgs', body'))), dgs) ->
      // lift nested let bindings
      val free = body.free-vars
      if dgs'.map(dg/bound-vars).unions.disjoint(free) then
        top-down-let(sub, acc, dgs' ++ [DefNonRec(def(defExpr = body'))] ++ dgs, body)
      else
        match free/uniquefy(Let(dgs', body'), free)
          Let(uniqDgs, uniqBody) ->
            top-down-let(sub, acc, uniqDgs ++ [DefNonRec(def(defExpr = uniqBody))] ++ dgs, body)
          _ -> failure/fail("core/simplify top-down-let: uniquefy changed let shape")
    Cons(dg, dgs) ->
      val sdg = sub.dg/(|->)(dg)
      match sdg
        DefRec([def]) ->
          if occurs-not(def.def-name, Let(dgs, body)) then
            top-down-let(sub, acc, dgs, body) // dead definition
          else
            top-down-let(sub, Cons(sdg, acc), dgs, body) // don't inline recursive ones
        DefRec(_) ->
          top-down-let(sub, Cons(sdg, acc), dgs, body) // don't inline recursive ones
        DefNonRec(Def(x, tp, se)) ->
          if !se.is-total then
            // cannot inline effectful expressions
            top-down-let(sub, Cons(sdg, acc), dgs, body)
          else
            val maxSmallOccur = simp-env.dup-max // should be 10 or higher to inline partial bind applications
            val size = se.size-of-expr
            fun inline-expr()
              top-down-let(Cons((TName(x, tp), se), sub), acc, dgs.pretend-decreasing, body)
            match occurrences-of(x, Let(dgs, body))
              Occur(0, _, _, 0) -> top-down-let(sub, acc, dgs, body) // no occurrence
              Occur(acnt, _, _, vcnt) | vcnt + acnt == 1 -> inline-expr() // occurs once: inline
              Occur(acnt, _, _, vcnt) | (acnt + vcnt * 3) * size <= maxSmallOccur -> inline-expr()
              Occur(0, _, _, vcnt) | vcnt * size <= maxSmallOccur -> inline-expr()
              Many(n) | n * size <= maxSmallOccur -> inline-expr()
              _ -> top-down-let(sub, Cons(sdg, acc), dgs, body)

// bind non-atomic expressions to fresh names
fun bind-exprs(exprs: list<expr>): simp-eff (expr -> pure expr, list<expr>)
  fun unique-bind(e: expr): _ (list<def-group>, expr)
    match e
      Var -> ([], e)
      ELit -> ([], e)
      Con -> ([], e)
      _ ->
        val name = "norm".unique-name
        val tname = TName(name, e.type-of)
        ([DefNonRec(make-tdef(tname, e))], Var(tname, InfoNone))
  val (defss, bexprs) = exprs.map(unique-bind).unzip
  (fn(e) make-let(defss.concat, e), bexprs)

fun unique-tname(TName(name, tp): tName): _ tName
  TName(to-unique-name(unique-id(""), name), tp)

// A fresh name that also avoids `avoid`.
//
// `unique-id` alone is fresh only against THIS module's counter, which is not
// enough when substituting into an INLINED body: that body was compiled in
// another module, its internal binders carry names minted by that module's
// counter, and both start from the same base (10000). A "fresh" name can
// therefore collide with a binder inside the body, and the substituted
// occurrences are captured by it -- silently miscompiling the function.
//
// Found as `pad-left` returning the fill instead of the padded string: the
// parameter substitution minted `s@0@10011`, exactly the name `pad-left`'s own
// body uses for its `fill.string` local. Fixed the same way upstream
// (`uniqueTNameAvoiding` in Core/Simplify.hs).
fun unique-tname-avoiding(tn: tName, avoid: rbset<tName>): _ tName
  val tn' = tn.unique-tname
  if avoid.member(tn') then tn.unique-tname-avoiding(avoid) else tn'

// Names bound anywhere inside an expression -- what a freshly minted name must
// stay clear of. `bound-vars` covers patterns/def-groups but not a whole expr.
fun expr/bound-names(ex: expr): _ rbset<tName>
  match ex
    Lam(pars, _, body) -> pars.foldl(tnames/empty, fn(acc, p) acc + p) + body.bound-names
    App(f, args) -> args.map(bound-names).unions + f.bound-names
    TypeLam(_, body) -> body.bound-names
    TypeApp(body, _) -> body.bound-names
    Let(dgs, body) ->
      val ds = dgs.flatten
      ds.foldl(tnames/empty, fn(acc, d) acc + d.defTname) +
        ds.map(fn(d) d.defExpr.bound-names).unions + body.bound-names
    Case(scruts, bs) ->
      fun branch-names(Branch(pats, gs): branch): _ rbset<tName>
        pats.map(bound-vars).unions +
          gs.map(fn(Guard(t, e)) t.bound-names + e.bound-names).unions
      scruts.map(bound-names).unions + bs.map(branch-names).unions
    _ -> tnames/empty

//--------------------------------------------------------------------------
// Bottom-up transformations; children have already been simplified
//--------------------------------------------------------------------------

fun bottom-up(ex: expr): simp-eff expr
  match ex
    TypeApp(TypeLam(tvs, body), tps) ->
      if tvs.length == tps.length then new/sub(tvs.zip(tps)).expr/substitute(body)
      else ex
    // eta contract
    TypeLam(tvs, TypeApp(body, tps)) ->
      fun var-equal((tv: type-var, t: ktype))
        match t
          TVar(tw) -> tv == tw
          _ -> False
      val bodyFtv = body.free-type-vars
      if tvs.length == tps.length && tvs.zip(tps).all(var-equal) && tvs.all(fn(tv) !bodyFtv.member(tv)) then body
      else ex
    App(Lam(pars, _, body), args) | pars.length == args.length ->
      // Unlike the top-down rule this KEEPS the parameter names, so it is only
      // valid when doing so cannot capture: a parameter must not be free in the
      // ARGUMENTS (it would then refer to the new binding) and must not be
      // re-bound inside the BODY (an occurrence after that binder would resolve
      // to the inner binding instead of to the argument). Upstream checks only
      // the first; the second is added here. NOTE: no repro exists for the
      // body-binder case yet -- see docs/parity-checklist.md.
      val argsFv = args.free-vars
      val bodyBound = body.bound-names
      if pars.all(fn(p) !argsFv.member(p) && !bodyBound.member(p)) then
        Let(pars.zipwith(args, make-par-def), body)
      else ex
    // constructor context composition with the empty context
    App(TypeApp(Var(cextend), _), [ctx1, App(TypeApp(Var(cempty), _), [])])
        | cextend.get-name == nameCCtxComposeExtend && cempty.get-name == nameCCtxEmpty -> ctx1
    App(TypeApp(Var(ctxcomp), _), [ctx1, App(TypeApp(Var(cempty), _), [])])
        | ctxcomp.get-name == nameCCtxCompose && cempty.get-name == nameCCtxEmpty -> ctx1
    App(TypeApp(Var(ctxcomp), _), [App(TypeApp(Var(cempty), _), []), ctx2])
        | ctxcomp.get-name == nameCCtxCompose && cempty.get-name == nameCCtxEmpty -> ctx2
    // case on a single-constructor application (like tuples): match the fields directly
    Case([scrut as App(TypeApp(Con(name, crepr)), args)], branches) | crepr.is-conSingle ->
      if match-on-con-ok(name, args, branches)
        then Case(args, branches.map(fn(b) extract-match-on-con(args.length, b)))
        else bottom-up-case(ex, [scrut], branches)
    Case([scrut as App(Con(name, crepr), args)], branches) | crepr.is-conSingle ->
      if match-on-con-ok(name, args, branches)
        then Case(args, branches.map(fn(b) extract-match-on-con(args.length, b)))
        else bottom-up-case(ex, [scrut], branches)
    Case(scruts, bs) -> bottom-up-case(ex, scruts, bs)
    // evidence index of a fixed effect
    App(TypeApp(Var(evvIndex), [effTp, hndTp]), [_htag]) | evvIndex.get-name == nameEvvIndex ->
      if effTp.is-effect-fixed
        then make-ev-index(effect-offset(hndTp.effect-label-from-handler, effTp))
        else ex
    App(TypeApp(clauseTail as Var(ct, info), Cons(effTp, tps)), [op]) ->
      match ct.get-name.is-clause-tail-name
        Just(n) ->
          if effTp.is-effect-fixed && effTp.extract-handled-effect.fst.is-empty
            then App(TypeApp(Var(TName(name-clause-tail-no-op(n), clauseTail.type-of), info), Cons(effTp, tps)), [op])
            else ex
        _ -> ex
    // box/unbox cancel
    App(Var(v), [App(Var(w), [arg])])
        | (v.get-name == nameUnbox && w.get-name == nameBox) || (w.get-name == nameUnbox && v.get-name == nameBox) -> arg
    // eta contract
    Lam(pars, _, App(f as Var(_, info), args)) | !info.is-infoExternal && pars.length == args.length ->
      fun arg-match-par((par: tName, arg: expr))
        match arg
          Var(name) -> par == name
          _ -> False
      if pars.zip(args).all(arg-match-par) then f else ex
    Lam(pars, eff, App(Var(ret), [arg])) | ret.get-name == nameReturn ->
      Lam(pars, eff, arg)
    _ -> ex

fun match-on-con-ok(name: tName, args: list<expr>, branches: list<branch>): _ bool
  branches.head.map(fn(b) b.patterns.length == 1).default(False) &&
    branches.all(fn(b) is-match-on-con(name, args.length, b))

fun bottom-up-case(ex: expr, scruts: list<expr>, bs: list<branch>): simp-eff expr
  // extract a common continuation from all branches
  match find-common-cont(bs)
    Just((common, cbs)) -> App(common, [bottom-up(Case(scruts, cbs))]) // bottom-up for potential case-of-known
    Nothing ->
      // case of known constructors
      match kmatch-branches(scruts, bs)
        Just(b) -> b
        Nothing -> ex

fun find-common-cont(bs: list<branch>): _ maybe<(expr, list<branch>)>
  match bs
    Cons(Branch(pat, Cons(Guard(_, App(v as Var(name), [_])))), _) ->
      if pat.map(pat/bound-vars).unions.member(name) then Nothing
      else extract-common-cont(v, name, bs)
    _ -> Nothing

fun extract-common-cont(contVar: expr, contName: tName, bs: list<branch>): _ maybe<(expr, list<branch>)>
  fun extract-g(g: guard): _ maybe<guard>
    match g
      Guard(test, App(Var(name), [arg])) | name == contName -> Just(Guard(test, arg))
      _ -> Nothing
  fun extract(Branch(pats, guards): branch): _ maybe<branch>
    val gs = guards.map(extract-g)
    if gs.all(is-just) then Just(Branch(pats, gs.map(unjust))) else Nothing
  val cbs = bs.map(extract)
  if cbs.all(is-just) then Just((contVar, cbs.map(unjust))) else Nothing

//--------------------------------------------------------------------------
// Case-of-known-constructor matching
//--------------------------------------------------------------------------

type kmatch<a>
  KMatch(x: a)
  KUnknown
  KNoMatch

fun kmatch/map(m: kmatch<a>, f: a -> e b): e kmatch<b>
  match m
    KMatch(x) -> KMatch(f(x))
    KUnknown -> KUnknown
    KNoMatch -> KNoMatch

fun kmatch-first(ms: list<kmatch<a>>): kmatch<a>
  match ms
    Cons(KNoMatch, rest) -> kmatch-first(rest)
    Cons(other, _) -> other
    Nil -> KNoMatch

fun kmatch-all(ms: list<kmatch<a>>): kmatch<list<a>>
  match ms
    Nil -> KMatch([])
    Cons(KMatch(x), rest) -> kmatch-all(rest).map(fn(xs) Cons(x, xs))
    Cons(KNoMatch, _) -> KNoMatch
    Cons(KUnknown, rest) -> if rest.any(is-knoMatch) then KNoMatch else KUnknown

fun kmatch-branches(scruts: list<expr>, branches: list<branch>): _ maybe<expr>
  match kmatch-first(branches.map(fn(b) kmatch-branch(scruts, b)))
    KMatch(e) -> Just(e.expr/uniquefy)
    _ -> Nothing

fun kmatch-branch(scruts: list<expr>, Branch(pats, guards): branch): _ kmatch<expr>
  fun match-guard(g: guard): kmatch<expr>
    if g.test.is-true then KMatch(g.body)
    elif g.test.is-false then KNoMatch
    else KUnknown
  match kmatch-patterns(scruts, pats)
    KMatch(bindings) ->
      kmatch-first(guards.map(match-guard)).map(fn(e) Let(bindings.map(DefNonRec), e))
    KUnknown -> KUnknown
    KNoMatch -> KNoMatch

fun kmatch-patterns(scruts: list<expr>, pats: list<pattern>): _ kmatch<list<def>>
  kmatch-all(scruts.zipwith(pats, kmatch-pattern)).map fn(ds)
    ds.map(fn((defs, newscrut)) defs ++ [make-def("scrut".new-hidden-name, newscrut)]).concat

fun kmatch-pattern(scrut: expr, pat: pattern): _ kmatch<(list<def>, expr)>
  match (scrut, pat)
    (_, PatWild) -> KMatch(([], scrut))
    (_, PatVar(name, p)) ->
      kmatch-pattern(scrut, p).map fn((defs, newscrut))
        (defs ++ [make-def(name.get-name, newscrut)], Var(name, InfoNone))
    (ELit(lit), PatLit(pLit)) ->
      if lit == pLit then KMatch(([], scrut)) else KNoMatch
    (Con(name), PatCon(pname, [])) ->
      if name == pname then KMatch(([], scrut)) else KNoMatch
    (App(conx as Con(name), args), PatCon(pname, pats)) ->
      if name != pname then KNoMatch
      else
        kmatch-all(args.zipwith(pats, kmatch-pattern)).map fn(ds)
          val (defs, scruts) = ds.unzip
          (defs.concat, App(conx, scruts))
    (App(conx as TypeApp(Con(name)), args), PatCon(pname, pats)) ->
      if name != pname then KNoMatch
      else
        kmatch-all(args.zipwith(pats, kmatch-pattern)).map fn(ds)
          val (defs, scruts) = ds.unzip
          (defs.concat, App(conx, scruts))
    (Let(letDefns, letBody), _) ->
      kmatch-pattern(letBody, pat).map fn((bindings, newscrut))
        (letDefns.flatten ++ bindings, newscrut)
    _ -> KUnknown

//--------------------------------------------------------------------------
// Optimization for matches on ConSingle (like tuples)
//--------------------------------------------------------------------------

fun is-match-on-con(name: tName, n: int, b: branch): _ bool
  match b.patterns
    [PatCon(cname, pats)] -> cname == name && pats.length == n
    [PatVar(v, pat)] ->
      if b.guards.map(fn(g) branch/free-locals(Branch([], [g]))).unions.member(v) then False // TODO: allow if we generate a binding
      else is-match-on-con(name, n, Branch([pat], b.guards))
    [PatWild] -> True
    [PatLit(_)] -> False
    _ -> False

fun extract-match-on-con(n: int, b: branch): _ branch
  match b.patterns
    [PatCon(_, pats)] -> Branch(pats, b.guards)
    [PatWild] -> Branch(list(1, n).map(fn(_) PatWild), b.guards)
    [PatVar(_, pat)] -> extract-match-on-con(n, Branch([pat], b.guards)) // name is free (due to is-match-on-con)
    _ -> failure/fail("core/simplify extract-match-on-con: invalid pattern")

//--------------------------------------------------------------------------
// Effects
//--------------------------------------------------------------------------

fun effect-label-from-handler(tp: ktype): _ name
  tp.label-name

fun effect-offset(l: name, effTp: ktype): _ int
  fun find-match(i: int, ls: list<ktype>): _ int
    match ls
      Cons(l', ls') -> if l'.label-name == l then i else find-match(i + 1, ls')
      Nil -> failure/fail("core/simplify effect-offset: label " ++ l.show ++ " is not in the labels")
  find-match(0, effTp.extract-handled-effect.fst)

//--------------------------------------------------------------------------
// Full traversal (upstream `Simplify` instances)
//--------------------------------------------------------------------------

pub fun dg/simplify(dg: def-group): simp-eff def-group
  match dg
    DefRec(defs) -> DefRec(defs.map(def/simplify))
    DefNonRec(def) -> DefNonRec(def.def/simplify)

pub fun def/simplify(d: def): simp-eff def
  val expr' = match d.defExpr
    TypeLam(tvs, Lam(pars, eff, body)) -> TypeLam(tvs, Lam(pars, eff, body.expr/simplify))
    Lam(pars, eff, body) -> Lam(pars, eff, body.expr/simplify)
    e -> e.expr/simplify
  d(defExpr = expr')

pub fun expr/simplify(e: expr): simp-eff expr
  val td = top-down(e)
  val se = match td
    Lam(pars, eff, body) -> Lam(pars, eff, body.expr/simplify)
    Var -> td
    App(f, args) -> App(f.expr/simplify, args.map(expr/simplify))
    TypeLam(tpars, body) -> TypeLam(tpars, body.expr/simplify)
    TypeApp(body, tps) -> TypeApp(body.expr/simplify, tps)
    Con -> td
    ELit -> td
    Let(dgs, body) -> Let(dgs.map(dg/simplify), body.expr/simplify)
    Case(exprs, branches) -> Case(exprs.map(expr/simplify), branches.map(branch/simplify))
  bottom-up(se)

pub fun branch/simplify(Branch(patterns, guards): branch): simp-eff branch
  Branch(patterns, guards.map(fn(Guard(test, body)) Guard(test.expr/simplify, body.expr/simplify)))

//--------------------------------------------------------------------------
// Occurrences
//--------------------------------------------------------------------------

fun size-of-expr(e: expr): div int
  match e
    Var -> 0
    Con -> 0
    ELit -> 0
    Lam(_, _, body) -> 1 + body.size-of-expr-x
    App(f, args) -> 1 + f.size-of-fun + args.map(size-of-expr).sum
    TypeLam(_, e') -> e'.size-of-expr
    TypeApp(e', _) -> e'.size-of-expr
    Let(dgs, body) -> dgs.map(fn(dg) dg.size-of-def-group(size-of-expr)).sum + body.size-of-expr
    Case(exprs, branches) -> 1 + exprs.map(size-of-expr).sum + branches.map(fn(b) b.size-of-branch(size-of-expr)).sum

// for functions we must be conservative or we could lose sharing from allocations
fun size-of-fun(e: expr): div int
  val maxSize = 10000
  match e
    Con -> maxSize
    Var -> 1
    ELit -> 0 // cannot happen?
    Lam(_, _, body) -> 1 + body.size-of-expr
    App(f, args) -> 1 + f.size-of-fun + args.map(size-of-expr).sum
    TypeLam(_, e') -> e'.size-of-fun
    TypeApp(e', _) -> e'.size-of-fun
    _ -> maxSize // give up

fun size-of-expr-x(e: expr): div int
  match e
    Var -> 0
    Con -> 0
    ELit -> 0
    Lam(_, _, body) -> 1 + body.size-of-expr-x
    App(f, args) -> 1 + f.size-of-expr-x + args.map(size-of-expr-x).sum
    TypeLam(_, e') -> e'.size-of-expr-x
    TypeApp(e', _) -> e'.size-of-expr-x
    Let(dgs, body) -> dgs.map(fn(dg) dg.size-of-def-group(size-of-expr-x)).sum + body.size-of-expr-x
    Case(exprs, branches) -> 1 + exprs.map(size-of-expr-x).sum + branches.map(fn(b) b.size-of-branch(size-of-expr-x)).sum

fun size-of-branch(Branch(_, guards): branch, size: expr -> div int): div int
  guards.map(fn(Guard(test, body)) test.size + body.size).sum

fun size-of-def-group(dg: def-group, size: expr -> div int): div int
  match dg
    DefRec(defs) -> defs.map(fn(d) d.defExpr.size).sum
    DefNonRec(def) -> def.defExpr.size

// occurrence analysis: count applied and plain variable occurrences
type occur
  Occur(apply-count: int, type-args-count: int, args-count: int, var-count: int)
  Many(count: int)

fun occur/add(oc1: occur, oc2: occur): _ occur
  match (oc1, oc2)
    (Many(n), Many(m)) -> Many(n + m)
    (Many(n), Occur(acnt2, _, _, vcnt2)) -> Many(acnt2 + vcnt2 + n)
    (Occur(acnt1, _, _, vcnt1), Many(n)) -> Many(acnt1 + vcnt1 + n)
    (Occur(acnt1, m1, n1, vcnt1), Occur(acnt2, m2, n2, vcnt2)) ->
      if acnt2 == 0 then Occur(acnt1, m1, n1, vcnt1 + vcnt2)
      elif acnt1 == 0 then Occur(acnt2, m2, n2, vcnt1 + vcnt2)
      elif m1 == m2 && n1 == n2 then Occur(acnt1 + acnt2, m1, n1, vcnt1 + vcnt2)
      else Many(acnt1 + acnt2 + vcnt1 + vcnt2)

alias occurs = name-map<occur>

fun ounion(oc1: occurs, oc2: occurs): _ occurs
  oc1.union-with(oc2, occur/add)

fun ounions(ocs: list<occurs>): _ occurs
  ocs.foldl(rb-map/empty(), ounion)

fun occurs-not(name: name, e: expr): _ bool
  e.occurrences.lookup(name).is-nothing

pub fun occurs-at-most-once(name: name, e: expr): _ bool
  match e.occurrences.lookup(name)
    Nothing -> True
    Just(Occur(acnt, _, _, vcnt)) -> acnt + vcnt == 1
    _ -> False

fun occurrences-of(name: name, e: expr): _ occur
  match e.occurrences.lookup(name)
    Nothing -> Occur(0, 0, 0, 0)
    Just(oc) -> oc

fun occurrences(e: expr): _ occurs
  match e
    App(TypeApp(Var(v), targs), args) ->
      ounions(Cons(rb-map/from-list([(v.get-name, Occur(1, targs.length, args.length, 0))]), args.map(occurrences)))
    App(Var(v), args) ->
      ounions(Cons(rb-map/from-list([(v.get-name, Occur(1, 0, args.length, 0))]), args.map(occurrences)))
    Var(v) -> rb-map/from-list([(v.get-name, Occur(0, 0, 0, 1))])
    Con -> rb-map/empty()
    ELit -> rb-map/empty()
    App(f, args) -> ounions(Cons(f.occurrences, args.map(occurrences)))
    Lam(pars, _, body) -> body.occurrences.remove-all(pars.map(get-name))
    TypeLam(_, body) -> body.occurrences
    TypeApp(body, _) -> body.occurrences
    Let(dgs, body) -> dgs.foldr(body.occurrences, occurrences-def-group)
    Case(scruts, bs) -> ounions(scruts.map(occurrences) ++ bs.map(occurrences-branch))

fun occurrences-branch(Branch(pat, guards): branch): _ occurs
  ounions(guards.map(fn(Guard(g, e)) ounion(g.occurrences, e.occurrences)))
    .remove-all(pat.map(pat/bound-vars).unions.list.map(get-name))

fun occurrences-def-group(dg: def-group, oc: occurs): _ occurs
  match dg
    DefNonRec(def) -> ounion(oc.remove(def.def-name), def.defExpr.occurrences)
    DefRec(defs) ->
      ounions(Cons(oc, defs.map(fn(d) d.defExpr.occurrences))).remove-all(defs.map(def-name))
