// Ported as of 2026-01-29; approx upstream baseline commit ef41bb5 of Core/Divergent.hs (backfilled 2026-07-23)
module compiler/core/divergent

import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/core/uniquefy
import std/data/rb-set

// Fix a group of recursive definitions to potentially include the divergence effect in their type
pub fun analyze-divergence(defs0: list<def>)
  match defs0
    [] -> False
    Cons(_, Cons) -> True // For mutual recursion, we assume divergence for now
    [d0] ->
      val DefRec([d1]) = DefRec([d0]).dg/uniquefy
      d1.is-divergent

// Is a recursive definition group potentially divergent?
// Assumes that the defintions are uniquefied
// A valid result is always to return 'True'
fun is-divergent(d: def): _ bool
  d.defExpr.is-divergent-body(d.def-name)

fun is-divergent-body(b: expr, dname: name)
  match b
    TypeLam(_, expr) -> expr.is-divergent-body(dname)
    TypeApp(expr) -> expr.is-divergent-body(dname)
    Lam(pars, _, e) -> e.is-divergent-fun(pars, dname)
    _ -> True

fun is-divergent-fun(b: expr, pars: list<tName>, dname: name): _ bool
  match pars
    Nil -> True
    _ ->
      val calls = run-div(dname, pars, {expr/div(b)})
      fun isAnOrder(cs: list<call>)
        cs.all(fn(call) match call.drop-while(fn(sz) sz == SEq) {Cons(SLt, _) -> True; _ -> False})
      // upstream is `not (any isAnOrder (map transpose (permutations (transpose calls))))`.
      // `Data.List.permutations` is lazy there, so `any` short-circuits and only one
      // ordering is live at a time. Building the list strictly instead costs
      // (#params)! entries -- 12 parameters is 479M -- so the orderings are streamed
      // and the search stops at the first one that works. Enumeration order does not
      // affect the result, only how soon the search stops.
      //
      // Rows are RAGGED when the recursive function is referenced as a value rather
      // than called (`id(recfun)(x)` contributes a single `Unknown`) or is applied
      // partially. `transpose` re-packs a ragged matrix instead of preserving which
      // entry belongs to which call, so dropping a column there can change the
      // answer. With uniform rows it cannot: only a parameter that decreases in some
      // call can supply the `SLt` an ordering needs, and one that never does is
      // either transparent to `drop-while(SEq)` or must sit after every call's `SLt`.
      // A differential test over 62802 matrices (scripts/divergent-prune-test.kk)
      // shows the uniform case agrees with the unpruned search exactly, and that the
      // ragged case does not -- hence the guard rather than pruning unconditionally.
      val lens = calls.map(fn(c) c.length)
      val uniform = match lens
        Cons(l, r) -> r.all(fn(x) x == l)
        Nil -> True
      if !uniform then !calls.transpose.any-permutation(fn(o) isAnOrder(o.transpose))
      else match calls
        // no recursive call reaches this definition, so nothing can diverge
        Nil -> False
        _ ->
          val cols = calls.transpose.filter(fn(col) col.any(fn(sz) sz == SLt))
          match cols
            // nothing decreases anywhere, so no ordering can work. Guarded because
            // `transpose([])` drops every call and `all` over none is vacuously true.
            Nil -> True
            _ -> !cols.any-permutation(fn(order) isAnOrder(order.transpose))

// Data.List.transpose: rows may be RAGGED, and empty rows are skipped rather
// than matched.
//   transpose ((x:xs):xss) = (x : [h | (h:_) <- xss]) : transpose (xs : [t | (_:t) <- xss])
fun transpose(xss:list<list<a>>): _ list<list<a>>
  match xss
    Nil -> Nil
    Cons(Nil, xss') -> transpose(xss')
    Cons(Cons(x, xs), xss') ->
      val hds = xss'.flatmap fn(row)
        match row
          Cons(hd, _) -> [hd]
          Nil -> []
      val tls = xss'.flatmap fn(row)
        match row
          Cons(_, tl) -> [tl]
          Nil -> []
      Cons(Cons(x, hds), transpose(Cons(xs, tls)))

// Does some permutation of `xs` satisfy `pred`? Streams the permutations and
// stops at the first hit, so only O(n) list cells are live at a time.
fun any-permutation(xs: list<a>, pred: (list<a>) -> <div|e> bool): <div|e> bool
  perm-search(xs, Nil, pred)

fun perm-search(rest: list<a>, acc: list<a>, pred: (list<a>) -> <div|e> bool): <div|e> bool
  match rest
    Nil -> pred(acc.reverse)
    _   -> perm-pick(Nil, rest, acc, pred)

// `left` holds the candidates already tried for this position (reversed).
fun perm-pick(left: list<a>, right: list<a>, acc: list<a>, pred: (list<a>) -> <div|e> bool): <div|e> bool
  match right
    Nil -> False
    Cons(x, rest) ->
      if perm-search(left.reverse ++ rest, Cons(x, acc), pred) then True
      else perm-pick(Cons(x, left), rest, acc, pred)


struct rel
  n: name
  ns: list<name-set>
  ns': list<name-set>

alias call = list<size>

type size
  SLt
  SEq
  Unknown

fun (==)(s1: size, s2: size): bool
  match (s1, s2)
    (SLt, SLt) -> True
    (SEq, SEq) -> True
    (Unknown, Unknown) -> True
    _ -> False

pub effect divergent
  val rel: rel
  fun add-call(n: name, c: call): ()

fun set-rel(r: rel, f: () -> _ a): _ a
  with override
    val rel = r
    fun add-call(n, c) add-call(n, c)
  f()

fun run-div(dname: name, args: list<tName>, f: () -> _ a): _ list<call>
  var calls: list<call> := []
  with handler
    val rel = Rel(dname, args.map(names/empty + _.get-name), args.map(fn(a) names/empty))
    fun add-call(n, c)
      calls := Cons(c, calls)
  f()
  // upstream's Div monad accumulates with `calls1 ++ calls2`, i.e. in traversal
  // order; prepending above reverses that, which is observable once the calls
  // are ragged (partial applications) since `transpose` is order-sensitive there
  calls.reverse

fun at(xs: list<name-set>, i: int): name-set
  xs[i].default(names/empty)

fun is-recursive-call(n: name): _ bool
  val Rel(rname) = rel
  rname == n

fun lookup-size(dname: name, argPos: int, argName: name): _ size
  val Rel(rname, eqs, lts) = rel
  if rname != dname then Unknown
  else
    val equal = eqs.at(argPos)
    val lower = lts.at(argPos)
    if lower.member(argName) then SLt
    elif equal.member(argName) then SEq
    else Unknown

fun add-relation(sz: size, name1: name, name2: name, div: () -> _ a): _ a
  if sz == Unknown then div()
  else
    val Rel(rname, eqs, lts) = rel
    fun addEqLt(eq, lt)
      if eq.member(name1) then
        match sz
          SLt -> (eq, lt.add(name2))
          SEq -> (eq.add(name2), lt)
          _ -> failure/fail("core/divergent add-relation: encountered Unknown")
      elif lt.member(name1) then
        (eq, lt.add(name2))
      else (eq, lt)
    val (eqs', lts') = eqs.zipwith(lts, addEqLt).unzip
    set-rel(Rel(rname, eqs', lts'), div)

fun expr/div(e: expr): _ ()
  match e
    Lam(_, _, expr) -> expr.expr/div
    // Ignore .open effect calls
    App(App(TypeApp(Var(openName)), [f]), args) | openName.get-name == nameEffectOpen ->
      App(f, args).expr/div
    App(TypeApp(App(TypeApp(Var(openName)), [f]), targs), args) | openName.get-name == nameEffectOpen ->
      App(TypeApp(f, targs), args).expr/div
    // applications
    App(TypeApp(v as Var), args) ->
      App(v, args).expr/div
    App(Var(tname), args) ->
      val isRec = is-recursive-call(tname.get-name)
      if isRec then
        val call = args.map-indexed(fn(i, a) argument/size(tname.get-name, i, a))
        add-call(tname.get-name, call)
      else
        ()
      args.map(expr/div)
      ()
    Var(tname) -> // recursive call may appear as argument, say id(recfun)(x)
      val isRec = is-recursive-call(tname.get-name)
      if isRec then
        add-call(tname.get-name, [Unknown])
      else
        ()
    App(f, args) ->
      f.expr/div
      args.map(expr/div)
      ()
    TypeLam(_, expr) -> expr.expr/div
    TypeApp(expr) -> expr.expr/div
    Let(dgs, expr) ->
      dgs.map(dg/div)
      expr.expr/div
    Case(exprs, branches) ->
      exprs.map(expr/div)
      branches.foreach(branch/div(exprs, _))
    _ -> ()

fun branch/div(exprs, Branch(pats, guards): branch): _ ()
  fun extractName(e: expr)
    match e
      Var(tname) -> Just(tname.get-name)
      App(TypeApp(Var(sameSize)), [Var(tname)]) | namesSameSize.any(_ == sameSize.get-name) ->
        Just(tname.get-name)
      _ -> Nothing
  fun guard/div(Guard(test, expr): guard)
    test.expr/div
    expr.expr/div
  // the size relations from the patterns must be in scope while processing the
  // guards (which hold the recursive calls); thread a continuation through
  pats/div(exprs.map(extractName).zip(pats), { guards.foreach(guard/div) })

// process each (name, pattern) in turn, keeping the size relations in scope for `k`
fun pats/div(nps: list<(maybe<name>, pattern)>, k: () -> _e ()): _e ()
  match nps
    Nil -> k()
    Cons((n, p), rest) -> pat/div(SEq, n, p, { pats/div(rest, k) })

fun pat/div(size: size, mbName: maybe<name>, p: pattern, k: () -> _e ()): _e ()
  match (mbName, p)
    (Just(n), PatVar(pname, pat)) ->
      add-relation(size, n, pname.get-name, { pat/div(size, mbName, pat, k) })
    (_, PatCon(_, pats, _, _, _, _, info)) ->
      val sz = if info.typeSort.is-inductive then SLt else size
      pats/div/con(sz, mbName, pats, k)
    (_, _) -> k()

fun pats/div/con(size: size, mbName: maybe<name>, pats: list<pattern>, k: () -> _e ()): _e ()
  match pats
    Nil -> k()
    Cons(p, rest) -> pat/div(size, mbName, p, { pats/div/con(size, mbName, rest, k) })

fun dg/div(dg: def-group): _ ()
  match dg
    DefNonRec(d) -> d.def/div
    DefRec(dfs) -> dfs.foreach(def/div)

fun def/div(d: def)
  d.defExpr.expr/div

fun argument/size(name: name, pos: int, arg: expr): _ size
  fun reduce-size(sz)
    match sz
      SEq -> SLt
      _ -> sz
  match arg
    Var(tname, _) ->
      lookup-size(name, pos, tname.get-name)
    // Ignore .open effect calls
    App(App(TypeApp(Var(openName)), [f]), args) | openName.get-name == nameEffectOpen ->
      argument/size(name, pos, App(f, args))
    App(TypeApp(App(TypeApp(Var(openName)), [f]), targs), args) | openName.get-name == nameEffectOpen ->
      argument/size(name, pos, App(TypeApp(f, targs), args))
    // special 'unsafeDecreasing' call
    App(TypeApp(Var(name'), [_]), [_]) | name'.get-name == nameDecreasing ->
      SLt
    // special case substr1
    App(Var(substrName), Cons(Var(sname), _)) | substrName.get-name == nameSubStr1 ->
      val sz = lookup-size(name, pos, sname.get-name)
      reduce-size(sz)
    // these two cases state that the call to a function f where f < name is itself < name
    App(Var(tname)) ->
      lookup-size(name, pos, tname.get-name)
    App(TypeApp(Var(tname))) ->
      lookup-size(name, pos, tname.get-name)
    _ -> Unknown

  

