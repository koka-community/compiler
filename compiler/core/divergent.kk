import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/core/uniquefy
import std/data/linear-set

// Fix a group of recursive definitions to potentially include the divergence effect in their type
fun analyze-divergence(defs0: list<def>)
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
      val orders = calls.transpose.permutations.map(transpose)
      fun isAnOrder(cs)
        cs.all(fn(call) match call.drop-while(_ == SEq) {Cons(SLt) -> True; _ -> False})
      !orders.any(isAnOrder)

fun transpose(xss:list<list<a>>): _ list<list<a>>
  fun combine(y, h, ys, t)
    Cons(Cons(y, h), transpose(Cons(ys, t)))
  match xss
    Nil -> Nil
    Cons(Nil, xss') -> transpose(xss')
    Cons(Cons(x, xs), xss') -> 
      val (hds, tls) = xss'.map(fn(Cons(hd, tl)) (hd, tl)).unzip
      combine(x, hds, xs, tls)

fun permutations(xs0: list<a>): _ list<list<a>>
  fun perms(xs, is)
    match xs
      Nil -> Nil
      Cons(t, ts) -> 
        fun interleave'(f, xs', r)
          match xs'
            Nil -> (ts, r)
            Cons(y, ys) ->
              val (us, zs) = interleave'(fn(x) f(Cons(y, x)), ys, r)
              (Cons(y, us), Cons(f(Cons(t, Cons(y, us))), zs))
        fun interleave(xs', r)
          interleave'(id, xs', r).snd
        is.permutations.foldr(perms(ts, Cons(t, is)), interleave)
  perms(xs0, Nil)

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

effect divergent
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
  calls

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
          _ -> fail("core/divergent add-relation: encountered Unknown")
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
  fun guard/div(Guard(test, expr))
    test.expr/div
    expr.expr/div
    ()
  exprs.map(extractName).zip(pats).foreach(fn((n, p)) pat/div(SEq, n, p))
  guards.foreach(guard/div)

fun pat/div(size: size, mbName: maybe<name>, p: pattern): _ ()
  match (mbName, p)
    (Just(n), PatVar(pname, pat)) ->
      with add-relation(size, n, pname.get-name)
      pat/div(size, mbName, pat)
    (_, PatCon(_, pats, _, _, _, _, info)) ->
      pats.foreach(fn(p') pat/div(if info.typeSort.is-inductive then SLt else size, mbName, p'))
    (_, _) ->
      ()

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

  

