// Port of src/Core/CheckFBIP.hs -- check whether `fip`/`fbip` annotated
// functions satisfy their declared allocation/deallocation/recursion budget,
// emitting warnings when they do not.
//
// Runs between `unreturn` and the initial simplify (see
// compiler/compile/type-check.kk).
//
// Monad mapping (upstream `Chk` = ReaderT (Env, Input) (WriterT (Output,
// [(Range,Doc)]) Unique)):
//  - Env readers  -> `chk-ctx` (constant) and `chk-fip`/`chk-current`
//    (`with override val` for the Reader-local pattern)
//  - Input        -> `chk-delta`/`chk-dg-names`/`chk-tail` override vals
//  - Writer Output-> `emit-out` op; `extract-output` re-handles it locally
//    (upstream `censor`/`listen`), warnings pass through untouched
//  - Unique       -> the ambient `unique` effect
module compiler/core/check-fbip
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/range
import compiler/common/syntax
import compiler/common/unique
import compiler/common/error
import compiler/platform/config
import compiler/kind/newtypes
import compiler/type/type
import compiler/type/assumption
import compiler/core/core
import compiler/core/corevar
import compiler/core/borrowed
import compiler/backend/c/parc
import compiler/backend/c/parc-reuse
import compiler/lib/pprint
import std/data/rb-set
import std/data/sort
import std/core/undiv
import std/data/rb-map
import std/data/int-map
import std/data/int-set
import std/num/int64

//--------------------------------------------------------------------------
// Rationals (upstream Data.Ratio -- reuse "probabilities")
//--------------------------------------------------------------------------

alias ratio = (int, int)  // (numerator, denominator); denominator > 0

val ratio/one: ratio = (1, 1)

fun ratio/add((a, b): ratio, (c, d): ratio): ratio
  (a * d + c * b, b * d)

fun ratio/div-by((a, b): ratio, n: int): ratio
  (a, b * n)

fun ratio/is-one((a, b): ratio): bool
  a == b

fun ratio/cmp((a, b): ratio, (c, d): ratio): order
  (a * d).cmp(c * b)

//--------------------------------------------------------------------------
// Allocation tree
//--------------------------------------------------------------------------

type alloc-tree
  ATAlloc(aid: int)             // allocation with unique identifier
  ATCall(alloc: fip-alloc)      // call using allocation credits
  ATCallSelf(alloc: fip-alloc)  // self-call using allocation credits
  ATSeq(l: alloc-tree, r: alloc-tree)
  ATMatch(children: list<alloc-tree>)
  ATLeaf

//--------------------------------------------------------------------------
// Output (upstream Output; Semigroup = pointwise union)
//--------------------------------------------------------------------------

// gamma-dia entries: token size -> allocations with a "probability",
// sorted in DESCENDING order of probability
alias dia-entry = (ratio, list<(tName, int)>)

struct chk-output
  gamma-nm: rbmap<tName, int>               // variable -> number of uses
  gamma-dia: int-map<list<dia-entry>>
  alloc-tree: alloc-tree

val output/empty: chk-output = Chk-output(rb-map/empty(), int-map/empty(), ATLeaf)

fun dia/merge(xs: list<dia-entry>, ys: list<dia-entry>): list<dia-entry>
  // upstream: `sortOn (Down . fst) (x ++ y)`
  (xs ++ ys).sort(?(<) = fn(e1: dia-entry, e2: dia-entry) e1.fst.ratio/cmp(e2.fst).is-gt)

fun output/union(o1: chk-output, o2: chk-output): chk-output
  Chk-output(
    o1.gamma-nm.union-with(o2.gamma-nm, fn(a: int, b: int) a + b),
    o1.gamma-dia.union-with(o2.gamma-dia, dia/merge),
    ATSeq(o1.alloc-tree, o2.alloc-tree))

//--------------------------------------------------------------------------
// The Chk effects
//--------------------------------------------------------------------------

struct chk-context
  chk-platform: platform
  chk-newtypes: newtypes
  chk-borrowed: borrowed
  chk-gamma: gamma
  chk-prog-name: name

effect val chk-ctx: chk-context
effect val chk-fip: fipT               // Env.fip
effect val chk-current: list<def>      // Env.currentDef
effect val chk-delta: name-set         // Input.delta (borrowed names)
effect val chk-dg-names: list<name>    // Input.defGroupNames
effect val chk-tail: bool              // Input.isTailContext

effect chk-out
  fun emit-out(o: chk-output): ()

effect chk-warns
  fun emit-warn-doc(rng: range, d: doc): ()

//--------------------------------------------------------------------------
// Entry point
//--------------------------------------------------------------------------

pub fun check-fbip(platform: platform, newtypes: newtypes, borrowed: borrowed, gamma: gamma,
                   prog-name: name, dgs: def-groups): _ ()
  var warns := []
  var sink := output/empty
  with handler
    fun emit-warn-doc(rng, d) warns := Cons((rng, d), warns)
  with handler
    fun emit-out(o) sink := sink.output/union(o)
  with val chk-ctx = Chk-context(platform, newtypes, borrowed, gamma, prog-name)
  with val chk-fip = noFip
  with val chk-current = []
  with val chk-delta = rb-set/empty()
  with val chk-dg-names = []
  with val chk-tail = True
  dgs.foreach(chk-def-group)
  add-warnings(warns.reverse.map(fn(rd) rd.to-warning(ErrStatic)))

fun chk-def-group(dg: def-group)
  match dg
    DefRec(defs) -> defs.foreach(fn(d) chk-top-level-def(defs.map(def-name), d))
    DefNonRec(d) -> chk-top-level-def([d.def-name], d)

fun chk-top-level-def(def-group-names: list<name>, d: def)
  with override val chk-current = Cons(d, chk-current)
  match d.sort
    // only check fip and fbip annotated functions
    DefFun(borrows, fip) | !fip.is-fip-top ->
      with override val chk-fip = fip
      val out =
        with override val chk-delta = rb-set/empty()
        with override val chk-dg-names = def-group-names
        with override val chk-tail = True
        extract-output({ chk-top-level-expr(borrows, d.defExpr) })
      check-output-empty(out)
    _ -> ()

fun is-fip-top(f: fipT): bool
  match f
    NoFip(False) -> True
    _ -> False

fun fip-allocation(f: fipT): fip-alloc
  match f
    Fip(n) -> n
    Fbip(n) -> n
    NoFip -> AllocUnlimited

// Lambdas at the top-level are part of the signature and not allocations.
fun chk-top-level-expr(borrows: list<param-info>, ex: expr): _ ()
  match ex
    Lam(pars, eff, body) ->
      chk-effect(eff)
      val bpars = zip-param-info(borrows, pars).filter(fn((pi, _)) pi == Borrow).map(snd)
      val opars = zip-param-info(borrows, pars).filter(fn((pi, _)) pi == Own).map(snd)
      with-borrowed(rb-set/from-list(bpars.map(get-name))) fn()
        val out = extract-output({ chk-expr(body) })
        emit-out(opars.foldl(out, fn(o, nm) bind-name(nm, NotReusable, o)))
    TypeLam(_, body) -> chk-top-level-expr(borrows, body)
    TypeApp(body, _) -> chk-top-level-expr(borrows, body)
    _ -> chk-expr(ex)

fun chk-expr(ex: expr): _ ()
  match ex
    TypeLam(_, body) -> chk-expr(body)
    TypeApp(body, _) -> chk-expr(body)
    Lam(pars, eff, body) ->
      chk-effect(eff)
      require-capability(may-alloc(), fn() Just("allocating a lambda expression".text))
      val out = extract-output({ chk-expr(body) })
      emit-out(pars.foldl(out, fn(o, nm) bind-name(nm, NotReusable, o)))
    App(TypeApp(Var(tname), _), _) | [nameCCtxSetCtxPath, nameLazyMemoizeTarget, nameLazyEnter, nameLazyLeave].any(fn(n) n == tname.get-name) ->
      ()
    App(TypeApp(Var(tname), _), [_, conApp]) | tname.get-name == nameLazyMemoize ->
      chk-expr(conApp)
    App(f, args) -> chk-app(f, args)
    Var(tname, info) -> mark-seen(tname, info)
    Let([], body) -> chk-expr(body)
    Let(Cons(DefNonRec(d), dgs), body) ->
      val out = extract-output({ chk-expr(Let(dgs, body)) })
      val gamma2 = bind-name(d.defTName, NotReusable, out)
      emit-out(gamma2)
      with-borrowed(rb-set/from-list(gamma2.gamma-nm.keys.map(get-name))) fn()
        with-tail-mod([Let(dgs, body)]) fn()
          chk-expr(d.defExpr)
    Let(_, _) ->
      emit-warning(fn() "internal: currently the fip analysis cannot handle nested function bindings".text)
    Case(scrutinees, branches) -> chk-branches(scrutinees, branches)
    Con(_, _) -> () // Atoms are non-allocated
    ELit(_) -> ()

fun chk-mod-cons(args: list<expr>)
  match args
    [] -> ()
    _ ->
      // zipWithM_ (\a tl -> withTailMod tl $ chkExpr a) args (tail $ tails args)
      fun go(l: list<expr>)
        match l
          Cons(a, tl) ->
            with-tail-mod(tl, fn() chk-expr(a))
            go(tl.pretend-decreasing)
          Nil -> ()
      go(args)

fun chk-branches(scrutinees: list<expr>, branches: list<branch>)
  val which-borrowed = scrutinees.map(is-borrowed-scrutinee)
  val branches' = branches.filter(fn(b) !b.is-pattern-match-error)
  val stypes = scrutinees.map(type-of)
  val outs = branches'.map(fn(b) extract-output({ chk-branch(which-borrowed, stypes, b) }))
  val gamma2 = join-contexts(branches'.map(patterns), outs)
  emit-out(gamma2)
  with-borrowed(rb-set/from-list(gamma2.gamma-nm.keys.map(get-name))) fn()
    with-tail-mod-product(branches') fn()
      which-borrowed.zip(scrutinees).foreach(chk-scrutinee)

fun is-borrowed-scrutinee(ex: expr): _ param-info
  match ex
    Var(tname, _) -> if chk-is-borrowed(tname) then Borrow else Own
    _ -> Own

fun chk-scrutinee((pi, ex): (param-info, expr)): _ ()
  match (pi, ex)
    (Borrow, Var(_, _)) -> ()
    (_, _) -> chk-expr(ex)

fun chk-branch(which-borrowed: list<param-info>, stypes: list<ktype>, Branch(pats, guards): branch)
  val tagged = which-borrowed.zip(pats.zip(stypes))
  val bor-pats = tagged.filter(fn((pi, _)) pi == Borrow).map(snd)
  val own-pats = tagged.filter(fn((pi, _)) pi != Borrow).map(snd)
  val outs =
    with-borrowed(rb-set/from-list(bor-pats.map(fst).map(pat/bound-vars).unions.list.map(get-name))) fn()
      guards.map(fn(g) extract-output({ chk-guard(g) }))
  val out = join-contexts(guards.map(fn(_) pats), outs)
  emit-out(own-pats.foldl(out, fn(o, p) bind-pattern(p, o)))

fun chk-guard(Guard(test, ex): guard)
  val out = extract-output({ chk-expr(ex) })
  with-borrowed(rb-set/from-list(out.gamma-nm.keys.map(get-name))) fn()
    with-non-tail(fn() chk-expr(test))
  emit-out(out)

// We ignore default branches that create a pattern match error
fun is-pattern-match-error(b: branch): bool
  match b
    Branch(pats, [Guard(Con(gname), App(App(_, [TypeApp(Var(TName(fnname)), _)]), _))]) ->
      pats.all(is-pat-wild) && gname.get-name == nameTrue && fnname == namePatternMatchError
    _ -> False

fun is-pat-wild(p: pattern): bool
  match p
    PatWild -> True
    _ -> False

fun bind-pattern((pat, tp): (pattern, ktype), out: chk-output): _ chk-output
  match pat
    PatCon(cname, pats, crepr, types) ->
      val size = get-constructor-alloc-size(crepr)
      provide-token(cname, size, pats.zip(types).foldl(out, fn(o, pt) bind-pattern(pt, o)))
    PatVar(tname, PatCon(_, _, crepr)) ->
      val size = get-constructor-alloc-size(crepr)
      bind-name(tname, size, out)
    PatVar(tname, PatWild) ->
      bind-name(tname, NotReusable, out)
    PatVar(_, pat') ->     // Else, don't bind the name.
      bind-pattern((pat', tp), out)  // The end of the analysis fails if the name is actually used.
    PatLit(_) -> out
    PatWild ->
      if needs-dup-drop-tp(tp) then
        val d = "binding a wildcard pattern of type".text |+| tp.show.text |+| "causes deallocation".text
        require-capability(may-dealloc(), fn() Just(d))
      out

fun chk-app(f: expr, args: list<expr>): _ ()
  match f
    TypeLam(_, fn') -> chk-app(fn', args) // ignore type machinery
    TypeApp(fn', _) -> chk-app(fn', args)
    App(TypeApp(Var(openName), _), [fn']) | openName.get-name == nameEffectOpen ->
      chk-app(fn', args)
    Con(cname, repr) -> // try reuse
      chk-mod-cons(args)
      chk-lazy-con(cname, repr)
      chk-allocation(cname, repr)
    Var(tname, info) | !info.isRefCounted -> // toplevel function
      val bs = chk-get-param-infos(tname.get-name)
      with-non-tail fn()
        zip-param-info(bs, args).foreach(chk-arg)
      chk-fun-callable(tname.get-name)
      if !(chk-tail || !chk-dg-names.any(fn(n) n == tname.get-name)) then
        val d = "non-tail call to a (mutually) recursive function:".text |+| chk-show-name(tname.get-name).text
        require-capability(may-recurse(), fn() Just(d))
    _ -> // local function
      with-non-tail fn()
        args.foreach(chk-expr)
      val isBapp = match f // does the bapp rule apply?
        Var(tname, _) -> chk-is-borrowed(tname)
        _ -> False
      if !isBapp then
        val d = "owned calls to functions require deallocation:".text |+| f.show.text
        require-capability(may-dealloc(), fn() Just(d))
        chk-expr(f)

fun chk-arg((pi, ex): (param-info, expr)): _ ()
  match pi
    Own -> chk-expr(ex)
    Borrow -> match ex
      TypeLam(_, fn') -> chk-arg((Borrow, fn'))
      TypeApp(fn', _) -> chk-arg((Borrow, fn'))
      App(TypeApp(Var(openName), _), [fn']) | openName.get-name == nameEffectOpen ->
        chk-arg((Borrow, fn')) // disregard .open calls
      Var(tname, info) -> mark-borrowed(tname, info)
      ELit(_) -> ()
      _ ->
        chk-expr(ex)
        if needs-dup-drop-tp(ex.type-of) then
          val d = "passing owned expressions as borrowed causes deallocation:".text |+| ex.show.text
          require-capability(may-dealloc(), fn() Just(d))

fun chk-wrap(tname: tName, info: var-info): _ ()
  val bs = chk-get-param-infos(tname.get-name)
  if bs.any(fn(b) b == Borrow) then
    emit-warning(fn() "a function with borrowed parameters is passed as an argument and implicitly wrapped (causing allocation)".text)
  val fip1 = chk-fip
  val fip2 = lookup-fip(tname.get-name)
  if !fip1.subsumes(fip2) then
    val d1 = ("the function " ++ tname.get-name.unqualify.show ++ " is passed as an argument, but has an incompatible FIP/FBIP annotation:").text |-|
             (" expected at least".text |+| fip1.fipt/show.text |+| "but found".text |+| fip2.fipt/show.text)
    emit-warning(fn() d1)
  if !(fip2.fip-allocation == AllocAtMost(0)) && !(fip1.fip-allocation == AllocUnlimited) then
    val d2 = ("the " ++ fip2.fipt/show ++ " function " ++ tname.get-name.unqualify.show ++ " is passed as an argument and may be called an unlimited number of times, causing unlimited allocation.").text
    emit-warning(fn() d2)

fun con-type-name(crepr: con-repr): name
  crepr.n

fun chk-allocation(cname: tName, crepr: con-repr): _ ()
  if crepr.is-conAsJust then ()
  elif crepr.con-type-name.unqualify.show.ends-with("_noreuse").bool then
    val d = "types suffixed with _noreuse are not reused:".text |+| chk-show-name(crepr.con-type-name).text
    require-capability(may-alloc(), fn() Just(d))
  else
    val size = get-constructor-alloc-size(crepr)
    get-allocation(cname, size)

// Only total/empty effects or divergence
fun chk-effect(tp: tau): _ ()
  fun is-fbip(tp': tau)
    match tp'.expand-syn
      TCon(tc) -> [nameEffectEmpty, nameTpDiv, nameTpPartial].any(fn(n) n == tc.name)
      TApp(tc1, [TCon(TypeCon(nm))]) -> eq-type(tc1, tconHandled) && nm == nameTpPartial
      _ -> False
  val (taus, _) = tp.extract-effect-extend
  if taus.all(is-fbip) then ()
  else emit-warning(fn() "algebraic effects other than".text |+| "pure".text |+| "may cause allocation.".text)

//--------------------------------------------------------------------------
// Reader/writer helpers
//--------------------------------------------------------------------------

// Run the given check, keep the warnings but extract the output.
fun extract-output(f: () -> _ ()): _ chk-output
  var out := output/empty
  with override handler
    fun emit-out(o) out := out.output/union(o)
  f()
  out

// Perform a test if the capability is not present
// and emit a warning if the test is unsuccessful.
fun require-capability(has-cap: bool, test: () -> _ maybe<doc>): _ ()
  if !has-cap then
    match test()
      Just(warning) -> emit-warning(fn() warning)
      Nothing -> ()

fun with-non-tail(f)
  with override val chk-tail = False
  f()

// Tail modulo a pattern-match. This handles modulo product contexts.
fun with-tail-mod-product(branches: list<branch>, f)
  match branches
    [Branch(_, [Guard(test, ex)])] | test.is-true -> with-tail-mod([ex], f)
    _ -> with-non-tail(f)

fun with-tail-mod(mod-exprs: list<expr>, f)
  with override val chk-tail = chk-tail && mod-exprs.all(is-mod-cons)
  f()

fun is-mod-cons(ex: expr): <div,exn> bool
  match ex
    Var(_, _) -> True
    TypeLam(_, e) -> e.is-mod-cons
    TypeApp(e, _) -> e.is-mod-cons
    Con(_, _) -> True
    ELit(_) -> True
    Let(dgs, e) -> dgs.flatten.all(fn(d) d.defExpr.pretend-decreasing.is-mod-cons) && e.is-mod-cons
    App(f, args) -> f.is-mod-cons-fun && args.all(fn(a) a.pretend-decreasing.is-mod-cons)
    _ -> False

// Functions with non-observable execution can be moved before the mod-cons call.
// This is necessary for various casts introduced in the effect checker.
fun is-mod-cons-fun(ex: expr): <div,exn> bool
  match ex
    TypeLam(_, e) -> e.is-mod-cons-fun
    TypeApp(e, _) -> e.is-mod-cons-fun
    Con(_, _) -> True
    Let(dgs, e) -> dgs.flatten.all(fn(d) d.defExpr.pretend-decreasing.is-mod-cons) && e.is-mod-cons-fun
    App(f, args) -> ex.type-of.has-total-effect && f.pretend-decreasing.is-mod-cons-fun && args.all(fn(a) a.pretend-decreasing.is-mod-cons)
    _ -> False

fun with-borrowed(names: name-set, f)
  with override val chk-delta = chk-delta.union(names)
  f()

fun chk-is-borrowed(nm: tName): _ bool
  chk-delta.member(nm.get-name)

fun mark-seen(tname: tName, info: var-info): _ ()
  if info.isRefCounted then // is locally defined?
    if needs-dup-drop(tname) then
      emit-out(Chk-output(rb-map/from-list([(tname, 1)]), int-map/empty(), ATLeaf))
  else chk-wrap(tname, info) // wrap rule

fun mark-borrowed(nm: tName, info: var-info): _ ()
  if !chk-is-borrowed(nm) then
    mark-seen(nm, info)
    if needs-dup-drop(nm) && info.isRefCounted then
      val d = "the last use of".text |+| chk-show-name(nm.get-name).text |+| "is borrowed (causing deallocation)".text
      require-capability(may-dealloc(), fn() Just(d))

//--------------------------------------------------------------------------
// Fip capabilities
//--------------------------------------------------------------------------

fun may-recurse(): _ bool
  match chk-fip
    Fip(_) -> False
    Fbip(_, isTail) -> !isTail
    NoFip(isTail) -> !isTail

fun may-dealloc(): _ bool
  match chk-fip
    Fip(_) -> False
    _ -> True

fun may-alloc(): _ bool
  chk-fip.fip-allocation == AllocUnlimited

fun chk-fun-callable(nm: name): _ ()
  fun is-callable-from(f2: fipT, f1: fipT)
    match (f2, f1)
      (Fip(_), _) -> True
      (Fbip(_, _), Fbip(_, _)) -> True
      (_, NoFip(_)) -> True
      _ -> False
  fun get-fip-info(infos: list<name-info>): maybe<fipT>
    match infos
      [InfoFun(fipt=f)] -> Just(f)
      [assumption/InfoExternal(fipt=f)] -> Just(f)
      _ -> Nothing
  val fip = chk-fip
  match get-fip-info(chk-ctx.chk-gamma.lookup-canonical(nm))
    Nothing | [nameCCtxSetCtxPath, nameFieldAddrOf].any(fn(n) n == nm) ->
      write-call-allocation(nm, Fip(AllocAtMost(0)))
    Nothing ->
      val d = "internal: fip analysis could not find fip information for function:".text |+| chk-show-name(nm).text
      emit-warning(fn() d)
    Just(fip') ->
      if fip'.is-callable-from(fip) then write-call-allocation(nm, fip')
      else
        val d = "calling a non-fip function:".text |+| chk-show-name(nm).text
        emit-warning(fn() d)

fun write-call-allocation(nm: name, fip: fipT): _ ()
  val defs = chk-current.map(def-name)
  val isSelf = defs.any(fn(d) d == nm)
  match fip
    Fip(n) -> emit-out(Chk-output(rb-map/empty(), int-map/empty(), if isSelf then ATCallSelf(n) else ATCall(n)))
    Fbip(n) -> emit-out(Chk-output(rb-map/empty(), int-map/empty(), if isSelf then ATCallSelf(n) else ATCall(n)))
    NoFip -> ()

fun chk-lazy-con(cname: tName, repr: con-repr): _ ()
  // you can use an fbip lazy constructor in a fip function
  fun is-callable-from(f2: fipT, f1: fipT)
    match (f2, f1)
      (NoFip(_), Fip(_)) -> False
      (NoFip(_), Fbip(_, _)) -> False
      _ -> True
  fun warn()
    val d = "internal: fip analysis could not find fip information for constructor:".text |+| chk-show-name(cname.get-name).text
    emit-warning(fn() d)
  val fip = chk-fip
  match chk-ctx.chk-newtypes.lookup(repr.con-type-name)
    Just(di) -> match di.constrs.filter(fn(ci) cname.get-name == ci.con-info/name)
      [conInfo] ->
        val fip' = conInfo.coninfo/lazy-fip
        if !conInfo.coninfo/is-lazy || fip'.is-callable-from(fip)
          then write-call-allocation(cname.get-name, fip')
          else
            val d = "allocating a non-fip lazy constructor:".text |+| chk-show-name(cname.get-name).text
            emit-warning(fn() d)
      _ -> warn()
    Nothing -> warn()

//--------------------------------------------------------------------------
// Reuse-token accounting
//--------------------------------------------------------------------------

fun get-allocation(nm: tName, size: reusable): _ ()
  match size
    NotReusable -> ()
    ReusableWithSize(sz) ->
      val id = unique-id("alloc")
      emit-out(Chk-output(rb-map/empty(), int-map/from-list([(sz.int64, [(ratio/one, [(nm, id)])])]), ATAlloc(id)))

fun pretty-con(tname: tName, sz: int): string
  tname.get-name.unqualify.show ++ "/" ++ sz.show

fun provide-token(debug-name: tName, size: reusable, out: chk-output): _ chk-output
  match size
    NotReusable -> out
    ReusableWithSize(sz) ->
      val fitting = out.gamma-dia.lookup(sz.int64).default([])
      val mbwarn = match fitting
        [] -> Just("the matched constructor".text |+| pretty-con(debug-name, sz).text |+| "is not reused".text)
        Cons((r, _), _) | !r.ratio/is-one ->
          Just("not all branches can reuse the space provided by".text |+| pretty-con(debug-name, sz).text)
        _ -> Nothing
      require-capability(may-dealloc(), fn() mbwarn)
      // upstream: `M.update (fmap snd . uncons) size` -- pop the head entry;
      // an EMPTY list at the key removes the key
      match out.gamma-dia.lookup(sz.int64)
        Nothing -> out
        Just([]) -> out(gamma-dia = out.gamma-dia.remove(sz.int64))
        Just(Cons(_, rest)) -> out(gamma-dia = out.gamma-dia.set(sz.int64, rest))

fun join-contexts(patss: list<list<pattern>>, cs: list<chk-output>): _ chk-output
  match cs
    [] -> output/empty
    _ ->
      val unionNm = cs.map(gamma-nm).foldl1(fn(m1, m2) m1.union-with(m2, fn(a: int, b: int) max(a, b)))
      val results = cs.map fn(c)
        val unused = unionNm.list.filter(fn((k, _)) c.gamma-nm.lookup(k).is-nothing).map(fst)
          .sort(?(<) = fn(a: tName, b: tName) a.get-name.name/cmp(b.get-name).is-lt)
        unused.foldl((True, c)) fn((allReusable, cc), tname)
          match add-type-reuse-info(tname, NotReusable)
            NotReusable ->
              val isHeapVal = needs-dup-drop(tname)
              (allReusable && !isHeapVal, cc)
            size -> (allReusable, provide-token(tname, size, cc))
      val noDealloc = results.map(fst)
      val cs' = results.map(snd)
      if !noDealloc.all(id) then
        val lines0 = patss.zip(cs.map(fn(o) o.gamma-nm)).map fn((ps, nm))
          (ps.map(pretty-pat-str).join(", ") ++ " -> " ++
            nm.list.map(fn((k, cnt)) chk-show-name(k.get-name) ++ "/" ++ cnt.show).join(", ")).text
        val d = vcat(Cons("not all branches use the same variables:".text, lines0))
        require-capability(may-dealloc(), fn() Just(d))
      val n = cs'.length
      val unionDia = cs'.map(fn(c) c.gamma-dia.map(fn(entries) entries.map(fn((p, x)) (p.ratio/div-by(n), x))))
                        .foldl1(fn(m1, m2) m1.union-with(m2, zip-tokens))
      Chk-output(unionNm, unionDia, ATMatch(cs'.map(alloc-tree)))

fun zip-tokens(xs: list<dia-entry>, ys: list<dia-entry>): _ list<dia-entry>
  match (xs, ys)
    (Cons((px, x), xx), Cons((py, y), yy)) -> Cons((px.ratio/add(py), x ++ y), zip-tokens(xx, yy))
    (xs', Nil) -> xs'
    (Nil, ys') -> ys'

fun pretty-pat-str(p: pattern): _ string
  match p
    PatCon(nm, []) -> chk-show-name(nm.get-name)
    PatCon(nm, pats) -> chk-show-name(nm.get-name) ++ "(" ++ pats.map(fn(p') p'.pretend-decreasing.pretty-pat-str).join(", ") ++ ")"
    PatVar(nm, PatWild) -> chk-show-name(nm.get-name)
    PatVar(nm, pat) -> chk-show-name(nm.get-name) ++ " as " ++ pat.pretty-pat-str
    PatLit(l) -> l.show
    PatWild -> "_"

fun add-type-reuse-info(nm: tName, size: reusable): _ reusable
  match size
    ReusableWithSize(_) -> size
    NotReusable ->
      match get-fixed-data-alloc-size(chk-ctx.chk-platform, chk-ctx.chk-newtypes, nm.type-of)
        Nothing -> NotReusable
        Just((sz, _)) -> ReusableWithSize(sz)

fun bind-name(nm: tName, msize: reusable, out: chk-output): _ chk-output
  match out.gamma-nm.lookup(nm)
    Nothing -> // unused, so available for drop-guided reuse!
      val (out', isReused) = match add-type-reuse-info(nm, msize)
        NotReusable -> (out, False)
        size -> (provide-token(nm, size, out), True)
      chk-drop(isReused, nm)
      out'
    Just(n) -> // variable is used 'n' times
      if n > 1 && needs-dup-drop(nm) then
        val d = "the variable".text |+| chk-show-name(nm.get-name).text |+| "is used multiple times (causing sharing and preventing reuse)".text
        require-capability(may-alloc(), fn() Just(d))
      out(gamma-nm = out.gamma-nm.remove(nm))

fun chk-drop(is-top-level-reused: bool, nm: tName): _ ()
  val isHeapValue = needs-dup-drop(nm)
  val isFlat = is-flat-type(nm)
  if !((is-top-level-reused && isFlat) || !isHeapValue) then
    // non-reused heap values are dropped
    val d = "the variable".text |+| chk-show-name(nm.get-name).text |+| "is unused (causing deallocation)".text
    require-capability(may-dealloc(), fn() Just(d))

//--------------------------------------------------------------------------
// Allocation credits (upstream AllocInLoop / getAllocCredits)
//--------------------------------------------------------------------------

// We record if the program has both an allocation and a self-call which may
// be executed in sequence. If that is the case, the program may use
// unlimited allocation.
struct alloc-in-loop
  has-alloc: bool
  has-self-call: bool
  has-both-in-sequence: bool

val ail/empty: alloc-in-loop = Alloc-in-loop(False, False, False)

// Sequential composition
fun ail/seq(x: alloc-in-loop, y: alloc-in-loop): alloc-in-loop
  Alloc-in-loop(x.has-alloc || y.has-alloc, x.has-self-call || y.has-self-call,
    x.has-both-in-sequence || y.has-both-in-sequence ||
    (x.has-alloc && y.has-self-call) || (y.has-alloc && x.has-self-call))

// Non-sequential composition
fun ail/join(x: alloc-in-loop, y: alloc-in-loop): alloc-in-loop
  Alloc-in-loop(x.has-alloc || y.has-alloc, x.has-self-call || y.has-self-call,
    x.has-both-in-sequence || y.has-both-in-sequence)

fun get-alloc-credits(not-reused: int-set, tree: alloc-tree): <div,exn> (fip-alloc, alloc-in-loop)
  match tree
    ATAlloc(id) ->
      if int-set/member(not-reused, id.int64) then (AllocAtMost(1), ail/empty(has-alloc = True))
      else (AllocAtMost(0), ail/empty)
    ATCall(alloc) -> (alloc, ail/empty)
    ATCallSelf(alloc) -> (alloc, ail/empty(has-self-call = True))
    ATSeq(a1, a2) ->
      val (x1, l1) = get-alloc-credits(not-reused, a1)
      val (x2, l2) = get-alloc-credits(not-reused, a2)
      (x1.combine(x2), l1.ail/seq(l2))
    ATMatch(as0) ->
      as0.foldl((AllocAtMost(0), ail/empty)) fn((a, b), t)
        val (a', b') = get-alloc-credits(not-reused, t.pretend-decreasing)
        (a.fipa/max(a'), b.ail/join(b'))
    ATLeaf -> (AllocAtMost(0), ail/empty)

fun pretty-fip-alloc(f: fip-alloc): string
  match f
    AllocAtMost(0) -> "nothing"
    AllocAtMost(n) -> "at most " ++ n.show
    AllocFinitely -> "a finite amount"
    AllocUnlimited -> "unlimited"

fun check-output-empty(out: chk-output): _ ()
  // Warn on the LARGEST unbound key
  match out.gamma-nm.keys.reverse
    Cons(nm, _) ->
      val d = "unbound name (which may have been used despite being borrowed):".text |+| chk-show-name(nm.get-name).text
      emit-warning(fn() d)
    Nil -> ()
  val notReused = int-set/from-list(out.gamma-dia.list.map(snd).concat.map(snd).concat.map(snd).map(int64))
  val (allocations0, allocInLoop) = get-alloc-credits(notReused, out.alloc-tree)
  val allocations = if allocInLoop.has-both-in-sequence then AllocUnlimited else allocations0
  val permission = chk-fip.fip-allocation
  if allocations.fipa/cmp(permission).is-gt then
    val d = "function allocates".text |+| pretty-fip-alloc(allocations).text |+| "but was declared as allocating".text |+| pretty-fip-alloc(permission).text
    emit-warning(fn() d)

//--------------------------------------------------------------------------
// Type/data helpers
//--------------------------------------------------------------------------

fun zip-param-info(xs: list<param-info>, bs: list<b>): _ list<(param-info, b)>
  // upstream: `zip (xs ++ repeat Own)`
  match (xs, bs)
    (_, Nil) -> Nil
    (Cons(x, xx), Cons(b, bb)) -> Cons((x, b), zip-param-info(xx, bb))
    (Nil, Cons(b, bb)) -> Cons((Own, b), zip-param-info([], bb.pretend-decreasing))

// value types with reference fields still need a drop
fun needs-dup-drop(tname: tName): _ bool
  if tname.get-name.is-cctx-name then False  // ignore generated contexts
  else needs-dup-drop-tp(tname.type-of)

fun needs-dup-drop-tp(tp: ktype): _ bool
  match get-data-info-x(chk-ctx.chk-newtypes, tp)
    Nothing -> True
    Just(di) ->
      // We pretend that integers are always small and don't need to be dropped.
      di.data-info/name != nameTpInt && needs-dup-drop-data(di)

fun is-flat-type(tname: tName): _ bool
  // A type is flat if no field of any constructor needs a dup/drop.
  match get-data-info-x(chk-ctx.chk-newtypes, tname.type-of)
    Nothing -> True
    Just(di) -> di.constrs.all(fn(ci) ci.con-info/params.all(fn((_, tp)) !needs-dup-drop-tp(tp)))

fun get-constructor-alloc-size(crepr: con-repr): _ reusable
  ru-is-reusable(crepr, chk-ctx.chk-platform)

// Return borrowing infos for a name. May return the empty list
// if no borrowing takes place.
fun chk-get-param-infos(nm: name): _ list<param-info>
  match chk-ctx.chk-borrowed.lookup(nm)
    Nothing -> []
    Just(pinfos) -> pinfos

// The port's `borrowed` map does not carry fip
// information, so look it up in gamma instead (same source of truth)
fun lookup-fip(nm: name): _ fipT
  match chk-ctx.chk-gamma.lookup-canonical(nm)
    [InfoFun(fipt=f)] -> f
    [assumption/InfoExternal(fipt=f)] -> f
    _ -> noFip

//--------------------------------------------------------------------------
// Warnings
//--------------------------------------------------------------------------

// show a name relative to the current module (upstream `ppName` with the
// module context)
fun chk-show-name(nm: name): _ string
  if nm.qualifier == chk-ctx.chk-prog-name then nm.unqualify.show else nm.show

fun emit-warning(makedoc: () -> _ doc): _ ()
  val (rng, nm) = match chk-current
    Cons(d, _) -> (d.nameRange, d.def-name)
    _ -> (range/null, name/nil)
  val fdoc = chk-fip.fipt/show.text |+| "fun".text |+| chk-show-name(nm).text |.| ":".text |+| makedoc()
  if nm.qualifier != nameCoreDebug then
    emit-warn-doc(rng, fdoc)
