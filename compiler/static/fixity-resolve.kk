import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/failure
import compiler/platform/config
import compiler/common/range
import compiler/syntax/syntax
import compiler/common/syntax
import compiler/common/color-scheme
import std/data/linear-map
import compiler/lib/pprint
// Updated to 7eb71dc on 2/10/25

fun fixity-resolve(fixMap: fixities, program: user-program)
  val fixMap1 = fixities-compose(fixMap, program.fix-defs.extract-fix-map)
  with handleFixities(fixMap1)
  val defs1 = program.defs.resolve
  val tdefs = program.typedefs.resolve
  program(defs=defs1, typedefs=tdefs)

fun extract-fix-map(fds: list<fix-def>): fixities
  fun extractFix(FixDef(name, fixity): fix-def)
    (name, fixity)
  fixities-new(fds.map(extractFix))

// Resolve lazy constructor definitions
fun tdefgroup/resolve(tdefg: typedef-group<user-type, user-kind>)
  match tdefg
    TypeDefRec(tdefs) -> TypeDefRec(tdefs.map(resolve))
    TypeDefNonRec(tdef) -> TypeDefNonRec(tdef.resolve)

fun tdef/resolve(tdef: user-typedef)
  match tdef
    DataType(tbinder, params, constrs, rng, vis, sort, ddef, deffect, doc) -> 
      DataType(tbinder, params, constrs.map(resolve), rng, vis, sort, ddef, deffect, doc)
    d -> d

fun con/resolve(constr: user-user-con)
  match constr
    UserCon(nm, exists0, params, result, Just((fipT, lzy)), nmrng, rng, vis, doc) ->
      UserCon(nm, exists0, params, result, Just((fipT, lzy.expr/resolve)), nmrng, rng, vis, doc)
    c -> c

// Rewrite syntax tree
fun def-group/resolve(dg: def-group<user-type>)
  match dg
    DefRec(dfs) -> DefRec(dfs.map(resolve))
    DefNonRec(df) -> DefNonRec(resolve(df))

fun def/resolve(d: def<user-type>)
  val binder' = d.binder.resolve
  d(binder=binder')

fun binder/resolve(b: value-binder<t, a>, ?resolve: (a) -> _ a): _ value-binder<t, a>
  val expr' = b.expr.resolve
  b(expr=expr')

fun list/resolve(ls: list<a>, ?resolve: (a) -> _ a): _ list<a>
  ls.map(resolve)

fun expr/resolve(ex: user-expr): _ user-expr
  match ex
    Lam(binds, expr, rng, tp) ->
      val binds' = binds.list/resolve
      val expr' = expr.resolve
      Lam(binds', expr', rng, tp)
    Let(defs, expr, rng) ->
      val defs' = defs.resolve
      val expr' = expr.resolve
      Let(defs', expr', rng)
    Bind(def, expr, rng) ->
      val def' = def.resolve
      val expr' = expr.resolve
      Bind(def', expr', rng)
    App(f, nargs, rng) ->
      val (names, args) = nargs.unzip
      val args' = args.map(resolve)
      val f' = f.resolve
      val nargs' = names.zip(args')
      match f
        Var(name) | name == nameOpExpr -> resolve(args')
        _ -> App(f', nargs', rng)
    Var -> ex
    Literal -> ex
    Ann(expr, ty, rng) ->
      val expr' = expr.resolve
      Ann(expr', ty, rng)
    Case(expr, brs, lzy, rng) ->
      val expr' = expr.resolve
      val brs' = brs.map(resolve)
      Case(expr', brs', lzy, rng)
    Parens(expr, nm, pre, rng) ->
      val expr' = expr.resolve
      Parens(expr', nm, pre, rng)
    Handler(shallow, scoped, over, allowMask, eff, pars, reinit, ret, finally, ops, hrng, rng) ->
      val ret' = ret.resolve
      val ops' = ops.map(resolve)
      val reinit' = reinit.resolve
      val final' = finally.resolve
      Handler(shallow, scoped, over, allowMask, eff, pars, reinit', ret', final', ops', hrng, rng)
    Inject(tp, expr, b, rng) ->
      val expr' = expr.resolve
      Inject(tp, expr', b, rng)

fun maybe/resolve(ex: maybe<a>, ?resolve: (a) -> _ a): _ maybe<a>
  ex.map(resolve)

fun branch/resolve(branch: branch<user-type>)
  match branch
    Branch(patt, guards) -> Branch(patt, guards.map(resolve))

fun guard/resolve(g: guard<user-type>)
  match g
    Guard(test, expr) -> Guard(test.resolve, expr.resolve)

fun handlerbranch/resolve(hb: handler-branch<user-type>)
  match hb
    HandlerBranch(branchExpr=e) -> hb(branchExpr=e.resolve)

// Fixity map for all operators
alias fixities = name-map<fixity>
val fixitiesEmpty: fixities = LinearMap([])

fun find-fixity(fixities: fixities, name: name): fixity
  fixities.lookup(name).default(FixInfix(50, AssocNone))

fun fixities-compose(fix1: fixities, fix2: fixities): fixities
  fix2.list.foldl(fix1) fn(acc, (name, fixity))
    match fix1.lookup(name)
      Just(x as FixInfix) -> acc.add(name, x)
      _ -> acc.add(name, fixity)

fun fixities-new(fs: list<(name, fixity)>): fixities
  fixitiesEmpty + fs.filter(_.snd.is-fixInfix)

effect fixityEff
  fun add-fix-error(s: doc, r: range): ()
  fun get-fixities(): fixities
  fun update-fixities(f: fixities -> pure fixities): ()

fun handleFixities(initial: fixities, f: () -> _ a): _ (a, fixities, list<doc>)
  var fixes := initial
  var errors := []
  with handler
    fun get-fixities()
      fixes
    fun update-fixities(f': fixities -> pure fixities)
      fixes := f'(fixes)
    fun add-fix-error(s, rng)
      errors := Cons(s, errors)
  (f(), fixes, errors)

// Resolve fixities:
// The algorithm is written a bit long to enable easy extension to prefix, postfix, and distfix operators

value struct op { expr: user-expr; fixity: fixity }
value type term
  Term(expr: user-expr)
  Oper(op: op)

alias expr-stack = list<user-expr>
alias op-stack = list<op>

fun fixities/resolve(exprs: list<user-expr>): _ user-expr
  val fixMap = get-fixities()
  terms/resolve([], [], exprs.map(_.to-term(fixMap)))

// Find out if this is an operator
fun to-term(expr: user-expr, fixities: fixities): term
  match expr
    Var(name, True) -> Oper(Op(expr, find-fixity(fixities, name)))
    _ -> Term(expr)

// The real resolve algorithm uses Dijkstra's strategy with two stacks
fun terms/resolve(exprs: expr-stack, os: op-stack, tms: list<term>): _ user-expr
  match (exprs, os, tms)
    // final term computed
    ([x], [], []) -> x
    // cleanup stage, apply all ops
    (xs, ops as Cons, []) -> 
      apply(xs, ops, [])
    // always push terms
    (xs, ops, Cons(Term(t), tt)) ->
      resolve(Cons(t, xs), ops, tt)
    // prefix operator
    (xs, ops, Cons(Oper(t as Op(Var, FixPrefix)), tt)) ->
      push(xs, ops, tt, t)
    // postfix operator
    (xs, ops, Cons(Oper(t as Op(_, FixPostfix)), tt)) ->
      push(xs, ops, tt, t)
    // infix operator
    (xs, ops, ts as Cons(Oper(t as Op(_, FixInfix(_, assoc))), tt)) ->
      val prec = t.precedence-op
      val precCtx =
        match ops
          Cons(o) -> o.precedence-op
          _ -> 0
      if prec > precCtx then push(xs, ops, tt, t)
      elif prec < precCtx then apply(xs, ops, ts)
      else
        ops.check-ambiguous(t)
        if assoc == AssocRight then push(xs, ops, tt, t) else apply(xs, ops, ts)
    ([], [], []) -> failure/fail("static/fixity-resolve resolveTerms: no term: fix parser")
    _ -> failure/fail("static/fixity-resolve resolveTerms: fixity resolver error")

fun precedence-op(Op(_, fix): op)
  fix.precedence

fun precedence(f: fixity)
  match f
    FixInfix(p) -> p
    FixPrefix -> 102
    FixPostfix -> 101

fun check-ambiguous(ops: op-stack, Op(op, fix): op)
  match (ops, fix)
    (Cons(Op(_, fixCtx as FixInfix(_, assocCtx))), FixInfix(_, assoc)) | assoc.is-assocNone || !(assocCtx == assoc) ->
      ambiguous(fixCtx, fix, op)
    _ -> ()

fun ambiguous(fixCtx: fixity, fix: fixity, op: user-expr)
  val opText =
    match op
      Var(nm) -> nm.pretty |.| space
      _ -> empty
  val msg = "Ambiguous ".text |+| fix.pp-fixity |+| "operator".text |+| opText |.| "in a".text |+| fixCtx.pp-fixity |+| "context".text |-| " hint: add parenthesis around the sub-expression to disambiguate".text
  add-fix-error(msg, op.range)

fun pp-fixity(f: fixity): doc
  match f
    FixInfix(_, assoc) ->
      match assoc
        AssocLeft -> "left-associative".text
        AssocRight -> "right-associative".text
        AssocNone -> "non-associative".text
    FixPrefix -> "prefix".text
    FixPostfix -> "postfix".text

// Helper operations: push and apply
fun push(xs: expr-stack, ops: op-stack, ts: list<term>, t: op): _ user-expr 
  resolve(xs, Cons(t, ops), ts)

fun apply(xs: list<expr<user-type>>, ops: list<op>, ts: list<term>)
  match ops
    Cons(Op(op, FixPostfix), rst) ->
      val ys = apply-unary-op(op, xs)
      resolve(ys, rst, ts)
    Cons(Op(op, FixPrefix), rst) ->
      val ys = apply-unary-op(op, xs)
      resolve(ys, rst, ts)
    Cons(Op(op, FixInfix(_, _)), rst) ->
      val ys = apply-infix-op(op, xs)
      resolve(ys, rst, ts)
    _ -> failure/fail("static/fixity-resolve apply: fixity resolver error")

fun apply-unary-op(op: expr<t>, ts: list<expr<t>>): _ list<expr<t>>
  match ts
    Cons(t, ts) -> Cons(App(op, [(Nothing, t)], t.range.combine(op.range)), ts)
    _ -> 
      add-fix-error("Unary operator has not enough arguments".text, op.range )
      ts

fun apply-infix-op(op: expr<t>, ts: list<expr<t>>): _ list<expr<t>>
  match ts
    Cons(t1, Cons(t2, ts)) -> Cons(App(op, [(Nothing, t1), (Nothing, t2)], t1.range.combine(t2.range)), ts)
    _ -> 
      add-fix-error("Infix operator has not enough arguments".text, op.range)
      ts
