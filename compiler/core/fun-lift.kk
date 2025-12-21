import compiler/lib/pprint
import compiler/common/failure
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/common/unique
import compiler/kind/kind
import compiler/type/type
import compiler/type/kind
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/assumption
import compiler/core/core
import compiler/core/corevar
import compiler/platform/config
import std/data/linearset

fun lift-functions()
  with handle-fun-lift()
  set-core-defs(lift-def-groups(get-core-defs(), True))

effect fun-lift-eff
  fun emit-lifted(dg: def-group): ()
  fun emit-lifteds(dgs: def-groups): ()
  fun collect-lifted(): def-groups

effect val currentDef: list<def>

alias liftDefEff = <fun-lift-eff, currentDef, pure, unique, comp-flags>

fun current-def-names()
  currentDef.map(def-name)

fun set-current-def(d: def, f)
  with override
    val currentDef = [d] ++ currentDef
  f()

fun handle-fun-lift(f)
  var lifted := []
  with handler
    fun emit-lifted(dg) lifted := Cons(dg, lifted)
    fun emit-lifteds(dgs) lifted := dgs ++ lifted
    fun collect-lifted() 
      val l = lifted
      lifted := []
      l
  with handler
    val currentDef = []
  f()

// Transform definition groups
fun lift-def-groups(defgs: def-groups, topLevel: bool): liftDefEff def-groups
  defgs.map(_.lift-defgroup(topLevel)).concat

fun subst-with-lifted-expr(d: def, subst)
  val body = match d.defExpr
    TypeLam(tpars, Lam(pars, eff, lbody)) -> TypeLam(tpars, Lam(pars, eff, corevar/expr/(|->)(subst, lbody)))
    Lam(pars, eff, lbody) -> Lam(pars, eff, subst |-> lbody)
    e -> fail("core/fun-lift lift-defgroup: expected lambda, got " ++ e.show)
  // Note here we only want to skip the substitution for fvs and tvs,
  // but we have skipped more than necessary, i.e.,
  // the part of those tpars and pars that are not in fvs and tvs.
  // But it is OK here, because fvs/tvs are in the scope on all defs,
  // and we have ensured that fvs/pars and tvs/tpars are always unique (see type/infer)
  d(defExpr = body)

fun lift-defgroup(defg: def-group, topLevel: bool)
  if topLevel then
    match defg
      DefNonRec(d) ->
        val d' = d.lift-def(True)
        // all lifteddefinitions are put before the current definition
        collect-lifted() ++ [DefNonRec(d')] 
      DefRec(defs) ->
        val defs' = defs.map(_.lift-def(True))
        val lifted = collect-lifted()
        // defs' depend on the lifted, but the lifted might depend on defs'
        // we could do a topological sort here (as in static/binding-groups) but for simplicity
        // we approximate here for now
        // Note that it can be important to have precise DefRec groups for other optimizations, like TMRC (compiler/core/ctail)
        val dnames = defs'.defsTNames
        val (gnonrecs, grecs) = lifted.partition(_.free-vars.intersection(tnames/empty + dnames).is-empty)
        (gnonrecs ++ [DefRec(grecs.flatten ++ defs')])
  else
    match defg
      DefNonRec(d) -> [DefNonRec(d.lift-def(False))]
      DefRec(defs) ->
        val pinfoss = defs.map(param-infos)
        val exprDocs = defs.map(fn(d) (d.defExpr, d.doc))
        val exprs = defs.map(defExpr)
        val names = defs.map(defTName)
        val fvs = exprs.map(free-locals).unions - names
        val tvs = exprs.map(free-type-vars).unions
        val (callExprs, liftedDefs0) = pinfoss.zip(names.zip(exprDocs)).map(fn((infos, (name, doc))) make-def(fvs.list, tvs.list, infos, name, doc)).unzip
        val subst = names.zip(callExprs)
        val liftedDefs = liftedDefs0.map(_.subst-with-lifted-expr(subst))
        val groups = DefRec(liftedDefs).lift-defgroup(True) // lift all recs to top-level
        emit-lifteds(groups)
        val defs' = defs.zipwith(callExprs, fn(d, c) d(defExpr = c, sort=d.sort.lift-sort(False)))
        defs'.map(DefNonRec) // change a DefRec to all DefNonRecs

fun lift-def(d: def, topLevel: bool)
  with set-current-def(d)
  val expr' = d.defExpr.lift-expr(topLevel)
  d(defExpr=expr', sort=d.sort.lift-sort(topLevel))

fun lift-sort(s: def-sort, b: bool)
  match (s, b)
    (DefFun, False) -> DefVal
    _ -> s

fun lift-expr(ex: expr, topLevel: bool)
  match ex
    App(f, args) -> App(f.lift-expr(False), args.map(_.lift-expr(False)))
    Lam(args, eff, body) -> // don't lift anonymous functions
      Lam(args, eff, body.lift-expr(False))
    Let(defgs, body) ->
      Let(defgs.lift-def-groups(False), body.lift-expr(False))
    Case(exprs, bs) -> Case(exprs.map(_.lift-expr(False)), bs.map(lift-branch))
    TypeLam(tvars, body) -> TypeLam(tvars, body.lift-expr(topLevel))
    TypeApp(body, targs) -> TypeApp(body.lift-expr(topLevel), targs)
    _ -> ex

fun lift-branch(Branch(pat, guards): branch)
  Branch(pat, guards.map(lift-guard))

fun lift-guard(Guard(test, expr): guard)
  Guard(test.lift-expr(False), expr.lift-expr(False))

fun make-def(fvs: list<tName>, tvs: list<type-var>, pinfos: list<param-info>, origName: tName, (expr, doc): (expr, string))
  val dnames = current-def-names()
  val (name, inl) = unique-name-current-def()
  fun unwild(TName(nm, tp): tName)
    TName(if nm.nameStem.head-char.unjust == '_' then prepend("wild", name) else name, tp) 
  val (tpars, pars, eff, body) = match expr
    TypeLam(tpars, Lam(pars, eff, lbody)) -> (tpars, pars.map(unwild), eff, lbody)
    Lam(pars, eff, lbody) -> ([], pars.map(unwild), eff, lbody)
    _ -> fail("core/fun-lift make-def: expected lambda, got " ++ expr.show)
  val alltpars = tvs ++ tpars
  val allpars = fvs ++ pars
  val allargs = allpars.map(Var(_, InfoNone))
  val allpinfos = fvs.map(fn(_) Own) ++ pinfos
  val liftedFun = add-type-lambdas(alltpars, Lam(allpars, eff, body))
  val liftedTp = liftedFun.type-of
  val funExpr = Var(TName(name, liftedTp), InfoArity(alltpars.length, allargs.length))
  val etaExpr = match (tvs, fvs)
    (Nil, Nil) -> funExpr
    _ -> add-type-lambdas(tpars, Lam(pars, eff, App(add-type-apps(alltpars, funExpr), allargs)))
  val liftedDef = Def(name, liftedTp, liftedFun, Private, def-fun(allpinfos), inl, null, "// lifted local: " ++ (dnames ++ [origName.get-name]).map(_.unqualify.show).join(", ") ++ "\n" ++ doc)
  (etaExpr, liftedDef)

fun unique-name-current-def()
  val current = currentDef.last.unjust
  val i = new-unique()
  val udef-name = to-hidden-unique-name(i,"lift",current.def-name)
  (udef-name, current.kinline)

// Don't lift a simple function. A function is simple if it's body is simply an
// application consisting of simple arguments.
// More general than eta-expanded expressions.
fun is-simple-fun(ex: expr)
  // The definition of simple arguments can be extended.
  fun is-simple-targ(t: ktype)
    match t
      TCon -> True
      TVar -> True
      TApp(ty, tys) -> is-simple-targ(ty) && tys.all(is-simple-targ)
      _ -> False
  fun is-simple-arg(a: expr)
    match a
      Con -> True
      ELit -> True
      Var -> True
      App(e, es) -> is-simple-arg(e) && es.all(is-simple-arg)
      _ -> False
  match ex
    Lam(_, _, App(_, args)) -> args.all(is-simple-arg)
    TypeLam(_, Lam(_, _, App(TypeApp(_, targs), args))) ->
      targs.all(is-simple-targ) && args.all(is-simple-arg)
    TypeLam(_, Lam(_, _, App(_, args))) -> args.all(is-simple-arg)
  
