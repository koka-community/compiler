import compiler/common/name
import compiler/common/name-collections
import compiler/common/unique
import compiler/core/core
import compiler/core/corevar
import compiler/type/type
import std/data/linearset
import std/data/linearmap

alias locals = name-set;
alias renaming = name-map<name>

effect uniquefy
  fun set-locals(l: locals): ()
  fun get-locals(): locals
  fun set-renaming(r: renaming): ()
  fun get-renaming(): renaming

fun full-localized(f)
  val locals = get-locals()
  val r = localized(f)
  set-locals(locals)
  r

fun localized(f)
  val ren = get-renaming()
  val r = f()
  set-renaming(ren)
  r

fun start/run-unique(start: int, f: () -> <unique,uniquefy|e> a): e a
  with common/unique/run-unique(start)
  with run-unique()
  f()

val eqName = fn(n1: name, n2: name) n1 == n2
fun fun/run-unique(f: () -> _ a): _ a
  var locals := names/empty
  var renaming := LinearMap([])
  with handler
    fun set-locals(l) locals := l
    fun get-locals() locals
    fun set-renaming(r) renaming := r
    fun get-renaming() renaming
  f()

fun expr/uniquefy(e: expr): _ expr
  uniquefy(e, tnames/empty)

fun free/uniquefy(e: expr, free: linearSet<tName>): _ expr
  val locals = LinearSet(free.union(e.free-locals).list.map(get-name))
  with start/run-unique(0)
  set-locals(locals)
  e.uniquefyx

fun uniquefyExprU(e: expr)
  with run-unique()
  val e' = e.uniquefyx
  (e', get-unique())

fun core/uniquefy(c: core): _ core
  c(defs=uniquefy(c.defs))

fun dgs/uniquefy(dgs: def-groups): _ def-groups
  with start/run-unique(0)
  val locals = get-locals()
  val topLevelDefs = dgs.flatten.map(def-name).filter(fn(n:name) !n.is-nil)
  set-locals(topLevelDefs.foldl(locals, fn(acc, n) acc.add(n.unqualify)))
  dgs.map(fn(dg) full-localized({uniquefyDG(dg)}))

fun dg/uniquefyDG(dg: def-group)
  match dg
    DefNonRec(d) -> DefNonRec(d(defExpr=d.defExpr.uniquefyx))
    DefRec(ds) -> DefRec(ds.map(fn(d) d(defExpr=d.defExpr.uniquefyx)))

fun dg/uniquefy(dg: def-group): _ def-group
  with start/run-unique(0)
  match dg
    DefNonRec(d) -> DefNonRec(d.uniquefy)
    DefRec(defs) ->
      val locals = get-locals()
      set-locals(defs.map(def-name).filter(!_.is-nil).foldl(locals, add))
      DefRec(defs.map(fn(d) d(defExpr=localized({d.defExpr.uniquefyx}))))

fun innerdefgroup/uniquefy(dg: def-group)
  match dg
    DefNonRec(d) -> DefNonRec(uniquefy(d))
    DefRec(defs) -> DefRec(recdefs/uniquefy(defs))

fun recdefs/uniquefy(defs: list<def>)
  val names = defs.map(_.def-name.uniquefy)
  val exprs = localized({defs.map(_.defExpr.uniquefyx)})
  names.zip(exprs).zip(defs).map(fn(((n, e), d)) d(def-name=n, defExpr=e))

fun def/uniquefy(d: def)
  val expr1 = localized({d.defExpr.uniquefyx})
  val name1 = d.def-name.uniquefy
  d(def-name=name1, defExpr=expr1)

fun expr/uniquefyx(e: expr)
  match e
    Lam(tnames, eff, expr) ->
      with localized  
      val tnames1 = tnames.map(uniquefy)
      val expr1 = expr.uniquefyx
      Lam(tnames1, eff, expr1)
    Var(tname, info) ->
      val renaming = get-renaming()
      match renaming.lookup(tname.get-name)
        Just(nm) -> Var(TName(nm, tname.type-of), info)
        Nothing -> e
    App(f, args) -> App(f.uniquefyx, args.map(uniquefyx))
    TypeLam(tvs, expr) -> TypeLam(tvs, expr.uniquefyx)
    TypeApp(expr, tps) -> TypeApp(expr.uniquefyx, tps)
    Con -> e
    ELit -> e
    Let(def-groups, expr) -> Let(def-groups.map(innerdefgroup/uniquefy), expr.uniquefyx)
    Case(exprs, branches) ->
      Case(exprs.map(uniquefyx), localized({branches.map(_.uniquefy(exprs.map(type-of)))}))

fun branch/uniquefy(b: branch, patTps: list<ktype>)
  val pats = b.patterns.zip(patTps).map(fn((p, t)) p.uniquefy(t))
  val guards = b.guards.map(uniquefy)
  Branch(pats, guards)

fun guard/uniquefy(g: guard)
  Guard(g.test.uniquefyx, g.body.uniquefyx)

fun pattern/uniquefy(pat: pattern, patTp: ktype)
  match pat
    PatVar(tname, p) -> PatVar(tname.uniquefy, p.uniquefyX(patTp))
    _ ->
      val name = "pat".new-hidden-name.uniquefy
      val p = pat.uniquefyX(patTp)
      PatVar(TName(name, patTp), p)

fun pattern/uniquefyX(p: pattern, patTp: ktype)
  match p
    PatWild -> p
    PatLit -> p
    PatCon(patName, pats, repr, typeArgs, kexists, typeRes, info, skip) ->
      PatCon(patName, pats.zip(typeArgs).map(fn((p', t)) p'.uniquefy(t)), repr, typeArgs, kexists, typeRes, info, skip)
    PatVar(tname, pat) -> PatVar(tname.uniquefy, pat.uniquefyX(patTp)) 

fun tname/uniquefy(tn: tName)
  TName(tn.get-name.uniquefy, tn.type-of)

fun make-full-unique()
  get-unique() != 0

fun name/uniquefy(n:name)
  if n.is-nil then n
  else
    val locals = get-locals()
    val full = make-full-unique()
    if full || locals.member(n) then
      val renaming = get-renaming()
      val name1 = if full then n.unique-name-from else find-unique-name(0, n, locals)
      set-locals(locals.add(name1))
      set-renaming(renaming.add(n, name1))
      name1
    else 
      set-locals(locals.add(n))
      n

fun find-unique-name(i: int, n: name, locals: name-set): _ name
  val name1 = to-unique-name(i, n)
  if locals.member(name1) then find-unique-name(i+1, n, locals)
  else name1