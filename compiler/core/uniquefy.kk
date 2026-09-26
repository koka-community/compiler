// Ported as of 2026-01-18; approx upstream baseline commit 3b07c76 of Core/Uniquefy.hs (backfilled 2026-07-23)
module compiler/core/uniquefy

import compiler/common/name
import compiler/common/name-collections
import compiler/common/unique
import compiler/core/core
import compiler/core/corevar
import compiler/type/type
import std/data/rb-set
import std/data/int-map
import std/num/int64
import std/data/hash
import std/data/rb-map

// PERFORMANCE: locals/renaming were a LinearSet/LinearMap -- association
// lists with O(n) member/lookup/insert -- inside the optimizer's hottest
// inner loop (uniquefy runs before every simplify-defs, and simplify calls
// free/uniquefy per Let). That made optimize cost ~10s on a ~100-line module
// and dominated cold builds (sampled: uniquefy 34k flattened frames vs
// specialize 216). Now hash-bucketed patricia tries keyed on the names'
// precomputed hash fields; buckets keep full name equality, so semantics
// are unchanged.
alias locals = int-map<list<name>>
alias renaming = int-map<list<(name, name)>>

// `hashStem`/`hashLocalQual`/`hashModule` are upstream-compatible FOUR-CHARACTER
// hashes (`take 4` of the lowercased text) -- kept that way because `name/cmp`'s
// ordering must match upstream's `Ord Name`. They are far too weak to BUCKET on:
// a compiler pass is dominated by generated names sharing a long prefix
// (`@uniq-...`, `@mlift-...`, `@lift-...`, `@spec-...`), so they all collapse
// into ONE bucket and `uq-member` degenerates into a linear scan whose every
// step is an allocating case-insensitive name comparison (profiling put ~4400
// of ~4500 name-comparison samples in uq-member/uq-add alone).
//
// Bucket on a hash of the FULL stem instead. It must be case-INSENSITIVE:
// name equality ignores case, so equal names have to land in the same bucket.
fun nkey(n: name): int64
  // `keyStem` is the same case-insensitive full-stem hash this used to compute
  // here, but cached on the name at construction. Computing it per call meant a
  // `to-lower` ALLOCATION plus a full rehash of the stem on every `uq-member`
  // and `uq-add` -- and those are on the hot path of every uniquefy pass.
  ((n.keyStem.int64 * 33.int64 + n.hashLocalQual.int64) * 33.int64 + n.hashModule.int64)

fun uq-member(l: locals, n: name): bool
  match l.lookup(n.nkey)
    Just(b) -> b.any(fn(x) x == n)
    Nothing -> False

fun uq-add(l: locals, n: name): locals
  l.insert-with(n.nkey, [n], fn(new, old) if old.any(fn(x) x == n) then old else new ++ old)

fun uq-from-names(ns: list<name>): locals
  ns.foldl(int-map/empty(), uq-add)

fun uq-ren-lookup(r: renaming, n: name): maybe<name>
  match r.lookup(n.nkey)
    Just(b) -> b.find(fn((k, _)) k == n).map(snd)
    Nothing -> Nothing

// OVERWRITES an existing entry (see the use site: add-if-absent semantics
// dropped resume bodies)
fun uq-ren-set(r: renaming, n: name, to: name): renaming
  r.insert-with(n.nkey, [(n, to)], fn(new, old) new ++ old.filter(fn((k, _)) k != n))

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
  var locals := int-map/empty()
  var renaming := int-map/empty()
  with handler
    fun set-locals(l) locals := l
    fun get-locals() locals
    fun set-renaming(r) renaming := r
    fun get-renaming() renaming
  f()

pub fun expr/uniquefy(e: expr): _ expr
  uniquefy(e, tnames/empty)

pub fun free/uniquefy(e: expr, free: rbset<tName>): _ expr
  val locals = uq-from-names(free.union(e.free-locals).list.map(get-name))
  with start/run-unique(0)
  set-locals(locals)
  e.uniquefyx

pub fun uniquefyExprU(e: expr)
  with run-unique()
  val e' = e.uniquefyx
  (e', get-unique())

pub fun core/uniquefy(c: core): _ core
  c(defs=uniquefy(c.defs))

pub fun dgs/uniquefy(dgs: def-groups): _ def-groups
  with start/run-unique(0)
  val locals = get-locals()
  val topLevelDefs = dgs.flatten.map(def-name).filter(fn(n:name) !n.is-nil)
  set-locals(topLevelDefs.foldl(locals, fn(acc, n) acc.uq-add(n.unqualify)))
  dgs.map(fn(dg) full-localized({uniquefyDG(dg)}))

fun dg/uniquefyDG(dg: def-group)
  match dg
    DefNonRec(d) -> DefNonRec(d(defExpr=d.defExpr.uniquefyx))
    DefRec(ds) -> DefRec(ds.map(fn(d) d(defExpr=d.defExpr.uniquefyx)))

pub fun dg/uniquefy(dg: def-group): _ def-group
  with start/run-unique(0)
  match dg
    DefNonRec(d) -> DefNonRec(d.uniquefy)
    DefRec(defs) ->
      val locals = get-locals()
      set-locals(defs.map(def-name).filter(!_.is-nil).foldl(locals, uq-add))
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
      match renaming.uq-ren-lookup(tname.get-name)
        Just(nm) -> Var(TName(nm, tname.type-of), info)
        Nothing -> e
    App(f, args) -> App(f.uniquefyx, args.map(uniquefyx))
    TypeLam(tvs, expr) -> TypeLam(tvs, expr.uniquefyx)
    TypeApp(expr, tps) -> TypeApp(expr.uniquefyx, tps)
    Con -> e
    ELit -> e
    Let(def-groups, expr) -> Let(def-groups.map(innerdefgroup/uniquefy), expr.uniquefyx)
    Case(exprs, branches) ->
      Case(exprs.map(uniquefyx), localized({branches.map(fn(b) localized({b.uniquefy(exprs.map(type-of))}))}))

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
    if full || locals.uq-member(n) then
      val renaming = get-renaming()
      val name1 = if full then n.unique-name-from else find-unique-name(0, n, locals)
      set-locals(locals.uq-add(name1))
      // `add` is add-if-absent and leaves a stale OUTER rename in
      // place when a nested binder shares the same name (e.g. two synthesized
      // `@action` handler params)
      set-renaming(renaming.uq-ren-set(n, name1))
      name1
    else 
      set-locals(locals.uq-add(n))
      n

fun find-unique-name(i: int, n: name, locals: locals): _ name
  val name1 = to-unique-name(i, n)
  if locals.uq-member(name1) then find-unique-name(i+1, n, locals)
  else name1
