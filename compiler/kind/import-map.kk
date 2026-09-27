// Ported as of 2026-01-18; approx upstream baseline commit c9c313f of Kind/ImportMap.hs (backfilled 2026-07-23)
module compiler/kind/import-map

import compiler/common/name
import std/core/undiv

// Maps short module aliases `core` to full module paths `std/core`.
// Upstream: `type ImportMap = [([String],Name)]` -- a plain association LIST
// from the REVERSED alias path to the full module name, NEWEST FIRST (extend
// prepends). The order is observable: it is the order of `list` and of the
// ambiguity candidates `resolve-path` reports.
pub alias import-map = list<(list<string>, name)>

pub val imports-empty: import-map = []

fun is-prefix(x: list<string>, y: list<string>): bool
  match (x, y)
    (Cons(x1, xs), Cons(y1, ys)) -> x1 == y1 && is-prefix(xs.pretend-decreasing, ys)
    (Nil, _) -> True
    _ -> False

pub fun extend(imp: import-map, alias-name: name, fullName: name): maybe<import-map>
  val rpath = alias-name.split-module-name.reverse
  match imp.lookup(fn(ralias) ralias == rpath)
    Just(fullName1) -> if fullName1 == fullName then Just(imp) else Nothing
    Nothing -> Just(Cons((rpath, fullName), imp))

// Given a fully qualified name, return the shorter aliased name.
// import f = system/foo => system/foo/bar -> f/bar
pub fun get-alias(imp: import-map, nm: name)
  val mname = nm.qualifier
  match imp.filter(fn((_, fullname)) mname == fullname)
    [(ralias, _)] ->
      val alias0 = ralias.reverse.unsplit-module-name
      qualify(alias0, nm.unqualify)
    _ -> nm

pub fun list(imp: import-map): list<(name, name)>
  imp.map(fn(x) (x.fst.reverse.unsplit-module-name, x.snd))

// expand name map@ takes a qualified name (@core/int@) and expands
// it to its real fully qualified name (@std/core/int@). It also returns
// the declared alias suffix (used to find case-errors). 
// On ambiguity, or if not found at all, it returns Left with a list of candidates.
pub fun expand(imp: import-map, name: name): _ either<list<name>, (name, name)>
  val rpath = name.qualifier.split-module-name.reverse
  imp.resolve-path(name.unqualify, rpath)

pub fun resolve-path(imp: import-map, basename: name, rpath: list<string>): _ either<list<name>, (name, name)>
  if rpath.length == 0 then return Right((basename, nil)) // unqualified
  match imp.filter(fn((ralias, _)) -> rpath.is-prefix(ralias))
    [] -> // No match - assume local qualification (note: rpath cannot be null)
      match rpath
        Cons(q, qs) -> 
          match imp.resolve-path(basename, qs)
            Right((qname, aliased)) -> Right((q.new-module-name.qualify-locally(qname), aliased))
            Left(err) -> Left(err)
    [(ralias, modName)] -> // Unique match
      val qname = qualify(modName, basename)
      val aliased = ralias.take(rpath.length).reverse.unsplit-module-name
      Right((qname, aliased))
    amb -> Left(amb.map(_.fst.reverse.unsplit-module-name))

