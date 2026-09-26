// Ported as of 2026-01-18; approx upstream baseline commit 909c268 of Core/Inlines.hs (backfilled 2026-07-23)
module compiler/core/inlines

import compiler/core/core
import std/data/rb-map
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections

pub alias inlines = name-map<inline-def>

val empty:inlines = rb-map/empty()

pub fun inlines(xs: list<inline-def>)
  empty.extends(xs)

// `foldr` applies the LAST list element's extend first (outermost),
// so the FIRST entry in `xs` ends up applied last and wins
pub fun extends(inls: inlines, xs: list<inline-def>)
  xs.foldr(inls, fn(inl, acc) acc.extend(inl))

pub fun extend(inls: inlines, inl: inline-def)
  rb-map/set(inls, inl.def-name, inl) // upstream M.insert: the new definition overwrites

pub fun merge(inls1: inlines, inls2: inlines)
  inls1.union(inls2)

// keep only inline defs whose name satisfies `p`
pub fun inlines-filter(inls: inlines, p: (name) -> e bool): e inlines
  rb-map/from-list(inls.entries.filter(fn((k, _)) p(k)))

pub fun defs/extract-inlines(dgs: def-groups, costMax: int)
  dgs.map(_.extract-inlines(costMax)).concat

pub fun dg/extract-inlines(dg: def-group, costMax: int)
  match dg
    DefRec() -> []
    DefNonRec(d) -> d.extract-inlines(costMax, False).map(fn(d') [d']).default([])

pub fun def/extract-inlines(d: def, costMax: int, isRec: bool)
  val inlineable = d.is-inlineable(costMax)
  if !inlineable then Nothing
  else
    val cost = (if d.def-name == nameBind || d.def-name == nameBind2 then 0 else d.cost)
    Just(InlineDef(d.def-name, d.defExpr, isRec, d.kinline, cost, d.sort, []))
