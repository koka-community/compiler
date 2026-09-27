// Ported as of 2026-01-18; approx upstream baseline commit 486ef0d of Core/Borrowed.hs (backfilled 2026-07-23)
module compiler/core/borrowed

import compiler/common/name
import std/data/rb-map
import compiler/core/core
import compiler/common/failure
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-collections
import compiler/common/range

// Map names to their borrowing info. If a name does not use borrowing
// it may not be in here.
pub alias borrowed = name-map<list<param-info>>

alias borrowDef = (name, list<param-info>)

// The initial borrowed
val empty:borrowed = rb-map/empty()

fun new(xs: list<borrowDef>): borrowed
  borrowed/empty.extend(xs)

fun list/extend(b: borrowed, xs: list<borrowDef>): borrowed
  xs.foldl(b, extend)

pub fun extend(b: borrowed, b1: borrowDef): borrowed
  rb-map/set(b, b1.fst, b1.snd) // upstream M.insert overwrites (linear-map add is add-if-absent)

pub fun core/extend(c: core, b0: borrowed): borrowed
  b0.extend(c.defs.extract-borrow).extend(c.externals.extract-borrow)

// Get borrow information from core
fun dgs/extract-borrow(dgs: def-groups)
  dgs.map(extract-borrow).concat

fun externs/extract-borrow(exs: externals)
  exs.map(extract-borrow).concat-maybe

fun ext/extract-borrow(ex: external)
  match ex
    External(nm, _, params) ->
      if params.any(_ == Borrow) then Just((nm, params)) else Nothing
    _ -> Nothing

fun dg/extract-borrow(dg: def-group)
  match dg
    DefRec(defs) -> defs.map(_.extract-borrow(True)).concat-maybe
    DefNonRec(d) -> d.extract-borrow(False).map(fn(d') [d']).default([])

fun def/extract-borrow(d: def, rec: bool)
  match d.sort
    DefFun(pinfos) | !pinfos.is-nil -> Just((d.def-name, pinfos))
    _ -> Nothing
    

