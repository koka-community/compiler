// Ported as of 2026-01-29; approx upstream baseline commit c2ff6bf of Kind/Newtypes.hs (backfilled 2026-07-23)
module compiler/kind/newtypes

import compiler/common/name
import std/data/rb-map
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config

pub alias newtypes = name-map<data-info>

pub effect newtypes-eff
  fun newtypes-extend(name: name, newtp: data-info): ()
  fun newtypes-lookup-any(name: name): maybe<data-info>
  fun newtypes-lookup-public(name: name): maybe<data-info>
  fun newtypes-find(name: name): data-info
  fun newtypes-list(): list<(name, data-info)>

pub fun withNewtypes(newtps0: newtypes, f: () -> _ a): _ a
  var newtps := newtps0
  with handler
    fun newtypes-extend(name: name, k: data-info) newtps := rb-map/set(newtps, name, k)
    fun newtypes-lookup-any(name: name) newtps.lookup-any(name)
    fun newtypes-lookup-public(name: name) newtps.lookup-public(name)
    fun newtypes-find(name: name) newtps.newtypes/find(name)
    fun newtypes-list() newtps.list
  f()

pub fun newtypes/new(lst: list<data-info>): newtypes
  rb-map/from-list(lst.map(fn(di) (di.name, di)))
pub fun newtypes/extend(newtps: newtypes, name: name, k: data-info)
  rb-map/set(newtps, name, k)
pub fun newtypes/lookup-any(newtps: newtypes, name: name)
  newtps.lookup(name)
fun newtypes/lookup-public(newtps: newtypes, name: name)
  match newtps.lookup(name)
    Just(di) | di.vis.is-public -> Just(di)
    _ -> Nothing
fun newtypes/find(newtps: newtypes, name: name)
  match newtps.lookup(name)
    Just(di) -> di
    _ -> failure/fail("newTypes lookup failed")
pub fun newtypes/compose(ntps1: newtypes, ntps2: newtypes)
  rb-map/unions([ntps2, ntps1])

fun single(name: name, d: data-info): newtypes
  rb-map/from-list([(name, d)])
pub val newtypes/empty:newtypes = rb-map/empty()

pub fun core/extract-newtypes(c: core): _ newtypes
  rb-map/unions(c.typedefs.map(extract-newtypes))

fun tdg/extract-newtypes(g: typedef-group): _ newtypes
  rb-map/unions(g.map(extract-newtypes))

fun td/extract-newtypes(d: typedef): _ newtypes
  match d
    Data(dataInfo) -> single(dataInfo.name, dataInfo)
    _ -> newtypes/empty

// TODO: Pretty print
