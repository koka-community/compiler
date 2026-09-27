// Ported as of 2026-01-29; approx upstream baseline commit c2ff6bf of Kind/Constructors.hs (backfilled 2026-07-23)
module compiler/kind/constructors

import compiler/common/name
import std/data/rb-map
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config

pub alias constructors = name-map<con-info>

effect constructors-eff
  fun constrs-extend(name: name, c: con-info): ()
  fun constrs-lookup(name: name): maybe<con-info>
  fun constrs-find(name: name): con-info
  fun constrs-list(): list<(name, con-info)>
  fun constrs-find-scheme(name: name): ktype
  fun constrs-unions(cs: list<constructors>): constructors

fun with-constructors(cnstrs0: constructors, f: () -> _ a): _ a
  var cnstrs := cnstrs0
  with handler
    fun constrs-extend(name: name, k: con-info)
      cnstrs := rb-map/set(cnstrs, name, k)
    fun constrs-lookup(name: name)
      cnstrs.lookup(name)
    fun constrs-find(name: name)
      match cnstrs.lookup(name)
        Just(con-info) -> con-info
        _ -> failure/fail("conInfo lookup failed")
    fun constrs-list()
      cnstrs.list
    fun constrs-find-scheme(name: name)
      rb-map/get(cnstrs, name).typeScheme
    fun constrs-unions(cs: list<constructors>)
      cnstrs := unions(cs.reverse) // Assumes left bias
      cnstrs
  f()

pub fun constructors-from-list(lst: list<con-info>): constructors
  rb-map/empty() + lst.map(fn(ci) (ci.con-info/name, ci))

val contructors/empty: constructors = rb-map/empty()

fun compose(a: constructors, b: constructors): constructors
  a.union(b) // ASSUMES left biased union

fun core/extract-coninfo(c: core): _ constructors
  c.typedefs.map(extract-coninfo).unions

fun tdg/extract-coninfo(g: typedef-group): _ constructors
  g.map(extract-coninfo).unions

fun td/extract-coninfo(d: typedef): _ constructors
  match d
    Data(dataInfo) | dataInfo.vis.is-public -> 
      rb-map/from-list(dataInfo.constrs.filter(_.vis.is-public).list/map(fn(ci) (ci.con-info/name, ci)))
    _ -> empty

// TODO: Pretty print
