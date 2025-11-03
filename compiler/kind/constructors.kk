import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap

alias constructors = name-map<conInfo>

effect constructorsEff
  fun constrs-extend(name: name, c: conInfo): ()
  fun constrs-lookup(name: name): maybe<conInfo>
  fun constrs-find(name: name): conInfo
  fun constrs-list(): list<(name, conInfo)>
  fun constrs-find-scheme(name: name): ktype
  fun constrs-unions(cs: list<constructors>): constructors

fun withConstructors(cnstrs0: constructors, f: () -> <constructorsEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var cnstrs := cnstrs0
  with handler
    fun constrs-extend(name: name, k: conInfo)
      cnstrs := cnstrs.set(name, k)
    fun constrs-lookup(name: name)
      cnstrs.lookup(name)
    fun constrs-find(name: name)
      match cnstrs.lookup(name)
        Just(conInfo) -> conInfo
        _ -> fail("conInfo lookup failed")
    fun constrs-list()
      cnstrs.list
    fun constrs-find-scheme(name: name)
      cnstrs.map/get(name).typeScheme
    fun constrs-unions(cs: list<constructors>)
      cnstrs := unions(cs.reverse) // Assumes left bias
      cnstrs
  f()

fun constructors-from-list(lst: list<conInfo>): constructors
  LinearMap([]) + lst.map(fn(ci) (ci.conInfo/name, ci))

val contructors/empty: constructors = LinearMap([])

fun compose(a: constructors, b: constructors): constructors
  a.union(b) // ASSUMES left biased union

fun core/extract-coninfo(c: core): <pure,comp-flags> constructors
  c.typeDefs.map(extract-coninfo).unions

fun tdg/extract-coninfo(g: typeDefGroup): <pure,comp-flags> constructors
  g.map(extract-coninfo).unions

fun td/extract-coninfo(d: typeDef): <pure,comp-flags> constructors
  match d
    Data(dataInfo) | dataInfo.vis.is-public -> 
      LinearMap(dataInfo.constrs.filter(_.vis.is-public).list/map(fn(ci) (ci.conInfo/name, ci)))
    _ -> empty

// TODO: Pretty print