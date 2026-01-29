import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linear-map

alias newtypes = name-map<data-info>

effect newtypes-eff
  fun newtypes-extend(name: name, newtp: data-info): ()
  fun newtypes-lookup-any(name: name): maybe<data-info>
  fun newtypes-lookup-public(name: name): maybe<data-info>
  fun newtypes-find(name: name): data-info
  fun newtypes-list(): list<(name, data-info)>

fun withNewtypes(newtps0: newtypes, f: () -> _ a): _ a
  var newtps := newtps0
  with handler
    fun newtypes-extend(name: name, k: data-info) newtps := newtps.set(name, k)
    fun newtypes-lookup-any(name: name) newtps.lookup-any(name)
    fun newtypes-lookup-public(name: name) newtps.lookup-public(name)
    fun newtypes-find(name: name) newtps.newtypes/find(name)
    fun newtypes-list() newtps.list
  f()

fun newtypes/new(lst: list<data-info>): newtypes
  LinearMap(lst.map(fn(di) (di.name, di)))
fun newtypes/extend(newtps: newtypes, name: name, k: data-info)
  newtps.set(name, k)
fun newtypes/lookup-any(newtps: newtypes, name: name)
  newtps.lookup(name)
fun newtypes/lookup-public(newtps: newtypes, name: name)
  match newtps.lookup(name)
    Just(di) | di.vis.is-public -> Just(di)
    _ -> Nothing
fun newtypes/find(newtps: newtypes, name: name)
  match newtps.lookup(name)
    Just(di) -> di
    _ -> failure/fail("newTypes lookup failed")
fun newtypes/compose(ntps1: newtypes, ntps2: newtypes)
  unions([ntps2, ntps1])

fun single(name: name, d: data-info): newtypes
  LinearMap([(name, d)])
val newtypes/empty:newtypes = LinearMap([])

fun core/extract-newtypes(c: core): _ newtypes
  c.typedefs.map(extract-newtypes).unions

fun tdg/extract-newtypes(g: typedef-group): _ newtypes
  g.map(extract-newtypes).unions

fun td/extract-newtypes(d: typedef): _ newtypes
  match d
    Data(dataInfo) -> single(dataInfo.name, dataInfo)
    _ -> newtypes/empty

// TODO: Pretty print