import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap

alias synonyms = name-map<syn-info>
effect synonyms-eff
  fun synonyms-extend(newtp: syn-info): ()
  fun synonyms-lookup(name: name): maybe<syn-info>
  fun synonyms-find(name: name): syn-info
  fun synonyms-list(): list<(name, syn-info)>
  fun synonyms-filter(modName: name): synonyms
  fun get-synonyms(): synonyms
  fun set-synonyms(syns: synonyms): ()

fun with-synonyms(synonyms0: synonyms, f: () -> _ a): _ a
  var synonyms := synonyms0
  with handler
    fun get-synonyms() synonyms
    fun set-synonyms(syns: synonyms) synonyms := syns
    fun synonyms-extend(k: syn-info)
      synonyms := synonyms.extend(k)
    fun synonyms-lookup(name: name)
      synonyms.lookup(name)
    fun synonyms-find(name: name)
      synonyms.synonyms/find(name)
    fun synonyms-list()
      synonyms.list
    fun synonyms-filter(modName: name)
      synonyms.filter(fn(k, v) (k.qualifier) == modName)
      // TODO: Should this modify the synonyms?
  f()

fun new(ls: list<syn-info>)
  LinearMap(ls.map(fn(si) (si.name, si)))
fun extend(synonyms: synonyms, k: syn-info)
  synonyms.set(k.name, k)
// fun lookup(synonyms: synonyms, name: name)
//   synonyms.map/lookup(name)
fun find(synonyms: synonyms, name: name)
  match synonyms.lookup(name)
    Just(di) -> di
    _ -> fail("synonyms lookup failed")
fun diff(synonyms: synonyms, syns1: synonyms, syns2: synonyms)
  syns2.filter(fn(k, v) syns1.lookup(k).is-nothing)
fun synonyms/filter(synonyms: synonyms, modName: name)
  synonyms.filter(fn(k, v) (k.qualifier) == modName)

fun compose(syns1: synonyms, syns2: synonyms)
  unions([syns2, syns1])

fun single(name: name, s: syn-info): synonyms
  LinearMap([(name, s)])
val empty:synonyms = LinearMap([])

fun core/extract-synonyms(c: core): _ synonyms
  c.typedefs.map(extract-synonyms).unions

fun tdg/extract-synonyms(g: typedef-group): _ synonyms
  g.map(extract-synonyms).unions

fun td/extract-synonyms(d: typedef): _ synonyms
  match d
    Synonym(syn-info) -> single(syn-info.name, syn-info)
    _ -> empty

// TODO: Pretty print