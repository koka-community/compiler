// Ported as of 2026-01-29; approx upstream baseline commit b8074c2 of Core/BindingGroups.hs (backfilled 2026-07-23)
module compiler/core/binding-groups

import compiler/lib/scc
import compiler/core/core
import compiler/core/corevar
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import std/data/rb-set
import std/data/sort
import std/data/rb-map
import compiler/common/name-collections

// Re-analyze a recursive binding group just after type checking.
// Due to overloading, functions that seem mutually recursive may not
// actually be mutually recursive after the types are resolved.
alias deps = rbmap<tName, rbset<tName>>
alias freeVar = rbset<tName>

// Re-analyze a recursive binding group and return a list of new
// definition groups. After type checking it is possible that definitions
// that seemed recursive are actually not mutually recursive.

pub fun regroup(dfs: list<def>): _ list<def-group>
  match dfs
    Cons(d, Nil) ->
      val fvdef = d.free-vars
      //  this is for recursive definitions where the type may still differ since we cannot improve too early for mutual recursive definitions (or we unify too eagerly, see "while")
      if fvdef.member(TName(d.def-name, d.ktype)) || 
        fvdef.list.map(get-name).filter(!_.is-qualified).any(_ == d.def-name) then
        [DefRec([d])]
      else
        [DefNonRec(d)]
    defs ->
      val def-names = defs.map(fn(d) TName(d.def-name, d.ktype))
      val defMap = rb-map/from-list(def-names.zip(defs))
      // The elements come
      // from the FIRST set, i.e. the definitions' own TNames
      val deps = rb-map/from-list(def-names.zip(defs.map(fn(d) rb-set/from-list(def-names).intersection(d.free-vars))))
      // determine strongly connected components
      val defOrder = deps.list.map(fn((nm, fvs)) (nm, fvs.list)).scc
      // create a definition group
      fun makeGroup(names)
        match names
          [nm] -> 
            if deps.get(nm).member(nm) then DefRec([defMap.get(nm)])
            else DefNonRec(defMap.get(nm))
          _ -> DefRec(names.map(defMap.get(_)))
      defOrder.map(makeGroup)

fun find(nameMap: list<(tName, b)>, nm: tName): _ b
  match find(nameMap, fn(n: (tName,b)) n.fst == nm)
    Just(x) -> x.snd
    _ -> failure/fail("core/binding-groups find: could not find: " ++ nm.show)


