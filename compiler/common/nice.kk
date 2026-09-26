//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/24: Commit b8074c2

module compiler/common/nice

import compiler/common/id
import compiler/type/type
import compiler/lib/pprint
import compiler/kind/kind
import compiler/common/syntax
import std/data/linear-map

// Map identifiers to /nice/ strings.
pub alias nice = id-map<string>

pub effect nice-eff<k>
  fun extend-nice(tv: k): ()
  fun get-nice(tv: k): string
  fun get-nice-doc(tv: k): doc

pub fun nice-env(f)
  var nice := LinearMap([])
  var effectIndex := 0
  var heapIndex := 0
  var typeIndex := 0
  var typeLetterIndex := 0
  var scopeIndex := 0
  with handler
    fun extend-nice(tv: type-var)
        val x =
          if tv.kind == kindEffect then
          effectIndex := effectIndex + 1
          "e" ++ (if effectIndex == 0 then "" else effectIndex.show)
          elif tv.kind == kindHeap then
          heapIndex := heapIndex + 1
          "h" ++ (if heapIndex == 0 then "" else heapIndex.show)
          elif tv.kind == kindScope then
          scopeIndex := scopeIndex + 1
          "s" ++ (if scopeIndex == 0 then "" else scopeIndex.show)
          else
          val s = (typeLetterIndex + 'a'.int).char.string ++ (if typeIndex == 0 then "" else typeIndex.show)
          match typeLetterIndex
            4 -> 
              typeIndex := typeIndex + 1
              typeLetterIndex := 0
            _ ->
              typeLetterIndex := typeLetterIndex + 1
          s
        nice := nice.extend(tv.tid, x)
        ()
    fun get-nice(tv: type-var)
      nice.show(tv.tid)
    fun get-nice-doc(tv: type-var)
      nice.pretty(tv.tid)
  f()

// Add fresh identifier substitutions give an (infinite) list of nice names.
pub fun extend(n: nice, id: int, name: string): nice
  n.set(id, name)

// Show the nice version of an identifier
pub fun show(n: nice, id: id): string
  match n.lookup(id)
    Just(name) -> name
    Nothing -> id.show-id

// Pretty print an identifier nicely.
pub fun pretty(n: nice, id: id): doc
  n.show(id).text