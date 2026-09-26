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
import std/data/rb-map
import std/data/int-map
import std/num/int64
import compiler/common/name-collections

// Map identifiers to /nice/ strings.
pub alias nice = id-map<string>

pub effect nice-eff<k>
  fun extend-nice(tv: k): ()
  fun get-nice(tv: k): string
  fun get-nice-doc(tv: k): doc
  // upstream's nice env is a FUNCTIONAL field of the pretty Env: extensions
  // made while printing a `forall` body are discarded when that scope is left
  // (sibling foralls re-use the same nice names, see test/type/hr1). The
  // mutable handler needs explicit scoping: push saves the full nice state,
  // pop restores it.
  fun nice-push(): ()
  fun nice-pop(): ()

// Run `f` with the current nice state, restoring it afterwards (the analog
// of upstream passing a locally-extended env down and continuing with the
// original).
pub fun nice-scoped(f: () -> <nice-eff<k>|e> a): <nice-eff<k>|e> a
  nice-push()
  // restore via `finally`: error-reporting scopes exit through an ABORTING
  // op (`add-errors` is a final ctl) and a plain trailing nice-pop() would be
  // skipped, leaking this scope's assignments into every later message
  with finally(nice-pop)
  f()

// Naming sequences follow upstream Type/Pretty.hs exactly:
//   regular type vars: a,b,c,d, a1,b1,c1,d1, a2,...  (letters a..d ONLY --
//     upstream deliberately stops at 'd' so a fifth type variable becomes
//     `a1` and can never collide with the effect-var namespace `e`)
//   effect vars: e, e1, e2, ...  (the FIRST one is unnumbered)
//   heap vars:   h, h1, ...      scope vars: s, s1, ...
// and upstream niceExtend (Common/IdNice.hs) inserts with keep-old
// (`insertWith (\new old -> old)`): re-extending an already-named variable
// neither renames it nor consumes a fresh name.
pub fun nice-env(f)
  var nice := int-map/empty()
  var effectIndex := 0
  var heapIndex := 0
  var typeVarIndex := 0
  var scopeIndex := 0
  var saved := []
  with handler
    fun extend-nice(tv: type-var)
      if nice.lookup(tv.tid.int64).is-just then () // keep-old
      else
        val x =
          if tv.kind == kindEffect then
            val i = effectIndex
            effectIndex := i + 1
            "e" ++ (if i == 0 then "" else i.show)
          elif tv.kind == kindHeap then
            val i = heapIndex
            heapIndex := i + 1
            "h" ++ (if i == 0 then "" else i.show)
          elif tv.kind == kindScope then
            val i = scopeIndex
            scopeIndex := i + 1
            "s" ++ (if i == 0 then "" else i.show)
          else
            val i = typeVarIndex
            typeVarIndex := i + 1
            val suffix = i / 4
            ('a'.int + (i % 4)).char.string ++ (if suffix == 0 then "" else suffix.show)
        nice := nice.extend(tv.tid, x)
        ()
    fun get-nice(tv: type-var)
      nice.show(tv.tid)
    fun get-nice-doc(tv: type-var)
      nice.pretty(tv.tid)
    fun nice-push()
      saved := Cons((nice, effectIndex, heapIndex, typeVarIndex, scopeIndex), saved)
    fun nice-pop()
      match saved
        Cons((n, e, h, t, s), rest) ->
          nice := n
          effectIndex := e
          heapIndex := h
          typeVarIndex := t
          scopeIndex := s
          saved := rest
        Nil -> ()
  f()

// Add fresh identifier substitutions give an (infinite) list of nice names.
pub fun extend(n: nice, id: int, name: string): nice
  n.set(id.int64, name)

// Show the nice version of an identifier
pub fun show(n: nice, id: id): string
  match n.lookup(id.int64)
    Just(name) -> name
    // upstream IdNice falls back to plain `show id` (Id = Int) -- NOT the
    // quoted `showId` form; an un-nice'd meta shows as `_10`, not `_"10"`
    Nothing -> id.int/show

// Pretty print an identifier nicely.
pub fun pretty(n: nice, id: id): doc
  n.show(id).text