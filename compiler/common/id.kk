//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/24: Commits b8074c2 (IdSet) e914563 (IdMap) b8074c2 (Id)
module compiler/common/id
import std/data/rb-set
import compiler/lib/pprint
import std/data/rb-map
import std/data/int-map
import std/data/int-set
import compiler/common/name-collections

/// Internal identifiers (just 'Int's).

/// Types aliases
/// A list of identifiers
pub alias ids = list<id>
// A map from identifiers to values.
// Patricia tree. Ids are `int`, the tree is keyed by `int64`, so callers convert at the
// boundary -- the `nice` helpers do it internally so their call sites are unchanged.
pub alias id-map<a> = int-map<a>
// A set of identifiers
pub alias id-set = int-set

/// Identifiers are unique compiler generated identities
pub alias id = int;

/// Show quotes around the id
pub fun show-id(id: id): string
  "\"" ++ id.int/show ++ "\""

/// Generate an 'Id' with a certain base name (which is ignored :-)
pub fun gen-id(baseName: string, i: int): id
  i.new-id

/// Create a fresh identifier
pub fun new-id(i: int): id
  i

pub fun new-id-from(id: id): id
  id + 1

/// Dummy identifier
pub val id-nil = 0.new-id

/// Only used internally to guarantee unique identifiers
pub fun id-number(id: id): int
  id
