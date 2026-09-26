//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 3/15/25: Commits 69fe3ab (NameMap) b8074c2 (NameSet) 3229cca QNameMap

import std/data/linear-map
import std/data/linear-set
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import std/test

alias name-map<a> = linear-map<name, a>;

alias name-set = linear-set<name>;
val names/empty: name-set = LinearSet([])

alias qname-map<a> = linear-map<name,list<(name,a)>>;

pub fun name-map/find(m: name-map<a>, n: name): _ a
  match m.lookup(n)
    Just(x) -> x
    _ -> throw("common/name-map/find: could not find: " ++ n.show)

pub type lookup<a>
  Found(name: (name, a))
  Ambiguous(names: list<name>)
  NotFound

pub fun lookup/(==)(a: lookup<a>, b: lookup<a>, ?(==): (a,a) -> e bool): e bool
  match (a, b)
    (Found(x), Found(y)) -> x.fst == y.fst && x.snd == y.snd
    (Ambiguous(xs), Ambiguous(ys)) -> list/(==)(xs, ys)
    (NotFound, NotFound) -> True
    _ -> False

pub fun lookup/show(a: lookup<a>, ?show: (a) -> e string): e string
  match a
    Found((name, _)) -> "Found(" ++ name.show ++ ")"
    Ambiguous(names) -> "Ambiguous(" ++ names.map(show).list/show ++ ")"
    NotFound -> "NotFound"

pub fun qname-map/single(n: name, a: a): qname-map<a>
  LinearMap([(n.unqualify, [(n, a)])])

pub fun qname-map/from-list(l: list<(name,a)>): _ qname-map<a>
  l.foldl(LinearMap([])) fn(qm, (name, x))
    qm.insert(name, x)

// Lookup a fully qualified name
pub fun qname-map/lookup-qualified(m: qname-map<a>, n: name): maybe<a>
  match m.lookup(n.unqualify)
    Just(xs) -> xs.lookup(_ == n)
    _ -> Nothing

// Lookup a potentially unqualified name within a module context. 
// (The module context is ignored if a qualified name is looked up)
pub fun qname-map/lookup(m: qname-map<a>, c: name, name: name): lookup<a>
  match m.lookup(name.unqualify)
    Just(Cons((qname,x), _)) | !name.is-qualified -> Found((qname, x))
    Just(xs) ->
      val qname = if name.is-qualified then name else c.qualify(name)
      match xs.filter(fn((n, _)) -> n == qname)
        Cons((realname, x), _) -> Found((realname, x))
        _ -> Ambiguous(xs.map(fst))
    _ -> NotFound

pub fun qname-map/insert-with(m: qname-map<a>, c: name, a: list<(name,a)>, combine: (list<(name,a)>, list<(name,a)>) -> e list<(name,a)>): e qname-map<a>
  m.map/update(c, a, combine)

pub fun qname-map/filter-names(m: qname-map<a>, p: (name) -> e bool): e qname-map<a>
  m.map fn(k, xs)
    xs.filter(fn((n, _)) p(n))

pub fun qname-map/insert(m: qname-map<a>, n: name, a: a): _ qname-map<a>
  m.update(n.unqualify, Cons((n, a), Nil)) fn(xs, ys)
    safe-combine("insert", xs, ys)

pub fun qname-map/union(m1: qname-map<a>, m2: qname-map<a>): _ qname-map<a>
  m1.union-with(m2) fn(xs, ys)
    safe-combine("union", xs, ys)

pub fun qname-map/union-left-bias(m1: qname-map<a>, m2: qname-map<a>): _ qname-map<a>
  m1.union-with(m2, list/(++))

pub fun qname-map/unions(ms: list<qname-map<a>>): _ qname-map<a>
  ms.foldl(LinearMap([])) fn(m1, m2)
    m1.qname-map/union(m2)

pub fun qname-map/safe-combine(s: string, xs: list<(name,a)>, ys: list<(name,a)>): _ list<(name,a)>
  if xs.any(fn(x) ys.any(fn(y) y.fst == x.fst)) then
    failure/fail("common/name-collections " ++ s ++ ": overlapping names: " ++ xs.map(fn((x, _)) x).list/show ++ ys.map(fn((y,_)) y).list/show)
  xs ++ ys
