//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 3/15/25: Commits 69fe3ab (NameMap) b8074c2 (NameSet) 3229cca QNameMap

module compiler/common/name-collections

import std/data/rb-map
import std/data/rb-set
import std/data/rbtree
import std/data/rbtree-bu
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import std/test

// name-map is a BOTTOM-UP red-black tree
//
// Upstream's gamma is `Data.Map.Strict Name [(Name,NameInfo)]` -- a balanced
// tree ordered by `Ord Name`. 
//
// Bottom-up (not top-down) because that is where the PLDI'24 artifact's
// `fbip(1)` coverage is: `bu/set`, `bu/add`, `bu/insert` and the balance
// helpers are all verified fully-in-place, so they reuse nodes rather than
// reallocating the spine. Top-down has one such function.
//
// Iteration order becomes key order.
pub alias name-map<a> = rbmap<name, a>;

// Every map operation (`update`, `union-with`, `unions-with`, ...) lives in
// `std/data/rb-map` itself, with `linear-map`'s names and semantics.

// Key-ordered, as rb-set iterates
pub alias name-set = rbset<name>;
pub val names/empty: name-set = rb-set/empty()

// qname-map is name-keyed too, so it rides the same tree
pub alias qname-map<a> = name-map<list<(name,a)>>;

pub fun name-map/find(m: name-map<a>, n: name): _ a
  match rb-map/lookup(m, n)
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
  rb-map/from-list([(n.unqualify, [(n, a)])])

pub fun qname-map/from-list(l: list<(name,a)>): _ qname-map<a>
  l.foldl(rb-map/empty()) fn(qm, (name, x))
    qm.qname-map/insert(name, x)

// Lookup a fully qualified name
pub fun qname-map/lookup-qualified(m: qname-map<a>, n: name): maybe<a>
  match rb-map/lookup(m, n.unqualify)
    Just(xs) -> xs.lookup(_ == n)
    _ -> Nothing

// Lookup a potentially unqualified name within a module context. 
// (The module context is ignored if a qualified name is looked up)
pub fun qname-map/lookup(m: qname-map<a>, c: name, name: name): lookup<a>
  match rb-map/lookup(m, name.unqualify)
    // fast path ONLY for a singleton entry: with
    // several entries we must fall through to the context-qualified filter so
    // the current module's definition takes precedence over imported ones
    Just([(qname, x)]) | !name.is-qualified -> Found((qname, x))
    Just(xs) ->
      val qname = if name.is-qualified then name else c.qualify(name)
      // upstream takes the context-qualified filter to be a SINGLETON:
      //   case filter (\p -> fst p == qname) xs of
      //     [(realname,x)] -> Found realname x
      //     _              -> Ambiguous (map fst xs)
      // matching `Cons(_, _)` here would accept the first of several equally
      // qualified candidates where upstream reports them as ambiguous
      match xs.filter(fn((n, _)) -> n == qname)
        Cons((realname, x), Nil) -> Found((realname, x))
        _ -> Ambiguous(xs.map(fst))
    _ -> NotFound

pub fun qname-map/insert-with(m: qname-map<a>, c: name, a: list<(name,a)>, combine: (list<(name,a)>, list<(name,a)>) -> e list<(name,a)>): e qname-map<a>
  rb-map/update(m, c, a, combine)

pub fun qname-map/filter-names(m: qname-map<a>, p: (name) -> e bool): e qname-map<a>
  rb-map/kvalue/map(m) fn(k, xs)
    xs.filter(fn((n, _)) p(n))

pub fun qname-map/insert(m: qname-map<a>, n: name, a: a): _ qname-map<a>
  // calls safeCombine(new, old) — flip so the new entry comes first
  rb-map/update(m, n.unqualify, Cons((n, a), Nil)) fn(xs, ys)
    safe-combine("insert", ys, xs)

pub fun qname-map/union(m1: qname-map<a>, m2: qname-map<a>): _ qname-map<a>
  rb-map/union-with(m1, m2) fn(xs, ys)
    safe-combine("union", xs, ys)

pub fun qname-map/union-left-bias(m1: qname-map<a>, m2: qname-map<a>): _ qname-map<a>
  rb-map/union-with(m1, m2, list/(++))

pub fun qname-map/unions(ms: list<qname-map<a>>): _ qname-map<a>
  ms.foldl(rb-map/empty()) fn(m1, m2)
    m1.qname-map/union(m2)

pub fun qname-map/safe-combine(s: string, xs: list<(name,a)>, ys: list<(name,a)>): _ list<(name,a)>
  if xs.any(fn(x) ys.any(fn(y) y.fst == x.fst)) then
    failure/fail("common/name-collections " ++ s ++ ": overlapping names: " ++ xs.map(fn((x, _)) x).list/show ++ ys.map(fn((y,_)) y).list/show)
  xs ++ ys
