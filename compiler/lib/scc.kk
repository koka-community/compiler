//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/23/24: Commit b8074c2
//
// Upstream `Lib/Scc.hs`. Its `Ord v` constraint is the `?cmp` the
// key-ordered containers take: `Graph v = Map.Map v [v]` is an `rbmap`,
// and the visited sets are `rbset`s. Their iteration order is OBSERVABLE -- it
// decides component emission order and the member order inside a component --
// and it follows whatever order a caller builds its input in.

module compiler/lib/scc

import std/data/rb-map
import std/data/rb-set
pub import compiler/common/name-collections
import std/core/undiv
import std/core/unsafe

alias graph<v> = rbmap<v, list<v>>;
alias edge<v> = (v,v)
pub alias node<v> = (v,list<v>)

fun nodes(g: graph<v>): list<node<v>>
  g.list

// A repeated node's successors combine NEW ++ OLD
fun graph(es: list<node<v>>, ?cmp: (v,v) -> order): graph<v>
  es.foldl(rb-map/empty()) fn(m, (v, ws))
    m.update(v, ws, fn(old, nw) nw ++ old)

fun edges(g: graph<v>): list<edge<v>>
  with v <- g.nodes.flatmap
  with w <- v.snd.map
  (v.fst, w)

fun vertices(g: graph<v>): list<v>
  g.nodes.map(fst)

fun successors(g: graph<v>, v: v, ?cmp: (v,v) -> order): list<v>
  g.get-default(v, [])

// upstream: `foldr add (Map.map (const []) m) (edges g)` with
// `add (v,w) m = Map.adjust (v:) w m` -- ADJUST, so an edge whose target is
// not a vertex adds nothing (inserting it would invent a vertex)
fun transpose(g: graph<v>, ?cmp: (v,v) -> order): graph<v>
  g.edges.foldr(g.value/map(fn(_) [])) fn((v, w), m)
    match m.lookup(w)
      Just(vs) -> m.set(w, Cons(v, vs))
      Nothing -> m

div type tree<v>
  Tree
    head: v
    fs: forest<v>

div type forest<v>
  Forest
    list: list<tree<v>>

fun dff(g: graph<v>, ?cmp: (v,v) -> order): forest<v>
  g.dfs(g.vertices)

// upstream `dfs g vs = prune (map (tree g) vs)` over LAZY trees. Strictly that
// is the King-Launchbury dfs: ONE visited set threaded across all roots (a
// per-root visited set + prune let a later root's tree re-traverse and swallow
// nodes of an earlier component, corrupting scc membership/order)
pub fun dfs(g: graph<v>, vs: list<v>, ?cmp: (v,v) -> order): forest<v>
  with unsafe-total
  val visited = ref(rb-set/empty())
  val ts = vs.flatmap fn(v)
    if (!visited).member(v) then []
    else
      visited.set((!visited) + v)
      [g.tree(v, visited)]
  Forest(ts)

fun tree(g: graph<v>, v: v, visited: ref<h, rbset<v>>, ?cmp: (v,v) -> order): <div,read<h>,write<h>> tree<v>
  val f = g.successors(v).flatmap fn(v')
    if (!visited).member(v') then []
    else
      visited.set((!visited) + v')
      [g.tree(v'.pretend-decreasing, visited)]
  Tree(v, Forest(f))

alias vset<v> = rbset<v>;

pub fun prune(fs: forest<v>, ?cmp: (v,v) -> order): forest<v>
  fun chop(ms: vset<v>, fs1: forest<v>, ?cmp: (v,v) -> order): (vset<v>, forest<v>)
    match fs1.list
      [] -> (ms, Forest([]))
      Cons(Tree(v, vs), fs2) ->
        if ms.member(v) then chop(ms.pretend-decreasing, Forest(fs2))
        else
          val ms0 = ms + v
          val (ms1, vs') = chop(ms0.pretend-decreasing, vs.pretend-decreasing)
          val (ms2, fs2') = chop(ms1.pretend-decreasing, Forest(fs2).pretend-decreasing)
          (ms2, Forest(Cons(Tree(v, vs'), fs2'.list)))
  rb-set/empty().chop(fs).snd

fun preorder(g: graph<v>, ?cmp: (v,v) -> order): list<v>
  with unsafe-total
  g.dff.preorderF

fun preorderF(f: forest<v>): div list<v>
  f.list.flatmap(preorderT)

fun preorderT(t: tree<v>): div list<v>
  Cons(t.head, t.fs.preorderF)

fun postorder(g: graph<v>, ?cmp: (v,v) -> order): list<v>
  g.dff.postorderF

pub fun postorderF(f: forest<v>): list<v>
  with unsafe-total
  postorderF'(f.list, [])

fun postorderT'(t: tree<v>, vs: list<v>): div list<v>
  postorderF'(t.fs.list, Cons(t.head, vs))

fun postorderF'(ts: list<tree<v>>, vs: list<v>): div list<v>
  match ts
    [] -> vs
    Cons(t, ts') -> postorderT'(t, postorderF'(ts', vs))

pub fun scc(nodes: list<node<v>>, ?cmp: (v,v) -> order): div list<list<v>>
  sccG(nodes.graph)

fun sccG(g: graph<v>, ?cmp: (v,v) -> order): list<list<v>>
  with unsafe-total
  g.sccF.map(preorderT)

fun sccF(g: graph<v>, ?cmp: (v,v) -> order): list<tree<v>>
  g.transpose.dfs(g.topsort).list.reverse

fun topsort(g: graph<v>, ?cmp: (v,v) -> order): list<v>
  g.postorder.reverse

fun reachable(g: graph<v>, v: v, ?cmp: (v,v) -> order): list<v>
  with unsafe-total
  g.dfs([v]).preorderF

fun path(g: graph<v>, v: v, w: v, ?cmp: (v,v) -> order): bool
  g.reachable(v).find(fn(x) cmp(x, w).is-eq).is-just
