// Differential test for the divergence-analysis pruning in core/divergent.kk.
//
// `is-divergent-fun` searches ORDERINGS of a recursive function's parameters,
// so it is factorial in the arity. The port prunes parameters that never
// decrease, which is exact ONLY when every recursive call supplies the same
// number of arguments. This enumerates small call matrices, ragged ones
// included, and compares each candidate against the unpruned upstream shape.
//
// Run:  ./koka -O2 --include=scripts -e scripts/divergent-prune-test.kk
//
// Expected: safeprune-diffs=0 (what the compiler implements). The other two
// counters are deliberately nonzero -- they are why the uniform guard exists:
//   select-diffs   -- selecting indices per call instead of transposing back
//                     disagrees with upstream on ragged rows
//   colprune-diffs -- pruning columns unconditionally does too

import std/core/undiv

type size
  SLt
  SEq
  Unknown

fun (==)(s1: size, s2: size): bool
  match (s1, s2)
    (SLt, SLt) -> True
    (SEq, SEq) -> True
    (Unknown, Unknown) -> True
    _ -> False

alias call = list<size>

fun transpose(xss: list<list<a>>): div list<list<a>>
  match xss
    Nil -> Nil
    Cons(Nil, xss') -> transpose(xss')
    Cons(Cons(x, xs), xss') ->
      val hds = xss'.flatmap(fn(row) match row { Cons(hd, _) -> [hd]; Nil -> [] })
      val tls = xss'.flatmap(fn(row) match row { Cons(_, tl) -> [tl]; Nil -> [] })
      Cons(Cons(x, hds), transpose(Cons(xs, tls)))

// Naive all-permutations reference. `any` over the set is order-independent,
// so this is interchangeable with Data.List.permutations for this test.
fun without(xs: list<a>, i: int): list<a>
  xs.map-indexed(fn(j, y) (j, y)).filter-map(fn((j, y)) if j == i then Nothing else Just(y))

fun permutations(xs: list<a>): div list<list<a>>
  match xs
    Nil -> [[]]
    _ -> xs.map-indexed(fn(i, x) permutations(xs.without(i)).map(fn(p) Cons(x, p))).concat

fun isAnOrder(cs: list<call>): bool
  cs.all(fn(c) match c.drop-while(fn(sz) sz == SEq) { Cons(SLt, _) -> True; _ -> False })

fun orig(calls: list<call>): div bool
  !calls.transpose.permutations.map(transpose).any(isAnOrder)

fun perm-search(rest: list<a>, acc: list<a>, pred: (list<a>) -> <div|e> bool): <div|e> bool
  match rest
    Nil -> pred(acc.reverse)
    _   -> perm-pick(Nil, rest, acc, pred)
fun perm-pick(left: list<a>, right: list<a>, acc: list<a>, pred: (list<a>) -> <div|e> bool): <div|e> bool
  match right
    Nil -> False
    Cons(x, rest) ->
      if perm-search(left.reverse ++ rest, Cons(x, acc), pred) then True
      else perm-pick(Cons(x, left), rest, acc, pred)
fun any-permutation(xs: list<a>, pred: (list<a>) -> <div|e> bool): <div|e> bool
  perm-search(xs, Nil, pred)

fun show(s: size): string
  match s
    SLt -> "Lt"
    SEq -> "Eq"
    Unknown -> "??"

fun showcall(c: call): string
  "[" ++ c.map(show).join(",") ++ "]"

fun showm(m: list<call>): string
  "{" ++ m.map(showcall).join(" ") ++ "}"

fun order-of(c: call, order: list<int>) order.filter-map(fn(i) c[i])

// index-selection with NO pruning: isolates whether selecting indices per row
// reproduces the transpose/permute/transpose round-trip on ragged input
fun noprune(calls: list<call>): div bool
  val allidx = calls.transpose.map-indexed(fn(i, _) i)
  !allidx.any-permutation(fn(order) isAnOrder(calls.map(fn(c) c.order-of(order))))

// upstream's exact structure (permute COLUMNS, transpose back), but with
// never-decreasing columns dropped first
fun colprune(calls: list<call>): div bool
  val cols = calls.transpose.filter(fn(col) col.any(fn(sz) sz == SLt))
  !cols.any-permutation(fn(order) isAnOrder(order.transpose))

// same, but only prune when rows are uniform (non-ragged)
fun safeprune(calls: list<call>): div bool
  val lens = calls.map(fn(c) c.length)
  val uniform = match lens { Cons(l, r) -> r.all(fn(x) x == l); Nil -> True }
  val cols0 = calls.transpose
  val cols = if uniform then cols0.filter(fn(col) col.any(fn(sz) sz == SLt)) else cols0
  !cols.any-permutation(fn(order) isAnOrder(order.transpose))

fun colprune2(calls: list<call>): div bool
  match calls
    Nil -> False
    _ ->
      val cols = calls.transpose.filter(fn(col) col.any(fn(sz) sz == SLt))
      match cols
        Nil -> True
        _ -> !cols.any-permutation(fn(order) isAnOrder(order.transpose))

fun safeprune2(calls: list<call>): div bool
  val lens = calls.map(fn(c) c.length)
  val uniform = match lens { Cons(l, r) -> r.all(fn(x) x == l); Nil -> True }
  if !uniform then (!calls.transpose.any-permutation(fn(o) isAnOrder(o.transpose)))
  else match calls
    Nil -> False
    _ ->
      val cols = calls.transpose.filter(fn(col) col.any(fn(sz) sz == SLt))
      match cols
        Nil -> True
        _ -> !cols.any-permutation(fn(order) isAnOrder(order.transpose))

fun newer(calls: list<call>): div bool
  val keep = calls.transpose.map-indexed(fn(i, col) (i, col))
                  .filter-map(fn((i, col)) if col.any(fn(sz) sz == SLt) then Just(i) else Nothing)
  !keep.any-permutation(fn(order) isAnOrder(calls.map(fn(c) c.order-of(order))))

fun rows(len: int): div list<call>
  if len <= 0 then [[]]
  else rows(len - 1).flatmap(fn(r) [SLt, SEq, Unknown].map(fn(s) Cons(s, r)))

fun matrices(ncalls: int, maxlen: int): div list<list<call>>
  if ncalls <= 0 then [[]]
  else
    val shorter = matrices(ncalls - 1, maxlen)
    val allrows = list(1, maxlen).flatmap(fn(l) rows(l))
    shorter.flatmap(fn(m) allrows.map(fn(r) Cons(r, m)))

fun main()
  var tested := 0
  var bad := 0
  var bad2 := 0
  var bad3 := 0
  list(1, 3).foreach fn(nc)
    list(1, 3).foreach fn(ml)
      matrices(nc, ml).foreach fn(m)
        tested := tested + 1
        val a = orig(m)
        val np = noprune(m)
        val b = newer(m)
        if a != np then
          bad := bad + 1
          if bad <= 4 then println("SELECT-DIFF orig=" ++ a.show ++ " noprune=" ++ np.show ++ " " ++ m.showm)
        val cp = colprune2(m)
        if a != cp then
          bad2 := bad2 + 1
          if bad2 <= 4 then println("COLPRUNE2-DIFF orig=" ++ a.show ++ " colprune=" ++ cp.show ++ " " ++ m.showm)
        val sp = safeprune2(m)
        if a != sp then
          bad3 := bad3 + 1
          if bad3 <= 4 then println("SAFEPRUNE2-DIFF orig=" ++ a.show ++ " safeprune=" ++ sp.show ++ " " ++ m.showm)
  println("tested=" ++ tested.show ++ " select-diffs=" ++ bad.show ++ " colprune-diffs=" ++ bad2.show ++ " safeprune-diffs=" ++ bad3.show)
