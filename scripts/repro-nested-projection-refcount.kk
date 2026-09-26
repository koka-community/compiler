// Minimal reproduction: a nested projection out of a value that stays live
// costs a dup, an is-unique test, a dead free-branch, and a dec-ref.
//
//   ./koka -O2 --showcore  --include=scripts -c scripts/repro-nested-projection-refcount.kk
//   ./koka -O2 --showfcore --include=scripts -c scripts/repro-nested-projection-refcount.kk
//
// This is the shape every effect operation goes through -- `@perform` is
// `match ev { Ev(_,m,h,_) -> match h { Hnd(..,f) -> f(..) } }` with `ev` still
// live -- but it needs no handler machinery, which is the point: the cost is
// general to nested projections, not specific to effects.
//
// BEFORE Parc (--showcore) the redundancy is already visible: the outer
// pattern binds `h` with `as` AND destructures it, so `f` is literally
// `@pat@2`, yet the inner match re-destructures it:
//
//   match e { Ev2(@pat@0, (@skip Hnd2(@pat@1, @pat@2) as h)) ->
//     match h { Hnd2(@pat@4, f) -> f(x) + ... } }
//
// AFTER Parc (--showfcore) that redundancy has become refcount traffic:
//
//   val _ = @dup(h);
//   match h { Hnd2(@pat@4, f) ->
//     if @is-unique(h) then { @drop(@pat@4); @free(h) }   // DEAD: `e` holds h
//     else { @dup(f); @dec-ref(h) } ... }
//
// The `@dup(h)` is what makes `@is-unique(h)` false, so it is load-bearing:
// cancelling the dup/dec-ref pair WITHOUT also folding the is-unique test
// would let the free-branch run and free a value `e` still references.

type hnd2
  Hnd2(cfc: int, op: (int) -> int)

type ev2
  Ev2(tag: int, hnd: hnd2)

// `e` is live after the inner match (we read `e.tag`), mirroring `ev` being
// passed on to the clause. `f` escapes the inner match (it is called).
pub fun perform2(e: ev2, x: int): int
  match e
    Ev2(_, h) ->
      match h
        Hnd2(_, f) -> f(x) + e.tag

pub fun main()
  val e = Ev2(7, Hnd2(0, fn(i) i + 1))
  println(perform2(e, 1).show)
