//-----------------------------------------------------------------------------
// Turning a discovered dependency graph into a parallel execution schedule.
//
// This is the deterministic half of Stage 3 increment 2: `build-waves` decides
// WHAT may run concurrently, with no concurrency of its own, so the schedule
// can be unit-tested and is identical on every run. The concurrent half then
// only has to execute one wave at a time.
//
// Kept free of `compile/build`'s types (it takes a plain adjacency list rather
// than a `dep-cache`) so it stays pure and does not create an import cycle.
//
// See docs/superpowers/specs/2026-08-11-parallel-compile-design.md
//-----------------------------------------------------------------------------
module compiler/compile/schedule
import compiler/common/name
import std/core/undiv

// Group modules into successive waves: every module in wave N has all of its
// in-graph dependencies in waves < N, so a whole wave can compile
// concurrently once the previous wave has finished.
//
// `deps` is the discovered graph as (module, its direct imports). An import
// that is NOT itself a key of `deps` is an interface-only module -- loaded
// from a .kki, never compiled here -- so it imposes no ordering.
//
// Determinism (required: the sweep compares output byte-for-byte):
//   - waves come out in dependency order;
//   - within a wave, modules keep their relative order in `deps`;
// so the schedule depends only on the graph, never on timing.
//
// Modules caught in an import cycle can never have their dependencies
// satisfied. Rather than drop them silently or loop forever, they are
// returned separately for the caller to report -- `resolve-module` already
// emits "recursive imports: a -> b -> a" with the full chain.
pub fun build-waves( deps : list<(name, list<name>)> ) : div (list<list<name>>, list<name>)
  val keys = deps.map(fst)
  fun in-graph( n : name ) : bool
    keys.any( fn(k) k == n )
  fun go( done : list<name>, remaining : list<(name, list<name>)>, acc : list<list<name>> ) : div (list<list<name>>, list<name>)
    if remaining.is-nil then (acc.reverse, [])
    else
      val (ready, blocked) = remaining.partition fn((_, ds))
        ds.all( fn(d) !in-graph(d) || done.any( fn(x) x == d ) )
      // No module became ready => every one that is left waits on another
      // that is left, which is exactly a cycle (or a chain into one).
      if ready.is-nil then (acc.reverse, remaining.map(fst))
      else
        val wave = ready.map(fst)
        go(done ++ wave, blocked.pretend-decreasing, Cons(wave, acc))
  go([], deps, [])

// The most modules that may run at once -- the widest wave. Useful both for
// reporting and for deciding whether spinning up tasks is worth it at all.
pub fun max-width( waves : list<list<name>> ) : int
  waves.foldl(0) fn(w, wave) max(w, wave.length)

// Total modules across all waves.
pub fun scheduled-count( waves : list<list<name>> ) : int
  waves.foldl(0) fn(n, wave) n + wave.length
