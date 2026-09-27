//-----------------------------------------------------------------------------
// The scheduler-owned module registry.
//
// `demand` is the ONLY way a module enters the build. It is idempotent, so two
// discoverers of the same import cannot race to register it twice -- which is
// what makes concurrent discovery safe once the build is parallel.
//
// The registry also records demand edges, so an import cycle is detected when
// the edge that closes it is added. Under the promise-based design a cycle
// would otherwise deadlock: every task waits, none publishes. Reporting it as
// a diagnostic keeps a cycle a compile error rather than a hang.
//
// See docs/superpowers/specs/2026-08-11-parallel-compile-design.md
//---------------------------------------------------------------------------
module compiler/compile/registry
import compiler/common/name
import std/core/undiv

pub struct registry
  mods  : list<name>            // discovery order
  edges : list<(name, name)>    // (from, to)

pub fun registry/empty() : registry
  Registry([], [])

pub fun known( r : registry ) : list<name>
  r.mods

// Register `m`, optionally as a dependency of `from`. Returns the updated
// registry and, when this edge closes a cycle, the diagnostic to report.
pub fun demand( r : registry, from : maybe<name>, m : name ) : div (registry, maybe<string>)
  val mods' = if r.mods.any( fn(x) x == m ) then r.mods else r.mods ++ [m]
  match from
    Nothing -> (Registry(mods', r.edges), Nothing)
    Just(f) ->
      val edges' = r.edges ++ [(f, m)]
      // Adding f -> m closes a loop exactly when m already reaches f.
      // The reported loop is m -> ... -> f -> m, which matches the wording
      // build.kk already emits for `recursive imports`.
      match path-from(edges', m, f, [])
        Just(p) -> (Registry(mods', edges'), Just(render-cycle(p ++ [m])))
        Nothing -> (Registry(mods', edges'), Nothing)

// Depth-first search for a path `src -> ... -> dst`, returning the nodes along
// it inclusive of both ends. `seen` guards against walking an existing cycle
// forever.
fun path-from( edges : list<(name, name)>, src : name, dst : name, seen : list<name> ) : div maybe<list<name>>
  if seen.any( fn(x) x == src ) then Nothing
  elif src == dst then Just([src])
  else
    val nexts = edges.filter( fn((f, _)) f == src ).map( snd )
    nexts.foldl(Nothing) fn(acc, nxt)
      match acc
        Just -> acc          // first path found wins; deterministic in edge order
        Nothing ->
          match path-from(edges, nxt, dst, Cons(src, seen)).pretend-decreasing
            Just(rest) -> Just(Cons(src, rest))
            Nothing -> Nothing

// Matches the wording build.kk already emits, so existing expectations and any
// recorded test output continue to hold.
fun render-cycle( nodes : list<name> ) : string
  "recursive imports: " ++ nodes.map(show-plain).join(" -> ")
