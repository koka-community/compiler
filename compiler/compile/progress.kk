//-----------------------------------------------------------------------------
// Structured build progress.
//
// These events NEVER affect compilation output. They exist so that one reporter
// can render live, grouped per module, or aggregated into a profile -- from a
// single stream. Dropping the stream entirely must not change what the compiler
// produces.
//
// Diagnostics deliberately do NOT travel this path: they ride the phase results
// so they can be flushed in build order and stay byte-identical regardless of
// how the build was scheduled.
//
// See docs/superpowers/specs/2026-08-11-parallel-compile-design.md
//---------------------------------------------------------------------------
module compiler/compile/progress
import compiler/common/name
import compiler/compile/phase

// Elapsed times are milliseconds. Kept as a plain int rather than a duration so
// that the event type carries no effect and can be constructed anywhere.
pub alias elapsed-ms = int

pub type progress-event
  ModDiscovered( m : name, deps : list<name> )
  PhaseBegin( m : name, p : mod-phase )
  PhaseEnd( m : name, p : mod-phase, elapsed : elapsed-ms )
  ModDone( m : name, status : mod-status, elapsed : elapsed-ms )
  Note( msg : string )

// Sum elapsed time per phase across all modules: "where did the build spend
// its time". Non-PhaseEnd events contribute nothing.
pub fun per-phase-totals( events : list<progress-event> ) : list<(mod-phase, elapsed-ms)>
  events.foldl([]) fn(acc, e)
    match e
      PhaseEnd(_, p, d) -> acc.bump-phase(p, d)
      _ -> acc

fun bump-phase( acc : list<(mod-phase, elapsed-ms)>, p : mod-phase, d : elapsed-ms ) : list<(mod-phase, elapsed-ms)>
  if acc.any( fn((q, _)) q.show == p.show )
    then acc.map( fn((q, t)) if q.show == p.show then (q, t + d) else (q, t) )
    else acc ++ [(p, d)]

// Sum elapsed time per module across all phases: "which modules were expensive".
pub fun per-module-totals( events : list<progress-event> ) : list<(name, elapsed-ms)>
  events.foldl([]) fn(acc, e)
    match e
      PhaseEnd(m, _, d) -> acc.bump-mod(m, d)
      _ -> acc

fun bump-mod( acc : list<(name, elapsed-ms)>, m : name, d : elapsed-ms ) : list<(name, elapsed-ms)>
  if acc.any( fn((n, _)) n == m )
    then acc.map( fn((n, t)) if n == m then (n, t + d) else (n, t) )
    else acc ++ [(m, d)]

// Lookups, so callers (and tests) do not have to know the association-list
// representation.
pub fun lookup-phase( totals : list<(mod-phase, elapsed-ms)>, p : mod-phase ) : elapsed-ms
  match totals.find( fn((q, _)) q.show == p.show )
    Just((_, t)) -> t
    Nothing -> 0

pub fun lookup-mod( totals : list<(name, elapsed-ms)>, m : name ) : elapsed-ms
  match totals.find( fn((n, _)) n == m )
    Just((_, t)) -> t
    Nothing -> 0
