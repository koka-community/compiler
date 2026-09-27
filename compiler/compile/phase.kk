//-----------------------------------------------------------------------------
// Build phases, module identity, and the staleness rule.
//
// This deliberately differs from upstream `Compile/Module.hs`. Upstream models
// a module as ONE record that advances, with a `modPhase` marker and mostly
// `Maybe` payload fields. That suits its design, where the same record is
// published into five per-phase maps. Ours differs in three ways, each for a
// reason:
//
//   1. Phases are ORDERED -- we need "how far did this module
//      get" for progress and work accounting, which an unordered enum cannot
//      answer.
//
//   2. Phases carry NO error variants (unlike upstream's PhaseTypedError etc.).
//      Our per-phase results already carry a `mod-status`; an error phase would
//      be a second encoding of the same fact, and two sources of truth can
//      disagree. It also cannot express `Skipped(blocked-on)`, which we want so
//      a diagnostic names the real cause rather than the module that merely
//      waited on it.
//
//   3. Identity is SEPARATE from payload (`mod-info` below). Upstream's single
//      record mixes name/paths/times with every phase's output, so most fields
//      are `Maybe` and which ones are valid depends on `modPhase`. Splitting
//      them removes that ambiguity: `mod-info` is computed once at discovery
//      and never changes; payloads are produced per phase.
//
// See docs/superpowers/specs/2026-08-11-parallel-compile-design.md
//---------------------------------------------------------------------------
module compiler/compile/phase
import compiler/common/name
import std/os/path
import std/data/rb-map
import compiler/common/name-collections

// Epoch seconds, as produced by `compiler/common/file/file-mtime`. koka's std
// has no stat/mtime primitive on this branch, so that function shells out.
// 0 means "absent", which makes a missing artifact infinitely stale with no
// special case at the call sites.
pub alias build-time = int

pub type mod-phase
  Lex           // lexemes
  ParseDeps     // imports, from the lexemes (cheap; drives discovery)
  Parse         // full program, from the SAME lexemes
  TypeCheck     // core + gamma
  Optimize      // final core + inline definitions
  CodeGen       // backend sources (.c/.h/.js)
  CCompile      // objects
  Link          // interface + executable

// Ordinal. Explicit rather than derived so that inserting a phase forces a
// deliberate decision about where it sits.
pub fun phase/int( p : mod-phase ) : int
  match p
    Lex -> 0
    ParseDeps -> 1
    Parse -> 2
    TypeCheck -> 3
    Optimize -> 4
    CodeGen -> 5
    CCompile -> 6
    Link -> 7

pub fun phase/show( p : mod-phase ) : string
  match p
    Lex -> "lex"
    ParseDeps -> "parse-deps"
    Parse -> "parse"
    TypeCheck -> "typecheck"
    Optimize -> "optimize"
    CodeGen -> "codegen"
    CCompile -> "ccompile"
    Link -> "link"

pub fun phase/(==)( p : mod-phase, q : mod-phase ) : bool
  p.int == q.int

pub fun phase/(<=)( p : mod-phase, q : mod-phase ) : bool
  p.int <= q.int

// "Has this module already produced what phase `q` produces?"
pub fun reached( p : mod-phase, q : mod-phase ) : bool
  q.int <= p.int

// Per-phase outcome. `Skipped` names the dependency that blocked us so the
// eventual diagnostic points at the cause, not the victim.
pub type mod-status
  Ok
  Failed
  Skipped( blocked-on : name )

pub fun mod-status/show( s : mod-status ) : string
  match s
    Ok -> "ok"
    Failed -> "failed"
    Skipped(b) -> "skipped(" ++ b.show-plain ++ ")"

// Module identity and filesystem facts: computed once at discovery, never
// updated. Three times rather than one because the staleness RULES differ --
// a locally built interface is compared against its source, whereas a
// precompiled library interface has no source in the tree and is trusted
// unless absent. One timestamp cannot express both.
pub struct mod-info
  name            : name
  source-path     : path
  iface-path      : path
  lib-iface-path  : path
  source-time     : build-time
  iface-time      : build-time
  lib-iface-time  : build-time

// A module built from source in this tree: its interface must be at least as
// new as its source.
pub fun has-source( i : mod-info ) : bool
  i.source-time > 0

// A phase must rerun when its own source is newer than the output it produced,
// or when any dependency published a result newer than that output.
//
// Transitivity is automatic: a rebuilt phase publishes `now`, so its dependents
// see a newer dependency time and rebuild in turn; an untouched module keeps its
// old mtime and stops the cascade.
//
// COMPARISON: strict `>` on nanosecond times (`file-mtime`). A dependency
// written in the same timestamp tick as our output does not trigger a rebuild,
// so on a filesystem with coarse timestamps (whole seconds) such a rebuild can
// be missed.
pub fun is-stale( source-time : build-time, out-time : build-time, dep-times : list<build-time> ) : bool
  if source-time > out-time then True
  else dep-times.any( fn(dt) dt > out-time )

// Staleness for a whole module, choosing the rule by provenance:
//   - has source  -> compare its interface against source and dependencies
//   - no source   -> a precompiled library interface; stale only if absent
pub fun mod-stale( i : mod-info, dep-times : list<build-time> ) : bool
  if i.has-source
    then is-stale(i.source-time, i.iface-time, dep-times)
    else i.lib-iface-time == 0
