# Optimising Koka code: standards and procedure

Written from the port's optimisation work. Every rule here exists because
breaking it produced a wrong answer that looked right.

## 0. Procedure, in order

1. **Pick the workload that IS the target.** Not a proxy that is 40x larger or
   smaller, and not one that omits stages. `ifacecost` (parse every `.kki` in a
   build dir) measures interface parsing ONLY -- it contains no inline-section
   parsing, no resolve walk, no codegen -- so it cannot tell you where a warm
   rebuild spends its time. Percentages may transfer between related workloads;
   absolute times never do. State which workload every number came from.
2. **Get a per-stage budget first** (`KOKA_TIMING=1`, `TIMING`/`WALL` lines),
   and check it adds up. Unaccounted time is where the answer usually is: twice
   the largest item was something nobody had named.
3. **Instrument sub-steps before theorising.** Four hypotheses about one stage
   were all wrong (quadratic gamma folds, quadratic synonym folds, deferrable
   inlines, LinearMap staleness scans) and cost more than the two real fixes,
   both of which were found by adding timers inside a function.
4. **Read the code for behavioural questions.** "Does upstream skip recompiling
   roots?" was settled by twelve lines of `src/Main/Run.hs` after four timing
   runs had muddled it. Measure cost; read source for semantics.
5. **Only then optimise**, and re-measure on the same workload.

## 1. Profiling

- **Build with `--cclinkopts=-Wl,-no_deduplicate`.** Identical-code folding
  merges kklib's many identical `static inline` refcount helpers into one
  symbol; the profiler reports a `<deduplicated_symbol>` bucket and
  redistributes the rest. Since changing those helpers changes *what* folds, an
  ICF build's before/after attribution is not like-for-like: one fix appeared to
  take refcounting from 32.6% to 1.6%, while a no-ICF profile of the same binary
  showed 25.2%. **A profile containing `<deduplicated_symbol>` is unusable.**
- macOS: xctrace Time Profiler, `time-profile` schema (not `time-sample`, which
  has raw addresses). Summarise with `scripts/profile-report.py` (self time, by
  module, and alloc/free/refcount split with paired attribution).
- Instruments' **Allocations template hangs** on these binaries. Don't retry it.
- Linux: `--fprofile` (`-pg` + frame pointers) with gprof gives *call-graph*
  attribution and sidesteps ICF entirely. Upstream ships `util/profile.kk` for
  this. Apple clang dropped `-pg`, so it is not an option on macOS.
- `MIMALLOC_SHOW_STATS=1` reports pages/arenas but NOT cumulative bytes
  allocated; that needs mimalloc built with `MI_STAT>=2`.

## 2. The Koka cost model -- what is actually expensive

- **Refcount operation VOLUME, not memory latency.** High self time in
  `kk_block_refcount` is not cache misses: a block whose refcount is being
  touched is one the program is actively using, so it is cache-warm. It means
  there are a lot of dup/drop operations.
- **Small integers are unboxed**, so `kk_integer_dup` on them is a no-op fast
  path. Don't chase it.
- **Value types do not help for anything stored in a list.** `list<lexeme>`
  boxes its elements regardless, so making `pos`/`range` value types buys
  nothing. Value types pay off only where the value genuinely lives inside
  another unboxed value.
- **Statics took the refcount slow path** until fixed: `RC_STUCK` is negative,
  so `rc <= 0` sent every dup/drop of a static out-of-line to do nothing. The
  *pattern* recurs -- look for out-of-line calls whose body is a no-op.
- **A `var` captured by a handler clause becomes a heap `kk_ref_t`.** Every read
  is a `ref_get` plus a dup of the payload. Look for `kk_ref_alloc` in the
  generated C of a function you thought used a local.
- **Effect operations cost ~9.5ns each** (13.5ns before two runtime fixes).
  Cost is linear in operation count; monadic lifting adds nothing measurable. A
  loop performing operations per input *character* pays that per character.
- **`@open-none` wraps every operation** in `evv-swap-create0(); ..; evv-set(w)`
  -- two per operation.

## 3. Allocation and reuse

- **Attribute alloc and free to the same owning caller.** A caller doing both is
  a reuse candidate; one that only frees tore down something built elsewhere.
- **But "frees more than it allocates" does NOT prove reuse is impossible.** In a
  chain of list-to-list passes, if one pass copies, later passes can still reuse
  the copy. Check `--showfcore` for `@reuse(`, `@assign-reuse`, `@alloc-at`,
  `@reuse-drop` -- do not infer from the profile.
- **What blocks reuse**, in order of suspicion: `var`/`ref` cells, a reference
  captured in a closure or handler-operation body, and a value held for a later
  use that could be recomputed or moved earlier.
- **`local-var/update` hands ownership** to its function, so the value arrives
  uniquely referenced and can be updated in place. `state := state(...)` reads
  the var (dupping it), defeats reuse, and allocates a fresh record per step.
  This was 16.9% of a warm interface load in the lexer.

## 4. Comparing against the Haskell reference compiler

- It is **not** that GHC allocates less. It allocates *more* -- 1.265GB at
  3.4GB/s on a warm 27-module rebuild -- and pays ~57ms of wall to reclaim it,
  because gen-0 collection runs in parallel across 8 threads. The port's
  reclamation is eager, serial, and per-object. Same data shapes, different cost
  model: **the port must allocate less or reuse, not match volume.**
- `+RTS -s` counts only the Haskell process's own CPU. Subprocess (clang, ld)
  time is the gap between MUT *CPU* and MUT *elapsed*.
- Use `scripts/compare-warm.sh`. Five separate faults each produced a plausible
  wrong number: mismatched artifacts, `-c` on a `main`-less module comparing
  error paths, zsh expanding globs before the build ran, the `./koka` wrapper
  costing 0.19s of `stack exec` per call, and a mangled flag bundle exiting
  non-zero. The script asserts against all five.
- **zsh does not word-split unquoted parameter expansions.** `koka $FLAGS f.kk`
  passes the whole string as ONE argument and exits non-zero. Write flags
  explicitly or use the script (`#!/bin/sh`, which does split).

## 5. Microbenchmarking

- **clang coalesces `dup`/`drop` pairs on the same block** and hoists them out of
  a loop, so a naive refcount benchmark reports the fewest operations as the
  slowest. Put each sequence behind `noinline`, pass blocks in as opaque
  arguments, and end every variant in an indirect call.
- Keep benchmarks in the repo (`scripts/bench-effect-op.kk`), not a scratch
  directory -- scratch files vanished three times mid-session.
- A wall delta smaller than the run-to-run spread is noise; interleave the
  variants and report the spread.

## 6. Generated code

`compiler/syntax/lex.kk` is generated from `compiler/syntax/koka.x` by the
`koka-community/alex` fork. Hand-edits to the generated file are silently
reverted by the next regeneration -- three fixes had accumulated there,
including a parallel-build use-after-free. **Optimise the template
(`data/alex-effects.kk`) or the grammar, then regenerate and diff.** Build the
fork's own `alex`; the one in `~/.cabal/bin` may be a year stale.
