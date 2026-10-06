# Port status

Written 2026-09-26.
Companions: `docs/port-optimization-state.md` (the optimization queue), `docs/roadmap-to-primary.md` (non-performance work), `docs/upstream-pr-burndown.md` (the upstream PR stack).

## Where the port stands

### Correctness

- Sweep: 425 pass / 21 skip / 2 known mismatches, runner and compiler both built by the port.
- Multimodule gate passes, including two incremental steps: relative imports, and a transitive chain with an earlier-build case.
- Self-hosting works; the pinned bootstrap (`.koka/bootstrap/driver`) is `2ac85cd`, and the language server uses it.
- Compiling a script needs neither `--sharedir` nor `-i` (`c1a5088`).
- Language server: mid-session restarts fixed (`f165f65`, libuv's zero-byte read treated as end of input); VS Code edit-latency test in `support/vscode/koka.language-koka` (`8f73d90`, run with `KOKA_BENCH=1`).

### Reference-compiler stack

- The fixes the port needs are 21 single-commit layers (`stack/*` in `~/koka`, top `stack/all`) on `upstream/dev`; see `docs/upstream-pr-burndown.md`.
- CI builds stage 1 with `port-reference` on `TimWhiting/koka`, the top of the stack plus the recursive-group type-argument fix (2026-10-05).
- Its `Type/TypeVar.hs` keeps upstream's kind assertions; `dev-compiler2`, the previous CI reference, comments them out, so a port built with it hid ill-kinded core.

### Port commits of 2026-09-25/26

- Nanosecond modification times (`3288102`).
- A leaf-first rebuild walk: every recompiled module goes through the parallel orchestrator (`2ac85cd`).
- Relative imports survive a recompile triggered by a dependency (`4139f25`).
- Worker thread priority is an option; the default is Normal (`458ddb5`).
- Include path and module naming match upstream (`c1a5088`).

### Performance (port only, measured 2026-09-25)

Method: `bench-vs-upstream.sh` flags (`-c -v0 --console=raw -O2 --target=c`), `/usr/bin/time -p`, one run per long case.

| workload | port |
| --- | --- |
| cold small (`scripts/probe-tiny.kk`) | 4.24s |
| warm small | 0.47-0.50s (best of 3) |
| cold big (the driver) | 147.9s |
| warm big | 16.6s |
| incremental: touch `main/driver.kk` (root only) | 17.6s |
| incremental: touch `type/infer.kk` (18 dependents) | 106.8s |
| incremental: touch `core/core.kk` (79 dependents) | 132.4s |
| language-server edit of `type/infer.kk` | ~37s per edit |

There is no upstream comparison from these dates.
The ratios in `docs/roadmap-to-primary.md` are from 2026-09-17, under different flags (`-g`, for one), so the current gap to upstream is unknown.

## Measurements

All on this machine (Apple silicon laptop, AC power), port only unless marked.
"Port" is the driver built from the commit current on that date.

### Latest (2026-09-24 to 2026-09-26)

| date | what | result | how |
| --- | --- | --- | --- |
| 09-26 | language-server edit, `type/infer.kk` | open 35.6-38.0s; each edit 36.0-40.4s; 4 of 4 runs clean, one server each | `KOKA_BENCH=1 npm test`, 4 runs, 5 edits each, after `f165f65` |
| 09-26 | where one such edit goes | type check 35.3s of 35.9s; interfaces 0.14s (110 of 110 reused) | server `KOKA_TIMING=1` log |
| 09-26 | type check of `type/infer.kk` alone | 53.3s CPU; `substitute` 36.6%, freeing ~28%, allocation 5.3% | `scripts/typecheck-probe.kk`, `-Wl,-no_deduplicate`, xctrace leaf samples |
| 09-26 | substitution composition, `type/infer` | 13,745 compositions, 2,735 overlapping, 13,983,195 entries rebuilt, 34,155 affected | temporary counters in `run-infer` |
| 09-26 | same, `type/infer-effect` | 17,798 / 3,050 / 19,569,996 / 28,507 | same |
| 09-26 | range-map entries substituted at zaps | `type/infer` 46,574; `type/infer-effect` 1,704,264 | same |
| 09-25 | cold / warm small | 4.24s / 0.47, 0.48, 0.50s | `bench-vs-upstream.sh` flags, port only, `/usr/bin/time -p` |
| 09-25 | cold / warm big (the driver) | 147.9s (1048s CPU, 7.1x) / 16.6s (71s CPU) | same |
| 09-25 | incremental, touch then rebuild the driver | root only 17.6s; `type/infer.kk` 106.8s (18 modules); `core/core.kk` 132.4s (79 modules) | same flags, warm build dir, one run each, all modules orchestrated |
| 09-25 | old vs new staleness rule, touch `type/infer.kk` | old 162.9s, 163.2s (16 modules on the serial walk); new 100.0s, 99.5s (0) | one binary, temporary `KOKA_OLD_STALE` switch |
| 09-25 | the rebuild walk itself | 2ms (6-module chain) | `KOKA_TIMING=1` |
| 09-25 | worker thread priority, cold port build | Interactive 161.6s, 162.0s; Normal 159.4s, 159.8s; Background 185.6s | one binary, temporary `KOKA_WORKER_PRIORITY` switch |
| 09-25 | same-second rebuilds | 5 of 5 recompile (were 2 of 5 with whole-second times) | touch + rebuild with no delay |
| 09-24 | cost of the sound `isHandlerFree` rule | `open_none` call sites 6226 vs 4797; evidence-swap self time 0.57% vs 0.53% of 623s CPU; wall 5:31 vs 5:22 | two reference-built drivers, cold port build under xctrace |
| 09-26 | sweep | 425 pass / 21 skip / 2 known mismatches | runner and compiler built by the port |

### Earlier comparisons with upstream (not re-measured since)

| date | what | port | upstream | notes |
| --- | --- | --- | --- | --- |
| 09-23 | dev loop: no-op / comment edit / full rebuild | ~17s / ~150-164s / 161-170s | 0.5s / 8.9-10.0s / 71.5s | the Haskell side is GHC building the Haskell compiler, not Koka |
| 09-17 | warm small (best of 30) | 0.31s (avg 0.37) | 0.47s (avg 0.49) | `-O2 --target=c`, before `-g` went off by default |
| 09-17 | cold small (avg of 5) | 4.09s | 3.80s | same |
| 09-17 | warm big / cold big | 15.5s / 249s | ~24s / ~469s | same |
| 09-13 | incremental, touch `type/infer.kk` | 257s | 246s, 269s | the port then compiled 16 of its 19 modules serially |
| 08-15 | compiling, warm with one module touched | ~2.2x upstream front-end CPU | | `compiler/compile/schedule.kk` |
| 08-15 | interface loading | ~67ms per interface | ~16ms | warm no-op; since reduced (sticky refcount, -14.6% on 09-04) |
| 09-04 | tail-resumptive handler operation | ~13.7ns (~11x a direct call) | | microbenchmark, 30M iterations |

## The dev-loop gap

The port building itself vs GHC building the Haskell compiler (2026-09-23, `docs/port-optimization-state.md`):

| operation | Haskell | port |
| --- | --- | --- |
| nothing changed | 0.5s | ~17s |
| comment-only edit | 9-10s | 107-164s |
| full rebuild | 71.5s | ~150s |

- Every rebuild pays ~17s of warm load: mostly interface parsing, and lexing through effect handlers.
- Compiling one module costs ~2.2x upstream's CPU (measured 2026-08-15).
- There is no early cutoff: a changed module recompiles everything downstream.
- Blocker: artifacts depend on build provenance; cold and incremental builds of identical sources give different generated ids, because the inline-definition set differs in 77 of 202 modules.

Next steps, in order:

1. Make artifacts provenance-independent (`KOKA_INLINE_FP` identifies the differing field).
2. Reinstate write-if-changed, tracking header generations.
3. Early cutoff through per-declaration hashing.
4. Split the largest translation units.

In parallel: cut the ~17s warm load, and attribute the warm-small regression (0.37s on 2026-09-17, 0.48s now).

## The language-server gap (substitution)

- Of the ~37s per `type/infer.kk` edit, 35s is type-checking that one module; the session reuses all 110 imports from memory.
- Substitution plus freeing the resulting copies is ~65% of that check (xctrace leaf samples, `scripts/typecheck-probe.kk` built with `-Wl,-no_deduplicate`).
- Composing substitutions rebuilds 13,983,195 stored entries; 34,155 of them mention a variable being bound.
- Planned fix, results unchanged: an occurrence index that re-substitutes only affected entries.
- Blocked: with the index, both compilers emit code that reads past the evidence vector (see Open bugs).
- Also planned: collect the range map only when requested (a fidelity gap with upstream), and substitute it incrementally at each zap, which is quadratic in modules with many top-level groups.
- Deferred to the new inference design: mutable-variable unification, and pruning out-of-scope type variables.

## Spikes, dead ends and corrected assumptions

- write-if-changed with stamp files: reverted; it broke object invalidation, never converged, and cannot pay off while artifacts depend on provenance.
- An interface flag, or lifting `open-none` regions, to cut evidence swaps: dropped; the sound `isHandlerFree` rule costs ~0.04% of a port build.
- `isHandlerFree`: upstream's trust in `std/core` is unsound, and #750's rule missed externals; the two tests show both.
- Overlapping the rebuild walk with compilation: not done; the walk takes ~2ms, and the preload and session reuse need its decisions first.
- Worker thread priority: Interactive gave no speed-up; Background was 15% slower.
- "The port recompiles fewer modules (19 vs 62)": misread; the set was always exact, and the real problem was 16 modules compiling serially, now fixed.
- Language-server restarts: the stray-bytes theory was wrong; the cause was the zero-byte read.
- A 9.1s "fast" profile of the substitution index was the crash; always check the probe's `type-checked` line.
- Earlier dead ends: deferred inline forcing (reverted); "quadratic gamma folds" and "monadic lifts cost the time" (measured, wrong); an empty-substitution short-circuit (regressed 2%, reverted); case-of-known via as-patterns (reverted).

## Crashes seen, and what causes them

- **Type checker segfault with the substitution index (OPEN, root cause unknown).**
  - Symptom: `scripts/typecheck-probe.kk` built with the index exits 139 on every run, at `-O2` and `-O0`, and with `KOKA_MAX_WORKERS=1`.
  - Mechanism, from ASAN (`--fasan`): a global-buffer-overflow READ in `kk_evv_at`, called from `kk_evv_swap_create1` <- `open-at1` <- `type/unify` `subsume`, on a compile worker thread. `open-at1(i)` reads index `i` of the current evidence vector, and the vector was shorter than the code's static effect row promises: code ran with evidence missing or cleared.
  - Trigger: the index change to `compiler/type/typevar.kk`, which is pure Koka and adds calls through `int-map` functions with effect-polymorphic callbacks (`insert-with`, `union-with`) and `list.foldl`. The same probe without the change runs cleanly.
  - Ruled out: port-only code generation (a reference-built probe crashes the same way), and the refined `isHandlerFree` rule (a compiler with #750's rule for externals, itself built without the index, produces a crashing probe too).
  - Conclusion so far: pure Koka cannot read outside the evidence vector, so this is a compiler bug shared by the port and the reference compiler, which the new code exposes. Not yet minimised.
  - The change is not in the tree; it is kept outside it until this is fixed.
- **ASAN stack overflow in `syntax/layout` (not a bug at normal frame sizes).** Under `--fasan` the main thread overflowed its stack in layout's recursive `check` on `type/infer.kk`, because instrumented frames are much larger. `ulimit -s hard` (64MB) gets past it; normal builds do not hit it.
- **Language server exiting mid-session (FIXED, `f165f65`).** libuv reports "no data yet" as a zero-byte read (`nread == 0`); the stdin read callback treated it as end of input, closed stdin, and the server exited cleanly (status 0). The client restarted it, then gave up. It happened while a long check left the client's messages queued; `tee` between client and server hid it by draining the pipe.
- **Language server SIGPIPE at teardown (OPEN, harmless).** Status 141: the server is still writing after the client has closed the pipe during shutdown.
- **The experimental compiler crashing while compiling (expected).** A compiler whose own `typevar.kk` contained the index hit the same evidence-vector crash when it ran; it confirms the crash is in the code produced, not in the probe.
- **The machine going down (FIXED).** A watchdog panic with clang at ~34.5GB: `-g` on a ~15MB translation unit, made worse by building pristine upstream `dev`, whose code generation emits far more C for the same modules. `-g` is now off by default at `-O1`+, the C-compile pool is capped at 2 workers when debug info is on, and pristine upstream `dev` is never built.

## Open bugs

- The type checker segfault with the substitution index (see above).
- Warm-small regression, unattributed.
- The language server exits with SIGPIPE (status 141) at teardown.
- The driver exits 0 on an unrecognised flag, and does not accept `-o file` with a space, as upstream does.
- A change to an `extern import`ed C file does not make its module recompile.
- "parallel compile of X failed" is not fatal if the sequential retry succeeds; whether that is intended is undecided.
