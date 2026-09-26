# Optimizing the port: where this stands

Written 2026-09-23.
Companion to `docs/roadmap-to-primary.md`, which covers the non-performance work.
Numbers here are wall-clock on this machine, `-O2`, C target, the port building its own driver (202 modules) unless stated.

## Landed

| change | effect |
| ------ | ------ |
| `-g` off by default at `optimize >= 1` | cold self-build 228s -> 161s; peak clang 9.9GB -> 1.8GB; total `.o` 678MB -> 110MB |
| C-compile pool width keyed off the build type (2 workers when debug info is on) | a 21MB translation unit peaks at ~9.9GB with `-g`; at `cpu/2` that is 70GB of resident memory, which took the whole machine down once |
| dispatch fix: resolve a check-stage dispatch against the type-checked map | 12 modules were compiled TWICE per incremental build (the second compile of `compiler/lsp/state` alone cost 29s); now 0 |
| interfaces declare every synonym they mention | an incremental build failed to link (`kk_compiler_lib_scc__graph` undefined); see `docs/upstream-pr-burndown.md` |

`-g` is worth understanding rather than just keeping off: it changes no generated code (identical `.o` code, the size difference is `__debug_*` sections), function-level profiles work without it, and `--profile` exists for when line-level attribution is actually needed.

## Reverted, and why

**write-if-changed + per-module `.kks` stamps.** Writing `.kki`/`.c`/`.h` only when their content differs, with a stamp file recording "last compiled".
It was reverted the same day:

- it cannot pay off while generated ids are provenance-dependent (see below): an incremental build legitimately rewrites ~98 of 202 `.c` files anyway;
- it broke object invalidation. `compile-objs` decides staleness by comparing a `.o` against its own `.c` ONLY -- safe purely because a recompiled module used to always rewrite its `.c`. Without that, an object survives a dependency's header change and links against a header generation that no longer exists. That is a silent-wrong-output risk; we saw it as a build failure only because a type name happened to disappear;
- it broke convergence. Interfaces written late in a build are newer than the stamps of dependents compiled earlier, so the next build recompiles them, and with unstable ids their interfaces change again. A no-op rebuild went from re-checking 2 modules to re-checking 90, and took 185s.

The invariant `compile-objs` relies on is now written down at that site.
Bring the change back only after ids are stable, and track header generations then.

## The blocker: artifacts depend on build PROVENANCE

For identical sources, a cold build and an incremental build produce different bytes: **55 of 202 interfaces and ~103 of 202 `.c` files differ**, several at identical length.
The difference is generated *name* ids (`@uniq-...@16447` vs `@...@16452`), not types or structure.

Established by measurement:

- module type-check counters are IDENTICAL cold vs warm (all 202 modules);
- `core-optimize` seeds its own counter at a fixed 10000, so seeding is not the problem;
- 44 of 101 shared modules diverge in their OPTIMIZER counters, by 2-4;
- the earliest visible divergence is `04-specialize-lift`, with the same definition COUNT but different names (`OPT-FP` only hashes top-level names, so body-level drift is invisible until a pass lifts a body);
- interface parsing does NOT renumber term names -- its `1000`-based counter feeds `env-extend`, i.e. TypeVar ids;
- **77 of 202 modules produce a different inline-definition set when LOADED from their interface than when COMPILED in the same run, with identical counts.** The optimizer's inlining decisions depend on that set, which is how a few uniques' worth of difference shifts every later id.

Upstream's interface format is lossy in the same way, by construction: `prettyInlineDef` serializes `cost` only inside a comment and the parser recomputes it (`if inl == InlineAlways then 0 else costExpr expr`), and the `inline` keyword conflates `InlineAlways` with `cost <= 0`.
So a definition that was `InlineAuto`/cost<=0 when compiled reads back as `InlineAlways`/0.

Next step: the `KOKA_INLINE_FP` diagnostic (in `compiler/compile/build.kk`) fingerprints name/cost/kind/is-rec/paramSpecialize per provenance, and `KOKA_INLINE_FP_MOD=<module>` dumps them per definition.
`std/core/lazy` has a single inline definition and still mismatches, so one run identifies the field.
If it is confined to `cost`/`kind`, normalise the COMPILED set to what a round-trip produces.
If `def-name`/`is-rec`/`paramSpecialize` differ too, it is a port-specific bug.

## Queue, in order

1. **Make artifacts provenance-independent** (above). Everything else is gated on it: while half the artifacts change on every rebuild, no staleness scheme can help.
2. **Reinstate write-if-changed**, tracking header generations this time.
3. **On-demand stale set.** `find-ready`/`next-work` already dispatch per module; `stale-set` is threaded through as a PRECOMPUTED filter derived from dependency SOURCE times, so every dependent of an edited module is condemned before anything is compiled. Decide at dispatch instead, when a dependency's real interface time is known, and demote `stale-set` to a hint.
4. **Per-declaration hashing** over an alpha-canonical form: fine-grained invalidation that does not care about id drift (GHC's per-declaration ABI hashes plus `mi_usages` are the precedent).
5. **Split translation units.** clang dominates cold builds and the largest generated TU is ~21MB; per-declaration hashes make partial C recompilation possible.
6. **Derived/structural names** (enclosing def + role + occurrence index rather than a counter). Not needed for determinism -- minting is already deterministic -- but it retires the capture hazard that `simplify.kk`'s avoid-set defends against per-site, after `pad-left` was silently miscompiled once. Rust's `DefPath`+disambiguator and GHC's session-scoped `Unique` (never serialized) are the models.

## Where the port stands against the reference compiler

The port builds itself in 161s cold and 17.3s for a no-op.
But the Haskell compiler's own dev loop is faster than any of that, and pretending otherwise would waste effort in the wrong place:

| operation | Haskell (`stack`, deps cached) | port |
| --------- | ------------------------------ | ---- |
| nothing changed | **0.5s** | 17.3s |
| comment-only edit | 8.9-10.0s (3-4 modules) | ~150-164s (100 modules) |
| exported binding added to a widely-imported module | 63.4s (87 modules) | ~150-164s (100 modules) |
| full rebuild from clean | 71.5s (109 modules + 2 exes) | 161-170s (202 modules) |

Caveats that matter: upstream's 109 modules do NOT include a standard library (Koka's `lib/` is compiled later, at run time), and GHC has no C backend -- it emits objects directly and shells out to clang only to assemble and link.
So "we will never match the C-backend cost" is true; "we cannot match the INCREMENTAL story" is not.
GHC's two cliffs (~9s when no interface changed, 63s when one did) are what items 1-4 above are chasing.

## Measurement discipline

- Concurrent load voids timings. Read counts (modules checked, artifacts rewritten, link errors) instead -- they stay valid.
- The sweep enforces a per-test timeout; under load it produces spurious failures. Do not gate on it while the machine is busy.
- A/B with the SAME binary where possible; a build directory's hash covers flags and compiler VERSION, not the identity of the binary that wrote it.
- Iterate warm. Cold builds are for a baseline, not for the edit loop.
