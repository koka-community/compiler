# Debug hooks

The port carries a handful of `KOKA_*` environment hooks that upstream does not
have. All of them are **read-only and inert unless set** — none changes
generated code, and none produces output on the default path. Anything that
*did* change generated code has been retired (see below).

## Core dumps

Upstream exposes `--showicore` / `--showcore` / `--showfcore`; these hooks dump
at finer-grained points that upstream has no flag for.

| var | dumps | file |
|---|---|---|
| `KOKA_SHOW_RAWCORE` | core straight out of the desugarer | `compile/type-check.kk` |
| `KOKA_SHOW_TCCORE` | core after type checking | `compile/type-check.kk` |
| `KOKA_SHOW_CORE` | full core with definition bodies | `main/driver.kk` |
| `KOKA_SHOW_FCORE` | final core handed to the backend | `compile/code-gen.kk` |
| `KOKA_SHOW_PREBOX_CORE` | C backend, before boxing | `backend/c/from-core.kk` |
| `KOKA_SHOW_BOX_CORE` | C backend, after boxing | `backend/c/from-core.kk` |
| `KOKA_SHOW_PARC_CORE` | C backend, after Perceus | `backend/c/from-core.kk` |
| `KOKA_SHOW_FINAL_CORE` | C backend, final | `backend/c/from-core.kk` |

`KOKA_PARSE_CONTEXT` adds source context to parse errors (`common/parse.kk`).

**Trap:** `--showcore` (and these) dump *every module compiled in that run*, so a
second invocation reusing the first's cache shows only the newly-built module.
When comparing against the reference compiler, give every module its own fresh
`--buildtag` or the numbers are meaningless.

## Measurement

| var | effect | file |
|---|---|---|
| `KOKA_TIMING` | per-phase timings | `compile/build.kk`, `main/driver.kk` |
| `KOKA_TRACE_ORCH` | orchestrator trace lines | `compile/build.kk` |
| `KOKA_CC_DEBUG` | echo the C compiler/linker command lines | `compile/link.kk` |

`KOKA_TIMING` measures **CPU** time (`clock()` sums across threads), not wall
clock — do not use it to compare parallel against sequential.

## Operational knobs

These change scheduling, not output.

| var | effect | file |
|---|---|---|
| `KOKA_NO_PARALLEL` | sequential module build | `main/driver.kk` |
| `KOKA_WAVE_ORCH` | wave-barrier orchestrator instead of RPC | `main/driver.kk` |
| `KOKA_MAX_WORKERS` | worker count | `main/driver.kk` |
| `KOKA_CC_JOBS` | parallel C compile jobs | `compile/link.kk` |

## Retired

- `KOKA_NO_GEN_INLINE`, `KOKA_NO_CTAIL`, `KOKA_NO_PRIM_INLINE` — A/B bisection
  aids that bracketed optimization passes. An env var that silently changes
  generated code has no place in a drop-in upstream replacement, so those
  passes now run unconditionally as upstream does.
- `KOKA_TARGET` — selected the C backend. The default target is now C/libc
  exactly as upstream (`flagsNull`'s `targetPlatformC64`); `--target=` is the
  only way to change it.
- `KOKA_DUMP_STAGES` — per-simplify-iteration file dumps, removed earlier.

## Build gotcha: `extern import c file` is not a staleness input

A module's staleness is computed from its `.kk` mtime. The C named by
`extern import c { file=.. }` is INLINED into the generated C, and editing it
does **not** invalidate the module — the stale `.o` is reused and the change
silently does nothing. `touch` the `.kk` (or `--rebuild`) after editing an
inlined C file.

This cost real time while debugging `compiler/lsp/stdio-inline.c`: three
successive fixes all appeared to fail because none of them was ever compiled.
