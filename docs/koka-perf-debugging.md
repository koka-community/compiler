# Debugging allocation and wasted time in Koka

Hard-won during the port's optimisation work. Ordered by how often each has
actually mattered, not by how interesting it is.

## Getting a profile you can trust

- **Build with `--cclinkopts=-Wl,-no_deduplicate`.** Identical-code folding
  merges kklib's many identical `static inline` refcount helpers into one
  symbol; the profiler then shows a `<deduplicated_symbol>` bucket and
  redistributes the rest. Worse, changing those helpers changes *what* folds, so
  an ICF build's before/after attribution is not like-for-like. One fix appeared
  to take refcounting from 32.6% to 1.6% of a profile; a no-ICF profile of the
  same binary showed 25.2%. **If a profile contains `<deduplicated_symbol>`, it
  is not usable.**
- Use the `time-profile` schema, not `time-sample` (raw addresses). Nodes are
  shared by `id`/`ref`; both must be resolved. `scripts/profile-report.py` does.
- Instruments' **Allocations template hangs** on these binaries (both processes
  at 0% CPU). Don't retry it; classify the time-profile leaves instead.
- `MIMALLOC_SHOW_STATS=1` reports pages/arenas but NOT cumulative bytes
  allocated -- that needs a mimalloc built with `MI_STAT>=2`.
- For the Haskell reference compiler, `+RTS -s -RTS` gives the MUT/GC split
  directly, in both CPU and elapsed time.

## Reading the numbers

- **High self time in `kk_block_refcount` means memory latency, not
  instructions.** It is a single header load. If it dominates, the fix is fewer
  live objects touched, not cheaper refcount ops.
- **Attribute alloc and free to the same owning caller** (`profile-report.py`
  does this). A caller doing both is a reuse candidate. A caller that only frees
  tore down something built elsewhere -- a different, harder fix.
- **But a caller that only frees does not prove reuse is impossible.** In a
  chain of list-to-list passes, if one pass copies, later passes can still reuse
  the copy. Check the generated core, don't infer from the profile.
- Reuse markers in `--showfcore`: `@reuse(`, `@assign-reuse`, `@alloc-at`,
  `@reuse-drop`. Their absence where you expect a `map`-shaped rewrite is the
  signal; their presence in quantity means it is at least partly firing.

## Things that quietly cost a lot

- **A `var` captured by a handler clause becomes a heap `kk_ref_t`.** Every read
  is a `ref_get` plus a dup of the payload; every write drops the old. Look for
  `kk_ref_alloc` in the generated C of a function you thought was using a local.
- **Effect operations are not free**: ~9.5ns each after two runtime fixes (13.5ns
  before). A loop performing operations per input *character* pays that per
  character. Cost is linear in operation count; monadic lifting adds nothing
  measurable.
- **`@open-none` wraps every operation** in `evv-swap-create0(); ..; evv-set(w)`.
  Two of those per operation.
- **Statics used to take the refcount slow path.** `RC_STUCK` is negative, so
  `rc <= 0` sent every dup/drop of a static out-of-line to do nothing. Fixed --
  but the *pattern* recurs: look for out-of-line calls whose body is a no-op.
- **Values that stay live block reuse.** Suspects, in order: `var`/`ref` cells,
  a reference captured in a closure or handler-operation body, and a value held
  for a later use that could be recomputed or moved earlier.

## Microbenchmarking traps

- **clang coalesces `dup`/`drop` pairs on the same block** and hoists them out of
  a loop, so a naive refcount benchmark reports the *fewest* operations as the
  slowest. Put each sequence behind `noinline`, pass the blocks in as opaque
  arguments, and end every variant in an indirect call.
- Keep benchmarks in the repo, not a scratch directory
  (`scripts/bench-effect-op.kk`, `scripts/profile-report.py`).

## Comparing against the reference compiler

`scripts/compare-warm.sh` bakes in every assertion below; use it rather than
ad-hoc timing. Five separate faults each produced a plausible wrong number:

1. **Mismatched artifacts.** Upstream's `-c` compiles every module's C to `.o`;
   the port did not for library targets. Assert equal `.c`/`.o` counts.
2. **Error-path comparison.** Upstream treats a `main`-less module as a program
   and fails synthesising `@main` -- fast. Use a `main`-bearing target.
3. **zsh expands globs at parse time**, so `rm -rf d; build; ls d/*/` reports
   "no matches" for a directory that exists by then. Count artifacts separately.
4. **Never time through `./koka`** -- the wrapper costs 0.19s per call for
   `stack exec which koka`. Use the direct binary.
5. **Assert exit 0.** A mangled flag bundle produced a 13ms "run" that looked
   like upstream short-circuiting a warm build.
6. **zsh does not word-split unquoted parameter expansions.** `F="-c -v0 ...";
   koka $F file.kk` passes the WHOLE string as ONE argument, and koka then
   reports `unrecognized option '- '` and exits non-zero. This bit twice: once
   producing a fake 13ms "early exit", once making a mtime test conclude that
   neither compiler relinks on a warm re-run (both do). Write flags explicitly,
   or use `scripts/compare-warm.sh`, which is `#!/bin/sh` and does split.

**Reading the reference compiler's budget.** `+RTS -s` counts only the Haskell
process's own CPU; subprocess (clang, ld) time is invisible to MUT/GC and shows
up as the gap between MUT *CPU* and MUT *elapsed*. For a warm rebuild of a
27-module closure: 0.263s own CPU, ~0.126s waiting on clang/link, 0.057s GC,
0.454s elapsed. Do not attribute the whole elapsed time to compiler work.

And: **read the code for behavioural questions.** "Does upstream skip
recompiling roots?" was answered by twelve lines of `src/Main/Run.hs`
(`buildcBuildEx (rebuild flags) roots {-force roots always-}` -- it does not
skip) after four timing runs had muddled it. Measure cost, not semantics.

## Backtraces from xctrace are not trustworthy; leaves are

Do not read an inclusive or call-tree view out of an xctrace Time Profiler
export of a Koka binary. Measured on the warm `scripts/probe-tiny.kk` rebuild,
which source-parses exactly ONE two-line file, the inclusive view attributed
**568ms (26% of the run)** to `syntax/parse/parse_program_from_string`, of it
277ms under a `discover_deps -> scan_deps -> parse_program_from_string` chain.
That chain never ran. Three independent checks:

1. `discover-deps` itself reports where each module's imports came from (`-v3`
   prints `discover: <module> (interface)` or `(source)`):
   **26/26 modules satisfied from `.kki`, zero `scan-deps` calls.**
2. Any real source parse lexes first. `compiler/syntax/lex` owns 85ms (3.8%)
   across the whole process -- nowhere near 26 std/core sources.
3. By INNERMOST owning frame, `compiler/syntax/parse` owns 58ms (2.6%).

A single `_trmc_` symbol also repeats up to 255x in one backtrace. The cause is
some mix of stale stack words and nearest-preceding-symbol resolution of local
symbols; either way the ancestor chain cannot be used for attribution, and a
plausible-looking stage table built on it is fiction.

What survives scrutiny is leaf-anchored: `SELF`, `CATEGORY` (alloc/free/refcount),
and `BY MODULE` (innermost owning frame). `scripts/profile-report.py` prints a
STACK TRUST CHECK and labels the inclusive section UNRELIABLE for this reason.

### There is no gprof on macOS

Verified, not assumed:

| route | result |
|---|---|
| `clang -pg` | compiles and links, emits **no `gmon.out`** |
| `gprof` via brew | not packaged (only `gprof2dot`, a viewer) |
| `-fxray-instrument` | compiles, but **no `xray-log.*`** is produced |
| `-finstrument-functions` | **works** (also `-after-inlining`, `-function-entry-bare`) |

So a genuine call breakdown has two viable routes, both immune to the
attribution problem above because neither walks the stack:

- **source-level phase timing** (what `KOKA_TIMING` / `tlog` already do) -- cheap,
  exact, and the right default;
- **`-finstrument-functions`** plus a small `__cyg_profile_func_enter/exit`
  hooks object, passed through Koka's `--ccompopts`. `call_site` gives real
  caller->callee edges, so this yields exact call counts and a true call graph.
  Verified working on this machine on a C test case. Cost is per-call overhead,
  so it measures counts and shape, not time.

## Concurrent interface loading has a latent race (readiness dispatch exposes it)

Wave barriers make every module in wave N+1 wait for the SLOWEST member of wave
N even when it imports only the fastest. Measured on this compiler's own
186-interface graph, weighting each node by interface bytes (interface parsing
runs at a uniform ~1MB/s):

```
sequential           71.7 MB   1.00x
wave-barrier floor   44.5 MB   1.61x
DAG critical path    32.1 MB   2.23x   <- barriers do 12.4MB (38%) of extra waiting
```

The wave-based pre-load measured **1.66x, i.e. exactly its own floor**, so the
barriers really are the binding constraint. Replacing them with readiness
dispatch (a module loads the moment its own imports are in, the rule
`compile-graph-rpc` already uses for compiles) moved the warm
`compiler/compile/build.kk` build:

```
preload  39.8s -> 26.5s wall   (1.66x -> 2.48x)
overall  80.0s -> 68.1s wall   (1.32x -> 1.58x)
```

**It was reverted anyway: the output stopped being reproducible.** Two
14-worker runs produced different entry artifacts (`@unroll-lift-imports-of-kki@442@0`
vs `@442@443`), roughly one run in three or four. Established by measurement, in
this order:

| variant | runs | result |
|---|---|---|
| preload OFF (sequential loads) | 4 | identical |
| wave barriers (committed) | 4 | identical |
| readiness dispatch | 5 | **3 distinct hashes** |
| readiness, `KOKA_MAX_WORKERS=1` | 2 | identical |

Two theories were tested and BOTH refuted, so do not retry them:

1. *Readiness gated on direct imports is too weak* -- `restrict-to-closure`
   grows its keep-set over each entry's CORE imports, a flattened superset of the
   lexical ones. Gating on the full transitive lexical closure instead: still
   nondeterministic.
2. *The env picks up unrelated modules that merely finished early* -- building
   each env from the module's own closure alone, never from "everything loaded
   so far": still nondeterministic.

What the evidence leaves: every run loads all 185 modules with 0 skipped, the
returned map is in canonical (wave) order, and the env is closure-only -- yet a
loaded module's CONTENT still varies. That points at shared mutable state in the
load path itself (the class in `parallel-shared-mutable-globals`), which waves
merely mask by running 2-7 loads at once where readiness keeps 14 saturated.

**So the committed wave-based pre-load is not proven safe, only not-yet-observed
to fail.** `KOKA_NO_PRELOAD=1` is the escape hatch. Finding the shared state is
the prerequisite for any further parallel-loading work -- and probably for the
cold-build nondeterminism in `[[cold-build-nondeterminism]]` too, which has the
same signature (an id shift in a generated name).

## Debugging reference counting

Refcounting is the largest single category in every Koka profile we have taken
(20.9% self time on the warm rebuild, against 15.3% for `free` and 5.1% for
`alloc`). These are the techniques that have actually produced answers here,
with the traps that produced wrong ones.

### Read the category split before anything else

`scripts/profile-report.py` prints `CATEGORY` (alloc / free / refcount) from
LEAF frames. Read it first, because it reframes the problem:

- **alloc is usually NOT the cost.** On the warm rebuild every hot
  `common/parse` frame allocates 0-2ms while freeing and refcounting 3-4x that.
  "Reduce allocations" is the wrong instinct; reduce dup/drop TRAFFIC and the
  cost of recursive frees.
- `kk_block_drop_free_recx` means a recursive free of a whole structure -- a
  tree dying, not a cell.
- High `kk_block_refcount` self time is **operation volume, not memory latency**.
  A refcounted block is one the program is actively using, so it is cache-warm.

### Traps that gave plausible wrong numbers

1. **ICF (identical code folding) destroys attribution.** Always profile with
   `--cclinkopts=-Wl,-no_deduplicate`. Without it refcounting read as 1.6% when
   it was really 25.2% -- the linker had folded the refcount helpers into
   unrelated symbols.
2. **Never read an inclusive/call-tree view** -- see the section above; ancestor
   frames on Koka binaries are not trustworthy. Refcount attribution must come
   from leaves plus the innermost owning frame.
3. **Microbenchmarks get optimised away.** A C benchmark of dup/drop coalesced
   the pair and measured nothing. Use `noinline`, opaque arguments, and an
   indirect call, and check the generated assembly actually contains the calls.
4. **Small ints are unboxed**, so their "dups" are a fast no-work path. Do not
   count them as refcount traffic, and do not convert list elements to value
   types hoping to avoid it -- a value type in a list is boxed anyway.

### Where the traffic comes from

- **Effect operations.** A tail-resumptive handler op measured ~13.7ns against
  ~11ns for a direct call. Of that, dead `@open-none` evidence-vector swap pairs
  were 44% and refcounting only 17%. Two kklib fixes (inlining the sticky-refcount
  test and the evv-empty accessor) took an op from 13.5ns to 9.5ns and interface
  parsing by -14.6%.
- **Projection out of a shared structure.** Pulling a field out of a value that
  survives forces a dup of the field. This is why the case-of-known-constructor
  optimisation needed "occurs exactly once": substituting a field of a surviving
  value loses its dup.
- **Borrowing.** `parcBorrowApp` keys on `getParamInfos (getName tname)`, so a
  borrow annotation only fires when the callee is a known name at the call site.
  Borrow does NOT apply to effect-operation parameters (`^` is rejected there).

### Attribute allocation and free to a CALLER, not a leaf

`profile-report.py`'s `ALLOC vs FREE by owning caller` pairs both against the
nearest compiler frame. A caller doing BOTH is a reuse (FBIP) candidate: it tears
a value down and builds one straight after, so the block could be handed over
instead of returned to the allocator. A caller that only frees is not -- its
allocation happened elsewhere, which is a much harder fix.

Beware reading a handler frame as an allocation site: `parse_error_fs__handle`
shows 0ms alloc against 12ms free and 12ms refcount. It is where the parse state
DIES, not where it is born.

### RESOLVED: it was `std/core`'s global `unique()`

The nondeterminism above (readiness dispatch changing warm-build output) and the
separate cold-build divergence on `std/core/list`/`bytes`/`show` were ONE bug.

`compiler/core/unroll.kk`'s `unique-tname-from` named its generated wrappers from
`std/core`'s `unique()`, which is a process-global `ref<global,int>` bumped with a
non-atomic read-modify-write (and typed `ndet` for that reason). Every other pass
uses the per-module `unique` effect, and so does upstream (`Core/Unroll.hs` has
its own `instance HasUnique Unroll`). Fixed by using `new-unique()`.

**How it was found, which is the reusable part.** Bisect by fingerprinting, never
by reasoning about where a race "should" be -- four plausible theories were wrong:

1. fingerprint what a phase PRODUCES, and compare across runs, not across code
   paths (`scripts/load-race-probe.kk`);
2. when that showed loading was identical, fingerprint the INPUT to the next
   phase (`KOKA_ENTRY_FP=1`) -- identical input, differing output localises the
   bug to one function;
3. then fingerprint after EVERY pass inside it (`KOKA_UNIQ_TRACE=1` in
   `core-optimize`) -- the first pass whose fingerprint diverges is the culprit,
   which took this from "somewhere in a 186-module concurrent build" to one line.

Unique COUNTERS were a red herring throughout: they matched at every checkpoint
in every run, precisely because the offending ids never came from them.

And self-test any hand-rolled hash. The first checksum used `^` as bitwise xor,
which Koka's `^` is not; it could not distinguish strings that plainly differed,
and briefly "proved" that types were identical when they had not been compared at
all. `PROBE_SELFTEST=1` now checks it.
