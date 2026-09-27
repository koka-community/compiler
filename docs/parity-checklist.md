# Upstream parity checklist

A pass-by-pass comparison of this port against the upstream Haskell reference
compiler (`~/koka/.worktrees/dev-compiler/src`), done 2026-08-18. Purpose: a
working checklist of known differences to iron out, not a bug tracker for
things already fixed — see `TODO_porting.md` for the chronological session
log and per-file sync-baseline table this complements.

Each item is classified:
- **INTENTIONAL DIVERGENCE** — deliberate, verified equivalent or a
  documented simplification; no action needed unless noted.
- **POSSIBLE INFIDELITY** — a real behavioral-risk gap; the port does
  something different from upstream in a way that could produce wrong output,
  not just different internal structure.
- **UNPORTED** — a whole upstream pass/check/feature with no port counterpart.
- **UNCLEAR** — needs a follow-up read before it can be classified; flagged
  rather than guessed at.

Every item below was checked by reading both sides directly (not inferred
from commit messages or comments alone), except where a line-count budget
forced a narrower "spot check, not exhaustive" scope — those are called out
explicitly so they aren't mistaken for a clean bill of health.

## Priority summary

**Current sweep (2026-08-30): 423 PASS / 17 SKIP / 2 MISMATCH.**
`scripts/test-runner.kk`. The port self-hosts: it compiles itself, and the
stage-2 binary compiles and runs programs. All 74 upstream CLI options are
recognised (`--host` is the only absentee and is commented out upstream too).
The 17 skips mirror upstream's own `config.json` excludes exactly.

`vendor/koka/lib` is the only default std library search root (matching
upstream's own `<shareDir>/lib` exactly -- `options.kk`'s
`process-initial-options`); koka-community/std is no longer included by
default anywhere and must be added explicitly with `-i<path>`. Module
resolution (`build.kk`'s `resolve-module-name`/`relative-fallback-dir`)
computes a relative import's search root from the importing file's own
DECLARED name (segment count), matching upstream `dc11bd31a` exactly.

Closed since the 2026-08-19 entry (418/17/6):

- **The four `async/*` mismatches** (`bchannel`, `bchannel-multi`, `xthread`,
  `xthread-stress`). Two root causes, both now fixed: `discover-deps`'s
  pre-scan parsed with the wrong target platform (fixed by threading `fl.tpl`
  through `discover-deps`/`scan-deps`/`parse-program-from-string`), and the
  port's DEFAULT TARGET being JS with a `flags-c` preset that set
  `C(CDefault)` -- a value `match-target` can never match against a
  `[host=libc|jsnode]` conditional import, since it treats CDefault as a
  wildcard only on its LEFT side. The struct default is now C/LibC/platform64
  as upstream's `flagsNull`, and `KOKA_TARGET` is gone.
- **The `compile-graph-rpc` concurrency bug.** Re-verified 2026-08-23 as
  FIXED, not merely masked: warm and cold caches, default worker count and
  `KOKA_MAX_WORKERS=1`, on `std/async/thread` and `std/async/channel`, plus
  every self-compile of the whole 100-module compiler -- all clean through
  the default RPC orchestrator. It was cured by the cross-thread fixes landed
  earlier (module-init CAS guard, `kk_ref_swap_borrow` shared-marking,
  thread-safe `delay`/`once`) together with the `isolate` type-inference
  soundness fix. `KOKA_NO_PARALLEL=1` is no longer needed.

Remaining mismatches:
- `cgen/specialize/recursive-arg.kk` -- one lifted helper's signature
  differs from upstream's (an internal monadic-lift decomposition
  difference, not a program-output difference; confirmed both produce the
  same runtime output).
- `medium/allsamples.kk` -- NOT a compiler defect; it PASSES under upstream's
  own conditions. Two harness gaps: (1) the sweep never puts the upstream root
  on the include path, where upstream finds `samples/all` via cwd (`.`);
  (2) warnings are emitted when a module is COMPILED, not when loaded from
  cache -- upstream's suite pre-compiles and runs WARM against a persistent
  `--buildtag=test`, the sweep compiles every test cold in a fresh per-worker
  buildtag. Measured on the port: cold = 5 warnings, warm = 0. With
  `-i<upstream-root>` on a warm buildtag the output matches the fixture
  exactly. (The older explanation here blamed cached `samples_*.o` from the
  `.koka-runtime` cache; that cache has since been removed entirely.)

### RESOLVED: the `cgen/specialize/*` cluster was a stale cache, not a port bug

12 of the original 14 default-build failures traced to `.koka-runtime`'s
`std_core_list.kki` (and siblings) missing `Core.Unroll`'s `@unroll-*`
helper wrappers for std lib's recursive functions (`foldl`, `(==)`, `cmp`,
`reverse-acc`, ...). Those wrappers only get generated when std lib is
compiled at `-O1` or higher; the live cache had apparently been rebuilt at
some point without `-O1` (this exact mistake happened at least twice before,
per `TODO_porting.md`'s 2026-08-06 session log and the
`port-extra-monadic-lift`/`runtime-interfaces-not-reproducible` project
memories). Without the pre-unrolled helper, `specialize.kk` falls back to
inlining `foldl`'s raw recursive body directly, which needs one extra
monadic-lift wrapper upstream doesn't — the "extra monadic lift" symptom
several session notes had flagged as a suspected fidelity bug.

**`specialize.kk`, `unroll.kk`, and `monadic-lift.kk` were all read
side-by-side against upstream during this investigation and are faithful —
this was never a bug in any of the three.** Fixed by rebuilding the cache
with `-O1` explicit (verified: a rebuild without it produces a
`std_core_list.kki` with ZERO `@unroll-*` content; with `-O1`, 261 matches).
Cannot regress again: the foreign cache this depended on is gone, and every
build now compiles std lib itself at the same optimization level as the rest
of the program.

### RESOLVED: `pub-import-closure`'s "missing `std/num/int32` init" theory was WRONG — real bug was a type-synonym scan-count miscalculation (`kind/repr.kk`, commit `eb0274e`)

Chasing the `KOKA_STDLIB_FROM_SOURCE=1` segfault (`std/time/timestamp`'s
`@init()` crashing) initially pointed at `pub-import-closure` (a missing
`std/num/int32` in a module's import-closure list). That theory did not
survive direct `lldb` inspection at the crash frame: both suspected globals
(`kk_std_num_ddouble_zero`, `kk_std_num_int32_zero`) were validly
initialized at the crash point. The REAL bug: `kind/repr.kk`'s
`extract-datadef-type` (used to classify a constructor field as raw-value
vs. boxed/scannable, for GC scan-count purposes) didn't expand type
SYNONYMS before matching -- `Timestamp`'s `since: timespan` field (where
`timespan` aliases `ddouble`) fell through to `Nothing`, defaulting to
"boxed/scannable" instead of resolving through the alias to `ddouble`'s real
raw-value representation. The wrong scan count gets baked into the
constructor's `kk_block_alloc_at_as(...)` call; `kk_block_mark_shared_rec`
then reads 16 bytes of raw struct data as if it were a pointer field and
segfaults. One-line fix (`tp0.expand-syn` before the match, matching
upstream's `case expandSyn tp of ...`). Verified:
`KOKA_STDLIB_FROM_SOURCE=1` sweep 388/17/36 -> 413/17/11 (25 more tests
passing -- this one bug was blocking a wide swath of std-from-source tests,
not just ones directly touching `Timestamp`).

`pub-import-closure` itself is UNCHANGED by this -- still believed to have
a real completeness issue (see "Module system / build / linking" below for
what's still suspected), just not the cause of THIS particular crash. Its
priority is downgraded since no currently-failing test is confirmed to
implicate it anymore.

### UPDATE (same day, third pass): two more real fixes landed

- **Relative-import resolution** (`compile/build.kk`, `main/driver.kk`,
  commit `bf446ca`): std lib files with no explicit `module X` declaration
  write locally-relative imports (`std/async/thread.kk`'s `import
  async/async`, resolving to `std/async/async`). `resolve-module` now
  retries against a fallback directory (one level above the importing
  file's own containing directory, matching upstream's `moduleNameResolve`
  `relativeDir` mechanism, reverse-engineered by direct tracing of the
  reference compiler since the Haskell source alone didn't make the exact
  arithmetic obvious). Fixes `async/async`/`async/internal` resolution
  outright. `KOKA_STDLIB_FROM_SOURCE=1` sweep: 388/17/36 -> 416/17/8
  (also fixed default-build's `jsgen/err.kk`, apparently coincidentally --
  confirmed separately flaky, not caused by this change).
- **`c-link` retries a missing `.o` instead of silently failing** (`link.kk`,
  commit `75df771`): `c-link` called the batch `compile-objs` helper
  directly instead of going through `compile-c-objs`'s existing
  retry-with-real-diagnostics logic, so a `.o` the batch silently dropped
  only ever surfaced as a cryptic "no such file" at link time. Now retries
  singly and surfaces the real compiler error. This didn't fix either
  underlying failure, but turned two opaque failures into their real
  causes (see below) -- a real diagnostic improvement, not a regression:
  sweep counts unchanged within measured run-to-run noise.

**`async/*` (4 tests) — current state (2026-08-19).** Resolution itself is
correct: koka-community/std's own (now-deleted) `async` subtree is gone, and
`vendor/koka/lib` is the sole default std root, so there is no longer a
two-tree collision to reason about. `relative-fallback-dir`
(`compile/build.kk`) computes each module's relative-import root from its
own declared name's segment count, matching upstream `dc11bd31a` exactly,
and `resolve-module`/`compile-graph`/`compile-graph-rpc` all alias an
as-written relative import (e.g. `async/internal`) to the same map entry as
its canonical name (`std/async/internal`) so every downstream lookup keyed
either way succeeds. What's left is two independent, unrelated things:
- **A genuine `compile-graph-rpc` concurrency bug**, not a resolution bug.
  `KOKA_NO_PARALLEL=1` compiles all four past name resolution cleanly, down
  to just the `timer-setup` gap below; the default parallel orchestrator
  segfaults on the compiler's own main thread (`lldb`: `EXC_BAD_ACCESS`,
  once a `kk_block_refcount` read on an implausibly small pointer, once a
  jump through a corrupted PC) whenever the stale-set includes
  `std/async/async` -- reproduces on a two-line file that only imports
  `std/async/thread`. A worker-thread stack-size theory (macOS defaults
  secondary pthreads to 512KiB) was tested with `uv_thread_create_ex` and an
  explicit 8MiB stack, verified baked into a from-scratch rebuild of both
  `.koka-runtime` and the compiler binary, and DISPROVEN (crash unchanged) --
  reverted. Root cause still open.
- **`async/api/uv/evloop.kk`'s `timer-setup` extern not visible from
  `async.kk`** (`identifier timer-setup cannot be found`) -- a real,
  independent gap, reproducible standalone under `KOKA_NO_PARALLEL=1`.
3. **`lib/slice.kk` (1 test) — RESOLVED (2026-08-19), commit `b806480`.**
   Ported upstream's `copyCLibrary`/`searchCLibrary` (Compile/CodeGen.hs)
   into `compile/link.kk`: for each `extern import c { library="X"; ... }`
   declaration, search already-installed system library paths (platform
   defaults + `--cclibdir`) and derive the matching `include` dir the same
   way upstream does (`.../lib/libX.a` implies `.../include`). Only this
   strategy is ported -- vcpkg/conan auto-install stays unported, a
   separately-scoped, much larger undertaking -- but it covers the common
   case (a dev-installed system library, e.g. Homebrew's `pcre2`) without
   needing either package manager. Verified: the produced `lib_slice`
   binary runs and its output matches upstream's fixture exactly; both
   sweeps clean of this failure now.
4. **`medium/allsamples.kk` (1 test)**: RESOLVED as a harness issue, not a
   compiler defect -- the port PASSES it under upstream's own conditions.
   The port compiles the whole `samples/` tree itself now (the reference-built
   `.koka-runtime` cache that used to supply it is gone). Two gaps remain on
   the sweep side: it does not put the upstream root on the include path
   (upstream finds `samples/all` via cwd), and it compiles every test cold in
   a fresh per-worker buildtag where upstream pre-compiles and runs warm.
   Warnings are only emitted when a module is COMPILED -- cold = 5, warm = 0
   -- so a cold run carries 13 warning lines the warm-generated fixture does
   not have. With `-i<upstream-root>` on a warm buildtag: exact match.
4. `cgen/specialize/recursive-arg.kk`, `jsgen/err.kk` are the same
   already-accepted cosmetic/flaky exceptions as the default build.
   - `cgen/specialize/recursive-arg.kk` is the same already-accepted
     cosmetic exception as the default build.
2. **`effect-extends` singleton-pattern over-match** (`type/type.kk:551-555`)
   — real and worth fixing, but **not currently linked to any known failing
   test**; a live-but-unobserved risk. One-line pattern tightening, low cost.
3. **`@cctx-setcp` C-backend special case unported** (`backend/c/expr.kk:765`)
   — same reasoning: real, but no currently-failing test exercises it. Worth
   a quick check of whether `ctail.kk`'s context-path specialization ever
   fires on the sweep before investing more here.
4. **`Core.Check` (core well-formedness checker) entirely unported — next up
   per project owner's direction.** Doesn't cause any CURRENT test failure by
   itself (it's a missing safety net, not a bug generator), but would have
   made the specialize-cluster investigation above much faster by catching a
   real Lam/TypeLam-shape mismatch at the point it's introduced rather than
   requiring a multi-hour trace through 5 optimization passes plus the
   runtime cache to rule each one out. See "Core optimization pipeline"
   below for what upstream's version checks and where it's invoked.
5. **Upstream's 2026-08-15 "unique typevar id" fix in `Core/Parse.hs`
   (`eae2ea61a`) not ported** — may already be subsumed by the port's own
   differently-shaped fix for a related symptom
   (`incremental-raw-tyvar-root-cause`, marked SOLVED in project memory), but
   unverified against upstream's actual regression tests (`test/cgen/specbox*.kk`,
   which aren't in the current sweep corpus — worth adding them).
6. **`Core.CheckFBIP` wiring is unclear** — file exists, a comment claims it's
   unported; contradiction unresolved. No known failing test implicates this.
7. Lower-risk / currently-inert items (the `unify-labels` TODOs per the note
   above, arity-guard asymmetries in `unroll.kk`, diagnostic-text/position
   differences, `TODO_porting.md`'s stale `kk_box_mark_static` entry) are
   listed in their sections below for completeness but don't need urgent
   attention — none are implicated in a currently-failing test.

### Parallel cross-thread races — RESOLVED
Three separate cross-thread races in parallel compilation were found and
fixed: a module-init guard, a build-type mismatch in the (since-removed)
foreign object cache, and `std/os/env.kk`'s `delay`-memoized `environ`/`argv`
caches (the same class as the earlier `lex.kk` `reserved-names` bug, fixed
upstream in `vendor/koka`). Verified 6/6 clean.

### `--buildhash` is parsed but never consulted — OPEN
`useBuildDirHash`/`--buildhash`/`--no-buildhash` (`options.kk:187,462`) is
declared and parsed but never read. `build-out-dir` names directories purely
by `buildTag`, with no content/flag hash, so two invocations sharing a
`buildTag` but differing in other flags (include paths, etc.) can silently
collide into one cache directory. Worked around so far with per-worker
buildtags in the sweep harness rather than fixed at the root.

---

## Parsing / syntax

### Upstream's Aug-15-2026 "unique typevar id" fix — NOT APPLICABLE (user judgment, 2026-08-23)
- The port generates unique type-variable ids through the `unique` EFFECT, not
  by threading a counter through a parse env, so it never had the aliasing
  upstream's `puniqueId`/`freshIds`/`envExtendWithId` scheme fixes. Confirmed
  empirically: `test/cgen/specbox.kk` produces the expected `1 2 99` on a cold
  cache. Left below for the record; no action.

#### (original entry)
- **Upstream**: commit `eae2ea61a` ("Fix parse assigning non-unique typevar
  ids", 2026-08-15) adds a `puniqueId` counter to `PState` and replaces
  `Core/Parse.hs`'s env-only type-variable binding — which reused the SAME
  env across multiple `many (inlineDef env)` / `semis (defDecl env2)` items,
  causing overlapping typevar ids — with a state-threaded
  `freshIds`/`setUniqueBase`/`envExtendWithId` scheme. Regression-tested via
  `test/cgen/specbox*.kk` (boxed/unboxed parameter mismatches from colliding ids).
- **Port**: `compiler/common/parse.kk`/`compiler/core/parse.kk` has no
  `puniqueId`/fresh-id-supply equivalent — still uses the older
  `env-extend`/`env-extend-local` approach. This is a DIFFERENT, narrower fix
  than the one already landed for a related symptom.
- **Classification**: UNPORTED — postdates the 2026-07-23 sync baseline, not
  a previously-deferred item.
- **Why it matters**: looks directly related to this project's own
  `incremental-raw-tyvar-root-cause` finding (marked SOLVED via the port's
  own narrower fix, not by porting this actual upstream commit). Needs
  verification: does the existing port fix fully subsume upstream's
  `freshIds`/`envExtendWithId` scheme, or only a subset of the cases upstream's
  `specbox*.kk` tests exercise? If not, interface typevar ids can still
  collide across declarations sharing an env, silently producing wrong
  boxed/unboxed specialized signatures downstream. **Action**: port
  `test/cgen/specbox*.kk` if missing from the sweep, diff against the actual
  commit rather than assuming equivalence.

### Parsec farthest-failure error merging — not ported (known, still open)
- Port's `parse-choices` reports the LAST/outermost failure instead of
  merging expectation sets at the farthest input position (Parsec's `<|>`
  semantics). Wrong-position errors on `kind/wrong/type7`,
  `syntax/wrong/braces1-2`, `medium/allsamples`.
- **Classification**: POSSIBLE INFIDELITY — error text/position only, doesn't
  affect successful compiles.

### Build-error message for missing module — differs from upstream (known, still open)
- Upstream: `build error: could not find module: X (imported from Y)` +
  search path. Port: bare parse error, null range. `static/wrong/module2`.
- **Classification**: POSSIBLE INFIDELITY — common failure mode (typo'd
  import), affects error golden tests and diagnostic quality.

### alex-koka single-regex string lexer over-munch — shared tooling bug, not compiler fidelity
- Affects `test/lib/json-test.kk` via the alex-koka fork's DFA generation;
  does NOT affect the compiler's own `syntax/lex.kk` (confirmed 68/68 on the
  parse sweep, different lexer mode).
- **Classification**: UNCLEAR — real but out of scope for compiler parity per se.

### Layout, semicolon insertion, fixity parsing, unicode/prefix-postfix ids, buildcfg guards — confirmed faithful
- Spot-checked against the most recent relevant upstream commits and found
  matching, including confirming that `identifyModules`/`scanImports`/
  `replaceModules` are DEAD CODE upstream too (not a port gap despite
  `layout.kk` being notably shorter than `Layout.hs`).
- **Classification**: INTENTIONAL DIVERGENCE / confirmed parity.

### Fixity error-message text differs cosmetically
- "The precedence must be between 0 and 100" (upstream) vs "fixity must be
  between 0 and 100" (port). No behavioral difference, shows up in exact-text
  golden comparisons.

---

## Kind / type inference, effect handling

(Upstream `HEAD` is one commit ahead of the port's recorded `Infer.hs` sync
baseline — a cosmetic fix already present in the port — so "already synced"
claims for handler/effect-row logic were re-verified directly here, not just
trusted from prior notes.)

### `effect-extends` singleton-pattern over-match — live infidelity risk
- **Upstream** (`Type/Type.hs:703-708`): the "keep as a bare synonym" special
  case is guarded by an EXACT SINGLETON list pattern `[lab@(TSyn...)]`.
- **Port** (`compiler/type/type.kk:551-555`): `Cons(lab as TSyn(...), _)`
  matches ANY non-empty list whose HEAD is a matching TSyn, not just a singleton.
- **Classification**: POSSIBLE INFIDELITY — real, not theoretical.
- **Why it matters**: when called with 2+ labels whose FIRST element is an
  unexpanded effect-type-synonym and the tail is `effectEmpty` (plausible:
  labels are name-sorted, so an early-alphabetic user effect alias can end up
  first; also plausible from `unify-labels`'s own diff-set reconstruction),
  upstream falls through and builds the full row; the port matches the
  special case and returns JUST `lab`, **silently dropping every other label
  in the row**. May be an unrecognized contributor to (or independent of) the
  already-documented "algeff/exn2 effect-alias display" divergence in
  `TODO_porting.md` (previously attributed only to display-time synonym
  loss) — worth re-investigating under this specific construction-time
  hypothesis.

### `unify-labels` GT-branch — port likely deliberately fixes an upstream bug (per user judgment)
- **Upstream** (`Type/Unify.hs:433`): `unifyLabels ls1 ll2 closed2 closed2`
  (GT case — BOTH args are `closed2`, discarding `closed1`; looks like an
  upstream typo).
- **Port** (`compiler/type/unify.kk:309`): `unify-labels(ls1, ll2, closed1, closed2)`,
  with the port's own inline comment: `// TODO: In Haskell it uses closed2 in both places!`
- **Classification**: user (project owner) judges this is likely an
  intentional correction, not an accidental infidelity — demoted out of the
  priority list on that basis (see Priority summary). Downgraded from
  POSSIBLE INFIDELITY. Still worth resolving the dangling `// TODO` to a
  documented decision rather than leaving it as an open question in the code.
- **Why it matters**: if it IS deliberate, no action needed beyond
  documenting it. If it turns out NOT to be deliberate, the two compilers can
  diverge on which unification error (or none) is raised for asymmetric
  closed/open effect rows when the mismatched label sorts before the
  recursion point — but this is no longer believed to be the case.

### `unify-labels` EQ/skolem-swap branch — same status as above
- **Upstream** (`Type/Unify.hs:443`): `unifyLabels ls2 ll2 closed1 closed2`
  (the `id1 >= id2` skolem-ordering branch).
- **Port** (`compiler/type/unify.kk:319`): `unify-labels(ls1, ll2, closed1, closed2)`,
  self-flagged: `// TODO: In Haskell it uses ls2!`
- **Classification**: same as the GT-branch item above — likely intentional
  per user judgment, demoted from POSSIBLE INFIDELITY. Resolve the `// TODO`
  to a documented decision either way.
- **Why it matters**: fires only for two distinct skolem scope-labels with the
  same name (multiple handler instances of the same effect in scope) — one of
  the trickiest corners of the type system, currently un-investigated.

### Handler inference, mask/override/inject desugaring — faithful, verified
- `infer-handler`, clause construction per operation sort, cfc-lub,
  linearity check, and the mask/override-to-`Inject` rewrite all verified
  line-by-line matching, including upstream's own dead code paths being
  faithfully reproduced as equally-dead rather than diverging.
- **Classification**: INTENTIONAL DIVERGENCE, no gap found.

### Argument matching, subsumption, generalization/isolation, alias re-synonymization — faithful
- `match-arguments`, `subsume` (including the previously-fixed substitution
  composition order), `generalize`/`isolate`/`improve` (heap-effect isolation),
  `normalizeX`/`nicefy-effect`/`realias-type` (io/st/pure/async alias
  re-synonymization) — all read closely, all match upstream structurally.
- **Classification**: INTENTIONAL DIVERGENCE, no gaps found.

### Implicit-parameter deferred-commit protocol — re-confirmed correct
- `resolve-implicit-arg`/`commit-implicit-constraints` re-checked directly;
  the "only the winning resolution registers evidence, exploration must be
  side-effect-free" invariant holds on both sides.

### Coverage caveat
- Sampled/critical-path functions checked directly; roughly half of
  `Infer.hs` (2764 lines vs the port's ~2400 combined across `infer.kk` +
  `infer-support.kk`) — record/pattern inference, branch/case inference
  internals, App-argument-matching internals beyond what's covered above —
  was NOT independently re-diffed this pass. The two `unify-labels`
  divergences and the `effect-extends` bug are the highest-value NEW findings
  here; a full function-by-function diff of the rest is a reasonable
  follow-up if this area keeps surfacing bugs.

---

## Core optimization pipeline

### Pipeline order and presence — verified faithful
- Full sequence matches upstream step-for-step: unroll → inline(2x,
  hnd-filtered) → simplify → specialize → simplify → lift-functions →
  simplify → ctail → mon-transform → open-resolve → simplify(no-dup) →
  monadic-lift → inline(primitives) → simplify(unsafe) → simplify(final) →
  uniquefy — including the "specialize can generate local recursive defs, so
  lift-functions must run after specialize" ordering constraint.
- **Classification**: INTENTIONAL DIVERGENCE, verified faithful.

### `Core.Check` (core well-formedness checker) — PORTED 2026-08-23
- `compiler/core/check.kk` (213 lines) is a direct port of `Core/Check.hs`,
  wired at upstream's three `coreOptimize` checkpoints ("monadic transform",
  "monadic lifting", "final") behind `--checkcore`, which was previously
  parsed and ignored. Default behaviour is unchanged: the flag is off by
  default upstream too.
- Divergences, all forced and documented in the file header:
  * upstream threads a `CheckEnv` reader record; the port keeps `liberalEff`,
    `allowPartialApps` and `currentDef` as ambient value effects and threads
    `gamma` explicitly. Nothing reads gamma in either compiler -- upstream's
    only consumer is `lookupVar`, called solely from the dead `findConstrArgs`
    -- so it is extended at every binder purely for structural fidelity.
  * `match` is renamed `type-match` (`match` is a Koka keyword).
  * `findConstrArgs` is not ported: its one call site is commented out
    upstream as well.
  * the mutually recursive walk needs an explicit closed effect alias
    (`check-eff`); with an open tail the REFERENCE compiler crashes with
    `internal error: Core.Core.splitTForall: Expected forall`. That is an
    upstream bug worth reporting separately.
- **Calibration matters before using this as an oracle**: upstream's own
  `--checkcore` emits 14 warnings on a hello-world (`kind error in type
  application`, `cannot unify (NoMatch)`), so a non-empty report is NOT by
  itself evidence of a port defect. The port emits 15 on the same file, in
  the same categories.
- **First real find, already fixed**: ten of the port's original fifteen
  warnings were `cannot unify (types do not match)` printing two IDENTICAL
  types (`hnd/htag<exn> =~ hnd/htag<exn>`). Not a `unify` bug -- the structural
  dump showed `TApp(TCon exn, [])` against a bare `TCon exn`.
  `open-resolve.kk`'s `ev-index-of` built `hndTp` with the raw `TApp`
  constructor where upstream uses `typeApp`, whose `typeApp t [] = t` case
  returns the head unchanged for a label with no type parameters. Semantically
  the same type, structurally different, so any pass comparing types by
  structure trips on it. Fixed to `hndCon.type-app(tpArgs)`; the port now
  reports 12 warnings against upstream's 14, with the unify failures down to
  3, matching upstream exactly. std/core open-insertion counts unchanged
  (bslice 84/84, hnd 15/15) -- `effect-offset` reads the head via `label-name`,
  which worked on either shape, so this was latent rather than miscompiling.
- **Remaining delta to diff when the checker is next used**: the port reports
  5 `expecting function type in application` where upstream's message text
  differs enough that the categories could not be matched by grep alone.

### `Core.CheckFBIP` wiring — RESOLVED 2026-08-23: ported AND wired
- `compiler/core/check-fbip.kk` is called from `type-check.kk:149`. The
  comment claiming otherwise was stale and has been corrected.
- **Classification**: RESOLVED, no gap.
- **Why it matters**: if the file is dead code, FBIP/borrow-checking coverage
  has a real silent gap letting malformed `fip`/`fbip`-declared functions
  through without the diagnostics upstream would produce. **Action**: check
  directly whether `check-fbip.kk` is actually called from `type-check.kk`'s
  pipeline.

### `unroll.kk`: Case-arity guard FIXED. The `bit8` bug was UPSTREAM, worked around.

- **Guard (fixed 2026-08-25)**: upstream matches `((Branch pats _):(_:_))` --
  at least TWO branches; the port matched one-or-more. The previous note called
  that inert; the reasoning was wrong, since `extract-nonrec-branches`'s overlap
  early-exit can return non-empty `recs` from a single branch. Now matches
  upstream. This was a separate latent bug and NOT the cause of `bit8`.

- **`bit8 = 0b000` — ROOT-CAUSED and FIXED UPSTREAM 2026-08-26.**

  **Cause: a unique-name collision between locally minted names and names baked
  into an inlined body imported from another module.** `Core/Simplify.hs`'s
  `topDown` beta rule renames parameters with `uniqueTName`, which is fresh only
  with respect to THIS module's counter. An inline body spliced in from another
  module carries binders minted by THAT module's counter, and both start from
  the same base (10000, see `runInfer`/`coreOptimize`). So the "fresh" name can
  already be bound inside the body, and the substituted occurrences are captured
  by it.

  Concretely: substituting `pad-left`'s parameter `s` minted `s@0@10011`, which
  is exactly the name `pad-left`'s own body uses for its `fill.string` local
  (minted when std/core was compiled and stored in `std_core_string.kki`). The
  inner binder captured the tail reference, so `... ++ s` returned the FILL:
  `show-binary(42,8)` = `"000"` instead of `"00101010"`.

  **Fix**: `uniqueTNameAvoiding`, which re-mints until the name is clear of the
  body's own binders (`boundNames`, added alongside since `bv` is not defined on
  `Expr`). Verified: the parameter now gets `s@10000`/`s@10007` and the tail is
  `s`; the original `pad-left`-based `show-binary` produces correct output for
  42, 1000 and -5.

  **How it was found.** The four "necessary ingredients" for the repro were all
  about reaching a SHAPE, yet a structurally identical repro stayed correct --
  which pointed away from "a rule mishandles this construct" and toward naming
  state. The decisive test was perturbing the unique counter WITHOUT changing
  the shape: adding one unrelated top-level definition ahead of `show-binary`
  made the miscompilation disappear entirely. That also explains why `-O1` and
  `--fno-unroll` "fixed" it (both change how many uniques are consumed) and why
  small repros never trigger: the collision needs the counter to land on a value
  a spliced body already uses.

  **Sweep after the fix**: 419 PASS / 17 SKIP / 1 TIMEOUT / 5 MISMATCH. The two
  apparently-new mismatches were checked individually and are NOT regressions --
  `cgen/mpat` produces exactly the expected output standalone, and `cgen/tail2`'s
  `0.25` vs `0@25` is the sweep harness's own sanitizer. Both, and the timeout,
  are the load-sensitivity documented elsewhere in this file.

  **Same fix applied to the PORT.** `compiler/core/simplify.kk` had both defects
  verbatim (`unique-tname` at the top-down beta rule; the missing body-binder
  check at the bottom-up one), which is expected -- it is a port of the same
  file. Both now match the fixed upstream. Verified by self-compile: the port
  builds itself and the stage-2 binary runs.

  **TODO -- separate repro needed for the BOTTOM-UP beta rule.** That rule keeps
  the parameter names and its guard checked only "parameter not free in the
  arguments", never "parameter not re-bound in the body". The missing check is
  now added in both compilers, but purely by reading: disabling the rule
  entirely did NOT change the `bit8` miscompilation, so it is a DIFFERENT latent
  bug with no known trigger. It needs its own repro before anyone treats the
  added check as validated -- a body that re-binds a parameter name, reached
  through the bottom-up path.

  **A better fix than either patch (not implemented).** Both patches harden one
  minting site each; the hazard is structural and will recur at the next site
  that mints names near spliced code. The root problem is that an inline body
  imported from another module carries binders from a foreign name space that
  overlaps the local one. Fixing it once, at the splice, is stronger: have
  `inl-lookup` (upstream `inlLookup`) alpha-rename the body's binders into the
  importing module's space before returning it, so no consumer can ever collide.
  This must be PER-SPLICE, not once per imported body: the same body is inlined
  at many sites in one module, so a single renaming would just move the
  collision (all copies would share the new names). It must also compose under
  nesting -- an inlined body can itself contain previously spliced bodies, so
  renaming has to cover the whole spliced result, not just the outermost layer.
  Note that upstream's existing `uniquefyDefGroups` after inlining does NOT do
  this -- it makes names unique within the group but never advances the counter
  past names embedded in spliced bodies, which is exactly why the collision
  survives it. Cost is one traversal per inlined body.

  **Port also made defensive**: `show-binary` no longer routes through
  `pad-left`, so building this repo with a compiler predating the upstream fix
  cannot reintroduce it.

### `monadic-lift.kk`'s `lift-expr` drops a 3-type-arg constraint that `lift-expr-inl` keeps
- Upstream requires the bind's `TypeApp` to carry exactly 3 type args in BOTH
  `liftExprInl` and `liftExpr`. Port's `lift-expr-inl` keeps this; `lift-expr`
  matches ANY arity. Currently inert (`nameBind`/`nameBind2` are always
  constructed with exactly 3 type params today), but an asymmetry between two
  sibling functions upstream keeps symmetric — would misfire if that
  invariant ever changes.

### "Extra monadic lift" bug (referenced from earlier project memory) — not independently confirmed
- Exhaustive grep across the repo found zero hits for this claim in
  `TODO_porting.md`, source comments, or `monadic-lift.kk`'s git log.
- **Classification**: UNCLEAR — either already fixed and the note was never
  persisted here, or needs re-verification against wherever it originated.
  The closest currently-real candidates are the two arity-guard findings
  above. **Action**: re-test directly (compare `--showfcore` output for a
  known-affected test between port and upstream) rather than trusting the
  prior claim as-is.

### `monadic.kk`/`Monadic.hs`, `monadic-lift.kk`/`MonadicLift.hs`, `inline.kk`/`Inline.hs` — high-fidelity, no other structural divergence found
- All match arms and magic constants (simplify iteration count `3`, dupMax
  `0`, inline cost threshold `4`) verified matching, including
  self-recursive/mutual-recursion inlining limitations being explicitly
  flagged in the port's own comments rather than silently diverging.
- **Classification**: INTENTIONAL DIVERGENCE (idiomatic boilerplate
  collapse via ambient effects instead of hand-rolled monads), no other gaps found.

### `ctail.kk` internals — not fully diffed, flagged as its own follow-up
- Call-site parameters and C-target gating verified matching, but the
  internal cctx-hole/extend/apply state machine (~600 upstream lines across
  `CTail.hs` + `AnalysisCCtx.hs`) was NOT diffed line-by-line. The port's own
  doc comment flags a deliberate structural deviation from importing
  `Core.AnalysisCCtx` directly.
- **Classification**: UNCLEAR — recommend a dedicated follow-up; ties
  directly to the `@cctx-setcp` gap found in the C backend (below).

### `specialize.kk` — pass-count/call-site parity confirmed, internals not fully diffed
- Both compilers call specialize exactly once per optimize run, no internal
  fixpoint loop in either. Full line-by-line diff of the ~600-650 line
  algorithm not completed — flagged as a follow-up if deeper fidelity is needed.

### `divergent.kk`/`Core.Divergent` — correctly excluded from the optimize pipeline in both
- Confirmed NOT a gap — runs elsewhere in both compilers (adjacent to type
  inference, to seed `<div>`), correctly absent from `optimize.kk`'s imports.

### Minor / doc-only
- `optimize.kk:7-9`'s module doc names the wrong primitive-inline env var and
  the wrong polarity (says opt-in via `KOKA_PRIM_INLINE=1`; code actually
  checks opt-out via `KOKA_NO_PRIM_INLINE`). Behavior is correct, comment is stale.
- Three debug-only env-var escape hatches (`KOKA_NO_GEN_INLINE`,
  `KOKA_NO_CTAIL`, `KOKA_NO_PRIM_INLINE`) don't exist upstream — inert when
  unset, but enlarge the port's config surface; a CI/dev env with one
  accidentally set would silently diverge from upstream.
- `optctailCtxPath && isC` re-AND at the `optimize.kk` call site duplicates
  logic already applied in `options.kk`'s derived-flags step — harmless
  (idempotent), just redundant.

---

### BuildContext query API — reviewed 2026-08-29, DIVERGED BY DESIGN

Upstream exposes 42 `buildc*` functions as a queryable facade over the build
context (`buildcGetRangeMap`, `buildcGetLexemes`, `buildcLookupTypeOf`,
`buildcPrettyEnvFor`, `buildcGetVisibleDefinitions`, ...); its language server
calls them and holds no compiler state itself.

The port inverts this. `compile/build-context.kk` exposes 12 functions, all
BUILD operations (`check-file`, `build-roots`, `compile-expr`) plus session
lifecycle. The QUERY surface lives in `lsp/state.kk`'s `doc` record, which
caches per document what upstream would ask the context for -- `rmap`, `prog`,
`ntypes`, `syns`, `gam` -- and handlers read it directly (e.g.
`d.rmap.rm/sort.find-at(p, lexemes)` in `lsp/definition.kk`, re-lexing on
demand instead of `buildcGetLexemes`).

CAPABILITY IS AT PARITY -- every `buildc*` capability probed has a home, and
`compile-expr` corresponds to `buildcCompileExpr`. STRUCTURE IS NOT: there is
no reusable build-context API, so a second consumer (REPL, docs generator,
another IDE front end) would have to duplicate `lsp/state.kk`'s caching rather
than call a facade.

Note that `build-context.kk` is also the ONLY compile-path module whose
signatures carry `async` -- the orchestration divergence and this API
divergence live in the same file. The port's build context is a BUILDER;
upstream's is a QUERYABLE CONTEXT.

Closing this is a refactor with no user-visible payoff unless a second consumer
is planned.

### JS backend — reviewed 2026-08-29, at parity

`backend/js/from-core.kk` is 838 lines against upstream's 1383
(`Backend/JavaScript/FromCore.hs`), which looked like a shortfall. It is not.
54 of upstream's 70 top-level functions have counterparts; of the 16 without:

- EIGHT are upstream's `Asm` monad (`newtype Asm a = Asm { unAsm :: Env -> St
  -> (a,St) }`): `runAsm`, `getInStatement`, `getModule`, `getPrettyEnv`,
  `withStatement`, `withTypeVars`, `withNameSubstitutions`, `newVarNames`.
  Effects here, so there is nothing to port.
- `extractExternal`/`genExternalExpr` are RENAMED, not missing: the port has
  `gen-expr-external` (applied call sites), `gen-wrap-external` (unapplied and
  partially-applied, incl. the `Var`/`TypeApp` `InfoExternal` cases), and
  `include-external`/`import-external` for declarations.
- `genTName`, `genDefName`, `genCommentTName`, `ppQName` are inlined/renamed.
- `debugComment`/`debugWrap` are GENUINELY ABSENT. They emit commentary into
  the generated JavaScript. Cosmetic; only worth porting if diffing generated
  JS against upstream becomes a fidelity target.

## C backend (PARC / reuse / codegen)

### Pass order, flag defaults/threading — verified faithful
- `genModule`'s box → parc → parc-reuse → parc-reuse-specialize sequence and
  all four PARC-related flag defaults/threading match upstream exactly.
- Note: `parcBorrowInference` is a dead flag in BOTH compilers (threaded
  through but never read by any pass in either) — don't mistake this for a
  missing pass; borrow info comes from `core/borrowed.kk` earlier in the
  pipeline in both.

### `kk_box_mark_static`/`kk_datatype_drop_small` — RESOLVED, but `TODO_porting.md` is stale
- Verified: `backend/c/expr.kk:152,155` and `dup-drops.kk:107` already emit
  these calls verbatim-matching upstream, and vendor/koka's pinned kklib DOES
  export both symbols now.
- **Action**: update/close the `TODO_porting.md` entry (~line 87) that still
  describes this as an open blocker pending a kklib submodule bump — it no
  longer reflects reality and could mislead a future auditor into thinking
  there's an active memory-corruption risk here.

### `@cctx-setcp` (TRMC context-path) C-backend special case — unported, live producer/dead consumer
- **Upstream** (`Backend/C/FromCore.hs:2033-2037`): a dedicated `genAppNormal`
  clause matches the `nameCCtxSetCtxPath` application and emits `kk_cctx_setcp(...)`.
- **Port**: `backend/c/expr.kk:765` defines the helper (`gen-cctx-set-ctx-path`)
  but it's NEVER CALLED — `gen-app-normal` has no matching clause. The
  PRODUCER side (`core/analysis-cctx.kk:148-152`, `make-set-ctx-path`) DOES
  still emit this node, tagged `InfoExternal("@cctx-setcp(#1,#2,#3)")`.
- **Classification**: POSSIBLE INFIDELITY.
- **Why it matters**: if `core/ctail.kk`'s TRMC-with-context-path
  optimization (on by default) ever constructs this node for a C-target
  program, the port falls through to the generic external-format path and
  emits the LITERAL TEXT `@cctx-setcp(...)` into the `.c` file — a compile
  failure at best, silent memory corruption at worst if ever mis-swallowed.
  **Unclear whether currently reachable by the test corpus** (may be latent)
  — needs a check of whether `ctail.kk`'s context-path specialization ever
  actually fires for programs the sweep currently exercises.

### `Parc.hs` vs `parc.kk` — verified faithful, no divergence found
- Deep read of last-use/drop insertion, borrowed-parameter handling,
  dup-at-field-access, guard-liveness, fuse/optimize-drop pipeline: matches
  upstream 1:1 in control flow and data shapes. This is the highest
  memory-safety-risk pass in the whole compiler and it checked out clean.

### `ParcReuse.hs`/`ParcReuseSpec.hs` — 1:1 structural match; reuse-credit semantics not fully verified
- Function-level correspondence confirmed by name listing.
- **Residual risk (UNCLEAR)**: the `available`/`reused` intersection/union
  semantics at branch-join points (`parc-reuse.kk:605-693`) — the subtlest
  part of the reuse pass (a reuse token is only safely "available" post-branch
  if available on ALL join paths) — were NOT diffed operator-by-operator
  against upstream's `Available`/`Reused` combinators. A bug here would
  manifest as writing into still-referenced/aliased memory (silent
  corruption, not a crash). Recommend a focused follow-up on just this
  ~100-line cluster.

### File-organization divergence — cosmetic
- Upstream: one `FromCore.hs` (2886 lines). Port: split across
  `constructors.kk`/`dup-drops.kk`/`expr.kk`/`helpers.kk`/`from-core.kk`. No
  behavioral risk, but makes future side-by-side auditing harder (as
  encountered doing this very review).

---

## JS backend

### `ValueBinder`'s `vrng` differs from upstream — POSSIBLE INFIDELITY

- Upstream's `inferDef` adds the inferred-result range-map entry at
  `endOfRange vrng`, and its own comment says that range ends at `)` -- the
  PARAMETER LIST. The port reads `vrng` from the same binder field, but its
  parser evidently stores the NAME's range there: traced at
  `fun annotated(y: int): int`, the port's `vrng` ends at column 13 (end of
  `annotated`) and the following lexemes are `(`, `y`, where upstream would see
  `:`, `int`.
- **Why it matters**: upstream's inlay-hint suppression for already-annotated
  definitions (`hasAnnot`) reads the two lexemes after that range. With the
  port's range that test can never fire, so every annotated definition would get
  a redundant `: <type>` hint. `compiler/lsp/server.kk` works around it by
  skipping a balanced parameter list first, but the underlying divergence
  remains and any other consumer of `vrng` inherits it.
- **Action**: find where the parser fills `ValueBinder`'s range field for
  function definitions and compare against upstream's `Syntax/Parse.hs`.

### Language server: inlay hints — DONE (partial)

- `textDocument/inlayHint` implemented from the range map, which already carried
  everything needed; `find-in`, `lexemes-from-pos` and
  `previous-lexemes-reversed` only had to be made `pub`.
- Implemented: inferred result types on unannotated definitions (upstream's
  `typeHint`) and the hints the type checker emits directly (`RIInlayHint`,
  e.g. eta-expanded parameter names -- upstream's `generalHint`).
- NOT implemented, both additive: qualifier hints (need `missingQualifier`) and
  implicit-argument hints (need `RIImplicits`' shorten callback rendered against
  a pretty env). The three `koka.languageServer.inlayHints.*` client settings are
  also not yet honoured -- `workspace/didChangeConfiguration` is acknowledged but
  its payload is ignored.
- One deviation, commented at the site: `lexemes-from-pos` drops until a lexeme
  CONTAINS the position, but a hint's range is zero-width and sits between
  tokens, so nothing contains it. The handler looks for the first lexeme
  starting at or after the position instead.

### Language server: request handling during a compile — partly done

- **Coalescing, precisely**: there is NO timer and no debounce. `didChange`
  marks a document dirty and returns; dirty documents are compiled when the
  message buffer next drains. So a burst arriving in one read coalesces to one
  compile, but a burst straddling a drain boundary produces two (measured: 8-10
  rapid edits -> 2 compiles). A client pacing edits slower than a compile takes
  would get one compile per edit.

- **Two strands** (`interleaved`): a reader pushing framed payloads onto a
  `channel`, and a worker draining it. What this buys is real but narrower than
  it sounds: the reader keeps draining stdin during a compile (so the OS pipe
  never fills and the client is never blocked writing) and edits are OBSERVED
  during a compile, which is what makes cancellation possible. It does NOT make
  requests answerable during a compile -- the worker strand both compiles and
  handles messages, so a request arriving mid-compile waits for it (measured:
  first hover during a cold compile 8.75s, subsequent 0.2s). Answering during a
  compile needs the compile to be its OWN strand that the worker awaits while
  still polling the inbox.

- **A `Core.Unroll`-independent orchestrator bug, found and fixed here.** An
  earlier attempt deadlocked, and the cause was NOT what it first appeared:
  `compile-graph-rpc`'s serve loop stopped on "nothing pending and nothing
  waiting", which is trivially true BEFORE any worker has registered. With
  cancellation signalled early the loop exited immediately, leaving every
  spawned worker blocked on a request nobody would receive, and the run then
  hung on `done-ch`. Now the loop runs until every worker has been released
  (`released >= n-workers`). Verified separately that a full compile, and the
  RPC/spawn-thread pattern generally, run fine inside `interleaved` -- the
  architecture was never the problem.

- **Cancellation checkpoints.** Originally there were three, all OUTSIDE a
  module's own compile: the orchestrator picking the next module, the
  orchestrator releasing workers, and `check-file-ex` before the entry compile.
  That is not enough for a language server: when one file is edited and every
  dependency is cached, the orchestrator has nothing to dispatch, so the entry
  compile is the only work there is -- and it sat entirely after the last
  checkpoint as one atomic unit. Type inference dominates it (measured 133ms of
  a 157ms entry compile; optimize 4ms, codegen 20ms).

  `compile-module` now takes a `cancelled` predicate polled BETWEEN phases:
  before type inference, and after it before optimize+codegen. A cancelled
  compile returns "nothing produced" rather than raising -- every caller already
  handles that, so cancellation needs no new failure path.

- The trigger counter is bumped by the READER strand, not the worker. A
  worker-side bump can never fire while it matters, because during a compile the
  worker is not processing messages -- verified: with the worker bumping, zero
  cancellations fired across 10 rapid edits; with the reader bumping,
  cancellation fires as expected. Anything arriving mid-compile (edit or
  request) means the compile is stale or is delaying an answer, and either way
  the right move is to stop and go round again. A superseded compile publishes
  nothing and leaves the document dirty, so the next idle pass redoes it.

### JS module imports emitted from the wrong list — FIXED 2026-08-23
- **Symptom**: any program reaching `std/async` failed at runtime under
  `--target=js` with `ERR_MODULE_NOT_FOUND: .../async_internal.mjs`.
- **Diff**: upstream `codeGenJS` passes `Core.coreProgImports core` to
  `javascriptFromCore`. The port passed `jsImports = mods.keys`, i.e. EVERY
  loaded module. `mods` holds aliased entries -- a module under both its
  canonical name and the as-written relative-import name (`resolve-module`'s
  own aliasing) -- so `std/async/internal` appeared twice and the JS backend
  turned each entry into a real `import ... from './<name>.mjs'`, emitting
  `./std_async_internal.mjs` (exists) alongside `./async_internal.mjs`
  (never written). The C backend was unaffected because it does not turn that
  list into imports; it uses it only as the link closure.
- **Fix**: `code-gen.kk` now passes `c.imports` to `javascript-from-core`, and
  the full loaded-module list is renamed `loadedModules` and kept for the C
  link closure only (upstream's `imported`), with a comment saying why the two
  must not be conflated.
- **Verified**: all 5 `test/jsgen/*` pass; on a 20-file `algeff`/`lib` sample
  the port's `--target=jsnode` output is byte-identical to the reference's on
  18, and the other 2 differ only in the known cosmetic parse-error hint
  indentation (both compilers reject the file the same way). C target
  unaffected.

### Overall codegen strategy — high-fidelity, faithful port
- ESM module shape, always-export convention, tail-call loop pattern, BigInt
  large-int literals with small-int32/int64 fast paths, external-format-string
  splicing, exact reserved-word list — all verified matching line-for-line.
  One of the most faithfully-ported clusters in the whole port.

### Main-entry async-handle path — both sides disabled, but fragile to future upstream changes
- Upstream's `async_handle` branch for an async main is dead code (wrapped in
  a Haskell block comment) at the synced baseline; the port doesn't even have
  the branch (not commented out, just absent).
- **Classification**: INTENTIONAL DIVERGENCE, currently a non-issue, but a
  standing note for future re-syncs: if upstream re-enables that branch
  (a single-line uncomment), the port will silently diverge until re-synced.

### No source-map support on either side — confirmed parity, not a gap.

---

## Module system / build orchestration / linking

(Compared `Compile/Build.hs`, `Compile/Module.hs`, `Compile/CodeGen.hs`
against `driver.kk`, `compile/build.kk`, `compile/schedule.kk`,
`compile/link.kk`, `compile/code-gen.kk`, `compile/options.kk` — this
section draws on hands-on work earlier in this project as well as direct
reading, not just a fresh comparative pass.)

### Concurrency model: OS processes vs. green threads in one process
- **Upstream**: `mapConcurrentModules` runs Haskell green threads inside ONE
  process, synchronizing per-module progress through FIVE separate
  `MVar`-backed module maps (parsed/typed/optimized/codegen/linked) — a
  module's codegen can start as soon as its dependencies reach that phase,
  without waiting for their codegen/link to finish. Fine-grained phase pipelining.
- **Port**: `compile-graph-rpc` dispatches WHOLE modules to `spawn-thread`
  workers; each worker runs parse→typecheck→optimize→codegen for its
  assigned module atomically in one round-trip, gated only on dependencies'
  interfaces being ready — no phase-level pipelining.
- **Classification**: INTENTIONAL DIVERGENCE, with a real performance-ceiling
  consequence (not correctness) — caps the port's achievable parallelism on
  wide-but-shallow dependency graphs below what upstream's finer-grained
  pipelining achieves. Worth knowing before drawing conclusions from
  per-module timing comparisons.

### Multi-process build-directory safety — test-harness-only issue, not a compiler bug
- `resolve-module`'s mtime-based incremental reuse has NO cross-process
  locking. Confirmed this session: 8 concurrent OS-process sweep workers
  sharing one buildtag directory produced spurious link failures that
  vanished once each worker got its own buildtag (fixed in the harness).
- **Classification**: POSSIBLE INFIDELITY, but scoped — not a bug in normal
  single-process usage. Worth a defensive fix (advisory lock per buildtag)
  since a user could hit this outside test harnesses too (parallel `make`,
  editor auto-build racing a manual build).

### `pub-import-closure` — suspected root cause of two independently-found symptoms
- **Upstream**: `moduleWaitForPubImports` computes each module's core import
  list as declared imports + closure of PUBLIC re-exports, level by level,
  first-occurrence order.
- **Port**: `compiler/compile/build.kk:313` `pub-import-closure` is a
  deliberate, well-commented port of this algorithm.
- **Classification**: UNCLEAR / already flagged elsewhere as buggy — earlier
  project memory records "the pub-import-closure narrowing is INCORRECT (12
  kind errors on a cold build.kk)" independent of this session's work. This
  session's own digging strongly suggests the SAME root defect resurfacing as
  a segfault (not a kind error) when a module is compiled fresh from source.
- **Why it matters**: arguably the single highest-leverage item on this
  whole checklist — suspected root cause of two independently-discovered
  symptoms, and blocks compiling std lib from source (several other findings
  depend on that being unblocked).

### Module `@init()` call sequence — completeness gap, not just ordering
- **Upstream** (`Backend/C/FromCore.hs:102-113`): emits `<import>@init()` for
  every entry in `coreProgImports core`, in listed order — no additional
  topological re-sort at this point. Correctness depends entirely on
  `coreProgImports` already being a complete, dependency-first closure.
- **Port** (`backend/c/from-core.kk:150`): does the identical thing — this
  part is faithfully ported; the divergence is upstream, in the closure
  computation, not here.
- **Classification**: POSSIBLE INFIDELITY — confirmed reproducible, not
  theoretical.
- **Why it matters**: reproduced this session with `KOKA_STDLIB_FROM_SOURCE=1`:
  `std/time/timestamp`'s `@init()` runs before `std/num/int32`'s despite
  needing its `zero` constant, because `std/num/int32` is simply ABSENT from
  the entry's own import list (not merely misordered) — segfault marking a
  still-null value thread-shared. An attempted fix (broadening the import
  list to the full transitive closure) fixed this but broke the DEFAULT
  build's `.kki` interface content for unrelated modules — confirming
  `core.imports` is load-bearing for more than init-call generation, so a
  real fix has to correct `pub-import-closure` itself, not patch around it downstream.

### Linking — at parity
- Both compilers compile every module's `.c` to its own `.o` with the SAME
  build that generated the `.c`, so object files are always internally
  consistent. The port previously linked against a foreign object cache
  built by the reference compiler; that cache is gone and this is no longer
  a divergence.

### Incremental staleness / rebuild granularity
- **Upstream**: phase-aware (`modulesReValidate` — a module can be
  `PhaseTyped` but not `PhaseOptimized`, partial re-validation possible).
- **Port**: `resolve-module`'s staleness check is all-or-nothing per module —
  no phase-level partial reuse.
- **Classification**: INTENTIONAL DIVERGENCE, consistent with the whole-module
  dispatch difference above. No known correctness risk, coarser reuse granularity only.

### `builtin-extend` bootstrap hardcoding — RESOLVED this session
- Recorded here for traceability only. Fixed in commit `0f91efe`: the type
  checker now uses `std/core/types.kk`'s real definitions instead of a
  hardcoded bool/`@optional` stand-in when that module is itself being compiled.

### Entry `@main` wrapper is not its own module — interface leak FIXED, structure still diverges

- **Upstream**: every entry program gets a synthesized virtual module
  `<entry>/@main` (`/@virtual/tiny/@main.kk`), compiled as its own module to
  `tiny__main.{c,h,o,kki}`, and the executable is linked from it and named
  `tiny__main`.
- **Port**: no wrapper module. For a unit `main` the entry module is linked
  directly (exe named `tiny`). For a NON-UNIT `main` the synthesized `@expr`
  def is appended to the entry program itself (`build.kk`'s `needsWrapper`),
  so the entry module's own `.kki` carries it.
- **Classification**: DIVERGENCE, and the non-unit case is a real fidelity bug
  — upstream keeps the synthesized def out of the entry's interface.
- **Also**: differing executable names are a drop-in difference (`tiny` vs
  `tiny__main`), and the extra module means artifact counts differ (28 vs 27
  on a one-module program), so a port-vs-upstream comparison is not exactly
  like-for-like. The bias is AGAINST the port — upstream does the extra module
  compile plus a clang invocation — so measured ratios are conservative.
- **Scope** (five interacting pieces, all in the entry path, which produced the
  `@main`-misses-async class of bugs):
  1. build a fresh `program` named `<entry>/@main`;
  2. add the compiled entry to `mods` and thread `defs-for` /
     `core-imports-from-modules`;
  3. give the wrapper its own `outBase` (`code-gen` derives `.c`/`.h` from the
     module name already, but `outBase` drives the `.kki` and the exe path);
  4. move the link to the wrapper module, stop linking from the entry;
  5. keep `completeMain`'s default-handler installation in the right module.
- **Verify on a one-module program** (`tiny.kk` with a unit `main`, and one with
  a non-unit `main`); per AGENTS section 3 do not scale up for this.

**Interface leak fixed** (`make-expr-def` now emits the def `Private`). The
port appends the synthesized `@expr` to the ENTRY module rather than a separate
one, and `Public` exported it in the entry's own `.kki` -- `pub fun @expr : ()
-> <console> ()` plus its inline body, in the public interface of a module a
user may import. Upstream's entry interface has no trace of it. Verified on
three-line programs: for a non-unit `main` the port's entry `.kki` exported
`@expr` and upstream's did not; both now export nothing. Programs still run
(`unit-main ok`, `42`); sweep 423/17/2/0.

**Still diverging, and now classified as cosmetic rather than a fidelity bug:**
upstream additionally emits `<entry>__main.{c,h,o,kki}` and names the exe
`<entry>__main`; the port generates the entry glue inside the entry module and
names the exe `<entry>`. Consequences are (a) a drop-in difference in the
produced executable name, and (b) artifact counts differ by one module, which
biases port-vs-upstream comparisons AGAINST the port (upstream does the extra
compile). Neither affects the port's interfaces or correctness, so the
five-piece restructure above is no longer urgent -- reassess only if drop-in
executable naming matters.
