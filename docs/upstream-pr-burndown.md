# Upstream PR burn-down

The port's compiler fixes that belong in `koka-lang/koka`, as a stack of single-commit branches in the HASKELL checkout (`~/koka`, branches `tim/*`).
`tim/all` is a name for the top of the stack, not a separate layer.

State as of 2026-09-24: **nothing is pushed**; no branch has a tracking ref.
The stack is restacked onto `upstream/dev` at `d881e92b6`, one commit per layer.
`scripts/restack-upstream-stack.sh` replays `branch.<layer>.stackBaseRev..layer` rather than using a merge-base, which is what stops an amended layer's OLD version from being swept into the next rebase.
Edit the stack in the detached worktree `~/koka/.worktrees/tim-stack`, so the script can check out any layer.

## Submission order

The stack layers were squashes by theme; the PRs are rebuilt from them standalone on `upstream/dev`, one per compiler pass or runtime area, folding in the related upstream PRs so there are fewer to track.
Local branches are `tim/pr/<name>` in `~/koka`; only #932 is pushed.

| # | branch | contents | folds in | tests |
| - | ------ | -------- | -------- | ----- |
| 1 | `tim/pr/iface-roundtrip` | interfaces round-trip what a module mentions | -- | mpat, synpriv, cctx-context-path; **draft PR [#932](https://github.com/koka-lang/koka/pull/932)** |
| 2 | `tim/pr/specialize` | termination, declining a specializable residual, dropping specialized parameter infos | your #906; Patrik's #899 (his commit, his authorship) | mutualspec, recursive-arg, spec-trmc-borrow |
| 3 | `tim/pr/simplify` | case-of-case duplication cap; fresh names avoid an inlined body's binders | Patrik's #902 (his commit) | caseofcase-and; none for the capture fix (a collision needs two counters to coincide) |
| 4 | `tim/pr/infer-effects` | open-resolve (cast only between matching tails; only proven code skips `open-none`); isolate keeps the effect row; divergence search pruning; locally qualified names | your #750 | open-resolve, open-none-core, open-none-extern, eff-var-local, divergent-arity, local-qualified-rec; masklocal4's recorded type was unsound |
| 5 | `tim/pr/parc` | defer pattern dups into a nested match; a function type has no fixed allocation size | -- | 4 dup-sinking programs; parc-closure-reuse |
| 6 | `tim/pr/bytes` | join leak; `advance` overrunning its bytes; borrowing `length`/`byte-at`; JS externs | fixes issue #903 | test/lib/bslice |
| 7 | `tim/pr/ref-update` | NEW API: `ref/update`, `local-var/update` | -- | test/cgen/ref-update |
| 8 | `tim/pr/threads` | shared statics safe across threads; worker threads and thread-safe channels; `spawn-thread` priority hint | your #910 (older version) | async/xthread, xthread-stress, bchannel, bchannel-multi |

Your open PRs #906, #750 and #910 would be closed in favour of these, and #899/#902 referenced as included.

## Review decisions made while cleaning

- Every comment is cut to purpose and invariant; incident stories moved into commit messages.
- `iface-roundtrip`: the `io-noexn` alias and the `makeImport` debugging message are dropped.
- `infer-effects`: the commented-out kind assertions in `Type/TypeVar.hs` and two unused imports in `Core/Monadic.hs` are dropped.
- `ref-update`: the JavaScript `update` passed a copy of the ref object and discarded the result; now `((#1).value = (#2)((#1).value))`. The benchmark that stood in for a test (timing output, no `.out`) is replaced by a deterministic test. Its `kk_box_mark_shared` change moved to `threads`.
- `threads`: the opt-in evidence-vector integrity checker (~300 lines of debug diagnostics) is dropped. The unconditional macOS user-interactive QoS pin became `spawn-thread(..., priority = Interactive)`: QoS classes on macOS, `uv_thread_setpriority` elsewhere (libuv 1.48+), minimal timer slack on Linux; `Normal` is the default and changes nothing.
- `threads`: the squash had reverted upstream's `interleave.kk` (dropping two `with mask<local>` and uncommenting the `strand done` trace) and removed `std/async/os/file` from `lib/toc.kk`; both restored.
- `bytes`: the new `byte-at` test exposed that `advance` kept `max(len, total - newstart)`, so an advanced slice ran past its bytes; fixed to `min` here and in the port.
- `bytes`: the earlier claim that this layer removed upstream's `is-empty` was wrong -- it adds a borrow (`^slice`); the revert scan counted the modified line as removed.

## Work items

- [x] Verify every branch standalone: each builds on `upstream/dev` and passes the full suite, with the suite's build dir wiped per branch (kklib's object is not rebuilt when a kklib source changes, so a shared one links the previous branch's runtime).
- [x] `infer-effects`: `isHandlerFree` is derived from the evidence invariant (code compiled for a closed row finds evidence at static offsets, so it must not run under extra evidence). A function variable is never handler-free, in any module: upstream's std/core trust returns 1 for 42 when a total std/core function installs a handler (open-none-core). An external is handler-free only if it cannot call a function it is passed (no function-typed parameter, or the identity `#1`): #750 still trusted it (open-none-extern). Measured on a cold port build: 6226 vs 4797 static `open_none` sites, evidence-swap self time 0.57% vs 0.53% of 623 s, CPU totals within 0.1%, so the sound rule costs nothing measurable and no interface flag or region lifting is warranted.
- [x] `parc`: closure-reuse regression test. The root cause was `getFixedDataAllocSize` sizing a function type by its result type, which made every lambda parameter of type `() -> t` a reuse donor the size of a `t`; the fix moved from the drop site to that lookup, and `test/parc/parc-closure-reuse` checks the `--showfcore` output (it fails without the fix).
- [x] Keep the stack (`tim/*`) consistent with these branches: `advance`, the closure-reuse root fix, the refined `isHandlerFree`, `maptwice.kk.out` in the infer-effects layer, and the thread priority option are all in; `tim/all` passes 437/0. `dev-compiler` has #932, the closure-reuse fix and the refined rule (431/0).
- [x] Port `lib`: the unconditional QoS pin is replaced by the priority option, and the compiler's workers use the default (`Normal`). Measured with one driver, priority switched by environment variable, one cold port build per run: Interactive 2:41.6 / 2:42.0, Normal 2:39.4 / 2:39.8, Background 3:05.6 (all 21 workers at utility priority 20, i.e. efficiency cores). Interactive buys nothing for a compile.
- [ ] The port's `kklib/mimalloc` pin is `60824be3f`; sync it to upstream's `cc00f6647`.
- [ ] Push the remaining branches and open the PRs, lowest risk first.

## How the squash went wrong, so it is not repeated

Each layer was squashed from `dev-compiler`, which branched from upstream at `24e09f90a`.
Taking a file's `dev-compiler` version wholesale silently reverts everything upstream changed in that file afterwards, and converts line endings where upstream uses CRLF.
Audit every layer for lines that are absent from the layer, present upstream, and added upstream after the branch point; a CRLF-insensitive version of that check found every case above.

## Known caveat

`test/cgen/specialize/recursive-arg` (added by layer 1) is one of the two standing MISMATCHes in the PORT's own sweep.
The Haskell side was verified (build ok, 426 examples / 0 failures), so this is a port-side gap, not a reason to hold the PR -- but expect the question.
