# Roadmap: from port to primary compiler

Written 2026-09-17, when the port stopped being slower than the reference compiler.
The goal this plans for: **one repo that builds itself, ships its own standard library, runs its own tests, and has no dependency on a Haskell checkout.**

## Where the port stands

Measured on this machine, same flags both sides (`-O2 --target=c`), port vs reference:

| workload | port | reference |
| --- | --- | --- |
| warm small (best of 30) | 0.31s (avg 0.37) | 0.47s (avg 0.49) |
| cold small (avg of 5) | 4.09s | 3.80s |
| warm big (the compiler) | 15.5s | ~24s |
| cold big | 249s | ~469s |

Cold small is the only workload still behind, by ~0.3s.
Correctness gate: 424 pass / 17 skip / 2 mismatch on the upstream corpus, plus the multimodule gate.
The two mismatches (`cgen/specialize/recursive-arg`, `medium/allsamples`) predate this work.

Performance is no longer the thing holding the port back. What follows is.

## Phase 1 — make the repo self-contained — DONE (2026-09-17)

The repository now builds itself with no other checkout on the machine: `lib` (the standard library), `kklib` (the C runtime), `test` (the corpus), `util`, `doc`, `support` and `samples` all live here, the `vendor/koka` submodule is gone, and nothing on any path points outside the tree.

What each item became:

1. **Standard library**: `lib/`, and the default share dir is this repository -- derived from the compiler's own location, so an installed compiler (`util/bundle.kk`'s `<prefix>/share/koka/v<version>`) works the same way. This also fixed the cwd-relative `kklib` path: linking now works from any directory.
2. **The `koka-community/std` modules**: the containers, `sort`, `json` and `std/test` graduated into `lib/std`; the assoc-list and list/char/vector helpers went into the `std/core` modules that own them (`core-extras` is gone, not moved); `pprint` stayed compiler-internal. `linear-map`, `intern` and `word-set` were NOT brought in -- `trie` (the lexer's keyword set) now keys its children off a plain association list.
3. **`-i../parsing`**: gone from every script.
4. **Test corpus**: `test/`, found relative to the repository root (`KOKA_TEST_ROOT` overrides). The runner compiles with the port, not the reference compiler.

The rest of this roadmap stands as written.

## Phase 1 as originally scoped

This was the blocking work: a working checkout needed two sibling repos and a Haskell worktree.

1. **Bring the standard library in.** `vendor/koka/lib` (a submodule of `TimWhiting/koka`, branch `dev-compiler`) is the std library the driver searches by default. Move it to a first-class `lib/` in this repo and make `--sharedir` default there. The submodule stays only for `kklib` (C runtime headers) until that moves too.
2. **Absorb the 15 `koka-community/std` modules the compiler imports.** They are `std/core-extras`, `std/data/{hash,int-map,int-set,json,rb-map,rb-set,rbtree,rbtree-bu,sort,trie,word-set}`, `std/pretty/{pprint,printer}` and `std/test`. Each one needs a decision: **graduate** into the std library (the containers and `sort` have earned it — the compiler is their stress test), or move under `compiler/lib/` as compiler-internal and unexported. `std/test` belongs in the repo either way, since the std library's own tests need it.
3. **Delete the `-i../parsing` include path.** Nothing in `compiler/` imports anything from `koka-community/parsing`; a probe build with the path removed succeeds. It appears in five scripts. Verify on a full driver build, then drop it.
4. **Bring the test corpus in.** `scripts/test-runner.kk` hardcodes `/Users/timwhiting/koka/.worktrees/dev-compiler/test`. `vendor/koka/test` already holds 443 of those 444 cases at the pinned commit. Point the runner at the submodule (or at a copied-in `test/corpus/`), and make the path a flag rather than a constant.

After this phase, `git clone --recursive && ./build.sh` is the whole setup, and no path in the repo names a directory outside it.

## Phase 2 — remove the quirks that block daily use

Each of these is small and independently shippable.

- ~~`kklibIncludeDir` is resolved against the current directory~~ — FIXED with phase 1: it comes from the sniffed share dir, so linking works from any directory. A failed link still exits 0; that part stands.
- **`scripts/build-driver.sh --pin` picks the newest `.koka/v3.2.7/clang-drelease*/compiler_main_driver__main`**, which is whatever a benchmark happened to write last. Pin by explicit path and verify the checksum.
- **The `~/.local/bin/koka-port` wrapper needs an absolute `--sharedir`.** Phase 1.1 removes the need for the wrapper entirely.
- ~~No `@main` module~~ — DONE 2026-09-18: a program's entry point is built as its own virtual `<root>/@main` module, so the program's artifacts carry no entry glue and the executable is `prog__main`.
- **`discover-deps` segfaults when the `out-dir` default argument is omitted** (`std/os/path`'s parse handler). Open, unreproduced in isolation; it is worked around by always passing the argument.

## Phase 3 — own the test story

Today the port is validated entirely against someone else's fixtures. That is the right gate for parity and the wrong one for a compiler that intends to move ahead of them.

As of 2026-10-05, CI (`.github/workflows/stage2.yml`) builds the port on four platforms and runs the corpus and the unit tests (`run-tests.kk`) with stage 2 on every push and pull request.

- **Tests for the std library, in this repo.** `std/data/rb-map`, `rb-set`, `int-map`, `sort` and `trie` have tests in `koka-community/std/test`; they come along in Phase 1.2. Everything else in `lib/` has none here.
- **Unit tests for compiler internals.** `test/tests/{lex,parse}` is the whole of it. The passes with the most porting risk and no direct test are specialize, parc/reuse, monadic lifting and the interface round-trip (`kkc-check.kk` covers the last one as a script, not as a test).
- **A regression test per fixed bug.** The specialize borrow/TRMC fix went upstream with a test; several earlier fixes (evidence-vector scramble, unroll unique counter, interface qualified wildcards) have none here.
- **Keep the upstream corpus as a parity gate**, pinned via the submodule, run before releases rather than on every change.

## Phase 4 — go past upstream on the language server

The port already implements every handler upstream has: hover, definition, completion, code action, document symbol, folding, inlay hints, signature help, diagnostics, commands.
With type-check-only checks at 7s warm on this compiler, the useful work is now the features upstream never had:

- rename, and find-references (both need a reverse index over the range map)
- workspace symbols
- semantic tokens (the highlighter already exists — `syntax/highlight.kk`)
- formatting (the README's original first priority; still unimplemented)
- call hierarchy

## Phase 5 — documentation hygiene

- `TODO_porting.md` (1072 lines) is a chronological session log with a per-file review list mixed in. Split it: the per-file "needs review" table stays as a checklist, the history goes away (it is in the commit log).
- `docs/parity-checklist.md` (982 lines, dated 2026-08-18) still carries 12 items marked UNPORTED or POSSIBLE INFIDELITY. Re-check those 12 against the current tree; most predate the build-pipeline work.
- `docs/linear-map-migration-queue.md` and `docs/async-segfault-root-cause-brief.md` describe finished work. Deleted — the findings live in the commit log and in the code comments they produced.

## Sequencing

Phase 1 first, and in its own order: it is what turns the repo into something another person can clone.
Phase 2 can interleave with it (the `kklib` path fix is a prerequisite for using the port outside this checkout anyway).
Phase 3 gates any further divergence from upstream — once the port has its own tests, dropping the upstream corpus becomes a choice rather than a risk.
Phase 4 is the first work that makes the port *better* rather than *equal*, and it is what will make people switch.
