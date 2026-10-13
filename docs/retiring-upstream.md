# Before retiring the Haskell compiler

Written 2026-10-12 for the discussion with Daan. What has to be true before this compiler replaces `koka-lang/koka`'s Haskell compiler as the one people use and develop.

## Where it stands

- CI (`.github/workflows/stage2.yml`) builds the port on Linux and macOS, x64 and arm64: the Haskell compiler builds stage 1, stage 1 builds stage 2, and stage 2 runs the corpus, the unit tests and a packaged smoke test.
- Corpus with stage 2: 438 pass, 21 skip, 1 known mismatch on every platform (`test/known-mismatches.txt`); unit tests: 43 pass.
- The port is faster than the Haskell compiler on every workload but a cold small build (`docs/roadmap-to-primary.md`).
- The browser playground runs this compiler as wasm: <https://koka-community.github.io/compiler/>.

## Must happen first

1. **Bootstrap without Haskell.** Stage 1 is still built by the Haskell compiler, from `port-reference` (21 single-commit fixes on `upstream/dev`, plus one more) pinned by commit. Instead: tag a release, and build stage 1 with the previous release's binary; keep a Haskell build only as a periodic parity check.
2. **No silently ill-kinded core.** The port's `new/sub` does not check kinds. Turning the check on crashes ordinary compiles, because computing the kind of some substituted type throws: something builds ill-kinded types. Find it and keep the check on. (The recursive-group type-argument bug was one such source; it is fixed in both compilers.)
3. **The shared evidence-vector crash.** A pure change to `compiler/type/typevar.kk` makes code from both compilers read past the evidence vector (`docs/port-status.md`, "Crashes seen"). It is a code generation bug in both; it needs a minimal repro and a fix before the port is the only compiler.
4. **The last corpus mismatch.** `cgen/specialize/recursive-arg`: the port creates three lifted copies in a different order than the Haskell compiler; only names differ, but it is a fidelity gap in lifting or specialization.
5. **Windows.** Not built or supported: the port drives the C compiler through a POSIX shell.

## Can follow

- **The edit loop.** A comment-only edit rebuilds in 107-164s against 9-10s for GHC; there is no early cutoff, and artifacts depend on build provenance (`docs/port-status.md`, "The dev-loop gap").
- **The JavaScript backend.** Only the 5 `test/jsgen` tests and the playground's harness exercise it.
- **The playground.** No language server in the browser (no `koka-lsp.wasm`), and deep mutual recursion overflows the worker stack; fusion fixes the four samples that crash, but needs the fixes in `docs/fusion-investigation.md` first.
- **Upstream PRs.** The fixes on `port-reference` and the open `std/async` PRs (#933-#935) are already in this compiler; they matter only to the Haskell compiler's users.

## Decisions for Daan

- Where the standard library lives once there is one compiler: this repository's `lib/` has diverged from `koka-lang/koka`'s (async fixes, the containers graduated from koka-community/std, the type-equality evidence for fusion).
- Whether language and library changes land here first, or keep landing upstream and get ported.
- What release and versioning the port uses, and when `koka-lang/koka`'s installers and VS Code extension switch to it.
