# Upstream sync

The port is synced with `koka-lang/koka` `dev` through **`0700777dc`** (2026-11-14, #971).
Update that line and the table below whenever upstream changes are brought in.

Per-file `// Updated as of ...: Commit <hash>` headers and `./check-upstream-sync.sh` (see `TODO_porting.md`) are older and finer-grained; this file is the sync point of the port as a whole.

## Checking for new upstream changes

```sh
git -C ~/koka fetch upstream
git -C ~/koka log --first-parent --oneline 0700777dc..upstream/dev
```

For a commit that touches `lib/`, `kklib/` or `test/`, those files are shared with upstream, so whether the port has it is mechanical: `git diff <c>^1 <c> -- lib | git apply --check -R` in this repository succeeds when the change is present.
A change to `src/` has to be ported by reading it.

## Upstream merges since v3.3.0 (757b1b80a)

| upstream | change | port |
| --- | --- | --- |
| 0700777dc #971 | LSP: diagnostics follow the editor buffer and the document version | b548344 (and drops `diagnosticProvider`, which upstream does not advertise) |
| 7e9c1e593 #962 | literate snippet includes; HTML popups | cb90ab1 (also adds the literate support the port lacked), 55f7f2e (book.js, playground embed) |
| bd457c10e #963 | entry module next to the module it calls (`foo_at_main`) | 8a305b9 |
| d23ee7cd7 #965 | CI; library fixtures are not tests | 2e0bae7 |
| 198fc3bbd #961 | playground color themes | a52c1a7 |
| 2f4925d20 #922 | constructor-context path in interfaces (`@cpath`) | present before the sync (`core/pretty.kk`, `core/parse.kk`) |
| 2295d5e35 #945 | `@evv-index` type arguments | a152624 |
| b733ab86b #949 | ctail: polymorphic recursion | 5a569d6 |
| d3521d313 #953 | monadic type lambda; substitute before generalizing | cda5511, 5a07fef |
| 8e357dc22 #954 | match guard fall-through | 8b14f68 |
| 85d6df519 | thread races on delayed values | present; 11ab577 takes upstream's comments |
| 5a7c368a6 #946 | aliases before a recursive group's data types | 7b14058 |
| a3b80e98e #948 | ctail/cctx primitive type schemes | 65509d4 |
| bb6c44a72 #952 | flat type applications under substitution | 0f34265 |
| 9c55695dd | open-resolve: cast only between matching tails | present; 58f01a4 takes upstream's test |
| 046254c13, cf5607640 | thread-shared refcount fixes | 09522bc (upstream's form; the port had its own) |
| 0be3eb036 | multi-scrutinee patterns in interfaces | present before the sync |
| 8b803da69 #936 | reject integer exponents >= 10^9 | 1a9efe1 |
| 5b2dd889d | a recursive type is never an automatic value type | b57e27b |
| 64324ad9f, 579644d92, a0e403d89 | parc-reuse, specialize and local-inference fixes | present before the sync (their tests pass) |
| e38005d97 | vfsCompose keeps the outer VFS | 8b5ed70 |
| d3c2f591a, f7dc86381, 8b8b4f3f1, cf11ce741, f8a664eea, d881e92b6 | bslice/bytes, grammar, assertion message, mimalloc | present before the sync |

## Known differences left by the sync

- A literate document's colorized `.md` has type popups but no definition links: the port's `fmt-comment` takes no range map (`syntax/colorize.kk`).
- `syntax/gen-doc.kk` names type variables per declaration; upstream's #962 threads one nice-name environment through each declaration's highlighting.
- The VS Code extension's test suite keeps the port's own harness (`src/test/runTest.ts`, `@vscode/test-electron`); upstream's `.vscode-test.mjs` workspace and its `@vscode/test-cli` dependencies in `package.json` are not brought in, the workspace setup is reproduced in `runTest.ts`.
- `web/playground/test/test-wasm.mjs` is the port's own; upstream's e38005d97 line (print the compile result on failure) has no counterpart there.
- The playground's default backend stays `wasm` (`editor/context.tsx`), as the port's language server does not run under WASI.
