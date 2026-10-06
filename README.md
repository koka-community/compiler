# Koka, self-hosted

A Koka compiler written in Koka: a port of the reference (Haskell) compiler, [koka-lang/koka](https://github.com/koka-lang/koka), that compiles itself.
It ships its own standard library (`lib/`) and C runtime (`kklib/`), and includes a language server and a web playground.

- **Status:** built by itself, it passes the reference compiler's test corpus (`test/`) apart from 2 known mismatches; see [docs/port-status.md](docs/port-status.md).
- **Platforms:** Linux and macOS, x64 and arm64. Windows is not supported: the compiler drives the C compiler through a POSIX shell.

## Install

CI builds an archive per platform, `koka-port-<os>-<arch>.tar.gz`. Tagged versions publish them under [Releases](https://github.com/koka-community/compiler/releases); every other run of the [stage2 workflow](https://github.com/koka-community/compiler/actions/workflows/stage2.yml) keeps them as artifacts.
Extract one anywhere and put its `bin` on your `PATH`:

```bash
tar -xzf koka-port-macos-arm64.tar.gz
export PATH="$PWD/koka-port-macos-arm64/bin:$PATH"
koka -e hello.kk
```

The compiler finds `lib` and `kklib` next to its own `bin`, so the archive works wherever it is extracted.

## Build from source

The build has two stages, the same ones CI runs (`.github/workflows/stage2.yml`):

1. **Stage 1:** the reference compiler builds the port.
2. **Stage 2:** stage 1 builds the port again. Stage 2 is what ships.

### Prerequisites

- A C compiler (clang or gcc) and `make`.
- [vcpkg](https://vcpkg.io), with `VCPKG_ROOT` set. The compiler installs libuv and pcre2 from it on demand.
- isocline, the REPL's line editor, which is in neither vcpkg nor conan:

  ```bash
  git submodule update --init --recursive
  scripts/install-isocline.sh            # or: scripts/install-isocline.sh <prefix>
  ```

- For stage 1 only: [stack](https://docs.haskellstack.org) and the reference compiler from [TimWhiting/koka](https://github.com/TimWhiting/koka) branch `port-reference`, which carries the reference-compiler fixes the port needs.

### Stage 1

```bash
git clone -b port-reference https://github.com/TimWhiting/koka ../koka-ref
(cd ../koka-ref && stack build)
KOKA_DEV_DIR=../koka-ref ./koka -O2 -c compiler/main/driver.kk
```

`./koka` runs the reference compiler with `--sharedir` set to this repository, so it uses this `lib` rather than its own.

### Stage 2

```bash
STAGE1=$(ls -t .koka/v*/*release-*/compiler_main_driver__main | head -1)
"$STAGE1" -i. -O2 -c --buildtag=bootstrap compiler/main/driver.kk
```

### The pinned driver

For day-to-day work, pin a known-good build and let it build the next one:

```bash
scripts/build-driver.sh --pin <driver>   # copy <driver> to .koka/bootstrap/driver
scripts/build-driver.sh --port           # the pinned driver builds the port, incrementally
```

The pinned driver is never rewritten by a build, so a bad change cannot poison the compiler that builds the next attempt.
Re-pin deliberately, once the tests pass.

## Use

```bash
koka -e hello.kk                          # compile and run
koka -c -o out/app src/main.kk            # compile to an executable
koka -i. -c --output=.koka/bin/app main.kk # in a package, with its own modules on the include path
```

`koka --help` lists every option.

## Test

The corpus (`test/`, from the reference compiler) is run by `scripts/test-runner.kk`, which compiles each test with a given driver and compares its output with the `.kk.out` fixture:

```bash
export LANG=C
"$STAGE2" -i. -O2 --buildtag=bootstrap -e scripts/test-runner.kk -- "$STAGE2"
"$STAGE2" -i. -O2 --buildtag=bootstrap -e scripts/test-runner.kk -- "$STAGE2" static/wrong   # one directory
```

It exits nonzero when a test fails. The tests listed in `test/known-mismatches.txt` are expected to fail and are reported as KNOWN; a listed test that passes fails the run, so the list stays accurate.

Environment variables:

| variable | effect |
| --- | --- |
| `KOKA_TEST_JOBS` | worker count (default 8) |
| `KOKA_TEST_DIFF=1` | print the full expected and actual output of every failure |
| `KOKA_TEST_ROOT` | the repository root, when running from elsewhere |

The unit tests are every `test/**/*-test.kk` that defines `pub fun suite()`:

```bash
KOKA="$STAGE2" "$STAGE2" -i. -e run-tests.kk
```

## Web playground

`web/playground` runs the compiler in the browser, as a WASI module built with [wasi-sdk](https://github.com/WebAssembly/wasi-sdk) 25:

```bash
(cd web/playground && npm install)
KOKA="$STAGE2" scripts/playground.sh         # the wasm compiler, precompiled std, samples
cd web/playground
npm run build
node test/test-wasm.mjs                      # compile and run samples through the wasm compiler
npx vite                                     # serve it locally
```

`scripts/playground.sh` finds wasi-sdk through `WASI_SDK_PATH`, `~/.wasi-sdk` or `~/wasi-sdk-*`.

## Repository layout

| directory | contents |
| --- | --- |
| `compiler/` | the compiler, language server and playground entry points |
| `lib/` | the standard library |
| `kklib/` | the C runtime |
| `test/` | the test corpus and the unit tests |
| `web/playground/` | the browser playground |
| `scripts/` | build, test and benchmark scripts |
| `util/` | packaging |
| `support/` | editor support |
| `samples/` | example programs |
| `docs/` | design notes and status; start at [docs/README.md](docs/README.md) |

## Known limitations

- Constructors larger than 128 words (roughly 100+ fields) crash when allocated: `kk_block_alloc_at` always uses mimalloc's small-object path.

## Contributing

Read [AGENTS.md](AGENTS.md) first: it sets the coding, porting, testing and optimisation rules.
The port follows the reference compiler's structure, and [docs/upstream-map.md](docs/upstream-map.md) records where each definition came from.
