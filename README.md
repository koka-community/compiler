# Self-Hosted Koka Compiler

Koka has a relatively simple compiler, and it should be mostly straightforward to implement it in itself.

First priorities are to get a formatter and package management? system working. 
For package management, I'm not thinking of anything huge to start out, mostly just grabbing repos from git (starting with koka-community packages), and storing them in some canonical place based on git hash.

The rationale behind the choice of these two features is that:

1. These particular features are things that are partially lacking in Koka's Haskell compiler
2. They provide a cornerstone for starting to replace Koka's Haskell compiler without having to support the full compiler pipeline (mostly just Syntax / Lexing / Parsing and Reading / Writing files)
3. They help us grow the ecosystem in ways that are semi-detached from the core efforts of the Koka project itself

Some major features missing to actually complete the full compiler transition are as follows:

- Standard Library Data Containers - Efficient Maps / Sets - for now we will just use what we have in `koka-community/std`
- Comprehensive async & threading support - we can probably make do with what we have, or start with a single threaded implementation

Given those two things, we could have a working compiler. 
However, Koka is much more than a compiler now - it is also a language server and interpreter which require the following:

- JSON-RPC support for the language server (Tim has a small sample using his fork of Koka with LibUV support)
- A few C libraries (isocline bindings)
- Language Server Library (ideally generated from the spec, with a couple of nice wrappers or utilities).

While implementing self-hosted Koka we should be concientious that the libraries and things we depend on can support usage in WASM.

For example we probably want to separate the interpreter and language server as external pieces, and not part of the core compiler libraries.

Additionally we should provide nice hooks into the compiler pipeline via effects:

This could for example allow:

- providing formatting options
- providing package resolvers
- providing different backends
- providing optimization passes
- adding a post-lexing macro pass

.. and in general a more extensible compiler.

While this is a goal that I see as worthy, I'm not sure if (Daan) the original author of Koka shares my views for such an extensible compiler.
However, I think we can agree that separating the core pieces of the code into a compiler library, and trying to acheive loose coupling between components is a good idea.
Thankfully the Koka compiler already is designed well which will help with acheiving low coupling.

# Notes on translation

There will of course be changes, as the Koka language has different features and strengths we can leverage than the original Koka Haskell compiler.

For example, all usages of type-classes will either be translated into:

- algebraic effects - for state / environment / reader / writer / logging / and error effects
- or implicits - for generic accessors, and other type-polymorphic code

Files that are translated will have a copyright that matches the Koka compiler's copyright acknowledging the original authors, as well as the translation author. 
The files will also have a comment with a hash indicating the commit of Koka's Haskell compiler that the source was last updated from, and comments explaining the differences, and the missing or incomplete features.

## Repository layout

The repository is self-contained: a clone builds the compiler with no other
checkout on the machine.

| directory | what it is |
| --- | --- |
| `compiler/` | the compiler itself |
| `lib/` | the standard library (`std/...`), the default `--sharedir` |
| `kklib/` | the C runtime |
| `test/` | the test corpus and the port's own tests |
| `util/`, `doc/`, `support/`, `samples/` | packaging (`util/bundle.kk`), documentation, editor support, samples |
| `scripts/` | build, benchmark and test drivers |
| `vendor/isocline/` | the one remaining submodule (the REPL's line editor) |

The compiler finds `lib` and `kklib` through its share directory, which it
derives from its own location: this repository when run from a build here, and
`<prefix>/share/koka/v<version>` when installed by `util/bundle.kk`.
`--sharedir` overrides it.

Containers and utilities the compiler needs live in the standard library where
they are generally useful (`std/data/rb-map`, `std/data/int-map`,
`std/data/sort`, `std/data/json`, `std/test`, and the list, char and vector
additions in `std/core`). What is specific to a compiler stays in
`compiler/lib` -- the pretty printer above all, whose API follows upstream's
`Lib/PPrint.hs` because the whole compiler prints through it.

## Building

Build the compiler with a compiler: the pinned one under `.koka/bootstrap/`, or
any recent build of this repository.

```bash
.koka/bootstrap/driver -i. -c -O2 --target=c compiler/main/driver.kk
```

The reference (Haskell) compiler is the fallback, through the `./koka` wrapper
-- it passes `--sharedir` so the reference compiler uses THIS repository's
standard library rather than its own:

```bash
./koka -i. -c -O2 compiler/main/driver.kk
```

## The pinned driver

`.koka/bootstrap/driver` is a known-good build of this compiler, pinned deliberately and never rewritten by a build.
It is not in git: a fresh clone builds the driver once (with `./scripts/build-driver.sh`, which uses the reference compiler) and pins it with `./scripts/build-driver.sh --pin`.

It also compiles projects outside this repository, and is the recommended compiler for koka-community packages: it finds this repository's `lib` (the standard library) and `kklib` from its own location, so no `--sharedir` is needed.

```bash
cd ../my-package
../compiler/.koka/bootstrap/driver -i. -c --output=.koka/bin/my-app src/main.kk
```

- The directory of `--output=<file>` (or `-o <file>`) must already exist.
- Constructors larger than 128 words (roughly 100+ fields) crash when allocated: `kk_block_alloc_at` always uses mimalloc's small-object path.

## Running the unit tests

```bash
./koka -e run-tests.kk        # or: <a built driver> -e run-tests.kk
```

Suites are discovered automatically from `test/**/*-test.kk`; each module
exposes `fun suite()`. No registration step.

Known-red: `test/lib/json-test.kk` expects `//` comments to be accepted, which
`std/data/json`'s parser does not implement. `parse-json` has no callers in the
compiler, so this is left failing rather than fixed here.

The fidelity gate is separate and lives in `scripts/test-runner.kk`, which runs
the corpus in `test/` (upstream's, brought into this repository) against the
port. Unlike the Python harness it
replaced, it must be COMPILED first (a few minutes; the binary is cached under
`.koka/` until the script changes):

```
./koka -O2 --no-buildhash -c scripts/test-runner.kk
./.koka/v3.2.7/clang-drelease/scripts_test_dash_runner__main
```

It takes an optional substring filter (`... __main static/wrong`) to run one
directory, and honours a few environment variables:

| var | effect |
| --- | --- |
| `KOKA_TEST_JOBS` | worker count (default 8) |
| `KOKA_TEST_DIFF=1` | print the full expected/actual for every failure |
| `KOKA_TEST_MODE=inprocess` | drive the compiler as a library instead of one process per test (currently slower and less faithful; see the notes in the script) |
| `KOKA_TEST_ROOT` | repository root, for running the suite from elsewhere (default: the working directory) |

## Native prerequisites

`std/text/regex` needs pcre2, which `extern import c { vcpkg=..; conan=.. }`
installs on demand. isocline (used by the REPL) is in neither vcpkg nor conan,
so the `vendor/isocline` submodule is built once into a static library:

    scripts/install-isocline.sh [prefix]

With no argument it installs `libisocline.a` and `isocline.h` into the first
writable prefix the compiler already searches (`/opt/homebrew`, `/usr/local`,
`/opt/local`); pass a prefix explicitly to override, and build with
`--cclibdir <prefix>/lib` if you choose one outside that list.

The submodule needs `git submodule update --init vendor/isocline` first. The
script compiles isocline's own single-translation-unit source (`src/isocline.c`,
which is what upstream's CMakeLists builds by default). Contributing an isocline
port to vcpkg would let `compiler/lib/isocline.kk` drop the script entirely and
say `{ vcpkg="isocline"; library="isocline" }`, like `std/text/regex.kk`.
