# Koka Playground

A browser-based Koka editor and compiler. The compiler is this repository's port, built as a WASI module and run in a Web Worker; programs compile to JavaScript and run in the page.

The frontend is upstream's (`web/playground` in koka-lang/koka), which runs a GHC-wasm build of the reference compiler. The port slots into the same worker protocol and file-system layout, see `src/editor/flags.ts`.

## Architecture

```
┌──────────────────────────────────────┐
│  React frontend                      │
│  Monaco editor                       │
└────────────────┬─────────────────────┘
                 │ compile & run
         ┌───────▼──────────────┐
         │ Compiler worker      │
         │ koka-playground.wasm │
         └──────────────────────┘
```

The worker runs the compiler as a WASI command (`compiler/main/playground.kk`): flags and the module name on the command line, the module's source on stdin, the standard library and precompiled interfaces in an in-memory file system. It prints the result as a JSON line on stdout and streams the build log on stderr.

The language-server backend (`koka-lsp.wasm`) is not built yet: the port's language server reads stdin through libuv, which has no WASI build. The frontend therefore defaults to the standalone compiler and only starts the language server when it is selected.

## Build & run

Prerequisites: [wasi-sdk](https://github.com/WebAssembly/wasi-sdk) (`WASI_SDK_PATH`, `~/.wasi-sdk` or `~/wasi-sdk-*`), a native build of the port (`scripts/build-driver.sh`), and Node.js 18+. binaryen's `wasm-opt` is used when found. Tested with wasi-sdk 25; the wasi-libc in 34.0-rc.1 defines `PAGE_SIZE` as a link-time address, which mimalloc cannot use in a preprocessor test.

```bash
cd web/playground && npm install && cd ../..
scripts/playground.sh            # wasm + precompile + deploy into web/playground/public
node web/playground/test/test-wasm.mjs
cd web/playground && npx vite --host
```

`scripts/playground.sh wasm|precompile|deploy` runs one step. `KOKA=<port binary>` chooses the native compiler that does the building.

## How the port runs without threads

The compiler is built with wasi-sdk rather than emscripten: emscripten's standalone WASI output has no file system (its `open` accepts only the standard streams). WASI has no processes either, so kklib's `run-system` and `run-system-read` report failure there.

A WASI host has one thread and no libuv:

- `std/async` uses `async/api/wasi/evloop`, a timer queue, for `host=wasm`, and `std/async/thread` uses the cooperative backend, where `native-threads()` is False.
- When `native-threads()` is False the build does its work on one strand: `compile-graph-rpc` is skipped and the resolve walk compiles each stale module in dependency order, and interfaces load and resolve their inline sections in order.
- The in-memory file system records no modification times; `file-mtime` reports an existing file as at least 1, since 0 means missing.

## Known limitations

- **No language server** (see above): no hover, completion or diagnostics while typing.
- **`SharedArrayBuffer`** is only needed by the language-server worker; `coi-serviceworker` provides the cross-origin isolation it requires.
