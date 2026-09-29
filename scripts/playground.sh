#!/bin/sh
# Build the web playground (web/playground) assets into web/playground/public.
#
#   scripts/playground.sh [wasm|precompile|deploy|all]    # default: all
#   cd web/playground && npm install && npx vite           # then serve it
#
#   wasm        the compiler (compiler/main/playground.kk) as a WASI module,
#               built by the port with wasi-sdk's clang
#   precompile  the standard library compiled to JavaScript, so a compile in
#               the browser only compiles the user's own modules
#   deploy      library and sample sources, icons, the service worker, and the
#               manifests the frontend fetches
#
# Upstream builds the same assets with util/playground.kk from a GHC-wasm build
# of the reference compiler; the frontend and its file-system layout are the
# same, see web/playground/src/editor/flags.ts.
#
# KOKA selects the (native) port binary that does the building; it defaults to
# the pinned bootstrap. wasi-sdk is found through WASI_SDK_PATH, ~/.wasi-sdk or
# ~/wasi-sdk-*; wasm-opt (binaryen) is used when on PATH or in ~/emsdk.
set -eu
cd "$(dirname "$0")/.."
ROOT=$(pwd)
KOKA=${KOKA:-$ROOT/.koka/bootstrap/driver}
PUB=$ROOT/web/playground/public
BUILD=$ROOT/.koka/playground

info() { printf '[playground] %s\n' "$*"; }

[ -x "$KOKA" ] || { info "no port binary at $KOKA (set KOKA, or pin one with scripts/build-driver.sh --pin)"; exit 1; }

find_wasi_clang() {
  for d in "${WASI_SDK_PATH:-}" "$HOME/.wasi-sdk" $(ls -d "$HOME"/wasi-sdk-* 2>/dev/null | sort -r); do
    if [ -n "$d" ] && [ -x "$d/bin/clang" ]; then WASI_CLANG="$d/bin/clang"; return 0; fi
  done
  info "wasi-sdk not found: install it (https://github.com/WebAssembly/wasi-sdk) or set WASI_SDK_PATH"; exit 1
}

build_wasm() {
  find_wasi_clang
  info "building the compiler for wasm with $WASI_CLANG"
  # A build directory of its own: its hash does not identify the compiler that
  # wrote it, and this one is written by another C compiler for another target.
  "$KOKA" --sharedir="$ROOT" -i"$ROOT" --target=wasm -O2 --cc="$WASI_CLANG" --builddir="$BUILD" \
          -c compiler/main/playground.kk --output="$BUILD/koka-playground"
  wasm="$BUILD/koka-playground.wasm"
  [ -f "$wasm" ] || { info "build produced no $wasm"; exit 1; }
  mkdir -p "$PUB"
  opt=$(command -v wasm-opt || true)
  [ -z "$opt" ] && [ -x "$HOME/emsdk/upstream/bin/wasm-opt" ] && opt="$HOME/emsdk/upstream/bin/wasm-opt"
  if [ -n "$opt" ]; then
    info "optimizing with $opt -O3"
    "$opt" -O3 --enable-bulk-memory "$wasm" -o "$PUB/koka-playground.wasm"
  else
    cp "$wasm" "$PUB/koka-playground.wasm"
  fi
  info "$(wc -c < "$PUB/koka-playground.wasm" | tr -d ' ') bytes: $PUB/koka-playground.wasm"
}

precompile() {
  info "precompiling the standard library to javascript"
  # the same flags the playground passes (flags.ts) apart from the paths, so the
  # interfaces are for the `js-debug` variant it looks up under --libdir
  rm -rf "$BUILD/js"
  "$KOKA" --sharedir="$ROOT" --target=js --library --builddir="$BUILD/js" lib/toc.kk
  out=$(ls -d "$BUILD"/js/v*/js-debug-* | head -1)
  [ -d "$out" ] || { info "precompile produced no js-debug directory under $BUILD/js"; exit 1; }
  rm -rf "$PUB/precompiled"
  mkdir -p "$PUB/precompiled"
  cp "$out"/*.kki "$out"/*.mjs "$PUB/precompiled/"
  info "$(ls "$PUB/precompiled" | wc -l | tr -d ' ') precompiled files"
}

# a JSON array of the files under $1 with extension $2 (any when empty), as
# paths relative to $1
manifest() {
  (cd "$1" && find . -type f -name "*$2" | sed 's|^\./||' | sort) |
    awk 'BEGIN { printf "[" } { printf "%s\"%s\"", (NR>1 ? "," : ""), $0 } END { printf "]\n" }'
}

deploy() {
  info "deploying sources and manifests"
  mkdir -p "$PUB/lib"
  rm -rf "$PUB/lib/std" "$PUB/samples"
  cp -R lib/std "$PUB/lib/std"
  cp -R samples "$PUB/samples"
  icons=support/vscode/koka.language-koka/images
  if [ -d "$icons" ]; then
    cp "$icons/koka-logo-filled.svg" "$PUB/koka-icon.svg"
    cp "$icons/koka-logo-filled-dark.svg" "$PUB/koka-icon-dark.svg"
    cp "$icons/koka-logo-filled-light.svg" "$PUB/koka-icon-light.svg"
  fi
  coi=web/playground/node_modules/coi-serviceworker/coi-serviceworker.js
  if [ -f "$coi" ]; then cp "$coi" "$PUB/"; else info "no $coi: run 'npm install' in web/playground first"; fi
  manifest "$PUB/lib" ".kk" > "$PUB/stdlib-manifest.json"
  manifest "$PUB/samples" ".kk" > "$PUB/samples-manifest.json"
  [ -d "$PUB/precompiled" ] && manifest "$PUB/precompiled" "" > "$PUB/precompiled-manifest.json"
  info "done: $PUB"
}

case "${1:-all}" in
  wasm)       build_wasm ;;
  precompile) precompile ;;
  deploy)     deploy ;;
  all)        build_wasm; precompile; deploy ;;
  *)          info "usage: $0 [wasm|precompile|deploy|all]"; exit 1 ;;
esac
