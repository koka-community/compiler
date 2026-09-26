#!/bin/sh
# Build isocline (the vendor/isocline submodule) as a static library and
# install it where the compiler's `search-c-library` already looks.
#
# isocline is packaged in neither vcpkg nor conan, so `extern import c {
# vcpkg=..; conan=.. }` cannot fetch it the way std/text/regex.kk fetches
# pcre2. Strategy (1) of the same chain -- search installed library paths,
# deriving the include dir as the sibling of the lib dir's parent -- does work,
# so all this has to do is put `libisocline.a` and `isocline.h` under one
# prefix.
#
#   scripts/install-isocline.sh [prefix]
#
# With no argument it picks the first WRITABLE prefix the compiler searches
# (see `target-lib-search-dirs` in compiler/compile/link.kk).
set -eu
cd "$(dirname "$0")/.."
SRC=$(pwd)/vendor/isocline

if [ ! -f "$SRC/src/isocline.c" ]; then
  echo "error: $SRC is empty -- run: git submodule update --init vendor/isocline" >&2
  exit 1
fi

pick_prefix() {
  for p in /opt/homebrew /usr/local /opt/local; do
    if [ -d "$p/lib" ] && [ -w "$p/lib" ]; then echo "$p"; return; fi
  done
  echo ""
}

PREFIX=${1:-$(pick_prefix)}
if [ -z "$PREFIX" ]; then
  PREFIX=$HOME/.local
  echo "note: no writable system prefix found; installing to $PREFIX"
  echo "      that path is NOT searched by default -- build with:"
  echo "         --cclibdir $PREFIX/lib"
fi

CC=${CC:-cc}
BUILD=$(mktemp -d)
trap 'rm -rf "$BUILD"' EXIT

# `src/isocline.c` is isocline's own single-translation-unit build: it
# #includes every other source. Upstream's CMakeLists does exactly this
# (`set(ic_sources src/isocline.c)`); the per-file list is behind their
# opt-in IC_SEPARATE_OBJS.
echo "building isocline (static) with $CC ..."
$CC -c -O2 -DNDEBUG -I"$SRC/include" -o "$BUILD/isocline.o" "$SRC/src/isocline.c"
ar rcs "$BUILD/libisocline.a" "$BUILD/isocline.o"
ranlib "$BUILD/libisocline.a" 2>/dev/null || true

mkdir -p "$PREFIX/lib" "$PREFIX/include"
install -m 644 "$BUILD/libisocline.a" "$PREFIX/lib/libisocline.a"
install -m 644 "$SRC/include/isocline.h" "$PREFIX/include/isocline.h"

echo "installed:"
echo "  $PREFIX/lib/libisocline.a"
echo "  $PREFIX/include/isocline.h"
