#!/bin/sh
# Build the port's driver binary.
#
# A warm rebuild of the driver (compiler modules already in the cache) is the
# pathological workload on BOTH the port and upstream -- it spends its time in
# interface parsing and reports nothing useful about a code change. Never
# benchmark or validate against one.
#
#   ./scripts/build-driver.sh          # std warm, all compiler modules cold (default)
#   ./scripts/build-driver.sh --cold   # everything cold
#   ./scripts/build-driver.sh --port   # INCREMENTAL build with the PINNED port binary (stage 1 -> stage 2)
#   ./scripts/build-driver.sh --cold-port # same, but start from scratch (baseline only)
#   ./scripts/build-driver.sh --pin [bin] # pin <bin>, or the newest built driver, as the bootstrap
#   ./scripts/build-driver.sh --guard  # drop artifacts written by a different compiler
#
# std-warm works because build artifacts are prefix-separated: std_* vs compiler_*.
#
# ---------------------------------------------------------------------------
# --port: iterate roughly 2.2x faster
#
# The port builds the 206-module driver in ~256s where the reference compiler
# takes ~9-10 minutes, and most compiler edits touch a module that nearly
# everything imports, so an "incremental" rebuild is near-full either way.
#
# The bootstrap binary is PINNED and never rewritten by a build. That is what
# makes this safe even when the change under test is to the interface FORMAT:
# stage 1 is a fixed, known-good compiler, so building stage 2 is reproducible,
# and a format mistake shows up as a stage-2 test failure instead of poisoning
# the next build. Do NOT roll the bootstrap forward automatically -- a rolling
# bootstrap amplifies a bad change into every later build. Re-pin deliberately,
# after the gates pass.
#
# The reference compiler is still the fidelity oracle: keep building with it at
# commit boundaries, and for any port-vs-upstream comparison.
#
# WHY A SEPARATE BUILD TAG: the build directory hash covers the flags and the
# compiler VERSION, not the IDENTITY of the compiler binary. Artifacts written
# by a different compiler are therefore reused silently -- that has produced a
# one-minute "rebuild" that reused 205 of 206 modules. A dedicated tag keeps
# bootstrap output apart from reference output by construction. (Source and
# transitive-dependency invalidation is a different mechanism and works
# correctly: editing a module three levels down rebuilds every dependent.)
set -eu
cd "$(dirname "$0")/.."
ROOT=$(pwd)
BOOTSTRAP=${KOKA_BOOTSTRAP:-$ROOT/.koka/bootstrap/driver}
INC="-i$ROOT"

case "${1:-}" in
  --pin)
    # Pins an EXISTING binary, never builds one: the given path, else the most
    # recently built driver, from a port build (.koka/v3.2.7-bootstrap) or a
    # reference build (.koka/v3.2.7) alike.
    built=${2:-$(ls -t "$ROOT"/.koka/v3.2.7-bootstrap/clang-*/compiler_main_driver__main \
                        "$ROOT"/.koka/v3.2.7/clang-*/compiler_main_driver__main 2>/dev/null | head -1)}
    [ -n "$built" ] && [ -x "$built" ] || { echo "[build-driver] no driver binary to pin" >&2; exit 1; }
    mkdir -p "$(dirname "$BOOTSTRAP")"
    if [ -e "$BOOTSTRAP" ]; then
      cp -p "$BOOTSTRAP" "$BOOTSTRAP.$(date -r "$BOOTSTRAP" +%Y-%m-%d-%H%M)"
      # A copy OVER an executable keeps its inode, and macOS then kills the new
      # binary on launch (code-signature cache mismatch, exit 137): remove first.
      rm "$BOOTSTRAP"
    fi
    cp "$built" "$BOOTSTRAP"
    echo "[build-driver] pinned $built"
    echo "[build-driver]     as $BOOTSTRAP"
    exit 0 ;;
  --port)
    [ -x "$BOOTSTRAP" ] || {
      echo "[build-driver] no pinned bootstrap at $BOOTSTRAP" >&2
      echo "[build-driver] build one with the reference compiler, then: $0 --pin" >&2
      exit 1; }
    echo "[build-driver] stage 1: $BOOTSTRAP"
    # INCREMENTAL on purpose -- do NOT wipe. Warm rebuilds are the iteration
    # loop; a cold build is for a baseline, not for development. The bootstrap
    # is pinned and does not move, so the only thing that could poison this
    # directory is a DIFFERENT compiler having written to it, which the guard
    # catches. Pass --cold-port if you genuinely want to start over.
    "$ROOT/scripts/cache-guard.sh" --fix "$BOOTSTRAP" "$ROOT/.koka/v3.2.7-bootstrap" || true
    exec "$BOOTSTRAP" $INC -O2 -c --buildtag=bootstrap compiler/main/driver.kk ;;
  --cold-port)
    [ -x "$BOOTSTRAP" ] || { echo "[build-driver] no pinned bootstrap at $BOOTSTRAP" >&2; exit 1; }
    echo "[build-driver] stage 1 (COLD): $BOOTSTRAP"
    rm -rf "$ROOT/.koka/v3.2.7-bootstrap"
    exec "$BOOTSTRAP" $INC -O2 -c --buildtag=bootstrap compiler/main/driver.kk ;;
  --cold)
    echo "[build-driver] fully cold"; rm -rf .koka ;;
  --guard)
    # artifacts a DIFFERENT compiler wrote are reused silently; drop them
    exec "$ROOT/scripts/cache-guard.sh" --fix "$(cd "${KOKA_DEV_DIR:-$HOME/koka/.worktrees/dev-compiler}" && stack exec which koka)" "$ROOT"/.koka/v3.2.7/clang-* ;;
  *)
    echo "[build-driver] std warm, compiler cold"
    n=0
    for d in .koka/v3.2.7/clang-*; do
      [ -d "$d" ] || continue
      c=$(ls "$d" 2>/dev/null | grep -c '^compiler_' || true)
      n=$((n + c))
      find "$d" -maxdepth 1 \( -name 'compiler_*' -o -name 'scripts_*' \) -delete
    done
    echo "[build-driver] removed $n compiler artifacts"
    [ "$n" -eq 0 ] && echo "[build-driver] WARNING: nothing removed -- this build is WARM" ;;
esac
# The reference compiler may have been rebuilt since these artifacts were
# written, and the build directory hash does not cover the compiler's identity.
"$ROOT/scripts/cache-guard.sh" --fix "$(cd "${KOKA_DEV_DIR:-$HOME/koka/.worktrees/dev-compiler}" && stack exec which koka)" "$ROOT"/.koka/v3.2.7/clang-* || true
exec ./koka -O2 -c compiler/main/driver.kk
