#!/bin/sh
# Compile targets that have REAL SOURCE dependencies.
#
# Why this exists: the 440-test upstream sweep is almost entirely single files
# importing only std/* modules, which resolve from interfaces (.kki) and never
# exercise source-module discovery or the multi-module build walk. A segfault
# in the dependency-discovery pre-pass sat behind a fully green 420/17/1 sweep
# because of exactly that gap. Any change to compile/build.kk, compile/schedule.kk
# or the driver's module walk must pass this as well as the sweep.
#
#   scripts/multimodule-gate.sh          # fast: two multi-module targets
#   scripts/multimodule-gate.sh --full   # also builds the whole 97-module compiler
#
# The default targets already fan out over many source modules, which is what
# catches discovery/walk bugs, and finish in about a minute against a warm
# cache. `--full` additionally compiles compiler/main/driver.kk; on a cold
# cache that is a ~25 minute build, so it is opt-in rather than the default.
#
# Exits nonzero on the first target that fails, and prints its phase timings.
set -eu
cd "$(dirname "$0")/.."

BIN=${KOKA_GATE_BIN:-$(ls -t .koka/v3.2.7/clang-*/compiler_main_driver__main 2>/dev/null | head -1)}
if [ -z "$BIN" ]; then
  echo "no release port binary; build with ./koka -O2 --no-buildhash -c compiler/main/driver.kk" >&2
  exit 1
fi
echo "gate binary: $BIN"
# Artifacts written by a DIFFERENT compiler are reused silently -- the build
# directory hash covers flags and version, not the compiler's identity. A gate
# run against a mixed cache reports on code that is no longer there; that is how
# a clean gate turned into a kind error on a cache holding three compilers'
# output.
./scripts/cache-guard.sh --fix "$BIN" .koka/v3.2.7-mmgate 2>/dev/null || true

FLAGS="-c -v0 --console=raw -O2 --buildtag=mmgate --target=c --include=."

# Increasing dependency depth. build.kk alone pulls in most of the front end,
# so both defaults exercise real source-module discovery and the build walk.
TARGETS="compiler/compile/schedule.kk compiler/compile/build.kk"
# The whole compiler, the widest graph there is. Opt-in -- expensive on a cold
# cache.
if [ "${1:-}" = "--full" ]; then
  TARGETS="$TARGETS compiler/main/driver.kk"
fi

fail=0
for t in $TARGETS; do
  printf '  %-40s ' "$t"
  if out=$(KOKA_TIMING=1 $BIN $FLAGS "$t" 2>&1); then
    # Exit status ALONE is not a gate. The parallel pre-pass absorbed every
    # compile failure into a per-module `Left` and let the sequential walk redo
    # the work, so a run with 152 `kind error`s still exited 0 and this script
    # printed "ok". Any diagnostic in the output is now a failure.
    errs=$(printf '%s\n' "$out" | grep -c -E 'kind error|type error|error:' || true)
    if [ "$errs" -ne 0 ]; then
      echo "FAIL ($errs diagnostics, exit 0)"
      printf '%s\n' "$out" | grep -E 'kind error|type error|error:' | head -10
      fail=1
      break
    fi
    disc=$(printf '%s' "$out" | grep 'TIMING discover' | head -1 || true)
    echo "ok    ${disc}"
  else
    st=$?
    echo "FAIL (exit $st)"
    printf '%s\n' "$out" | tail -20
    fail=1
    break
  fi
done

# Incremental: a module recompiled because a DEPENDENCY changed, while its own
# interface is newer than its source, still resolves its relative and
# host-conditional imports. Build, touch the backend std/async/thread selects,
# rebuild; the rebuild must recompile std/async/thread (a no-op rebuild would
# pass vacuously) and report nothing.
if [ "$fail" -eq 0 ]; then
  printf '  %-40s ' "incremental: relative imports"
  IFLAGS="-c --console=raw -O2 --buildtag=mmgate-inc --target=c --include=."
  if ! $BIN $IFLAGS scripts/gate-incremental-import.kk > /dev/null 2>&1; then
    echo "FAIL (first build)"; fail=1
  else
    touch lib/std/async/api/uv/thread.kk
    out=$($BIN $IFLAGS scripts/gate-incremental-import.kk 2>&1) && st=0 || st=$?
    errs=$(printf '%s\n' "$out" | grep -c -E 'kind error|type error|error' || true)
    rechecked=$(printf '%s\n' "$out" | grep -c -E 'check +: std/async/thread$' || true)
    if [ "$st" -ne 0 ] || [ "$errs" -ne 0 ] || [ "$rechecked" -ne 1 ]; then
      echo "FAIL (exit $st, $errs diagnostics, std/async/thread rechecked $rechecked times)"
      printf '%s\n' "$out" | grep -E 'error' | head -5
      fail=1
    else
      echo "ok"
    fi
  fi
fi

# Transitive: editing the bottom of a chain r -> y -> z -> a -> b -> c must
# recompile every module above it, and all of them through the parallel
# orchestrator -- none left to the sequential walk (`resolve compile-source`).
# Then a rebuild with nothing changed must compile nothing. Then the earlier-
# build case: `x` also uses `b`, so building `x` after editing `c` rebuilds
# `c` and `b`; building `r` next must still rebuild `a`, `z` and `y`, whose
# interfaces are now older than `b`'s. Works on a copy so the fixture is never
# edited.
if [ "$fail" -eq 0 ]; then
  printf '  %-40s ' "incremental: transitive chain"
  W=.koka/gate-chain
  rm -rf "$W"; cp -R scripts/gate-incremental-chain "$W"
  CFLAGS="--console=raw -O2 --buildtag=mmgate-chain --target=c --include=. -e"
  first=$($BIN $CFLAGS "$W/r.kk" 2>&1 | tail -1)
  $BIN $CFLAGS "$W/x.kk" > /dev/null 2>&1 || true
  printf '// edited by multimodule-gate.sh\npub fun k() : int\n  2\n' > "$W/c.kk"
  out=$(KOKA_TRACE_ORCH=1 $BIN $CFLAGS "$W/r.kk" 2>&1) && st=0 || st=$?
  walked=$(printf '%s\n' "$out" | grep -c 'resolve compile-source' || true)
  orch=""
  for m in c b a z y; do
    printf '%s\n' "$out" | grep -q -E "ORCH compiled +$m " || orch="$orch $m"
  done
  again=$(KOKA_TRACE_ORCH=1 $BIN $CFLAGS "$W/r.kk" 2>&1) || true
  recompiled=$(printf '%s\n' "$again" | grep -c -E 'ORCH compiled|resolve compile-source' || true)
  printf '// edited by multimodule-gate.sh\npub fun k() : int\n  3\n' > "$W/c.kk"
  xout=$($BIN $CFLAGS "$W/x.kk" 2>&1 | tail -1)
  later=$(KOKA_TRACE_ORCH=1 $BIN $CFLAGS "$W/r.kk" 2>&1) || true
  walked=$((walked + $(printf '%s\n' "$later" | grep -c 'resolve compile-source' || true)))
  for m in a z y; do
    printf '%s\n' "$later" | grep -q -E "ORCH compiled +$m " || orch="$orch later:$m"
  done
  if [ "$first" != "11111" ] || [ "$st" -ne 0 ] || ! printf '%s\n' "$out" | grep -q '^11112$' \
     || [ "$walked" -ne 0 ] || [ -n "$orch" ] || [ "$recompiled" -ne 0 ] \
     || [ "$xout" != "13" ] || ! printf '%s\n' "$later" | grep -q '^11113$'; then
    echo "FAIL (first=$first exit=$st walk-compiled=$walked not-orchestrated:${orch:- none} no-op-recompiled=$recompiled x=$xout)"
    printf '%s\n' "$out" | grep -E 'ORCH (compiled|resolve)|error|^[0-9]+$' | head -12
    fail=1
  else
    echo "ok"
  fi
fi

if [ "$fail" -ne 0 ]; then
  echo "multimodule gate: FAILED" >&2
  exit 1
fi
echo "multimodule gate: all targets ok"
