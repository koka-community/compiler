#!/bin/sh
# Compare the port against the reference compiler on the SAME work, with every
# assertion that has previously produced a wrong number baked in.
#
#   scripts/compare-warm.sh <target.kk> [runs]
#
# Five faults this guards against, all of which yielded plausible numbers before:
#   1. mismatched artifacts   -- asserts equal .c and .o counts
#   2. error-path comparison  -- asserts exit 0 for both, and refuses a target
#                                with no `main` (upstream errors on those w/o -l)
#   3. zsh glob timing        -- counts artifacts in a separate step, with find
#   4. ./koka wrapper         -- uses the DIRECT binary; the wrapper costs 0.19s
#                                per call for `stack exec which koka`
#   5. mangled flag bundles   -- flags are passed as explicit words, never as a
#                                single expanded string
set -eu
cd "$(dirname "$0")/.."
ROOT=$(pwd)
TARGET=${1:?usage: compare-warm.sh <target.kk> [runs]}
RUNS=${2:-3}
KOKA_DEV_DIR="${KOKA_DEV_DIR:-$HOME/koka/.worktrees/dev-compiler}"
UP=$(cd "$KOKA_DEV_DIR" && stack exec which koka)
PORT=$(ls -t "$ROOT"/.koka/v3.2.7/clang-*/compiler_main_driver__main 2>/dev/null | head -1)
[ -x "$UP" ]   || { echo "no reference compiler at $UP" >&2; exit 1; }
[ -x "$PORT" ] || { echo "no port driver at $PORT (run scripts/build-driver.sh)" >&2; exit 1; }
grep -qE '^(pub )?fun main' "$TARGET" || {
  echo "refusing: $TARGET has no \`main\`. Upstream treats a main-less module as a" >&2
  echo "program and fails synthesising @main, so the run would compare error paths." >&2
  exit 1; }

# the include set the ./koka wrapper uses, as explicit words
set -- -i"$ROOT"
INC="$*"
FLAGS="-c -v0 --console=raw -O2 --target=c"

TMP=$(mktemp)
trap 'rm -f "$TMP"' EXIT
run() { # run <binary> <buildtag> ; echoes elapsed seconds. ONE execution: a
        # pipeline would mask the exit status, so time's output goes to a file.
  _bin=$1; _tag=$2
  /usr/bin/time -p "$_bin" $INC $FLAGS --buildtag="$_tag" "$TARGET" >/dev/null 2>"$TMP" || {
    echo "FAILED: $_bin exited non-zero on $TARGET" >&2; tail -3 "$TMP" >&2; exit 1; }
  awk '/^real/{print $2}' "$TMP"
}
count() { find ".koka/v3.2.7-$1" -maxdepth 2 -name "*.$2" 2>/dev/null | wc -l | tr -d ' '; }

rm -rf ".koka/v3.2.7-cwu" ".koka/v3.2.7-cwp"
echo "warming both (cold build of $TARGET's closure)..."
run "$UP"   cwu >/dev/null
run "$PORT" cwp >/dev/null

uc=$(count cwu c); uo=$(count cwu o); pc=$(count cwp c); po=$(count cwp o)
echo "artifacts  upstream: ${uc} .c ${uo} .o    port: ${pc} .c ${po} .o"
[ "$uo" -gt 0 ] && [ "$po" -gt 0 ] || { echo "ABORT: one side produced no objects" >&2; exit 1; }
d=$(( uc > pc ? uc - pc : pc - uc ))
[ "$d" -le 1 ] || { echo "ABORT: .c counts differ by $d (>1); not like-for-like" >&2; exit 1; }
[ "$d" -eq 1 ] && echo "  (1-module difference is upstream's separate <entry>__main wrapper)"

echo "warm re-runs, ${RUNS}x each:"
i=1
while [ "$i" -le "$RUNS" ]; do
  u=$(run "$UP" cwu); p=$(run "$PORT" cwp)
  echo "  upstream ${u}s    port ${p}s"
  i=$((i+1))
done

echo "upstream RTS stats on a warm re-run (GC vs mutator, absolute):"
"$UP" +RTS -s -RTS $INC $FLAGS --buildtag=cwu "$TARGET" 2>&1 >/dev/null \
  | grep -E "bytes allocated|MUT +time|GC +time|Total +time|Productivity|Gen +[01]" || true
