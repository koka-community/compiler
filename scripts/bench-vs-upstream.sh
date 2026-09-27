#!/bin/sh
# Port vs the reference compiler on the SAME source tree and flags.
#
#   scripts/bench-vs-upstream.sh warm-small | cold-small | warm-big | cold-big | module
#
# Each side gets its OWN buildtag (so its own build directory), and a cold case
# removes that directory first. Per AGENTS.md, one run is enough for anything
# over ~40s; the fast cases repeat and report the best.
set -eu
cd "$(dirname "$0")/.."
ROOT=$(pwd)
# Newest release driver, not a hard-coded hashed directory: the hashed dir
# changes with the flag set, and a stale path here fails as exit 127 inside
# `/usr/bin/time`, which reports "real 0.00" and looks like a fast build.
PORT=$(ls -t "$ROOT"/.koka/v3.2.7/clang-*/compiler_main_driver__main 2>/dev/null | head -1)
[ -n "$PORT" ] && [ -x "$PORT" ] || { echo "no release port binary; build with ./koka -O2 --no-buildhash -c compiler/main/driver.kk" >&2; exit 1; }
echo "port binary: $PORT"
UP=$(cd "${KOKA_DEV_DIR:-$HOME/koka/.worktrees/dev-compiler}" && stack exec which koka)
# -O2, matching what the port actually ships and is built with
# (`build-driver.sh`). This was -O1 for a long time, which measured a
# configuration nobody uses; the port-vs-upstream RATIOS were still valid (both
# sides ran the same flags) but the absolute numbers were not the real thing.
# `scripts/test-runner.kk` stays at -O1 on purpose -- it mirrors upstream's
# `test/Spec.hs`, which sets -O1 as the suite default with per-test .flags
# overrides.
FLAGS="-c -v0 --console=raw -O2 --target=c"
LIB=""
INC="-i$ROOT"

run() { # run <bin> <tag> <target> ; prints "real cpu par"
  /usr/bin/time -p "$1" $INC $FLAGS $LIB --buildtag="$2" "$3" >/dev/null 2>/tmp/bvu.err || {
    echo "FAILED $1 on $3" >&2; tail -3 /tmp/bvu.err >&2; exit 1; }
  awk '/^real/{r=$2} /^user/{u=$2} /^sys/{printf "%s %.1f %.2f\n", r, u+$2, (u+$2)/r}' /tmp/bvu.err
}
best() { # best of N, by wall
  _bin=$1; _tag=$2; _t=$3; _n=$4; _b=""
  i=1; while [ "$i" -le "$_n" ]; do
    o=$(run "$_bin" "$_tag" "$_t")
    [ -z "$_b" ] && _b="$o"
    [ "$(echo "$o" | awk '{print $1}')" \< "$(echo "$_b" | awk '{print $1}')" ] && _b="$o"
    i=$((i+1))
  done
  echo "$_b"
}
case "${1:?usage: bench-vs-upstream.sh <case>}" in
  # A target with no `main` MUST be built with -l: upstream treats a main-less
  # module as a program and fails synthesising @main, so without it the two
  # sides are not even running the same job (the port accepts it, upstream errors).
  small)  T=scripts/probe-tiny.kk;     LIB="";   N=3 ;;   # has main
  big)    T=compiler/main/driver.kk;   LIB="";   N=1 ;;   # has main: the whole compiler
  module) T=compiler/type/infer.kk;    LIB="-l"; N=1 ;;   # library module
  *) echo "unknown case $1" >&2; exit 1 ;;
esac
# A warm case still has to build the closure once. TIME that build rather than
# throwing it away -- on the big targets it is a ten-minute cold build, and the
# cold number is worth having for free.
for side in port upstream; do
  tag="bvu-$1-$side"
  bin=$PORT; [ "$side" = upstream ] && bin=$UP
  rm -rf ".koka/v3.2.7-$tag"
  # `run` is called inside $(...), where its `exit 1` only ends the subshell:
  # check the captured result, or a failed compile prints a blank timing line
  # and the script carries on with exit status 0
  cold=$(run "$bin" "$tag" "$T") && [ -n "$cold" ] || { echo "  $side cold FAILED" >&2; exit 1; }
  printf "  %-9s cold %s\n" "$side" "$cold"
  warm=$(best "$bin" "$tag" "$T" "$N") && [ -n "$warm" ] || { echo "  $side warm FAILED" >&2; exit 1; }
  printf "  %-9s warm %s\n" "$side" "$warm"
done
