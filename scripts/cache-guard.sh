#!/bin/sh
# Refuse to reuse build artifacts that a DIFFERENT compiler produced.
#
#   scripts/cache-guard.sh <compiler-binary> <build-dir>...      # check, exit 1 if stale
#   scripts/cache-guard.sh --fix <compiler-binary> <build-dir>...# check and delete them
#
# WHY THIS EXISTS. A build directory's name hashes the FLAGS and the compiler
# VERSION -- not the identity of the compiler BINARY. Rebuild the same sources
# with a different compiler into the same directory and every artifact the old
# compiler wrote is reused silently. Observed twice in one session: a "rebuild"
# after changing the reference compiler recompiled 1 of 206 modules and relinked
# in ~1 minute, producing a binary that looked new (different md5) but was
# byte-identical in size because 205 modules came from the previous compiler.
# A benchmark run against it would have measured the OLD codegen.
#
# This is NOT the source/transitive-dependency check, which works correctly:
# editing a module three levels down rebuilds every dependent. This is purely
# about the compiler that produced the artifacts.
#
# The test is mtime: any .kki/.o older than the compiler binary was written by
# something else. Conservative in the right direction -- rebuilding when you did
# not need to costs time; reusing when you should not have costs a wrong answer.
set -eu
fix=0
if [ "${1:-}" = "--fix" ]; then fix=1; shift; fi
bin=${1:?usage: cache-guard.sh [--fix] <compiler-binary> <build-dir>...}
shift
[ -x "$bin" ] || { echo "[cache-guard] not executable: $bin" >&2; exit 2; }
rc=0
for d in "$@"; do
  [ -d "$d" ] || continue
  # `-newer <file>`, NOT `-newermt @epoch`: the latter is rejected by BSD find
  # ("Can't parse date/time"), and with stderr suppressed this guard counted 0
  # stale artifacts and passed silently -- failing OPEN, which is worse than not
  # having it. stderr stays visible here for the same reason.
  stale=$(find "$d" \( -name '*.kki' -o -name '*.o' \) ! -newer "$bin" | wc -l | tr -d ' ')
  total=$(find "$d" \( -name '*.kki' -o -name '*.o' \) | wc -l | tr -d ' ')
  [ "$stale" -eq 0 ] && continue
  echo "[cache-guard] $d: $stale of $total artifacts predate $(basename "$bin")"
  if [ "$fix" -eq 1 ]; then
    find "$d" \( -name '*.kki' -o -name '*.o' -o -name '*.c' -o -name '*.h' \) ! -newer "$bin" -delete
    echo "[cache-guard]   removed them; this build will be cold"
  else
    echo "[cache-guard]   REFUSING: rerun with --fix, or use a build tag of its own" >&2
    rc=1
  fi
done
exit $rc
