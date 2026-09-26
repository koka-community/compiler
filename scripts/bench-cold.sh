#!/bin/sh
# Reproducible COLD-compile benchmark.
#
# Cold and warm builds have completely different profiles here (warm is
# dominated by interface parsing, cold by kind inference), so an optimisation
# must state which workload it targets and be measured on that one.
#
# Target: one module plus its full closure, built from an empty build dir.
# Reports wall AND cpu -- a change that trades wall for cpu (or vice versa)
# is a different thing than a change that removes work.
set -eu
cd "$(dirname "$0")/.."
BIN=${BIN:-$(ls -t .koka/v3.2.7/clang-*/compiler_main_driver__main 2>/dev/null | head -1)}
MOD=${MOD:-compiler/compile/schedule.kk}
N=${N:-3}
for i in $(seq 1 "$N"); do
  rm -rf /tmp/bench_cold
  /usr/bin/time -p "$BIN" -O2 -c --builddir=/tmp/bench_cold \
      -i. "$MOD" >/dev/null 2>/tmp/bench_cold.err || true
  awk '/^real|^user|^sys/{printf "%s=%s ", $1, $2} END{print ""}' /tmp/bench_cold.err
done
