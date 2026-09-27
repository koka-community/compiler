#!/bin/sh
# Regenerate compiler/syntax/lex.kk from compiler/syntax/koka.x.
#
#   scripts/regen-lexer.sh          # regenerate in place
#   scripts/regen-lexer.sh --check  # fail if the committed file is not what
#                                   # koka.x currently generates
#
# lex.kk is GENERATED. Hand-edits to it are silently reverted by the next
# regeneration -- three fixes had accumulated there once, including a
# parallel-build use-after-free. Change `koka.x`, or the fork's runtime template
# (`data/alex-effects.kk`), and regenerate.
#
# This must be run from the repo root and write to `compiler/syntax/lex.kk`,
# because two things in the output are derived from the invocation itself: the
# `/// LINE n "<path>"` directives come from the grammar path as given, and the
# `c file "inline/<name>"` include is derived from the OUTPUT file name. Running
# it any other way produces a file that differs from the committed one for no
# semantic reason -- which is what made regeneration look unfaithful.
#
# `-k` selects the Koka backend; without it alex emits Haskell.
set -eu
cd "$(dirname "$0")/.."

# Replaces compiler/alex.sh, which hard-coded a ../../../ path chain and had no
# way to check the committed file was current.
ALEX_SRC="${ALEX_SRC:-$HOME/koka-community/alex}"
ALEX="${ALEX:-}"
if [ -z "$ALEX" ]; then
  # The FORK's own build -- the alex in ~/.cabal/bin may be a year stale, and a
  # stale one silently produces a different scanner.
  ALEX=$(find "$ALEX_SRC/dist-newstyle" -type f -name alex -perm -111 2>/dev/null | head -1)
  [ -n "$ALEX" ] || ALEX=$(find "$ALEX_SRC/.stack-work" -type f -name alex -perm -111 2>/dev/null | head -1)
fi
[ -n "$ALEX" ] && [ -x "$ALEX" ] || {
  echo "no alex binary for the fork at $ALEX_SRC" >&2
  echo "  build it:  (cd $ALEX_SRC && cabal build)   # or: stack build" >&2
  exit 1; }
[ -f "$ALEX_SRC/data/alex-effects.kk" ] || {
  echo "no runtime template at $ALEX_SRC/data" >&2; exit 1; }

OUT=compiler/syntax/lex.kk
if [ "${1:-}" = "--check" ]; then
  TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
  cp "$OUT" "$TMP/lex.kk.committed"
  "$ALEX" -k --template="$ALEX_SRC/data" compiler/syntax/koka.x -o "$OUT"
  if cmp -s "$OUT" "$TMP/lex.kk.committed"; then
    echo "lex.kk is up to date with koka.x"
  else
    cp "$TMP/lex.kk.committed" "$OUT"
    echo "STALE: compiler/syntax/lex.kk is not what koka.x generates" >&2
    echo "  run scripts/regen-lexer.sh" >&2
    exit 1
  fi
else
  "$ALEX" -k --template="$ALEX_SRC/data" compiler/syntax/koka.x -o "$OUT"
  echo "regenerated $OUT from compiler/syntax/koka.x"
fi
