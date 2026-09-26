#!/bin/sh
# Keep the upstream PR stack consistent after PR feedback changes a layer.
#
# RUN THIS IN THE HASKELL CHECKOUT (koka-lang/koka), not here: it operates on the
# `tim/*` branches that carry this port's fixes upstream. It lives in this repo
# only so it is version controlled alongside the work it serves.
#
# The stack is a LINE: each layer is based on the one below it, so the TOP layer
# is already "everything combined" -- `tim/all` is just a name for that.
#
# Each layer records the commit it was based on (`branch.<layer>.stackBaseRev`),
# which is what makes restacking exact: amending a layer rewrites it, and a
# merge-base against the rewritten branch would then sweep the OLD version of
# that layer into the next one's rebase. Replaying `recorded-base..layer` avoids
# that.
#
#   git checkout tim/iface-roundtrip && ...edit... && git commit --amend
#   util/restack.sh
#
# `gh stack sync` does the same rebasing AND retargets the pull requests; this is
# the plain-git equivalent, and is also what updates `tim/all`.
set -eu
BASE=${BASE:-upstream/dev}
LAYERS="tim/runtime-thread-safety tim/std-async-threads tim/bslice-bytes-borrow tim/ref-update tim/iface-roundtrip tim/specialize-simplify tim/parc-reuse tim/infer-effects"
prev=$BASE
for b in $LAYERS; do
  recorded=$(git config --get "branch.$b.stackBaseRev" || git rev-parse "$prev")
  if [ "$recorded" != "$(git rev-parse "$prev")" ]; then
    echo "restacking $b onto $prev"
    git rebase --onto "$prev" "$recorded" "$b"
  fi
  git config "branch.$b.stackBaseRev" "$(git rev-parse "$prev")"
  prev=$b
done
if [ "$(git symbolic-ref -q --short HEAD || true)" = "tim/all" ]; then
  git reset --hard "$prev"
else
  git branch -f tim/all "$prev"
fi
echo "tim/all -> $prev ($(git rev-parse --short tim/all))"
