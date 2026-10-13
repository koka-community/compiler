# Mutual-recursion fusion (koka-lang/koka#900) in the port

Written 2026-10-12. The port of the pass is on the local branch `fusion` in this repository (commit `4e2c937`, not pushed); the upstream PR is `stack-usage` on TimWhiting/koka.

## Why it matters here

The playground runs the compiler as wasm. Without the wasm tail-call proposal, a C sibling call is a real call, so mutual tail recursion in the compiler grows the browser's worker stack, which is far smaller than a native one.
`handlers/ambient`, `handlers/nim`, `handlers/scoped` and `handlers/unix` crashed the playground compiler with "Maximum call stack size exceeded".

- The deepest frames were `std/data/int-map`'s `map-loop` and its lifted local `map-zip-up`: 846 frames of mutual tail calls (`node --stack-size=500`, frame histogram from the unoptimized wasm).
- clang's `-mtail-call` emits 47,813 `return_call`s in the compiler, but not these: both functions keep a frame on wasm's linear-memory stack, which rules out a sibling call.
- The other deep recursion is `extend-gamma` nesting one handler per definition group (about 56 levels for `nim`); fusion does not touch it.

## What the port does

`compiler/core/fusion.kk` translates `src/Core/Fusion.hs`, with the PR's supporting changes (`std/core/types` evidence, `kind/repr` scan padding, the `@coerce` rules in `core/simplify`, `core/ctail` and `core/monadic` seeing through `@coerce`, the pass in `compile/type-check`, regrouping before `ctail`, `--fno-fusion`).

- The PR's `test/cgen/mutrec` passes.
- The port fuses effect-polymorphic groups, `int-map`'s included, into a driver that loops (`goto kk__tailcall`).
- With the playground compiler built this way, the four samples above compile and run in Chrome. Under node, `nim` compiles with `--stack-size=500` (it overflowed before) but not 300.
- The pass silently does nothing when `std/core/types` lacks `@type-eq`: check that first if a group is not fused.

## Why it is not merged

The full corpus with the pass gives three new failures; the PR's own branch fails the same three in upstream's suite.

### `lazy/queue/physicists-stack`: a stack overflow, not a miscompile

- The fused binary segfaults with the default 8MB stack and prints the right `Checksum: 0` with `ulimit -s 65520`.
- On a minimal chain of lazy `Tail` thunks the deepest chain that evaluates drops from ~87,000 to ~12,800 with fusion (bisected, same compiler, `--fno-fusion` against default).
- The fused group is the lazy protocol (`lazy-eval`, `lazy-whnf`, `lazy-force`, `lazy-eval-locked`). Forcing a thunk is a non-tail call, and each level now goes through the driver several times, each time paying a full `@run` frame (128 bytes, it holds every member's locals; clang `-fstack-usage`) plus a wrapper frame (64), where the unfused functions take 48-64 bytes and partly inline into each other.
- The wrappers are not inlined at those non-tail sites, which the PR's design says they should be. Not yet explained.

### `parc/parc22` and `parc/parc23`: a definition-order change

- They fail with `--fno-fusion` too: the regroup before `ctail` runs on every module and reorders definitions (in `parc22`, `hello/i` moves later). The code is the same.

## Next steps

Upstream first, then the port:

1. Fuse a group only if every call between its members is a tail or modulo-cons call. A non-tail call through the driver can only add stack; this keeps `int-map`'s pair and leaves the lazy protocol alone.
2. Regroup before `ctail` only when the module had a group fused, so every other module keeps its output.
3. Separately, the lazy protocol's own hand-offs can become tail calls: move the indirection loop into `lazy-eval`, release the lock inside `lazy-eval-locked`, and drop the second force of an already forced field. Each level of a lazy chain then costs only the one essential non-tail frame (forcing the field the constructor matches on), which no transformation removes.
4. Find out why the wrappers are not inlined at non-tail call sites.
