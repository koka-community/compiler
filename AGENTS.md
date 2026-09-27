# Repository rules

Rules for anyone — human or agent — working on this port. Short on purpose.

## 1. Coding standards

- Markdown docs should not line-wrap unnecessarily. Only break at periods in paragraphs, and never in a bullet pointed list - bullet points should be kept brief.
- Match the surrounding code: naming, comment density, layout. A diff should be hard to pick out of the file it lands in.
- Names are `kebab-case`. Qualify a name (`local-var/update`, `dir/is-file`) when it is ambiguous; the compiler will tell you when it is.
- Comments say WHY, not what. A comment that restates the code is noise; a comment recording a measurement, or a non-obvious constraint is the most valuable thing in the file.
- When you record a number, record how it was measured.
- COMMENTS STATE INVARIANTS, NOT LINEAGE. Say what must hold and why; do not cite the reference compiler to show that the port agrees with it. "upstream does the same", "upstream tests this way", "matches upstream exactly" are noise: they age badly, they are unverifiable at the point of reading, and they say nothing about the code. Reference upstream ONLY where the port DIFFERS from it, or where a non-obvious behaviour exists solely because the reference compiler requires it -- then name the upstream function, so the difference can be checked.
- Comments describe the CURRENT invariants and approach, in the present tense. They never narrate history: no "used to be X", "previously we Y", "changed from Z", no stale invariant left standing next to the rule that replaced it. If the history matters, it belongs in the commit message, the changelog, or a doc under `docs/` -- not in the file. A rejected alternative is worth a comment only as a live constraint ("a `var` here boxes the value type"), not as a story about what was tried.

## 2. Porting standards

The port follows upstream (`~/koka/.worktrees/dev-compiler`) structurally, so a reader can diff the two. Translate idioms, do not redesign:

| upstream (Haskell) | here (Koka) |
| --- | --- |
| type classes | overloading + implicit parameters |
| monads / monad transformers | effects and handlers |
| `IORef`/`MVar` state threading | `var` / `ref`, or an effect |
| explicit dictionary passing | implicits |

- Keep upstream's function and module names recognisable. Cite the upstream name in `docs/upstream-map.md` when it diverges.
- DIVERGE ONLY WITH A REASON, AND WRITE THE REASON DOWN. A deliberate divergence is fine; an accidental one is a bug that will be found much later.
- One common pre-approved divergence is overloading names when the first argument's type differs. Don't include types in the name unless it is a qualifier in the name: `string/cmp`.
- Before concluding "upstream does X", read upstream's source. Not its interface files, not its behaviour, not your memory of it.
- If a bug is found while porting, first fix it upstream and then fix it in the port.

## 3. Test standards

- MINIMISE FIRST. Find the smallest input that shows the problem before investigating it. A 60-second reproduction beats a 13-minute one many times over, and the difference compounds across iterations.
- DO NOT SCALE UP A TEST THAT ALREADY ANSWERED THE QUESTION. If a small input verifies the behaviour, stop there. Only go to a medium or large input when the thing under test IS total compilation time, or when correctness genuinely depends on scale (a build race, a memory ceiling, a graph shape that only appears at size). Re-running at size "to be sure" buys nothing and costs tens of minutes per iteration.
- BUILD THE HARNESS ON THE SMALL INPUT FIRST. Harness bugs are indistinguishable from results. Three separate ones (mismatched artifacts, an invocation that compared error paths, zsh expanding globs before the build ran) each produced a plausible wrong number, and each would have been obvious in seconds on a one-module program.
- REPRODUCE BEFORE DIAGNOSING. A failure you cannot reproduce on demand is a failure you cannot verify you fixed.
- The sweep (`scripts/test-runner.kk`) is the final gate for a compiler fix. One passing case is not evidence that a change is correct; it is evidence that one case passes.
- The sweep and the gates are a prerequisite for approving a change, not for profiling or experimenting. Skip them for a temporary instrumented or experimental build; run them before a change is committed. Remind the user that we need to test / commit before moving onto a separate unrelated change. One caveat here is that the large gate tests should often be skipped when the difference shouldn't affect behavior - i.e. small optimizations of the port's code (not of the compiled output) proved correct on a subset of the tests. 
- Never conclude from an absence. Assert a POSITIVE signal: the binary exists, the count went up, the symbol is present. Exit 0 with no output has meant "silently did nothing" here more than once.
- Run test suite with `export LANG=C`
- A BUILD DIRECTORY DOES NOT KNOW WHICH COMPILER WROTE IT. Its hash covers the flags and the compiler VERSION, not the identity of the compiler BINARY, so artifacts written by a different compiler are reused silently. Twice in one session a "rebuild" after changing the reference compiler recompiled 1 of 206 modules and relinked in a minute, producing a binary that looked new and carried the OLD codegen for 205 modules. Run `scripts/cache-guard.sh --fix <compiler> <build-dir>` after changing compilers, or give the run a build tag of its own; `build-driver.sh` and `multimodule-gate.sh` now do this themselves. This is NOT the source/transitive-dependency check, which works correctly.
- A GUARD THAT FAILS OPEN IS WORSE THAN NO GUARD. The first version of `cache-guard.sh` used `find -newermt "@<epoch>"`, which BSD find rejects, with stderr suppressed -- so it counted zero stale artifacts and passed silently. Never suppress stderr in a check, and always confirm a new check FIRES on a case you know is bad before trusting it to be quiet.

## 4. Bug-fixing standards

- TRACE, DO NOT GUESS. When a hypothesis costs a build cycle to test, it is cheaper to add a trace that prints the actual state. Instrument the thing you are reasoning about and read the value. If it is available via a debugger / tracing tools that should be attempted before any code changes.
- Ask what the evidence CANNOT be, not just what it fits. Several wrong conclusions here were consistent with the data because the data was gathered with a filter that silently dropped half of it.
- When a fix does not change the symptom, that is information: the mechanism is elsewhere. Do not layer a second fix on the first.
- Revert rather than leave a half-fix in the tree. Record the finding in the current plan / working notes where the next person will look.
- SEEN ONCE IS NOT A BUG YET. Write down what you saw and the exact conditions, then try to reproduce those conditions. Chase it only once it reproduces -- an unreproduced one-off usually costs more to hunt than it costs to wait for a second sighting, and you cannot verify a fix for it either way.

## 5. Optimisation standards

Work in this order. Skipping a step wastes the ones after it.

1. MEASURE THE RIGHT WORKLOAD. Cold and warm builds have completely different profiles here (warm: interface parsing; cold: kind inference). Profiling the workload you are already thinking about will confirm what you already think.
2. UNDERSTAND THE LEAVES. What is the CPU actually executing? Attribute leaf samples to the nearest meaningful frame, not just the leaf symbol.
3. UNDERSTAND WHAT INVOKES THEM. A leaf is rarely the fix. Walk out to the function whose behaviour you would change. (i.e. the fact that maps are used a lot, could be an algorithmic problem at a higher level and doesn't mean we need to optimize map functions - unless they have obviously bad big-O complexity).
4. REMOVE DUPLICATED WORK FIRST. The largest wins here have all been work done twice or work whose result was discarded.
5. IMPROVE THE ALGORITHM SECOND. Removing O(n^2) in a hot path beats any constant factor.
6. TUNE ALLOCATION AND REUSE LAST. Real, but a constant factor.

7. PROFILE WITH IDENTICAL-CODE FOLDING DISABLED (`--cclinkopts=-Wl,-no_deduplicate`). The linker folds the many identical copies of kklib's inline refcount helpers into one symbol, and the profiler then reports a `<deduplicated_symbol>` bucket and silently redistributes the rest. Worse, a change to those helpers changes WHAT gets folded, so an ICF build's before/after attribution is not comparing like with like: the sticky-refcount fix appeared to take refcounting from 32.6% to 1.6% of a profile, when a no-ICF profile of the same binary shows it is still 25.2%. Wall-clock deltas were unaffected; only the attribution was wrong.

8. VERIFY THE ATTRIBUTION, NOT JUST THE CLOCK. An algorithmic change must be justified and confirmed by a PROFILE BREAKDOWN before and after, not by wall time alone. Capture the symbol-level profile of the benchmark workload before the change, and capture it again after. State the target symbol's share in both. If the wall time moved but the target symbol's share did not, the change is not what moved it -- find out what did before claiming the win. If the symbol's share collapsed but wall time did not, the work moved elsewhere; say so rather than reporting a win.

   A wall-time delta smaller than the run-to-run spread is NOISE, and no number of repeated runs converts it into a result. The profile is what makes a small delta interpretable: a 3% wall win is credible when the symbol you targeted went 36% -> 2%, and is meaningless when it did not move.

Also:

- DO NOT ITERATE AGAINST UPSTREAM. The port is faster than the reference compiler everywhere measured (warm small 0.37s vs 0.49s, warm big 15.5s vs ~24s, cold big 249s vs ~469s; cold small 4.09s vs ~3.8s is the exception), so an upstream run costs minutes and measures a compiler we are no longer focused on. A/B the port against itself -- ideally the same binary with the feature switched off (`KOKA_CC_WORKERS=0`) -- in ONE command with one harness. Run upstream only when the question is parity of OUTPUT (a `.kk.out` fixture, the interface format) or when a comparison number is explicitly asked for. Upstream SOURCE remains the porting reference; see rule 2.
- Do not chase a number you cannot match. Upstream spends ~46% of its CPU in a concurrent GC; its CPU/wall ratio is not a target.
- NEVER PROFILE OR TIME A FULL WARM BUILD unless explicitly asked. A warm build of the whole compiler takes tens of minutes and has run past 40 on `compile/build.kk` alone; one measurement burns the session. Profile a SUBSET that isolates the same work -- `ifacecost` (parse every `.kki` in a build dir) for interface loading, `scripts/bench-effect-op.kk` for handler cost -- and only revisit the full warm build once a subset has shown the cost is down. (TODO: Based on numbers I'm not sure this rule is still required)
- BUILD THE DRIVER COLD, OR WITH ONLY std WARM -- `scripts/build-driver.sh`. A warm driver rebuild is the pathological workload on both the port and upstream: it is dominated by interface parsing and tells you nothing about the change you made. It is never a valid benchmark or validation build. It is valid for working on optimizing the warm case or parsing. (TODO: Is this really the case?)
- ONE BUILD AT A TIME. Concurrent builds sharing a build directory corrupt each other and invalidate timings.
- A correct change that does not move a profiling number is worth it depending on it improves (reduces) code complexity or if it improves correctness.
- Make sure nothing else intense is running when timing things. And make sure the battery isn't low or performance is otherwise throttled.

- **One run is enough for a long build.** For any compile of ~40s or more, a single timing is a fine approximation -- do not repeat it to measure spread or take a median. Repeat runs only for fast targets, where run-to-run noise can rival the effect being measured.