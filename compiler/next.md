# Next

Live work queue. The detailed gap analysis lives in `TODO_porting.md`
("Comprehensive state audit 2026-08-27"); this file is just what to do next.

Rewritten 2026-08-27 — the previous contents (a per-module porting checklist from
the early phase) are fully superseded: everything it listed under "All dependencies
ready" and "Needs dependencies" is ported, including `core/*`, `backend/c/*`,
`type/infer`, `compile/*`, `main`, and the language server.

## Goal

Be a drop-in replacement for the upstream compiler.

## 1. Compile-expr  ← DONE (2026-08-27), except the items listed at the end

Upstream `buildcCompileExpr` / `buildcCompileEntry` (`Compile/BuildContext.hs:333`):
compile a SYNTHETIC module that wraps an expression, then return its type and an
entry point. The port has no equivalent, and this is the single largest functional
gap.

It blocks:
- the whole REPL expression family: `Eval`, `:type`, `:kind`, interactive
  `Define`/`TypeDef` (all currently answer `not-wired`)
- the listing commands `:s[ource]`, `:d[efines]`, `:alias`
- LSP `koka/compileFunction`, which this port built differently (via
  `mainEntryName` + `outFinalPath`). **This should have been built first and
  `compileFunction` layered on top of it**; once compile-expr exists,
  `compileFunction` should be rebuilt on it so both front ends share one path.

Done:
- [x] `compile-expr` in `compile/build-context.kk` (two passes: type-check to learn
      the type, then build with the result show-wrapped)
- [x] `koka/compile` AND `koka/compileFunction` re-pointed at it, so both front ends
      share one path and the `mainEntryName`/`outFinalPath` workaround is gone
- [x] REPL `Eval` and `:type`
- [x] REPL listings `:t` (ShowTypeSigs), `:k` (ShowKindSigs), `:alias` (ShowSynonyms)
      — `type-check` now also returns the kgamma, carried on `module-check`
- [x] REPL `:edit` ($EDITOR)

Still not wired:
- [ ] `:kind <type>` (upstream `compileType` — needs a synthetic module for a TYPE,
      not an expression)
- [ ] interactive `Define` / `TypeDef` (upstream accumulates them in `defines` and
      re-emits them into each synthetic module)
- [ ] `:s[ource]` / `:d[efines]` (ShowSource needs Colorize, see section 3)

Perf note: routing the LSP entry compiles through compile-expr initially doubled the
warm run-lens time (2.1s -> 4.1s) because it added passes. Fixed by (a) skipping the
type-check pass when `add-show = False` — an entry point does not need the type — and
(b) adding `module-name-of`, a lenient header parse, so the file no longer needs a full
check just to learn its module name. Back to 2.11s.

## 2. Code-action generators  ← DONE (2026-08-27)

All six ported and verified on both a monomorphic and a polymorphic type:
`show`, `==`, `cmp`, `order2`, `map`, overloaded, over the `syn-general-unary` and
`syn-binary-op` scaffolds.

Building them exposed SEVEN fidelity bugs in `syntax/pretty.kk` + `common/name.kk`,
all fixed (this printer is shared, so these affected far more than code actions):
- the inline annotation was printed into the def header (`pub inlinefun`)
- no `ppSyntaxDefUserType`/`ppFunDef` annotated clause, so the whole RESULT TYPE
  was dropped and generated definitions came out untyped
- `TpApp(con,[])` printed `shape()`; `TpApp(con,args)` printed `list(int)` with
  PARENS instead of `list<int>`
- `TpFun` lost its `->` entirely and printed parameter names upstream omits
- `TpQuan` printed its binder bare instead of `forall<a>`; `TpAnn` printed `t :: k`
- `prettyComment` did not strip the trailing newline, leaving a blank line between
  a doc comment and its definition
- IMPLICIT PARAMETERS lost their `?` sugar (`@implicit/a/show`), so a generated
  definition's implicit was no longer implicit when read back — not cosmetic
- one unconditional infix rule where upstream guards on
  `not (isQualified || isLocallyQualified)` and prints the bare stem, so a
  qualified operator was written infix (`left tree/(==) left0`); upstream's
  singleton-constructor and tuple cases were missing too (`Leaf()` for a nullary
  constructor, `Tuple2(a, b)` instead of `(a, b)`)

Still cosmetic: names print fully qualified (`p/tree`, `std/core/types/string`)
because the port's name printer does not shorten against the module context the way
upstream's `ppName env` does. Output is valid, just verbose.

## 3. GenDoc / Colorize  ← in progress

- [x] `syntax/colorize.kk` — first cut. Syntax-highlighted HTML for `--html`,
      wired into `compile-module` (upstream does it in `CodeGen.hs:101`, before
      the backend runs, so a codegen failure still leaves the HTML behind).
      `--html=2` emits a full document, `--html` just the `<pre>` block.
      Every span it emits is byte-identical to the reference compiler's.
- [x] the RANGE-MAP layer (`colorizeLexemes`/`transform`): declaration anchors,
      `<a class="pp">` links to definitions, and type popups. The port's `fmt`
      EFFECT made this much smaller than upstream's explicit scan -- the handler
      already sees lexemes in order, so it can own the open-range stack directly
      instead of reimplementing `scan`.
      **Verified by diffing the generated HTML against the REFERENCE compiler on
      the same file**: anchors, hrefs, popups and every outer span are
      byte-identical.
- [x] the two `highlight.kk` classification gaps: ONE-WORD bug in
      `highlight-lexemes`. Its fold accumulator is named `ctx'` but the body
      called `highlight-lexeme(transform, c, ...)` -- passing `c`, the INITIAL
      context, so the context never advanced and every lexeme was classified
      against the starting state. Inside a type that meant `(` never pushed
      `NestParen`, so a parameter name came out `TokTypeVar` instead of
      `TokTypeParam` and `)` popped an empty stack back to `CtxNormal`, losing
      its type classification. Affects the CONSOLE highlighter too.
- [x] `--htmlcss` default: upstream's `flagsNull` (Options.hs:352) uses
      `"styles/" ++ programName ++ ".css"`; the port defaulted to empty.
- [x] name escaping in `fmt-html`: upstream routes names through
      `fmtNameString` (escapes, and wraps `-`/`_`/`/` in spans) and operators
      through `fmtOpString`. The port emitted the raw string, so a type operator
      like `<$` wrote an unescaped `<` into the HTML.
- [x] kinds in popups used the raw `show` (`(->) V V`) instead of upstream's
      `prettyKind` (`V -> V`).

**`--html` output is now BYTE-IDENTICAL to the reference compiler** on a simple
module (verified with `diff`). On a polymorphic one, one difference remains and
it is arguably in the PORT's favour: a skolem type variable renders as `a` here
and as its raw id `63` in the reference, because `ktp/pretty-string` assigns nice
names where upstream's colorizing env does not. Decide whether to match upstream
exactly or keep the more readable output.

- [x] `syntax/gen-doc.kk` — `Syntax/GenDoc.hs` (598 lines), the `.xmp.html` API
      documentation, wired into `compile/build.kk` right after the `-source.html`
      write (upstream `CodeGen.hs:114`). It renders from CORE, not the syntax
      tree, so it lists exactly what a module exports with resolved types.
- [x] `fmtLiterate` + `fmtQualify` + `linkFromId`/`linkFromTypeId` (they live in
      `Colorize.hs`, and were the last thing between the port and byte-identical
      documentation). These resolve each name INSIDE a rendered type, and inside
      a doc comment's inline code, against kgamma/gamma so it becomes a link
      with a type popup.

**`.xmp.html` is BYTE-IDENTICAL to the reference compiler** on both a simple
module and one exercising structs, effects, aliases, constructor docs and
generated accessors (verified with `diff`). `-source.html` remains byte-identical
on the simple module; see the residual list below for the harder one.

Bugs this diff exposed, all REAL and none of them cosmetic-only (they reach the
`.kki`, hover and completion too, not just the HTML):
- `kind/synthesize.kk:183` used `nameLocalQual` (the local QUALIFIER) where
  upstream uses `nameLocal`, so every generated `is-Con` predicate documented
  itself as "Tests for the `` constructor of the `:` type."
- `syntax/builders.kk` put the GENERATED "Call the `fun op` operation of the
  effect `:e`" sentence inside `if doc.is-empty`, so an operation declared
  without its own doc comment got no documentation at all. Upstream only makes
  the AUTHOR's doc conditional. Also "Call the**n**" -> "Call the" (twice).
- `colorize.kk` `shorten` split on `" "` where upstream uses `words`, which
  drops empty fields — so the trailing space `class-prefix` adds was emitted as
  `class="koka "`.
- `colorize.kk` `fmt-lexs` was missing upstream's `dropColon`, so a type written
  `` `:shape` `` in a doc comment rendered with a leading `:`.
- `colorize.kk` `signature` had upstream's `isLiterate` PARAMETER folded into
  `html-env.literate`. GenDoc always passes `True`, so documentation pages were
  emitting bare same-page anchors instead of linking to the rendered source.
- `colorize.kk` `signature`'s link guard tested `nameLocal` for emptiness where
  upstream tests `nameIsNil mname`.

Two traps worth remembering for the next person:
- upstream's GenDoc SHADOWS `Colorize.doctag`/`atag` with versions that do NOT
  prepend the `doc ` class. Koka has no cross-module shadowing, so they are
  ported as `dtag`/`dlink`. Using Colorize's gives `class="doc decl"` where the
  reference emits `class="decl"`.
- `kg` from `type-check` ALREADY holds the module's own types as well as its
  imports (it is kind inference's result), which is exactly what upstream passes
  as `defsKGamma`. Unioning the core's typedefs on top duplicates every local
  type, and a duplicated entry makes the qname lookup AMBIGUOUS — which silently
  degrades to an unlinked name rather than failing.

Residual `-source.html` differences on a struct/effect-heavy module (all
PRE-EXISTING, none introduced by this work; the simple module is byte-identical):
- a struct's name at its DECLARATION is `NITypeCon` upstream but `NICon` in the
  port's range map, so it links to the con anchor and is coloured `co` not `tp`
- the `]` of an empty-list pattern is linked to `con_space_Nil` upstream; the
  port has no range-map entry for it
- a skolem renders as `a` here and as its raw id (`$127`) in the reference —
  already recorded above, and arguably in the port's favour

Ported infrastructure that made the first cut small: `syntax/highlight.kk` was
already done, and the port had already turned upstream's `fmtFun` PARAMETER into
a `fmt` EFFECT -- so HTML rendering is just a second handler alongside the
console one.

Bug found while diffing against the reference: `highlight.kk`'s `is-keyword-op`
had its condition INVERTED (`c.is-alpha` where upstream is `not (isAlpha c)`), so
`pub`/`fun`/`type` were classified as operator keywords and `:`/`->` as ordinary
ones. Wrong colour on the console highlighter as well as the wrong CSS class.
The `shorthands` class-abbreviation table was also invented rather than ported;
it is now upstream's verbatim (which deliberately leaves `comment`, `number` and
others unshortened).

### Gates re-run after this work (2026-08-28)

- sweep: **423 PASS / 17 SKIP / 2 MISMATCH / 0 TIMEOUT** over 442 files, after
  fixing two HARNESS faults (below). Neither mismatch is a compiler defect:

  - `cgen/specialize/recursive-arg` -- ORDERING ONLY, measured: 55 lines
    expected, 55 produced, and the sorted line multisets are IDENTICAL. The
    whole diff is two `(key@xxx : string, ...)` lines two positions earlier in
    the port's `--showhiddentypesigs` dump. This is the caveat the sweep
    script's own header already records for the `-O2` binary it uses
    (unique-consumption order differs from the debug build; cosmetic, decided).
  - `medium/allsamples` -- two independent harness gaps, NO compiler defect.
    **It PASSES** given upstream's own conditions.

    1. `could not find module: samples/all`. Upstream's Spec.hs runs with
       cwd = the koka repo root, so its search path
       (`"." : <shareDir>/lib : -i...`) finds `samples/all.kk` via `.`. The
       sweep runs the port from its own root and never puts that tree on the
       include path. Add `-i<upstream-root>` and it resolves.
    2. WARM vs COLD. Warnings are emitted when a module is COMPILED, not when
       it is loaded from cache. Measured on the port, same buildtag:
       cold = 5 warnings, warm = 0. Upstream's suite prints "pre-compiling
       standard libraries..." and then runs every test against a persistent
       `--buildtag=test` cache, so it is warm and never sees them; the sweep
       gives each worker a fresh buildtag and compiles every test cold.

    With `-i<upstream-root>` on a warm buildtag the port's output matches the
    fixture EXACTLY. The fixture is NOT stale: re-running upstream's own runner
    in `--mode=update` rewrote it byte-identically (clean `git status`).

    This is the concrete argument for the precompile-shared-deps model: it does
    not just remove the per-worker duplication and the stale-`.o` hazard, it
    makes diagnostic output match upstream's, because warm runs suppress
    recompilation warnings exactly as upstream's do.

## Removed: the `.koka-runtime` object cache

Upstream has no counterpart. Its only prebuilt-object fast path is a single
installed `libkklib.o` (`kklibBuild`, "use pre-compiled installed binary"); it
never caches `std_*.o` or arbitrary module objects. The port's cache was built
by the REFERENCE Haskell compiler, so its objects could reference internal
helper symbols the port does not emit -- undefined-symbol link failures that
reproduce nowhere else, plus a rebuild-at-the-right-opt-level hazard.

Verified optional before removing: `cgen/specbox` passes with no cache present.
Gone with it: `ccRuntimeObjDir`, `runtime-cache-variant` (renamed
`build-variant`, upstream's term -- it still names the build output dir),
`kki-search-dirs`, `neededStems`/`freshStems`/`cacheObjs`, the dead
`compile-c-objs`, the now-unused `loadedModules` parameter, and
`scripts/rebuild-runtime.sh`. The JS backend writes its `.mjs` to the build dir,
which is upstream's single shared outputdir.

`medium/allsamples` was the one test leaning on it, and not for objects: the
cache also supplied the `samples/` tree's INTERFACES. Upstream resolves
`samples/all` from source because it runs with cwd = the koka repo root (its
search path is `"." : <shareDir>/lib : -i...`). Given the same tree on the
include path the port compiles and runs the whole samples suite, and on a WARM
buildtag its output matches the fixture exactly -- see the sweep notes above for
why cold runs differ.

## Warning fidelity

Both compilers emit the same five warnings for `allsamples` when the modules
are actually COMPILED (a warm run emits none). Two differences, both fixed:

- **paths**: upstream shows a diagnostic's path relative to the process working
  directory (`showRange` -> `relativeToPath cwd src`, with `cwd <- getCwd`
  threaded in from `Main/Run.hs`). `common/range.kk`'s `show-range` already took
  a `cwd` and ignored it, with a `// TODO`. Implemented pure (whole-component
  prefix match) rather than reusing `common/file.kk`'s correct port of the same
  function, whose `pathsep()` is `ndet` and would infect every `show`. The
  driver and the worker path in `orchestrate.kk` now pass the real cwd; the
  empty default remains for the language server, which is keyed by absolute path.
- **ordering**: upstream prints warnings at the very END of a compile, after
  errors and after the program's own output under `-e`. `build-context.kk`
  flushed every module's diagnostics as soon as the wave build finished, which
  is before the entry module's code-gen -- and under `-e` the program runs
  inside that code-gen. `mod-outcome` now carries `warn-messages` apart from
  `messages`; errors still flush in build order, warnings flush after the entry.

The test suite could not see either: the sweep's `sanitize` strips the upstream
root, so both compilers' warning text compares equal, and only the position
differed.

## Multi-root build context + test runner

Prep for driving the compiler as a LIBRARY from `scripts/test-runner.kk`.

`compile/build-context.kk`, following upstream's `BuildContext`:
- `session` carries `roots: list<name>` (upstream `buildcRoots`), plus
  `session-clear-roots` / `session-remove-root` (`buildcClearRoots` /
  `buildcRemoveRootModule`).
- `paths/session-invalidate` invalidates a SET in one pass over the dep cache;
  folding the single-path version would rescan `deps` once per member.
- `check-file-ex` now takes a LIST of roots. All are parsed, their imports are
  UNIONED into one `discover-deps`, one wave build runs over that shared graph,
  and then a fold compiles each root as its own ENTRY -- so each gets its own
  `main` and its own executable. `mods` threads through the fold, so a module
  resolved for one root is already present for the next. Source directories are
  the union of every root's directory, since a batch can span directories and
  sibling imports resolve relative to the importing file.
- new `build-roots(fl, fnames, sess, ...)` is the library entry point;
  `check-file` / `check-file-session` are `[fname]` wrappers, so the CLI, LSP
  and REPL paths are unchanged by construction.

This mirrors `buildcBuildEx :: Bool -> [ModuleName] -> [Name] -> ...`, where
`getMainEntry gamma mainEntries mod` picks the entry whose qualifier matches
each module -- upstream has supported many roots and many mains all along.

`scripts/test-runner.kk` -- PRE-COMPILE shared dependencies, which is upstream
Spec.hs's "pre-compiling standard libraries..." step:
- scans every test's `import std/...` lines (33 distinct modules across the
  suite), generates one synthetic module importing them all, and compiles it
  SERIALLY into the shared `--buildtag=ktest` before any test runs.

That one step fixes three separate things measured today:
1. no test pays std's cold build (cold `lib/time7` ~25s serial, ~41s under
   8-way contention, vs ~8.6s warm);
2. the concurrent-write RACE that forced the Python harness into per-worker
   buildtags disappears -- with std pre-built the tests only READ those
   objects -- and with it the stale-`.o` hazard that produced the phantom
   `cgen/specbox` link failure;
3. diagnostics match upstream, because warnings are emitted when a module is
   COMPILED, not when loaded from cache (see the `allsamples` notes above).

Measured progress bringing the Koka runner to parity (Python harness:
423 PASS / 17 SKIP / 2 MISMATCH):

| fix | PASS |
| --- | --- |
| as found | 178 |
| + `config.json` excludes, correct `--include` | 180 (SKIP now 17, exact) |
| + the five MISSING sanitize rules | 407 |
| + `_renumber_meta_ids` (stateful pass) | **416** (COMPILEFAIL -> 0) |

Four bugs, each found by diffing behaviour against the working harness rather
than by reasoning from one example:
- it passed `--include=.` / `../std` / `../parsing` -- the flags for compiling
  the SCRIPT, not the tests. A test resolves sibling imports out of the upstream
  test tree (upstream's `-itest`).
- `config.json`'s `"exclude"` list was never read: 0 SKIP where the harness
  reports 17.
- the root prefix was stripped WITHOUT its trailing slash, leaving a leading `/`
  on paths. Real, but NOT the cause -- fixing it alone changed nothing.
- five sanitize rules were missing, above all `\.` -> `@`. That is why fixtures
  read `hm1@kk` / `stack@yaml`; without it every test naming a file or a
  qualified name mismatches. This was the dominant cause (180 -> 407).
- `_renumber_meta_ids` was absent entirely. It is NOT a regex rule but a
  STATEFUL, order-preserving map from each token's first appearance to a
  sequential id, run over actual and expected alike. Ids are unique-counter
  sensitive (`_<digits>` meta type vars, `-x<digits>` hidden locals); mapping by
  first appearance keeps distinct ids distinct where a blanket `_\d+ -> _N`
  would conflate them. It also reconciles `fn(x: 14)` with `fn(x: a)`, a printer
  divergence: upstream's Box pass erases TypeLam binders so the param type
  prints as a raw id, while the port's ambient nice-env still holds the letter.

### Output isolation -- diagnosed

The 7 remaining extra failures were isolated to CONCURRENCY, and the mechanism
identified. Same 7 tests, same warm shared buildtag:

| | result |
| --- | --- |
| run SERIALLY | all 7 PASS |
| run CONCURRENTLY (7 at once) | 5 MISMATCH |

and the failures are all of one shape:

    error: call to undeclared function 'kk_std_core_list__unroll_map_<N>'
    note: did you mean 'kk_std_core_list__unroll_lift_length_620_<M>'?

i.e. a test's generated `.c` was compiled against one generation of
`std_core_list.h` while another process re-emitted std with fresh unique-counter
ids. The SAME failure class as the deleted `.koka-runtime` cache -- mixed
generations of std artifacts -- now arising within a single run.

So **pre-building std narrows the window but cannot close it**: concurrent
processes sharing a build directory are unsafe for this compiler, because any
std re-emission renumbers symbols under a concurrent reader. Note the Python
harness is not immune either; per-worker buildtags simply shrink the window to
one worker. Its duplication IS its isolation mechanism.

Three options, and only the third gets both safety and speed:
1. per-worker buildtags (the Python's) -- safe, but rebuilds std N times, which
   is the dominant cost;
2. shared buildtag + pre-built std -- cheap, but unsafe (measured above);
3. **one process, one build graph via `build-roots`** -- no concurrent writers
   at all, parallelism from the compiler's own wave scheduler, which already
   orders module emission correctly.

(3) is the design to build on, and the MEASUREMENTS say why. One warm test
(`cgen/mpat`), `KOKA_TIMING`:

    parse 2ms | discover 400ms | load-modules 993ms | typecheck 4ms
    optimize 1ms | codegen 652ms | wall total 3566ms

std is NOT recompiled (the pre-build works), but `discover` + `load-modules` =
**~1.4s per test** of dependency resolution and interface re-loading, paid once
per PROCESS -- 442 times -- while the test's own type-checking is 4ms. The port
is ~4x upstream on interface loading specifically, so this is the dominant
redundancy. `build-roots` removes it: one session, one resolved module map, std
interfaces loaded once per GROUP.

Harness timings, all warm, same port binary except upstream's:

| harness | compiler | wall | result |
| --- | --- | --- | --- |
| upstream `stack test` | reference | 66s | 425 examples, 2 failures |
| Python sweep (8 per-worker caches) | port | 216s | 423/17/2 |
| Koka runner, contiguous chunks | port | 477s | 416/17/9 |
| Koka runner, round-robin chunks | port | 430s | 416/17/9 |

Round-robin chunking (477 -> 430s) confirms scheduling was only part of it; the
rest is the per-process 1.4s. The upstream/port gap is mostly the COMPILERS
(~4x per compile), not the harnesses -- Python vs Koka on the same binary is the
comparison that isolates harness design. Output isolation then splits cleanly:
- BUILD artifacts: no isolation needed, the race is gone by construction.
- DIAGNOSTICS: capture per root with a scoped effect handler around each entry
  compile -- genuinely better than upstream, which can only attribute output by
  running one test per process.
- PROGRAM output under `-e`: build with `evaluate = False`, take each root's exe
  from `on-exe` (already per-root) and run it from the runner, capturing stdout
  per test.

Known deficiencies in the runner as it stands:
- `println` output is BLOCK-BUFFERED when redirected, so a multi-minute run
  shows nothing until it exits and a kill loses everything. `std/core/console`
  offers no `flush` and no stderr writer; only `trace` (std/core/debug) is
  unbuffered. This is a real trap: an in-flight run looks like a finished run
  that printed nothing.
- static contiguous chunking leaves a long tail -- 7 of 8 strands finished well
  before the last. A shared work queue would balance it; the current comment
  explains the choice as avoiding per-batch barriers, but static chunks trade
  that for load imbalance.
- `run-system-read` captures stdout only (correct -- upstream Spec.hs compares
  stdout and discards stderr), but without an explicit `2>/dev/null` the test
  program's stderr interleaves into the RUNNER's own output. Now redirected.

Two bugs found by running it against the Python harness's numbers (178 PASS /
191 MISMATCH / 73 COMPILEFAIL vs 423 PASS), both fixed:
- it passed `--include=.` / `../std` / `../parsing` -- the flags for compiling
  the SCRIPT, not the tests. A test resolves sibling imports out of the upstream
  test tree, which is what upstream's `-itest` and the Python harness pass.
- `config.json`'s `"exclude"` list was never read, so tests upstream does not
  run were run anyway and counted as failures (0 SKIP reported where the Python
  harness reports 17).

### The `emit` effect -- compiler output as a routable channel

`build-roots-isolated` captured DIAGNOSTICS, but a large class of tests compares
output the compiler printed with a bare `println`, bypassing diagnostics
entirely: `--showtypesigs`' signature listing (build.kk) and the
`--showcore`/`--showfcore`/`--showasm` dumps (code-gen.kk, type-check.kk) -- 14
sites. Without capturing those, per-root results cannot reproduce most fixtures,
so this was the prerequisite for batching.

`lib/log.kk` now carries an `emit` effect beside `log`, for the same reasons the
`log` doc comment gives: the handler is SCOPED (so "the front end installs this"
is type-checked, not a convention) and a worker cannot silently reach for the
main strand's. Kept distinct from `log` because they route differently -- phase
logging is verbosity-gated and may become `window/logMessage`, whereas this IS
the program's observable output and must be reproduced verbatim.

  * CLI: `with-console-emit`, printing to stdout exactly as before.
  * workers: captured into `mod-outcome.emitted`, apart from diagnostics.
  * `root-result`: `messages` / `warns` / `emitted` / `exe` -- everything needed
    to reconstruct a test's expected output, per root, inside a SHARED build.
  * LSP: routed into the phase log. fd 1 there is the JSON-RPC TRANSPORT, so a
    core dump written to stdout drops the connection mid-frame. `claim-stdout`
    already rerouted stray `println`s; this makes it a typed obligation for the
    whole class rather than a consequence of an fd trick.

VERIFIED transparent: driver builds clean and the sweep is 423/17/2, unchanged.
Only library callers see any difference.

Worth noting the type checker enforced the isolation properties rather than
merely documenting them -- it rejected closing an isolated compile over the
`async` cancellation token, over a stack-local `var` (`local<h>`), and left the
LSP unable to compile until it declared where this output goes.

### Roots as graph nodes -- ATTEMPTED AND REVERTED

The orchestrator dispatches each module the moment ITS OWN dependencies land
(its doc comment: wave barriers achieved 1.16x against a 1.74x ceiling, the gap
being "wave-boundary stalls between modules that share no dependency"). Roots
compiled in a phase AFTER the graph reintroduce that stall one level up: a root
waits on modules it does not depend on. Roots are leaves, so making them graph
nodes is the natural fix, and the change is small -- add them to
`dcache`/`stale-set`, decide `isEntry` from membership, and per-root results
come back as the `mod-outcome`s the orchestrator already returns.

It was tried and REVERTED. The compiler self-compiled fine, but the sweep went
423 -> 103, and after fixing the first cause -> 318. Three problems:

1. `o.emitted` was captured into the outcome and never flushed, so all
   `--showtypesigs`/`--showcore` output vanished. Fixed (103 -> 318), and
   fixing it settled the COMPOSITION ORDER question -- see below.
2. A root that legitimately FAILS -- every `*/wrong/*` test -- is reported
   TWICE: its own diagnostic, plus the orchestrator's
   `error : parallel compile of X failed`. That line is a build-level report
   meant for dependencies, where a failure is fatal; for a root the failure IS
   the expected output. 91 tests.
3. 13 unexplained TIMEOUTs and a 2x SLOWDOWN (216s -> 435s) -- the opposite of
   the intended effect, suggesting the readiness machinery costs more than it
   saves when there is only ONE root, which is the CLI's case.

(2) is clearly fixable. (1) is fixed. (3) needs understanding before retrying.
The natural place to retry is alongside the runner switch, where the caller
builds with `evaluate = False` and captures program output itself -- which
removes the interleaving that makes the single-root CLI case awkward.

### Composition order -- DETERMINED (not assumed)

    errors -> PROGRAM OUTPUT -> emitted -> warnings

`compileShowInfo` runs AFTER `code-gen`, and `code-gen` is what runs the program
under `-e`. Pinned by `algeff/cps1.kk.out`: `[1,3]` from the program, THEN the
signature listing. An earlier reading of this as errors -> emitted -> program
output was wrong -- the fixtures consulted (`cgen/rec4`, `parc/parc18`) each
contained only ONE of the two parts, so they could not distinguish.

Also load-bearing: the parts CONCATENATE WITH NO SEPARATOR. `cgen/rec4`'s main
is `print`, not `println`, so its fixture reads
`1test/cgen/rec4@kk(2,13): type warning: ...`. Composing a root's output with
`join("\n")` would fail that test.

STILL TO DO for true in-process batching: `build-roots` prints diagnostics
rather than returning them per root, so a library caller cannot attribute
output to a test without capturing stdout. The natural shape is to extend
`mod-outcome`'s messages/warnings split to the entry compiles too.

## Explicitly skipped

- `Backend/CSharp/FromCore.hs` — decision 2026-08-27, not worth the surface area
- `Compile/Package.hs` — deprioritised earlier

## Smaller open items

- [ ] Warm `koka/compile` ~2.1s vs 0.71s for a warm CLI build. Interface loading and
      discovery are 0ms now, so the remainder is entry codegen + C link.
- [ ] LSP requests are not answerable during a compile (the compile owns the work
      strand).
- [ ] Diagnostics-only checks still run optimize + codegen. Skipping them speeds the
      edit loop but removes the artifacts that make `koka/compile` warm — measure
      before changing.
- [ ] `termTrace` (upstream's verbose>1 channel) — 4 of its 5 sites are HTML/C#
      output, so it is mostly moot until GenDoc lands.
- [ ] Bottom-up beta rule still has no repro.
- [ ] Per-splice alpha-renaming in `inl-lookup` — the preferred fix for the
      unique-counter collision.
- [ ] Upstream `Core/Simplify.hs` fix is still uncommitted in the dev-compiler
      worktree.
