# Porting TODOs

This file tracks inconsistencies and missing features identified while porting the Koka compiler from Haskell to Koka.


- backend/c/helpers.kk - some ascii / character unique aspects about the port.
- backend/c/parc* - needs review
- common/name.kk - some C function inlining inside the file itself / hashing / name equality, we should see which ones actually pull their weight and which can be simplified now that we have better timing / comparison to upstream machinery, also we should investigate improving the hash at least a bit - not using the noted terrible 4 byte hash. - core/uniquefy.kk explicitly avoids that hash
- common/parse.kk - needs more review
- common/range.kk - the relative path machinery should be in common/file.kk or some other utility
- compile/*.kk - needs review
- core/analysis-match.kk - needs review of the removal of throwing functions
- core/binding-groups.kk - needs review - did we move away from linear-map - and if so we should update the note / code accordingly
- core/core.kk - tsubst - understand how we differ from usptream, and whether we can put this it's dependencies elsewhere.
- core/corevar.kk - lingering usages of linear-set
- core/divergent.kk - legitimate differences
- core/open-resolve.kk - left some comments that are legitimate invariants, but mention upstream a bit much
- kind/infer-effect.kk - NOTE about effect bug potentially
- kind/infer-kind.kk - need performance (linear-set)
- kind/infer.kk - lost a bunch of lazy constructor support -> moved to synthesize.kk?
- kind/pretty.kk - linear-map + note about missing fidelity.
- kind/repr.kk - padding size was changed?
- kind/synonyms.kk - still missing pretty-print from upstream? - or got put elsewhere?
- lib/scc.kk - notes something - maybe an upstream bug? - linear-set
- static/binding-groups.kk - note on a regression - is it just test output or something more serious
- syntax/pretty.kk - inline?
- syntax/promote.kk - typevar ordering / sort
- type/assumption.kk - linear-map / set - working on this

- type/pretty.kk - leftover linear-sets/maps, note about synonyms effect codegen bug - interface synonyms? Is it fixed. Other things to improve for performance.

## Toolchain

Build/typecheck with `./koka` (wrapper that invokes the koka from `~/koka/.worktrees/dev-compiler` — Tim's
branch with the bytes/bslice stdlib — plus this repo's include paths; override with `KOKA_DEV_DIR`).
`./run-test.sh <test.kk>` uses it too. Upstream `dev` cannot build this port (no bytes/bslice stdlib), and
`koka-community/std` required small fixes for the dev-uv-based toolchain (io-noexn→ioc compat alias in the
toolchain's `lib/std/core.kk`, `with override handler<eff>` syntax in `std/test`, `try(hndl, action)` argument
order in `std/test/run`).

Compiler-side fixes made in the `dev-compiler` toolchain while syncing (upstream-worthy, especially the first):
- `Core/Pretty.hs prettyPatterns`: multi-scrutinee branch patterns were emitted in **reverse** into `.kki`
  inline sections, so cross-module inlining of any `match (a,b)` function mis-bound the components
  (present upstream in dev-uv too!). Fixed by reversing the fold accumulator.
- `Core/Pretty.hs extractDepsFromSignatures`/synonym imports: skip unqualified (existential/skolem) typecons
  instead of asserting (`makeImport: invalid import`), which blocked `type/operations.kk` and dependents.
- `kklib box.h`: added `kk_uint8_box`/`kk_uint8_unbox` (uint8 became a C prim without box helpers).

## Upstream sync status

Checked 2026-07-23 against the `dev-compiler` branch (`0ed6ce07d`, in `~/koka/.worktrees/dev-compiler`).
Each ported file records the upstream commit it was synced to in its `// Updated as of ...: Commit <hash>` header;
`./check-upstream-sync.sh` regenerates this comparison (update its table when adding baselines).
When re-syncing a file, update both its header comment and this table.

2026-07-23: re-synced the parse cluster (`common/syntax.kk`, `common/parse.kk`, `syntax/parse.kk`,
`syntax/parse-type.kk`, `syntax/builders.kk` — conditional imports + buildcfg target guards, handler grammar
rework, eta-expansion fixes, multi-effect mask), the syntax AST (`syntax/syntax.kk` — External/ExternalImport
now hold the already-resolved entry for the target platform), regenerated `syntax/lex.kk` from `koka.x` with
the prefix/postfix `@idsym` fix (via `../alex -k`, runtime template in `../alex/data/alex-effects.kk` updated
for the new bslice `maybe2` API), and the small syncs: `common/name.kk`, `common/name-prim.kk`, `kind/repr.kk`,
`static/binding-groups.kk`, `syntax/lexeme.kk`, `common/range.kk`, `syntax/highlight.kk`, `type/pretty.kk`,
`syntax/range-map.kk`, `type/operations.kk` (realias logic lives in `type/infer-effect.kk`), `type/unify.kk`.
`kind/infer.kk` bridges the new syntax AST to the still-old core AST by wrapping externals in `DefaultTarget`
(TODO: thread the actual target platform through kind inference).

2026-07-23 (second sweep): synced ALL of `core/`, `kind/`, and `type/` to upstream HEAD:
- core AST modernization: `External` holds a single format string, `ExternalImport` flat key/values,
  `InfoExternal` a single string, `Import` carries a name range; `lookup-target` removed
  (`analysis-cctx`, `open-resolve`, `pretty`, `parse`, `backend/c` shape-updated to match).
- Target platform threaded through kind inference (`run-kind-infer` takes a `target-platform`;
  externals formatted via `format-call(tpl)`; the DefaultTarget bridge is gone) and through the
  type-inference env (`inferEnv.tplatform`, `get-target-platform`, `subst-nice`).
- `kind/infer.kk` split: data-type synthesis (accessors/testers/tags/lazy) now lives in
  `kind/synthesize.kk` (type resolution injected via the small `lazy-resolve` effect).
- `type/infer.kk` split: dependency-free helpers (expectation contexts, arg/pattern matching helpers,
  eta expansion, generalization wrappers) now live in `type/infer-support.kk`.
- `type/infer.kk` synced: named-before-positional argument matching with `match-rest`,
  `infer-isolated` (local-var escape check), `with-nice-names`/`is-named-lam`/`subst-iconstraints`
  monad helpers; the file now typechecks fully for the first time (main `expr/infer` is still a stub).
- `core/analysis-match.kk` turned out to already follow the rewritten (unification-based) match
  analysis; only its stale annotation was fixed.

### Files behind upstream (deferred)

2026-08-03: **`check-upstream-sync.sh` methodology fixed.** It previously counted
`git log base..HEAD -- file | wc -l` ("commits behind"), which is unreliable on this
upstream checkout's history (at least one rebase/squash, e.g. around the dev-uv merge,
means a recorded baseline commit is often not an ancestor of current HEAD) -- it counted
superseded/unrelated commits as "behind" even when file CONTENT was byte-identical. Of 87
tracked entries, 70 were falsely flagged this way (several-to-dozens of commits behind) but
are in fact content-identical, including everything previously listed here except the two
rows below -- `lib/trace.kk`, `lib/{pprint,printer}.kk`, and `syntax/lexer.kk` are all
confirmed identical now and have been dropped from this table. The script now uses
`git diff --shortstat base..HEAD -- file` instead; baselines were bumped to `eb98b61d` for
every file confirmed content-identical. Two NEW real divergences turned up in the process
(not previously listed) and are added below: the `kind/{infer,synthesize}.kk` +
`type/{infer,infer-support}.kk` cluster, and `kind/infer-effect.kk` + `type/infer-effect.kk`.

2026-08-03 (later): **All 5 "newly identified" clusters above triaged and confirmed ALREADY
PORTED** -- each turned out to be another instance of the same false-positive pattern (the
diff tool showed upstream's OWN history changed, not whether the PORT lacks that change).
Read every diff by hand and confirmed the port's current code matches, often word-for-word
in comments: `kind/infer.kk`'s `lam-valuebinder/kinfer` (implicit-param unpacking fallback),
`kind/infer-effect.kk`'s `lookup-infkind-name`, `type/infer.kk`'s `infer-implicit-unpack`
(type-annotation-aware unpacking + better error message) and `infer-lam` (propagated-type
reordering), and `type/infer-effect.kk`'s full deferred-commit implicit-constraint protocol
(`fresh-iconstraint`/`register-iconstraint`/`commit-implicit-constraints`) plus `lookup-inf-name`'s
disambiguation fix. All baselines bumped to `eb98b61d`. Also triaged `backend/c/box.kk`'s
4-line diff (already matches: `InfoExternal` single-format-string shape) and bumped it too.

| Ported file | Base | Upstream file | Behind (lines) | Why deferred |
|---|---|---|---|---|
| `backend/c/{constructors,dup-drops,expr,from-core,helpers}.kk` | `d3b244c` | `src/Backend/C/FromCore.hs` | 246 | genuine unported fix (upstream 6d4e672ed "fix cross-thread heap corruption from shared globals with plain refcounts": marks heap-allocated toplevel constants as static/stuck via a NEW kklib primitive `kk_box_mark_static`; also renames `kk_datatype_{,ptr_}drop` -> `kk_datatype_{,ptr_}drop_small` and adds `kk_bytes_t` to the box/unbox fast-path). Porting the `.kk` codegen alone would emit C calling undefined symbols -- `vendor/koka`'s vendored kklib does NOT yet have `kk_datatype_drop_small`/`kk_box_mark_static`. Needs a kklib submodule bump (bigger, riskier: affects the whole `.koka-runtime` object cache) before the codegen side can be ported. |
| `common/file.kk` | `336bf9b` | `src/Common/File.hs` | 213 | upstream is mid-libuv/async reorg (dev-uv WIP) |

2026-07-24: **`expr/infer` implemented** — the central type-inference dispatcher in `type/infer.kk`
now exists and typechecks: all expression forms are wired (Lam/Let/Bind, the App specials for
return/assign/byref/handler-mask/ctx-holes, Ann, Handler incl. the override-to-mask rewrite, Case,
Var, Lit, Parens, Inject), plus new `infer-lit`, `infer-assign`, `infer-inject`, `uses-locals`,
`infer-bind-def`, `infer-def`, and `infer-def-group`. The recursive effect knot is tied with the
`infer-eff-full` alias (`infer` + error reporting + flags; the `infer` alias itself cannot be widened
because the `def-infer-effect` op signatures mention it recursively).
2026-07-25: **End-to-end type checking + .kki emission works.** DefRec is complete
(`create-gammas`, `check-rec-val`, `fix-canonical-name`, `add-divergent-effect`, `infer-rec-def2`,
regrouping + divergence analysis in `infer-def-group`), and the module level is wired:
`infer-def-groups`, `arrange` (std/core key defs), `run-infer` (installs the full `infer-full`
handler stack: pretty env, range map, unique, synonyms/newtypes, a persistent unify/subst handler,
infer-env, base `infer-state`/`infer-eff`/`def-infer-effect` handlers — the latter two live in
`infer-effect.kk` as `handle-infer-eff`/`handle-iconstraints`, base variants of the override-only
installers), and `infer-types` (applies the final global substitution over all core defs).
`compiler/main/driver.kk` is a mini Compile layer: parse -> kind infer -> type infer -> pretty-print
core -> write `.kki`. `test/driver/smoke.kk` (self-contained defs; empty initial environments, so no
imports/primitives) round-trips with principal types identical to the Haskell compiler
(e.g. `compose : forall<a,b,c,e> (f : (a) -> e b, g : (c) -> e a) -> total ((c) -> e b)`).
Bugs found by running end-to-end (all fixed):
- `infer-isolated` destructured `improve`'s result as `(eff, tp, coref)` but it returns `(tp, eff, coref)`.
- **substitution composition direction** was backwards in three places (`run-unify`'s `add-sub`,
  `run-infer`'s `add-sub`, kind `extend-ksub`): `subst.compose(new)` keeps stale chains (`a->b` never
  advances to `a->c`); upstream composes new-on-left (`s @@ sub st`). This made `free-in-gamma` miss
  unified effect vars and `normalizeX` wrongly closed inner-lambda effects to `total`.
- kind `mgu` used plain substitution (`sub2 |-> sub1`) where upstream composes (`sub2 @@ sub1`).
- `pp-decl-type` dropped the *result type* of a function whose effect is total.
- `infer-app-fun-first` conflated the call-site propagated (result) type with the propagated
  *function* type (upstream keeps them separate: closure over `propagated` + `prop` param); this
  broke `id(one)` and inserted a spurious arrow level in inferred schemes.
- a leftover `throw("")` debug stub in `infer-argsN`'s `infer-arg-expr`.
- `infer-kinds` now also returns the constructor gamma (`gamma1`) needed to seed type inference.
2026-07-25 (later): **Core pass pipeline runs end-to-end.** Ported `core/simplify.kk`
(Core/Simplify.hs: topDown let-inlining/beta/case-of-case/case-of-let, bottomUp
case-of-known (`kmatch*`), occurrence analysis, sizes; entry `simplify-defs(unsafe, ndebug,
nRuns, dupMax)` with `simp-env` effect val). Finished `core/unreturn.kk` (was a partial port
referencing nonexistent `urExpr`/`urDef`). The driver now runs the upstream TypeCheck+Optimize
sequence after type inference: unreturn -> simplify -> lift-functions -> mon-transform ->
open-resolve -> simplify -> monadic-lift -> unsafe simplify (removes remaining `.open`) ->
simplify -> uniquefy; smoke test emits identical principal types. Also fixed:
- `expr/type-of` was missing the general `TypeApp` case (commented out); implemented with a
  local `tsubst` in core.kk (cannot import type/typevar: recursive imports).
- dev-compiler HASKELL fix (InferMonad.lookupInfName) + same fix in the port's
  `lookup-inf-name`: mutually recursive locally-qualified defs sharing an unqualified base name
  (e.g. `expr/unreturn` + `let/unreturn`) hit the ambiguous-local assertion; now disambiguated
  by module-stripped (`unqualify`) name match.
Not ported (not needed for JS yet): Core/Check, Core/CheckFBIP, Core/CTail (C-only),
Core/Inline, Core/Specialize (optimizations).
Next: JS backend (Backend/JavaScript/FromCore.hs -> compiler/backend/js/from-core.kk).

2026-07-25 (later still): **JS backend ported and generating runnable JavaScript.**
`compiler/backend/js/from-core.kk` (port of Backend/JavaScript/FromCore.hs, complete: module
frame + ES imports, type-def constructor objects (all con-repr shapes), tail-call elimination
(`tailcall: while(1)` + argument override with capture-by-value wrapping), match compilation
(genMatch special cases: single branch, if/return, boolean conditional, guard-free chain,
labeled break), externals with #1 argument splicing + exn try-wrapping, list literals via
vlist, reserved-word name encoding, string/char escaping). The driver now also emits `.mjs`;
`test/driver/smoke.mjs` passes `node --check` and runs: `id(42) == 42`, `apply_id() == 1`.
Fixed on the way:
- std/pretty/pprint rendered `Char` docs with `show-char` (and one path `Text` with `show`),
  so dquote-enclosed strings emitted `\"` — now renders verbatim (std@compiler-js 6237bca).
- `brk` is a Koka keyword (final-ctl alias) — cannot be used as a binder.
Note: effectful functions reference `$std_core_hnd.yield_bind` from the monadic transform;
running those needs the JS stdlib runtime (import resolution — future Compile-layer work).

2026-07-25 (part 3): **Datatypes, recursion, and TCO verified end-to-end in node.**
`test/driver/data.kk` (enums, recursive nat, records) and `test/driver/d1.kk` (recursive match)
compile to .mjs that runs correctly: enum constructors as ints, `Zero` as `null` (list-like),
tagless cons cells, generated testers, and TCO (`walk` over a 100k-deep chain, no stack
overflow). Deep bugs fixed by these tests:
- `Promote.promote-ex` destructured `[args..,eff,res]` without upstream's `reverse` — every
  partially annotated `fun f(x: t)` got a type with the first arg as the RESULT.
- kind `resolve-type` and `synthesize` built empty type applications `TApp(t, [])` (upstream's
  `typeApp` smart constructor collapses them) — these fail all unification matches; now use
  `type-app`.
- `getDataRepr` port checked `is-rec` where upstream checks `dataInfoIsOpen` (recursive types
  got ConOpen tags referencing undefined `_tag_X` globals) and was missing the DataEnum case.
- `unify` routed the wrong side into `unify-effect-var` (passed the variable's own type instead
  of the effect row) — spurious Infinite errors on `e ~ <div|e2>`.
- `subsume` skolemized BOTH sides; upstream skolemizes the expected and INSTANTIATES the given
  (recursive definitions failed with "abstract types do not match").
- `split-module-name`/`split-local-qual-name` returned `[""]` for empty qualifiers (Koka
  `"".split` artifact) so `match-qualifiers` never matched unqualified names against
  module-qualified infgamma entries (recursive occurrences "cannot be found");
  `match-rev-qualifier-paths` also aligned with upstream (unconditional unqualified match,
  removed a disjunct upstream has commented out).
- kind env extensions from typedef groups were unwound before value defs were kind-checked
  (upstream threads state); now reinstalled via `with override val inf-kind-env`.
- driver: modules without a `module` decl get named from the file stem; minimal builtin gamma
  (bool + optional constructors) and newtypes (`@optional`) until .kki loading exists.

2026-07-26: **THE COMPILE LAYER WORKS: programs importing the real std library compile and
run.** `compiler/main/modules.kk` loads `.kki` core interfaces transitively (from the JS stdlib
output of the Haskell compiler at `.koka/v3.2.7/js-debug-*/`), extracts
gamma/kgamma/synonyms/newtypes (`defs-from-modules`), and the driver seeds inference with them,
resolves fixities from the loaded cores, and emits `.mjs` that runs on the Haskell-built JS
stdlib runtime. Verified in node: hello (unqualified `println` with overload+implicit
disambiguation), `fib(20) = 6765` (operators/fixities/recursion/`.show` implicit), and
`[1,2,3].map(fn(x) x*2).show`. The `.kki` parser round-trips all 29 stdlib interfaces
(loudly — the inline section marker is converted to a special token).
Merged `pr/uv-thread-safety` into dev-compiler for later parallel builds (also brings JS
backend fixes + async test suite).
Port bugs fixed:
- core/parse: missing `[l,c,l,c]` ranges (type/alias/def/extern/local-alias), missing `= tag`
  for constructors, param names falling back to the constructor name, import provenance
  (`pub`/`type`/`inline`), inline-section detection.
- `parse-qualified-var-id` flattened structured names via `show-plain.new-name` (local
  qualifiers ended up inside stems).
- gamma extraction keyed by `unqualify` (kept local qualifiers); now keyed by the full stem via
  `gamma/single` like upstream `gammaExtend` (`unqualifyFull`).
- `create-name-infoEX` computed the default-namespace depth `-1` and then ignored it — the
  `default/` overload deprioritization never fired, making e.g. `println` ambiguous.
- `import-map/resolve-path` returned the alias path unreversed ("types/core/std").
- `find-infkind` returned the current-module-qualified name instead of the resolved one
  (spurious "should be cased as" errors on every std type annotation).
- `is-type-var` tested the local qualifier instead of the stem (all type variables parsed as
  TpCon).
- fixity resolution: infix operands popped from the stack un-swapped (`a - b` compiled as
  `b - a`); wired `fixity-resolve` into the driver (upstream runs it before kind inference).
- `make-nil` wrapped `Nil` in a zero-argument application.
Known gaps / next: effect declarations ("Invalid type" — kind/synthesize effect machinery);
module-local names do not take precedence over std imports on ambiguity (smoke.kk renamed);
inline-definition sections are parsed but not used; single hard-coded kki search dir.

2026-07-26 (later): progress on effect declarations (still incomplete):
- `make-effect-decl` used the old `KindCon(HX)` result kind; upstream expands it to
  `(E, V) -> V` (`makeKindHandled`) — ported (reusing parse-type's helper shape).
- `resolve-constructor` discarded the incoming datatype-parameter idmap and resolved
  constructor fields with only the existentials in scope ("Type variable @e is undefined").
Remaining: a kind mismatch on the generated effect tag (`htag<ask>` vs `htag<_a>`) — next
stop in the effect-decl desugar/kind-inference chain.

2026-07-26 (part 2): **EFFECT HANDLERS WORK END-TO-END.** `test/driver/handler.kk` (fun
clause) prints 42; `test/driver/yield.kk` (`ctl` clause with `resume`) prints yielded 1/2/3 —
identical to the Haskell compiler — running in node against `$std_core_hnd`.
Implemented `infer-handler` (was a stub): clause construction per operation sort
(val/fun/final-ctl/ctl/raw-ctl with resume/rcontext binders), handler constructor with
control-flow-context lub, wrapping via the generated `@handle` + `@hhandle`, action-type
extraction from the handle function, linearity check. Port bugs fixed on the way:
- core/parse env `bound.add` never overwrote bindings: type variables reused across
  declarations in one interface file kept their FIRST kind (scrambled quantifier kinds in
  every later declaration — `@hhandle`'s binders were shuffled).
- `check-skolem-escape` had the condition INVERTED (errored exactly when nothing escaped).
- `infer-handled-effect`: non-instance guard was missing its negation; ctx matchSome flag.
- `check-coverage/field-to-op-name` read the local qualifier instead of the stem and did not
  strip the `@` before reading the operation sort.
- `expr/is-total` used `is-total` for the function position of applications; upstream uses
  `isTotalFun` where a bare `Var` is NOT total — the unsafe simplify deleted any effectful
  statement whose result was unused (`println(a); println(b)` compiled to just `b`!).
- driver: core passes now get the full gamma (imports + own defs) for open-resolve.
- `prefix` is a reserved word (fixity keyword) — cannot be a binder.

Remaining inference TODOs:
- driver starts from empty environments: no `.kki` loading, so no imports/primitives (Compile layer).
- `fix-canonical-name` gamma resolution TODO; `uniq0` seed for infer-types is a fixed 10000 (should
  thread the kind-phase unique counter through).
- effect-label duplication: `check-file`'s inferred row duplicates `colors`/`div` (explicit rows in
  `infer-full` + open tails), worked around in `main` with a double `colors` install + `collapse-div`.

### Known gaps

- `syntax/range-map.kk`: `substNiceRangeMap` not ported yet (no caller ported; needs `realias-type`).

#### Test-fidelity findings (2026-08-05 sweep, classes needing deeper work)

- ~~non-ASCII chars in string literals dropped~~ RESOLVED 2026-08-05: not the lexer
  (verified correct via a direct `lexer/lex` harness) -- backend/c/helpers.kk `cString`
  had `// TODO: BIG UTF-8` and emitted nothing for chars > 0x7F; now emits the UTF-8
  bytes as `\xNN` escapes exactly like upstream `cstring`.
- **`gen-fun-sig: expected lambda expression` backend crash** (cgen/returnscrut, cgen/mutual1):
  a DefFun's expr reaches backend/c/expr.kk `gen-fun-sig` as a non-lambda; upstream would
  crash identically on the same core, so an earlier port pass (unreturn/monadic?) produces
  a different def shape. Repro: early-`return` inside `match` scrutinee position.
- **lib/double2 + medium/caesar + medium/fibonacci(?) segfault at runtime** (compiled
  program SIGSEGV) — float64/string-heavy programs; genuine codegen bug, try an
  ASAN build of the generated C to localize.
- **kind/alias3: "type alias not fully applied"** where upstream accepts an alias used as a
  type-constructor argument (`ap<id,foo>`) — kind-inference alias application.
- ~~meta-var unique-id magnitude~~ RESOLVED harness-side 2026-08-06: the sweep sanitize
  chain now renumbers unique-counter-sensitive tokens order-preservingly (`_<digits>`
  metas, `-x<digits>` hidden locals, bare letter/number param types in `fn(...)`
  headers), applied to both actual and expected. Distinctness is preserved so different
  ids never conflate; blanket digit normalization was measured and REJECTED (it masks
  the genuine scheduler2-4 off-by-one column bugs and wrong numeric program output).
  Upstream Box-pass note: `TypeLam`/`TypeApp` erasure in Box.hs is load-bearing (box
  erases TForall at the TYPE level too; retaining the nodes crashes splitTForall --
  verified experimentally). If upstream ever wants `fn(x: a)` instead of `fn(x: 14)`
  in backend core, the fix is printer-side (seed the body's nice env from the scheme).
- **kgamma ambiguity-hint order** (static/wrong/alias1, module1): expected lists the
  LAST-imported module first (`modAWrong, modA`) while the pub-closure fold produces
  declaration order; upstream's kgammaUnionLeftBias + defsMerge should give the same --
  needs a trace through upstream's actual module list for these tests.
- **core/specialize crash** (cgen/specialize/map*, while): `fn-type-params: not a function:
  Lam(...)` -- replace-call receives `mb-type-args = Just(...)` (call site had a TypeApp)
  but the stored inline def expr is a MONOMORPHIC Lam (no TypeLam); upstream's stored
  inline for the same def must retain the TypeLam. Suspect inline-def capture or unroll
  interaction in the port.
- **type/eff5a inference divergence**: port infers `choose: forall<a,b> (x : a, y : b) -> a`
  where upstream unifies both params (`forall<a> (x : a, y : a) -> a`), and
  `ok: forall<a,b> (f : a) -> ...` -- REAL unification/generalization divergence, not display.
- **jsgen suite**: blocked on the known JS-target runtime `.mjs` file resolution gap
  (tests run node against `test/jsgen/std_core_types.mjs` which is never emitted there).
- **lifted-param names now THE dominant class (~17 tests incl. specialize suite + async
  typesig residuals)**: upstream's `@lift`/`@unroll` sigs show NAMELESS params
  (`(list<int>) -> ...`) where the port shows uniquified locals (`xs@8016 : ...`).
  Verified upstream's typeOf(Lam) KEEPS TName names and ppParam only hides nil/wild/
  hidden/field names -- so upstream's lifted-lambda param TNames must BE nil/hidden at
  that point. Next probe: Core/Parse.hs's inline-section lambda parsing (specialized
  bodies originate from kki inlines for std functions) vs the port's core/parse.kk --
  do parsed lambda params get nil names upstream? PROBED 2026-08-06: NO -- upstream
  Core/Parse `parseFun`/`parameters` keeps real param names (`Lam [TName name tp ...]`),
  so kki-parsed inline lambdas are named upstream too. Next hypotheses, in order:
  (a) dump upstream's @lift def RAW (trace prettyDef in FunLift) on
  cgen/specialize/bintree to see whether the Lam's TNames are nil-named at CREATION or
  only render nameless via some pp path not yet identified; (b) diff the port's
  specialize `replace-call`/uniquefyExprU param handling against upstream's
  (`fnParams expr` after uniquefy) for a name-dropping difference in reverse: the PORT
  may be RETAINING names upstream loses inside `Core.Uniquefy` (check upstream
  uniquefyExprX's Lam case: does it rename params via `uniqueTName`-style fresh names
  that keep the stem, or via nil?). ROOT CAUSE FOUND 2026-08-06: upstream
  `uniquefyName` in FULL mode (uniquefyExprU, used by Specialize) renames via
  `uniqueNameFrom = toHiddenUniqueName i "uniq" name` -- a HIDDEN name
  (`@uniq-<stem>@<i>`), which ppParam then suppresses (isHiddenName). The port's
  uniquefy full-rename keeps a visible `<stem>@<i>` name. FIX: make the port's
  core/uniquefy.kk full-mode rename produce make-hidden-name("uniq",
  to-unique-name(i, name)) exactly like upstream Common/Unique.uniqueNameFrom;
  then the ~17 lifted-param-name tests should collapse (params render nameless).
- **specialize/@lift sigs** (cgen/specialize suite): upstream shows NAMELESS params
  (`(tree<int>) -> ...`) for lifted defs and one MORE `@lift` def than the port; the port
  shows uniquified user names (`tree@8016 : ...`). Both the param-name provenance and the
  missing specialization need investigation in core/specialize.kk + core/fun-lift.kk.
- **parc suite import lists**: the port's kki emission imports extra modules
  (undiv/unsafe/...) and orders `int` differently vs upstream's pub-closure; see the gamma
  InfoImport architectural note.
- **alias doc-comments** (kind/type9/type10): `// comment` preceding `pub alias` doesn't
  reach `syn-info.doc` (parse-doc-keyword only sees the doc on the `alias` lexeme; the
  layout pass attaches the comment to `pub`).
- **scheduler2-4 effect-subsume range off-by-one**: for `fun driver()` (ADJACENT parens)
  upstream anchors the infinite-type error AT the closing paren (32,14) while the port
  points one past (32,15); with spaced parens (`driver  ()`) BOTH point one past. The
  propagated-effect range's construction differs somewhere in the fun-decl parse or the
  recursive-def propagation; empirical probes show the anchor is token-spacing-sensitive
  upstream. Needs a trace of `Just (topEff, r)` provenance in inferExpr.Lam. 3 tests.
- **parsec-style farthest-failure error reporting** (kind/wrong/type7, syntax/wrong/braces1-2,
  medium/allsamples): the port's parse-choices reports the LAST/outermost failure (often
  `peof expected end of file` at the wrong position) where parsec merges and reports the
  farthest-position expectation set. Needs error-merging in common/parse.kk.
- **peek-dispatch fallbacks in `core/parse.kk` (`parse-lit`, `parse-atomic`) -- revisit.**
  Both dispatch on the next token and keep the old `parse-choices-nb` list in the `_`
  arm, so each states its grammar twice. Measured worth ~0.4% CPU (see the
  parser-choice-handler note); the open question is whether the `_` arms can collapse.
  What was established 2026-09-16:
  - The `_` arm does NOT buy a richer message. When every alternative fails,
    `parse-choices-nb` raises `"expected " ++ str` at `peek().range`, and the reporter
    substitutes the recorded expectation set only when
    `far-rng.start.off > r.start.off` -- STRICTLY beyond. Here they are equal, so the
    printed message is just `expected literal`; the four accumulated labels are never
    rendered at that position.
  - So the fallback buys exactly two things: that message string, and the
    `precord-expect` records, which matter ONLY to an enclosing parser that fails at an
    earlier offset and finds this position to be the deepest progress. Those records do
    survive -- `parse-maybe-nb` never calls `pfar-restore`.
  - A `<?>`-style combinator reproduces both in three lines:
    `fun expected(str, lbls)` = record each label at `peek()`, then
    `parse-error("expected " ++ str, t.range)`. Note it must raise the SECTION LABEL;
    joining the labels would silently change the message.
  - `parse-lit`'s arms provably cover its four alternatives, so it can collapse.
    `parse-atomic` is unresolved: its arms look like they cover the sub-parsers'
    first-sets (`LexCons`/`@cpath` -> `parse-con`, `LexId`/`LexOp`/`LexIdOp` ->
    `parse-var`, the literals, `(`), but qualified constructor tokenization was not
    verified. Settle it by tracing the `_` arm over a full build and collapsing only if
    it never fires.
  Related: the farthest-failure entry above -- the merge machinery now EXISTS
  (`precord-expect`/`far-msgs`), so that entry's "reports the LAST/outermost failure"
  wording is stale; the gap is now the strictly-greater-offset condition.
- **build-error message for missing module** (static/wrong/module2): upstream prints
  `build error: could not find module: X (imported from Y)` + the search path; the port
  prints a bare parse error with a null range.
- **alex-koka single-regex strings over-munch**: the JSON bench lexer (`../parsing/parsers/alex`)
  lexes `\" @character* \"` past the closing quote (crossing unescaped quotes); `test/lib/json-test.kk`
  fails on this. The compiler lexer is unaffected (it lexes strings in chunked `<stringlit>` mode and
  the full std sweep passes 68/68). Needs investigation in the alex fork's DFA translation for
  single-regex terminated tokens.

(Resolved 2026-07-23: UTF-8 lexing — `koka.x` declared `%encoding "utf8"` while upstream `Lexer.x` uses
`%encoding "latin1"`; in utf8 mode alex re-encodes the byte-range patterns as codepoints so the utf8valid
byte patterns could never match. Also fixed an out-of-bounds `unsafe-idx` on the `alex-check` table in the
alex-koka runtime template (`../alex/data/alex-effects.kk`): the guard ran *after* the read, which faults
on Koka's heap unlike GHC's raw Addr# reads — this segfaulted on `//` inside block comments with the
latin1 tables. The full `test/syntax/parse.kk` std-library sweep now parses 68/68.)

### Up to date

Everything else with a recorded baseline, including the whole parse cluster, `syntax/lex.kk` (dd91082),
`common/{name,name-prim,syntax,range,parse}.kk`, `kind/repr.kk`, `static/binding-groups.kk`,
`syntax/{lexeme,highlight,range-map,syntax}.kk`, `type/{pretty,operations,unify}.kk`,
`common/color-scheme.kk`, `common/error.kk`, `common/failure.kk`, `common/message.kk`, `common/nice.kk`,
`common/resume-kind.kk`, `common/id.kk` (Id/IdMap/IdSet), `common/name-collections.kk` (NameMap/NameSet/QNameMap),
`kind/kind.kk`, `lib/scc.kk`, `syntax/layout.kk`, `syntax/pretty.kk`, `syntax/promote.kk`.

### Backfilled baselines

2026-07-23: the previously unannotated files (all of `core/`, `kind/`, `type/`, `backend/c/`, `lib/`,
`common/unique.kk`, `platform/config.kk`, `static/fixity-resolve.kk`, `syntax/lexer.kk` — 47 files) now
carry `// Ported as of <date>; approx upstream baseline commit <h>` headers, derived from each file's last
port-repo commit date and the upstream commit as of that date. These are *approximate* — verify against the
actual upstream content when re-syncing a file, then replace the header with an exact `// Updated as of`
line. `check-upstream-sync.sh` covers all 85 entries now; run it for the current behind-list
(~27 files behind as of today, headed by `core/analysis-match.kk` (26), `type/infer.kk` (11),
`kind/infer.kk`/`core/pretty.kk`/`core/parse.kk`/`backend/c/*` (9 each)).

Only `lib/core.kk`, `syntax/format.kk`, and `syntax/original/*` remain untracked (Koka-native, no upstream
counterpart).

## `compiler/lib/printer.kk` (via `std/pretty/printer`)
- [ ] **File Buffering Performance**: The current `file-printer` reads the entire file into a string, appends to it, and writes it back on every flush. This is `O(N)` per write. 
    - **Fix**: Use append-mode file handles or proper buffered IO to achieve `O(1)` performance.

## `compiler/common/color-scheme.kk`
- [ ] **Relative Paths**: The `show-range` function currently has a `TODO` regarding printing paths relative to the current working directory (`cwd`).
    - **Fix**: Implement `relative-to-path` logic similar to Haskell's implementation.

## `compiler/common/range.kk`
- [ ] **Source Storage**: Koka stores source content as `string` (UTF-8), while Haskell uses `ByteString`. This might have performance or memory implications for large files.
    - **Action**: Evaluate if `string` is sufficient or if a raw byte buffer is needed.
- [ ] **Literate Script Support**: `extractLiterate` is missing.
    - **Fix**: Implement parsing/extraction for literate Koka files (`.lagda` style or similar if supported).
- [ ] **BOM Stripping**: `readInput` (or its equivalent) does not check for or strip the UTF-8 Byte Order Mark (BOM).
    - **Fix**: Add BOM detection to file reading.

## `compiler/common/failure.kk`
- [ ] **Stack Traces**: The `raise` function currently does not print stack traces in debug builds, marked by `// Figure out stack traces`.
    - **Fix**: Integrate with Koka's runtime stack trace capabilities if available.
- [ ] **Error Message Processing**: The `catch` handler has a `TODO` for adjusting error messages (e.g., stripping "user error:" or "IO Error:" prefixes).
    - **Fix**: Implement the string processing logic found in Haskell's `catchIO`.

## `compiler/kind/kind.kk`
- [ ] **Missing Helpers**: `kindAddArg` function is missing (also it seems to be unused in the Haskell codebase)

## `compiler/syntax/highlight.kk`
- [ ] **Isocline Integration**: `// TODO: Isocline stuff`
- [ ] **Formatting Attributes**: `// TODO: FmtAttr`

## `compiler/syntax/lexer.kk`
- **Note**: Literate script support (`extractLiterate`) is missing (tracked under `compiler/common/range.kk`).

## `compiler/syntax/parse.kk`
- [x] **Handler Parsing** (resolved 2026-08-03): `parse-handler-expr` already matches
  upstream's `handlerExpr`/`handlerExprWith`/`handlerClauses` as of upstream 4266dfbee
  "update parser for handlers further" -- the stale TODO comment has been removed.
- [ ] **Raw Value Definitions**: `parse-handler-op` asks `// TODO: is "raw" needed for value definitions?`.

## `compiler/syntax/parse-type.kk`
- [ ] **Error Context**: `parse-type-binder` has a `TODO` to add error context.

## `compiler/syntax/builders.kk`
- [ ] **Record Operations**: `make-effect-decl` and `make-operation-decl` have `TODO` to use record operations.
- [ ] **Resume Parameters**: `bind-expr-to-val` has `TODO` to add parameters to resume.

## `compiler/syntax/promote.kk`
- **Note**: `extend`, `makeEffectExtends`, and `extract` are missing compared to Haskell, but the file header notes this is intentional (unused/unexported).

## `compiler/syntax/syntax.kk`
- **Status**: Defines the AST. Matches `src/Syntax/Syntax.hs` very closely (1:1 structures).

## `compiler/syntax/pretty.kk`
- [ ] **Dot Notation**: Koka's `App` printing is generic `e(args)` where Haskell tries to reconstruct dot notation `arg0.fun(args)`.
- [ ] **Guards**: Koka iterates all guards printing `->`, while Haskell checks `alwaysTrue` to skip the guard arrow/expr if the guard is just `True`.

## `compiler/syntax/range-map.kk`
- **Status**: Faithful port of `src/Syntax/RangeMap.hs`. API and helper functions match for supporting "IntelliSense" (finding blocks, previous lexemes, etc.).

## `compiler/syntax/format.kk`
- **Status**: Work-in-progress formatter. Not present in Haskell reference (likely new Koka-native tooling).
- [ ] **Features**: Many TODOs for implementing `use-tabs`, `add-braces`, `remove-braces`, `add-semicolons`, etc.
- [ ] **Strings**: TODO regarding "Strings have bad ranges".

## `compiler/type/type.kk`
- **Status**: Defines `ktype` (matching `Type.hs`). Includes utilities like `is-optional`, `make-optional`, etc. from `Infer.hs` in Haskell.

## `compiler/type/typevar.kk`
- **Status**: Matches `TypeVar.hs`. Defines `sub` substitution map and type variable utilities.

## `compiler/type/kind.kk`
- **Status**: Matches `src/Type/Kind.hs`. Contains effect checks (`label-is-linear`, `effect-is-affine`) and `get-operation-effect`.

## `compiler/type/unify.kk`
- [ ] **Status**: Ported. Needs verification of `match-arguments` logic against complex cases.

## `compiler/type/infgamma.kk`
- [ ] **Status**: Ported. Implements the inference monad and implicit constraint handling.

## `compiler/type/infer-effect.kk`
- [ ] **Status**: Ported. Handles effect inference and `isolate` logic.

## `compiler/type/assumption.kk`
- [ ] **Status**: Ported. Manages name assumptions and gamma.
- [ ] **Gamma-fidelity gap** (found 2026-08-03 while wiring up `--showtypesigs`): upstream's
  `Gamma` only ever holds names LOCAL to the module being compiled, plus lightweight
  `InfoImport` aliases for everything imported -- so filtering `not (isInfoImport info)`
  alone isolates a module's own definitions (`ppGamma`, used by `compileShowInfo`/
  `--showtypesigs`, and elsewhere for scoped name-resolution diagnostics). This port's
  `type-check.kk`'s `gamma0` is instead a flat `unions([defs.defs-gamma, extract-gamma(...),
  extract-gamma-imports(...)])` that merges every transitively imported module's FULL real
  gamma in directly (needed so type inference can resolve imported names' real schemes)
  rather than wrapping them as `InfoImport` -- so `is-info-import` can't distinguish "this
  module's own def" from "resolved through an import" on `gamma0` anywhere it's used.
  `--showtypesigs` was fixed by using `driver.kk`'s `ownCoreGamma` (built from the finished
  core's own defs) instead of `gamma0` for that ONE call site -- a real fix there, not a
  workaround, since `ownCoreGamma` is genuinely local-only by construction. But the
  underlying representation gap in `gamma0` itself is still real and could matter elsewhere
  (e.g. correctly-scoped "did you mean" suggestions, IDE hover/completion) -- a proper fix
  would track a genuinely separate local-only gamma alongside the full resolution gamma,
  matching upstream's actual Gamma/InfoImport split.

## `compiler/type/operations.kk`
- [ ] **Status**: Ported. Implements instantiation, skolemization, and heap divergence checks.

## `compiler/type/infer.kk`
- [ ] **Incomplete Port**: The main expression inference function `infer-expr` is missing/commented out.
    - **Note**: `infer-arg-expr` contains a `throw("")` placeholder.
    - **Action**: High priority to implement the main type checking loop.

## `compiler/type/pretty.kk`
- [ ] **Status**: Ported. Implements `pp-type` and related type printing functions.

## `compiler/core/core.kk`
- **Status**: Ported. Defines Core language AST (`expr`, `def`, `core`) and traversals (`expr/cost`, `is-total`).

## `compiler/core/corevar.kk`
- **Status**: Ported. Handles variable substitutions (`|->`) and free variable analysis.

## `compiler/core/monadic.kk`
- **Status**: Ported. Implements monadic translation (`mon-expr`, `mon-branch`).

## `compiler/core/monadic-lift.kk`
- **Status**: Ported. Implements lambda-lifting (`lift-expr`, `make-def`).

## `compiler/core/inlines.kk`
- **Status**: Ported. Manages inline definition catalog and extraction.

## `compiler/core/pretty.kk`
- **Status**: Ported. Implements `pretty-core` and Core expression printing using `pp-env`.

## Performance: the TIMEOUT cluster (profiled 2026-08-05)

The 30 sweep TIMEOUTs (lib/time*, lib/ddouble*, lazy/queue/*, heavy algeff)
are a genuine compile-time pathology, not a harness artifact: `lib/time2.kk`
takes **3m20s of CPU and then segfaults (SIGSEGV, likely C-stack overflow)**
during type inference. `sample`-profiling shows the time inside the inference
pipeline with `std_core_hnd__hhandle`/`mask_at` (effect-handler dispatch) and
`extend-inf-gamma`/`inf-gamma` frames dominating the call graph.

What was tried and did NOT help (kept anyway as harmless handler-frame
reduction, verified regression-clean): removing the per-AST-node
`with trace-indent` handlers from type/infer.kk's hot path -- no measurable
change (3m17s), i.e. the sample's 14% `trace_indent` attribution was
inclusive-time noise.

Leading hypothesis for the real cost (NOT yet verified): every gamma /
inf-gamma / kgamma in the port is a `std/data/linear-map` -- an ASSOCIATION
LIST -- where upstream uses `Data.Map` (balanced tree). A module importing the
large std/time / std/num/ddouble interface trees puts thousands of symbols in
those flat lists, making every identifier lookup O(total defs) and unions
O(n*m); the segfault is plausibly deep non-tail recursion over those lists.
Next step: measure gamma sizes on lib/time2, then replace the hot maps
(type/assumption gamma, inf-gamma, newtypes/synonyms/kgamma) with an
ordered-tree or hash map. This is the entry point for the broader performance
workstream (and likely also fixes the 2 stack-overflow CRASHFAILs noted
earlier, eff-rec1/eff-rec1a).

## Session findings 2026-08-06 (focus 1+3 batch: uniquefy hidden names, parc order/pretty, -O1 cache)

Implemented this batch (rebuild + sweep pending as of writing):
1. **common/unique.kk `unique-name-from`** now mirrors upstream `uniqueNameFrom`
   (`to-hidden-unique-name(i, "uniq", nm)` -> hidden `@uniq-<stem>@<i>`); ppParam
   suppresses hidden names, expected to collapse the ~17-test lifted-param class
   (cgen/specialize suite + parts of async/parc sig residuals).
2. **core/pretty.kk `pretty-pattern`**: (a) the arg-doc foldr appended instead of
   prepending, printing PatCon args REVERSED (`Cons(tail, head)` -- parc11/15/17/18/20
   and most parc diffs); (b) missing ` : ` colon before the PatCon result type.
3. **type/pretty.kk `pp-decl-type`** hardcoded `Own`, dropping `^` borrow markers
   from def signatures (parc21). Now zips `pinfos ++ repeat Own` like upstream.
4. **backend/c/parc.kk set iteration order**: upstream `S.toList`/`foldMapM` iterate
   TName sets sorted by `Ord Name` (hash-first compare, port `name/cmp` already
   matches); the port's linear-set `.list` is insertion-ordered which changed emitted
   dup/drop ORDER and even which drop `optimize-disjoint` specializes first
   (parc12/14/parc3 drop placement). Added `sorted` (sort by name/cmp) at all
   gen-dup/gen-drop/optimize-disjoint/fuse-alias sites.
5. **common/nice.kk + type/pretty.kk**: upstream's nice env is a FUNCTIONAL env
   field -- extensions inside a printed `forall` scope are discarded on exit, so
   sibling inner foralls both print `<a>` (type/hr1). Added `nice-push`/`nice-pop`
   ops + `nice-scoped`, used in `pp-type` TForAll; body also now prints at
   `precTypeTop` (upstream sets `prec = precTop`; port added spurious parens
   around function-typed forall bodies).
6. **type/infer.kk unused-pattern warning**: upstream reports only the FIRST unused
   name (sorted), singular "pattern variable x is unused", hint "start with an
   underscore" (parc18 warning text diff).
7. **.koka-runtime cache rebuilt at -O1** (`clang-drelease` flavor, moved into
   `.koka-runtime/clang-debug`; old -O0 cache kept as `clang-debug-O0.bak`).
   ROOT CAUSE of the parc2-style "unroll wrapper missing" class: the old cache
   was built -O0 so its .kki files had NO inline sections with `@unroll-*`
   wrappers (upstream Spec builds std at -O1: `.koka/v3.2.7-test/clang-drelease`
   has `inline fip fun append ... @unroll-append@10004`); the port therefore
   never inlined `std/core/list/append`'s unroll wrapper into test bodies.
   **compile/link.kk KK_DEBUG_FULL** define switched to upstream's literal
   `buildType == DebugFull` gate to stay consistent with the new drelease cache
   (the old `fl.debug` gate matched the old debugfull-flavored cache; mismatch
   manifests as mimalloc crashes -- re-verify if the cache is ever rebuilt).

Investigated, root area identified, NOT yet fixed (needs runtime probes):
- **cgen/mutual1 + returnscrut + tail2 "gen-fun-sig: expected lambda"**: the port's
  INITIAL core for mutually-recursive zero-arg defs is `forall<a>. forall<b>. fn() ...`
  (DOUBLE TypeLam, scheme has ONE forall) where upstream has a single TypeLam.
  Because the def expr is not `TypeLam(tvs, Lam(...))`, def-level simplify recurses
  into it and the eta rule contracts `fn() bar()` -> `bar`, leaving a non-lambda
  in a DefRec which crashes the C backend sig gen. The double-generalize happens
  before/inside infer-rec-def2 (its own logic matches upstream inferRecDef2);
  suspect the first-pass rec def is already generalized where upstream keeps it
  mono. Probe: trace resCore1 shape in infer-rec-def2 for mutual1.
- **algeff/exn2 effect-alias display**: port keeps `io` when it's the WHOLE effect
  (`test2: () -> io list<bool>` OK) but expands it inside a row (foo's annotated
  `<amb,state<int>,io>` prints fully expanded+sorted). kind/infer.kk already uses
  shallow-effect-extend; the TSyn is lost LATER (something orders/extracts the
  annotated effect during inference -- upstream `extractOrderedEffect` expands
  synonyms, so upstream must never apply it to the stored annotation type).
  Also spotted: port prints `console/console` where upstream shows `console`
  (shortenSystemCoreName/removeCommonPrefix difference in label display).
- **lazy/sieve C compile error (lazy is_unique boxing)**: port passes `kk_box_t`
  `_brw_*` temps to `kk_datatype_ptr_is_unique`/`kk_lazy_atomic_enter`; upstream's
  generated `lazy_sieve.c` has `kk_lazy_sieve__integers _lazy` (concrete type, no
  borrow let-floating -- args stay Vars). kind/synthesize's syn-lazy-eval matches
  upstream structurally; suspect the port's synthesized eval def's `@lazy` param
  type stays a TVar (boxed) instead of the concrete lazy datatype. Probe:
  --showcore lazy/sieve, check `integers/lazy-eval` param type.
- **kind/type9 + parc20 doc-comment drops**: port loses `//` doc comments on some
  decls (alias in type9, fun in parc20) while keeping them in others (parc21) --
  doc attachment rule differs somewhere in the parser/kind-infer path.
- **medium/caesar + lib/double2 segfaults**: still need an ASAN run of the
  generated C.

## Session findings 2026-08-07 (newtypes closure + -O1-exposed codegen fixes)

Fixed (PASS 329 -> 335):
1. **driver.kk newtypes closure**: core-optimize AND code-gen (parc runs in the C
   backend!) now receive newtypes over ALL loaded modules (`unions([nt,
   fullDefsNewtypes])`), not just the pub-import-closure set -- parc analyzes
   types inside INLINED imported code (cgen/imports: std/time/timestamp).
2. **backend/c/constructors.kk**: multi-field no-tag value structs emitted
   `return _con;` with `_con` UNDECLARED -- upstream's else branch (decl +
   per-field assigns) was missing entirely (overload/implicit-unpack,
   lazy/queue bench.h, and the medium/caesar SEGFAULT -- uninitialized struct).
3. **driver.kk add-default-handlers**: instantiated every `@default-<eff>`
   handler with `[typeTotal]`; for `forall<a,..>` handlers that set the RESULT
   type to `total` (lib/time11's C returned the total struct from @main). Now
   instantiates by kind: effect vars -> total, star vars -> entry result type.
   (Upstream wraps at the source level and re-typechecks.)
4. **backend/c/expr.kk gen-local-def**: the "single assignment without
   declarations" branch compared defDoc against the KOKA name (`@ru-x149 =`)
   instead of the C-mangled name (`_ru_x149 =`), AND had the nameIsNil guard
   inverted -- so `kk_reuse_t _ru = kk_reuse_null;` initializers were dropped,
   leaving reuse tokens uninitialized when only one branch of the following
   is-unique if assigned them (lib/dir -Wsometimes-uninitialized).
5. **compile/code-gen.kk exe naming**: use the module-name-encoded stem
   (test/lib/lib_dir) like the .c/.h files -- the plain source stem collided
   with the test's own `dir/` DIRECTORY.

Remaining after this batch (51 MISMATCH): lazy/* (the lazy is_unique boxing bug
now also visible in lazy/queue/bankers etc: `_brw_*` box temps passed to
kk_datatype_ptr_is_unique), effect-alias display (algeff/exn2 + async 4),
mutual-rec double-TypeLam (cgen/mutual1/returnscrut + open1), specialize
residuals (7: $h skolem + shapes), parc placement residuals (9), jsgen (5),
doc-comment drops (kind/type9/10, parc20), garcia-wachs, eta-expand warnings,
masklocal1/eff8b, static/wrong 2, ops2/reactive1/busy-beaver. lib/dir now runs
but reads `test/lib/dir/` relative to the CWD -- the harness runs the port from
PORT_ROOT so the path misses (upstream Spec runs koka from the koka repo root);
harness/environment question, not a codegen bug.

## Session findings 2026-08-07b (name-hash ordering, lazy-prim boxing, harness parity)

Fixed (PASS 335 -> 355):
1. **common/name.kk `hash`**: the foldl lambda had (acc, elem) SWAPPED --
   computed `elem*256 + acc` (last-char dominant) instead of upstream's
   `acc*256 + elem`; ALSO padded short strings with `'_'` (95) instead of
   NULs. `name/cmp` (hash-first Ord Name) therefore ordered names differently
   from upstream EVERYWHERE: effect re-alias subset walks always failed with
   interleaved user labels (io/ioc/st/pure never re-formed: algeff/exn2, the
   4 async typesigs, type/eff8b), and parc drop / lift quantifier orders were
   subtly off. One-line fix cascaded through ~17 tests.
2. **backend/c/box.kk**: added upstream Box.hs's "special internals" case --
   lazy primitives (atomic-enter/leave, datatype-ptr-is-unique/-whnf/-thread-
   shared, memoize(-target), indirect-compress) box each ARG at its own type
   and drop the TypeApp instead of coercing to the polymorphic signature
   (fixes `kk_box_t` passed to `kk_datatype_ptr_is_unique` in lazy/sieve and
   lazy/queue/*).
3. **Harness**: `.flags` files parse like upstream Spec (`words` + koka arg
   unquoting -- `"-e --showtypesigs"`'s quotes are NOT shlex grouping), and
   per-dir config.json now CASCADES from parent directories (upstream
   `extendCfg`) -- lazy/queue/* actually ran with `-e --showtypesigs` for the
   first time; 5 of 8 pass immediately.

Remaining 30 MISMATCH: jsgen 5 (parked), parc residuals 5 (18/20/21/22/23:
drop placement + borrow-inline + doc comment), mutual-rec double-TypeLam 3
(mutual1/returnscrut/open1), specialize 3 (while $h skolem, sieve, maptwice),
lazy 4 (indirect-compress content, bankers kind-warning text, realtime-fip x2),
doc-comment drops 2 (kind/type9/10), static/wrong 2 + ops2 + reactive1 +
garcia-wachs + eta-expand warnings + masklocal1 + lib/dir (cwd-relative test
data, see 2026-08-07 note). COMPILEFAIL 18: parse-error texts (parked),
scheduler2-4, tail2, allsamples, div1/2, type7, module2. TIMEOUT 15 (linear-map
perf, parked; queue benches sit near the 30s limit under load).

## Session findings 2026-08-08 (comment lexing, kind extraction, stderr policy)

Fixed (PASS 355 -> 363):
1. **Lexer comment fidelity** (syntax/koka.x + generated lex.kk): comment-END
   actions now include the matched text like upstream `withmore` (line
   comments keep their trailing '\n', block comments the closing '*/'), and
   chunk STARTS keep the full match ('//'+$symbol* -- previously '//----'
   lexed as '//', '//#kki:' as '//kki:', '//.inline-section' lost its dot).
   This made layout's doc-comment association line-arithmetic work for the
   FIRST time (docs now attach to decls: kind/type9/10, parc20) and the //.
   marker is recognized in layout itself. NOTE: first attempt broke kki
   parsing (the now-working doc association swallowed the dotless
   '//inline-section' marker before core-parse saw it) -- retaining the dot
   fixed that via layout's own '//.' special-case.
2. **kind/infer-kind `inf-extract-kind-fun`**: `inj` returned the ARGUMENT
   kind as the extraction result (upstream returns the tail's result), so
   `H -> X` extracted with result H and `mask<local>` failed its label-kind
   check (type/masklocal1). Also mirrored upstream's shadowed arrow patterns
   (no arrow-equality guard).
3. **Warning text**: op-sort quoting without spaces (algeff/wrong/ops2);
   memoize warnings include the lazy constructor name + full '(N vs M bytes)
   -- using an indirection instead' detail (lazy/indirect-compress, bankers).
4. **stderr policy**: compile/link.kk run-exe/run-js no longer merge the
   child's stderr (upstream runSystemEcho leaves it on the terminal and
   Spec.hs captures stdout only -- trace() output excluded); harness scripts
   likewise capture stdout only (algeff/reactive1).

Remaining 23 MISMATCH buckets:
- gen-fun-sig/mutual-rec double-TypeLam: cgen/mutual1, returnscrut, open1,
  medium/garcia-wachs (+ cgen/tail2 in COMPILEFAIL). add-divergent-effect and
  infer-rec-def2 match upstream textually; needs an INSTRUMENTED probe of
  resCore1's shape (suspect infer-subsume's coref wrapping the already-
  generalized defExpr in a TypeApp so the TypeLam match in infer-rec-def2
  misses). Plan: add a temporary trace in infer-rec-def2, one build, probe
  all 4 tests.
- FBIP checker NOT PORTED: upstream Core/CheckFBIP.hs (812 lines) runs at
  type-check (Compile/TypeCheck.hs:120) emitting the fip/fbip warnings that
  lazy/queue/{bankers,physicists-stack,realtime-fip} expect. Well-scoped
  full-module port.
- specialize 3 (while $h skolem, sieve, maptwice), parc residuals 4
  (18/21/22/23), jsgen 5 (parked), static/wrong hint order 2 (kgamma
  ambiguity list order -- import fold direction), syntax/eta-expand (port
  missing 'types do not match' warnings), lib/dir (cwd-relative test data).

## Session findings 2026-08-08b (mutual-rec class resolved)

Fixed (PASS 363 -> 367):
1. **core/corevar `beta/add-type-apps`** (upstream CoreVar addTypeApps): type
   application to a literal TypeLam SUBSTITUTES (beta) instead of wrapping in
   TypeApp(TypeLam ...). Instantiation now uses it; the mutual-rec
   double-TypeLam (add-divergent-effect -> instantiate -> re-generalize)
   collapses to a single merged TypeLam and def-level simplify keeps the
   lambda (cgen/mutual1). Diagnosed with a temporary resCore1 shape trace in
   infer-rec-def2.
2. **core/unreturn local-continuation case**: built the `cont` def but never
   emitted upstream's `makeLet` -- the @cont-x var dangled FREE
   (cgen/returnscrut, medium/garcia-wachs crashed in C sig-gen via a parc
   dup of the unbound name).
3. **backend/c/constructors**: (a) conAsJust `arg` computed eagerly, crashing
   on parameterless constructors (upstream relies on laziness; cgen/open1's
   open singletons); (b) the ConOpen tag test was missing the VALUE argument
   in `kk_datatype_as(tp, x)`.
4. gen-fun-sig crash message now names the def and prints the expr.
5. kind/infer-kind: restored arrow-equality guards as a DELIBERATE divergence
   (upstream's `KICon kindArrow` patterns bind a shadowing variable --
   upstream issue, report upstream).

Remaining 19 MISMATCH: FBIP checker not ported (3: lazy/queue bankers/
physicists-stack/realtime-fip), jsgen 5 (parked), specialize 3 ($h skolem +
sieve + maptwice), parc residuals 4 (18/21/22/23), static/wrong hint order 2,
syntax/eta-expand, lib/dir (cwd). COMPILEFAIL 18: parse-error texts (parked),
scheduler2-4, tail2 (type error in float64 context), allsamples (kki reparse
of lazycons sample), div1/2, type7, module2.

## Session findings 2026-08-08c (CheckFBIP ported)

**compiler/core/check-fbip.kk**: full port of upstream Core/CheckFBIP.hs (the
fip/fbip warning analysis), invoked from compile/type-check.kk between
unreturn and the initial simplify. Zero spurious warnings across the suite;
the 3 lazy/queue fip tests match upstream exactly. Notes:
- upstream Borrowed carries (ParamInfo, Fip); the port's borrowed map has only
  param infos, so `lookup-fip` reads gamma instead.
- WARNING ORDER: upstream prints kind-inference warnings AFTER later-phase
  warnings (verified live: bankers' checkFBIP warnings precede the
  "Cannot update the lazy constructor" kind warning). type-check.kk now
  buffers infer-kinds' warnings and flushes them at the END.
- reuse probabilities use a tiny (num,den) rational; upstream Data.Ratio.

PASS 367 -> 369. Remaining 16 MISMATCH: jsgen 5 (parked), specialize 3
($h skolem), parc 4 (18/21/22/23), static/wrong hint order 2, eta-expand,
lib/dir (cwd). TIMEOUT 15 (linear-map perf parked; lazy/queue/physicists-stack
sits at the 30s limit since check-fbip adds compile time -- will flip PASS on
an idle machine or when gamma lookups get faster maps).

## Session findings 2026-08-08d (performance: TIMEOUTs eliminated)

Verified the chronic TIMEOUTs were genuine slowness, not loops: algeff/implicits
terminates with CORRECT output in 144s (upstream 1.7s). Profiles (macOS sample)
attributed the time to assoc-list structures in the inference hot path.

Three fixes, measured at each step (PASS 375 -> 384, TIMEOUT 9 -> 0):
1. type/typevar `sub` + `tvs` -> std/data/int-map (Patricia tree; ~ upstream
   Data.IntMap), keyed by tvar id. Same-name op battery so call sites compile
   unchanged. implicits 144s -> 17s.
2. koka-community/std pprint `display-string` -> accumulator style (the
   right-recursive `++` overflowed the C stack rendering large docs -- this
   was the algeff/scoped + lib/ddouble2 SEGFAULT at ~16s, and almost surely
   the old lib/time2 3m20s segfault too).
3. common/name `(==)`: removed the hash-consistency assert. Upstream's
   `assertion` compiles out in release; the port's STRICT assert built four
   fully-explicit name strings per call in the hottest function in the
   compiler. time4 45s -> 10.5s, implicits -> 5.3s (27x total).

NOTE the general lesson of (3): upstream `assertion`/`trace` guards are FREE
in Haskell release builds but the port pays for strict message construction --
audit any future assert with a computed message in hot code.

Remaining perf headroom (time4 10.5s vs upstream ~2s), profiled:
- common/parse parse-maybe/parse-choices (~27% inclusive): the kki interface
  parser's backtracking combinators over the big std/time interfaces.
- ktype/substitute traversal/rebuild churn (~17%) + allocator traffic.
- name-keyed maps (gamma etc.) no longer dominate but are still assoc lists;
  swap candidates: std/data rb-map or hash-map keyed by name hash.

Remaining 16 MISMATCH (all previously triaged): jsgen 5, specialize 3, parc 4,
static/wrong 2, eta-expand, lib/dir. COMPILEFAIL 18 (parse-error texts etc.).

## Order-sensitive diagnostics in recursive groups (shared bug with upstream)
Type inference of a recursive def-group processes members in SCC order
(upstream: Data.Map key order ~ name-hash; port now matches, see lib/scc.kk).
Effect-dependent diagnostics that run during body inference (unused-expression
warning, potentially linearity/val checks) observe the group's shared effect
meta BEFORE divergence insertion (`add-divergent-effect`), so their outcome
depends on member order: if a `val` member is inferred first, its totality
constraint collapses the effect meta to `total` and later members' checks
misfire. Reproduce IN UPSTREAM: rename `recursive` to `zzz` in
test/type/wrong/div1 -> spurious "expression has no effect and is unused".
Principled fix (apply to BOTH compilers together + regenerate expectations):
defer intra-group val-totality constraints until after divergence insertion,
or extend inferRecDef2 to re-check effect-dependent diagnostics against the
final substituted types.

## O0 (no-specialize) memory blowup on compiler/syntax/lex.kk [open]
Self-compiling lex.kk explodes >8GB whenever SPECIALIZE IS OFF (-O0 default,
or -O1 --fno-specialize); plain -O1 is fine. Not prim-inline (KOKA_NO_PRIM_
INLINE still blows), not ctail (KOKA_NO_CTAIL still blows) => monadic
transform / open-resolve / monadic-lift / unsafe simplify / box / parc /
C-gen on the UNSPECIALIZED higher-order alex-scan core. The sweep never
tests O0, so this class is invisible to the harness. Also: the port REJECTS
compiler/core/core.kk ("external/rng is already defined ... use a local
qualifier?") which the reference accepts -- second self-compile blocker.

## Session findings 2026-08-18 (specialize cluster: stale cache, not a port bug)

Investigated the 12-test `cgen/specialize/*` sweep cluster (was thought to be
a port fidelity bug in `specialize.kk`/`monadic-lift.kk`, per the
`port-extra-monadic-lift` project memory). Traced end to end via
`--showfcore` diffs against the real reference compiler (not just the
`.kk.out` fixtures): `specialize.kk`, `unroll.kk`, and `monadic-lift.kk` are
all faithful ports (read side-by-side against `Specialize.hs`/`Unroll.hs`/
`FunLift.hs`, no divergence found). The actual cause: `.koka-runtime`'s
`std_core_list.kki` (and siblings) was missing `Core.Unroll`'s `@unroll-*`
helper wrappers for std lib's recursive functions -- those only get
generated when std lib is compiled at `-O1` or higher, and the live cache
had been rebuilt at some point without `-O1` (this exact mistake already
happened once before, 2026-08-06, per the session note above; apparently
regressed again since).

Confirmed directly: a from-scratch reference-compiler build of `std/core/list.kk`
without `-O1` produces a `.kki` with literally 0 unroll-tagged entries;
the SAME build with `-O1` produces 261. Rebuilt `.koka-runtime/clang-debug`
via `stack exec koka -- --sharedir=$(pwd) --target=c -O1
--outputdir=.koka-runtime/clang-debug -r -e util/link-test.kk` (now wrapped
in `scripts/rebuild-runtime.sh`, which asserts the unroll-content check so
this can't silently regress a third time without at least a loud failure).

**Sweep: 410/17/14 -> 422/17/2.** The 2 remaining mismatches are the
already-accepted `cgen/specialize/recursive-arg.kk` (cosmetic) and
`jsgen/err.kk` (known separate JS `.mjs` gap). `parc/parc2.kk`, part of the
original 14, is also now fixed -- its "extra imports, wrong `int` ordering"
was a downstream symptom of the same stale cache, not an independent
`pub-import-closure` bug as earlier suspected.

`.koka-runtime/` is gitignored, so this fix is local-cache-only -- anyone
building this repo fresh needs to run `scripts/rebuild-runtime.sh` (with its
built-in `-O1`) or will see this same 12-test class reappear.

## Comprehensive state audit 2026-08-27 (upstream-replacement gap analysis)

Method: mapped every upstream `src/**/*.hs` module (excluding `Platform/{haddock,hugs,wasm}`
and `Main/playground`) to a port file by CamelCase -> kebab-case, then hand-checked every
apparent miss. **87 of ~124 upstream modules have a same-named port file**; the 37 apparent
misses are almost all naming differences, verified individually below.

Reliability signal: **83 of 135 port `.kk` files carry a `// Ported as of` / `// Updated as of
... Commit <hash>` header**. The 52 without one are almost entirely the code we wrote
DIFFERENTLY from upstream rather than ported line-by-line -- all of `lsp/`, plus
`compile/{orchestrate,rpc,vfs,build-context,schedule,progress,registry}`, `interpreter/`,
`lib/log`, `main/driver`. Those are the files where "does it match upstream?" is not even the
right question; the parity risk there is behavioural, not textual.

### Genuinely NOT ported

| Upstream | Notes |
| --- | --- |
| `Backend/CSharp/FromCore.hs` | `--target=cs` still reachable upstream (`Target = Default \| CS \| JS \| C`). Port has `backend/c` and `backend/js` only. **Decision 2026-08-27: skip.** |
| `Compile/Package.hs` | Not ported (deprioritised). |

(`Syntax/Colorize.hs` -> `syntax/colorize.kk` and `Syntax/GenDoc.hs` ->
`syntax/gen-doc.kk` were both ported 2026-08-27 and moved out of this table,
including `fmtLiterate`/`fmtQualify`/`linkFromId`/`linkFromTypeId`. BOTH the
`-source.html` and the `.xmp.html` output are byte-identical to the reference
compiler on the modules tested; the residual `-source.html` differences on a
struct-heavy module are pre-existing range-map issues listed in
`compiler/next.md`, not Colorize/GenDoc gaps.)

### Apparent misses that are only naming differences (verified)

`Core/CTail`->`ctail.kk`, `Core/CheckFBIP`->`check-fbip.kk`, `Core/CoreVar`->`corevar.kk`,
`Core/UnReturn`->`unreturn.kk`, `Core/AnalysisCCtx`->`analysis-cctx.kk`,
`Kind/Synonym`->`kind/synonyms.kk`, `Lib/PPrint`->`lib/pprint.kk`, `Lib/JSON`->`lib/json.kk`,
`Type/TypeVar`->`type/typevar.kk`, `Type/InfGamma`->`type/infgamma.kk`,
`Common/{IdMap,IdSet,NameMap,NameSet,QNameMap}`->`common/name-collections.kk`+`common/id.kk`,
`Common/IdNice`->`common/nice.kk`, `Main/Run`->`main/driver.kk`,
`Platform/cpp/*`->`platform/config.kk` + std lib.
`Kind/InferMonad` and `Type/InferMonad` are folded into `kind/infer.kk` / `type/infer.kk`
(the port uses effects where upstream threads a monad).
LSP handlers map to `lsp/*`: `DocumentSymbol`+`Folding`->`symbols.kk`,
`TextDocument`->`diagnostics.kk`+`state.kk`, `Monad`->`state.kk`,
`Run`/`Handlers`/`Main`->`server.kk`.

### The REPL is the largest functional gap

`compiler/interpreter/` is 416 lines against upstream's 984 (`Command.hs` 309 + `Interpret.hs` 675).

Working: `:load`, `:reload`, `:set`, `:cd`, `:!`, `:?`, `:version`, quit.

**Not wired (each answers `not-wired`):** `Eval` (evaluating an expression -- the actual point of
a REPL), `:type`, `:kind`, interactive `Define`/`TypeDef`, `:edit`, and the listing forms of
`:s[ource]`, `:d[efines]`, `:alias`, `:t`, `:k`.

All of these need upstream's `buildcCompileExpr` -- compile a synthetic module wrapping the
expression. **The port has no equivalent.** Note this is the same machinery upstream uses for
`koka/compileFunction`, which this port implemented differently (via `mainEntryName` +
`outFinalPath`); compile-expr should have come first and `compileFunction` been built on it.

### Language server: ported vs missing

Ported: diagnostics (push + pull), hover, definition, completion, inlay hints (3 kinds, with the
client's three config toggles), document symbols, folding, signature help,
`workspace/executeCommand` (`koka/compile`, `koka/compileFunction`, `koka/set-colors`,
`koka/signature-help/set-context`), `window/logMessage` + `$/progress` phase reporting.

Code actions: **1 of 6 generators.** `syn-general-unary` scaffold + `show` work end to end.
Missing: `syn-binary-op` scaffold and `==`, `cmp`, `order2`, `map`, overloaded.

Not ported: `Pretty.hs`'s `asKokaCode`/`ppComment` are done, but nothing renders documentation
into completion items (upstream puts only the module name there, so this is faithful).

### Fidelity bugs found and fixed during this audit cycle

- `syntax/parse.kk` `parse-fun-decl`: binder range was `nameRng`, upstream is
  `combineRange nameRng parsRng` (Parse.hs:1498). Inference places the `result` range-info at
  `vrng.end-of-range` (`{-')'-}` upstream), so the inferred-result inlay hint rendered
  `fun main : eff ()()` instead of `fun main() : eff ()`. Fixed.
- `syntax/pretty.kk`: printed the inline annotation into the def header (`pub inlinefun`, does
  not parse); had no `ppSyntaxDefUserType`/`ppFunDef` annotated clause so the **entire result
  type was dropped**; printed `TpApp(con,[])` as `shape()`; lost the fip annotation from
  `defSortShowFull`; and did not implement `prettyComment`'s trailing-newline strip, leaving a
  blank line between a doc comment and its definition. All fixed.
- `syntax/range-map.kk` `drop-to-lex-matching`: missing upstream's `isEndLex l` guard, so the
  scan stopped after the first token instead of finding the matching delimiter. Signature help
  inside an argument list found no function. Fixed.
- `syntax/range-map.kk` `previous-lexemes-reversed`: `<` where upstream has `<=`, dropping the
  lexeme at the query position -- every dot-call read as a bare identifier. Fixed.
- `syntax/range-map.kk` `get-function-name-reverse`: `Cons(v as LexId)` matched any tail where
  upstream matches a SINGLETON list, shadowing the `x.partial` rule. Fixed.
- `std/data/json.kk` (koka-community/std, separate repo): escaped only `"\ \n \r \t`; RFC 8259
  requires every char below 0x20 escaped. Any raw control char produced invalid JSON. Fixed.

### Known-remaining (non-feature)

- Warm `koka/compile` ~2.1s vs 0.71s for a fully warm CLI build; interface loading and discovery
  are now 0ms, so the gap is entry codegen + the C link. Uninvestigated.
- LSP requests are not answerable during a compile (the compile owns the work strand).
- Diagnostics-only checks still run optimize + codegen. Skipping them would speed the edit loop
  but would remove the artifacts that make `koka/compile` warm -- a genuine trade, measure first.
- `termTrace` (upstream's verbose>1 channel) not ported; 4 of its 5 sites are HTML/C# output.
- Bottom-up beta rule still has no repro; per-splice alpha-renaming in `inl-lookup` still the
  preferred fix for the unique-counter collision.

## `@open import` fails to parse [FIXED 2026-08-27]

Minimal repro — a file whose first line is `@open import std/core`:

```
$ <port> -c f.kk
f.kk(1, 1): parse error: invalid syntax
 peof expected end of file
```

`pub import std/core` parses fine, and the REFERENCE compiler accepts `@open import`
(it proceeds past parsing to type checking). So this is a port bug, not invalid syntax.

Ruled out so far: the grammar rule is identical to upstream
(`@lowerid = [\@]? $lower @idchar* $finalid*`, koka.x:89 vs Lexer.x:86); the parser DOES
have the production (`parse-special-id("@open")` in `parse-import-declaration`,
syntax/parse.kk:188, mirroring upstream's `specialId "@open"`); `read-qualified-name`
looks equivalent to upstream's `readQualifiedName` for this input (no `?`, `/`, or `#`,
so it should yield a name whose `show-plain` is `"@open"`).

Prime suspect: rule precedence between `@qvarid` (alex action 6, `LexId(get-qname())`)
and `@lowerid` (action 8, `LexId(s.new-name)`) — the two build the name by DIFFERENT
functions in the port, so whichever alex picks determines whether `show-plain` round-trips
to `"@open"`. Worth dumping the token stream for `@open` first.

**ROOT CAUSE (none of the suspects above).** It was never the lexer or the import
grammar: it was `allowAt`. `Syntax/Layout.hs`'s `checkIds` rejects `@` in identifiers
unless `allowAt` is set, with a narrow exemption for an id directly following
`fun`/`val`/`extern` — which is exactly why `pub fun @expr()` parsed while
`@open import` did not, and why it worked as a SECOND import (by then the parser was
past the failing lexeme) and with a `module` header.

Upstream passes `allowAt = True` unconditionally when lexing a module
(`Compile/Build.hs:680`; the commented-out predecessor restricted it to primitive
modules and the synthetic `@main.kk`). The port passed `False` at all four
`parse-program-from-string` call sites in `compile/build.kk` and
`compile/build-context.kk`.

Fixed by introducing `pub val allow-at = True` in `compile/build.kk` (documented
against Build.hs:680) and using it at every module-lexing call site. `compile-expr`
now emits `@open import` as upstream does, so REPL expressions reach a module's
PRIVATE definitions:

```
> :l m.kk          # `fun secret()` is private
> :t secret()
   secret() : int
> secret()
99
```

Diagnosis note: `KOKA_PARSE_CONTEXT=1` is what cracked this — it surfaced the real
error (`"@": identifiers cannot contain '@' characters`) behind the generic
`peof expected end of file`.
