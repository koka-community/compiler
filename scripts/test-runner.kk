// Parallel test runner, in Koka.
//
// Runs the port against the test corpus in `test/`: for every `<t>.kk` that has a
// sibling `<t>.kk.out`, invoke the port, sanitize its stdout the same way the
// expected output was sanitized, and compare.
//
// The point of writing this in Koka rather than extending the Python harness
// is that the runner is itself a realistic parallel workload for the port --
// dozens of independent, IO-and-CPU-heavy jobs with no shared state. It also
// removes a Python dependency from the test path.
//
// Usage (with the reference compiler wrapper):
//   ./koka -O2 -e --include=. scripts/test-runner.kk
//   KOKA_TEST_JOBS=1 ./koka -O2 -e --include=. scripts/test-runner.kk   # serial
//
// `KOKA_TEST_JOBS` bounds concurrency (default 8). Setting it to 1 gives the
// serial baseline, so the runner can measure its own speedup.
module test-runner

import std/os/path
import std/os/dir
import std/os/file
import std/os/env
import std/core/unsafe
import std/os/process
import std/text/regex
import std/async
import std/async/thread
import std/data/sort
import std/core/undiv
import compiler/common/file
import compiler/common/range
import compiler/common/error
import compiler/common/parse
import compiler/common/color-scheme
import compiler/platform/config
import compiler/compile/options
import compiler/compile/vfs
import compiler/compile/build-context
import compiler/compile/orchestrate
import compiler/lib/log

// The corpus and the repository it lives in. `KOKA_TEST_ROOT` overrides the
// repository root for a checkout somewhere else; the corpus is always `test/`
// under it, and the fixtures' paths are relative to it (see `sanitize`).
// Read per call, NOT cached in a top-level `val`: a top-level value that reads
// the environment runs its initialiser during module init, on whichever thread
// touches it first, and the workers here are threads (a segfault, seen once as
// exit 139 with no output). An effect val cannot serve either -- a worker must
// never reach for evidence installed on the spawning thread.
fun test-root(): io path
  get-env-value("KOKA_TEST_ROOT").default(cwd().string).path

fun corpus-test(): io path
  test-root() / "test".path

pub struct outcome
  file   : string
  status : string   // PASS | SKIP | MISMATCH | COMPILEFAIL | TIMEOUT
  detail : string

// ---------------------------------------------------------------------------
// sanitize -- the normalisation the upstream corpus's fixtures assume
// (ported from the Python harness this file replaced, rule for rule)
// ---------------------------------------------------------------------------

// Applied in the SAME order as the Python harness (which reverses its list
// before applying); a different order changes results, e.g. `[ \t]+ -> " "`
// must run after the multi-line elisions.
val sanitize-steps: list<(string, string)> = [
  // These five were MISSING and are applied FIRST. `\.` -> `@` in particular
  // is why a fixture reads `hm1@kk` and `stack@yaml`: without it essentially
  // every test whose output names a file or a qualified name fails to match.
  ("(console|hnd|sslice|string|list)/", ""),
  ("\\.", "@"),
  ("@hnd-", ""),
  ("(^[a-zA-Z0-9]+/.+:.*) [a-zA-Z]+\\d+@\\d+ :", "$1 a00.000 :"),
  ("(@m?)lift-[a-zA-Z0-9@-]+", "$1lift-xxx"),
  ("@unroll-[a-zA-Z0-9@-]+", "@unroll-xxx"),
  ("([a-zA-Z][a-zA-Z]+)\\d\\d\\d+", "$1xxx"),
  ("<\\d+>", "<0>"),
  ("([a-zA-Z])\\.\\d+\\.\\d+", "$1@xxx"),
  ("([a-zA-Z])@[\\d@]+", "$1@xxx"),
  ("(@[a-zA-Z])\\d+", "$1xxx"),
  ("@box-x\\d+(-x\\d+)?", "@box-xxx"),
  ("\\\\", "/"),
  ("[ \t]+", " "),
  ("[\r\n]+", "\n"),
  ("(std_core\\.js:)\\d+", "$1"),
  ("\n[ \t]+at .*", ""),
  ("^Up to date\n", ""),
  ("^[ \t]*search path:.*(\n [^\n]*)*", "search path: <elided>"),
  ("^compile *:.*kklib.*\n", ""),
]

// ---------------------------------------------------------------------------
// `_renumber_meta_ids` -- the Python harness's final, STATEFUL pass
// ---------------------------------------------------------------------------
//
// Not a regex rule: an ORDER-PRESERVING map from each token's first appearance
// to a sequential id, applied to actual and expected alike. Two independent
// maps, exactly as the Python harness has them.
//
// It exists because ids are unique-counter sensitive. `_<digits>` are meta
// type-variable ids and `-x<digits>` uniquified hidden locals (`@ru-x155`);
// renumbering by first appearance keeps DISTINCT ids distinct (a blanket
// `_\d+ -> _N` would conflate them) while ignoring the counter's absolute
// values. Bare digits elsewhere are deliberately NOT touched -- that would mask
// real divergences like an off-by-one source column.
//
// The `fn(...)` header case is a printer divergence, not a port bug: upstream's
// Box pass erases TypeLam binders, so a param type referencing the def's forall
// var has no binder and upstream prints its RAW id (`fn(x: 14)`), where the
// port's ambient nice-env still holds the assignment and prints the letter
// (`fn(x: a)`). Normalizing both through one map makes `fn(x: 16, y: 17)`
// equivalent to `fn(x: a, y: b)` but still distinguishes `fn(x: a, y: a)`.
fun renumber-meta-ids(s0: string): _ string
  var seen : list<(string, string)> := []
  fun map-tok(pfx: string, tok: string): _ string
    match seen.lookup(fn(k) k == tok)
      Just(v) -> v
      Nothing ->
        val v = pfx ++ (seen.length + 1).show
        seen := seen ++ [(tok, v)]
        v
  val s1 = s0.replace-all(regex(r"_\d+\b|-x\d+\b")) fn(caps)
    val tok = caps.list/maybe/head.map(sslice/string).default("")
    map-tok(if tok.starts-with("-x").bool then "-xid" else "_id", tok)
  // second map, independent of the first
  var tseen : list<(string, string)> := []
  fun map-tv(tok: string): _ string
    match tseen.lookup(fn(k) k == tok)
      Just(v) -> v
      Nothing ->
        val v = "t" ++ (tseen.length + 1).show
        tseen := tseen ++ [(tok, v)]
        v
  // bare param types inside `fn(...)` headers
  val s2 = s1.replace-all(regex(r"\bfn\([^)]*\)")) fn(caps)
    val hdr = caps.list/maybe/head.map(sslice/string).default("")
    hdr.replace-all(regex(r"(: )([a-z]\d*|\d+)\b")) fn(cs)
      val pre = cs.drop(1).list/maybe/head.map(sslice/string).default("")
      val tok = cs.drop(2).list/maybe/head.map(sslice/string).default("")
      pre ++ map-tv(tok)
  // raw binderless type-var ids in type position: `(z: 56)`, `? 128`
  val s3 = s2.replace-all(regex(r"(: |\? )(\d+)(?=[,)>\]])")) fn(cs)
    val pre = cs.drop(1).list/maybe/head.map(sslice/string).default("")
    val tok = cs.drop(2).list/maybe/head.map(sslice/string).default("")
    pre ++ map-tv(tok)
  // all-digit angle lists: `pair2<37,38>`
  s3.replace-all(regex(r"<(\d+(?:,\d+)+)>")) fn(cs)
    val body = cs.drop(1).list/maybe/head.map(sslice/string).default("")
    "<" ++ body.split(",").map(map-tv).join(",") ++ ">"

fun sanitize(s0: string): <io|_e> string
  // TRAILING SLASH is load-bearing: an absolute test path has to collapse to
  // `test/type/wrong/hm1.kk`, which is what the fixtures contain. Without it
  // every path-bearing diagnostic keeps a leading `/` and fails to match its
  // fixture -- which is most of the suite.
  // TWO substitutions with different jobs, in this order: a CORPUS path
  // collapses to `test/type/wrong/hm1.kk` (what the fixtures contain), and any
  // OTHER path into this repository -- the working directory a test prints --
  // becomes `...`, which a later step turns into `@@@` (see `cgen/open-resolve`).
  val root = test-root().string
  val s1 = s0.replace-all(root ++ "/test/", "test/")
             .replace-all(root, "...")
  val s2 = sanitize-steps.foldl(s1) fn(acc, step)
    val (pat, repl) = step
    // `$1` in a replacement refers to the first capture group
    fun expand(caps: list<sslice>): _ string
      match caps
        Cons(_, Cons(g1, _)) -> repl.replace-all("$1", g1.string)
        _ -> repl
    acc.replace-all(regex(pat, multiline = True), expand)
  s2.renumber-meta-ids.trim

// ---------------------------------------------------------------------------
// discovery and per-directory config (upstream Spec.hs `extendCfg`)
// ---------------------------------------------------------------------------

fun discover(dir: path): io list<path>
  val entries = dir.dir/list-directory.sort(fn(a, b) a.string < b.string)
  entries.flatmap fn(p)
    if p.dir/is-directory then discover(p.pretend-decreasing)
    elif p.extname == "kk" && (p.string ++ ".out").path.dir/is-file then [p]
    else []

// `<dir>/config.json` cascades from parent directories, flags concatenated
// parent-first (upstream Spec.hs `extendCfg`). The file is either a bare JSON
// string of flags, or an object with a "flags" key -- e.g. test/algeff holds
// `"--showtypesigs -e"`, which is what makes those tests RUN rather than just
// compile. A test may also carry its own `<test>.kk.flags`.
fun dir-flags(dir: path): io list<string>
  val cfg = (dir / "config.json".path)
  val mine = if cfg.dir/is-file then parse-config-flags(cfg.file/read-text-file) else []
  val parent = dir.dirname.path
  if parent.string == dir.string || !dir.string.starts-with(corpus-test().string).bool
    then mine
    else dir-flags(parent.pretend-decreasing) ++ mine

// A `config.json` may also carry an "exclude" list -- tests upstream does not
// run at all. Without this they are run anyway and their output counted as a
// failure (the Python harness reports 17 SKIP; this reported none).
fun dir-excludes(dir: path): io list<string>
  val cfg = (dir / "config.json".path)
  val mine = if cfg.dir/is-file then parse-config-excludes(cfg.file/read-text-file) else []
  val parent = dir.dirname.path
  if parent.string == dir.string || !dir.string.starts-with(corpus-test().string).bool
    then mine
    else dir-excludes(parent.pretend-decreasing) ++ mine

fun parse-config-excludes(txt: string): _ list<string>
  // `"exclude": [ "a", "b" ]`. `find` yields the whole matched text (same
  // shape `parse-config-flags` relies on), so strip the syntax and keep the
  // strings.
  match txt.find(regex("\"exclude\"[ \t]*:[ \t]*\\[[^\\]]*\\]"))
    Nothing -> []
    Just(m) ->
      m.replace-all("exclude", " ").replace-all("\"", " ").replace-all(",", " ")
       .replace-all(":", " ").replace-all("[", " ").replace-all("]", " ")
       .split(" ").map(trim).filter(fn(x) !x.is-empty)

// upstream Spec.hs / the Python harness: a pattern containing regex
// metacharacters is matched as a regex, anything else compared literally
// (with or without the `.kk` extension).
fun is-excluded(base: string, pats: list<string>): _ bool
  pats.any fn(pat)
    if "()[]+*?".list.any(fn(c) pat.contains(c.string))
      then base.find(regex(pat)).is-just
      else base == pat || base == pat ++ ".kk"

// Minimal reader for the two shapes actually used: a bare quoted string, or an
// object with a "flags" string. Avoids pulling in a JSON parser for this.
fun parse-config-flags(txt0: string): _ list<string>
  val txt = txt0.trim
  val body = if txt.starts-with("{").bool
               then match txt.find(regex("\"flags\"[ \t]*:[ \t]*\"([^\"]*)\""))
                 Just(m) -> m
                 Nothing -> ""
               else txt
  body.replace-all("\"", " ").replace-all("flags", " ").replace-all(":", " ")
      .split(" ").map(trim).filter(fn(s) !s.is-empty && s != "{" && s != "}")

// ---------------------------------------------------------------------------
// pre-compiling shared dependencies (upstream Spec.hs: "pre-compiling
// standard libraries...")
// ---------------------------------------------------------------------------

// Every test shares ONE build directory (`--buildtag=ktest`), so std must be
// built exactly once -- and it must be built BEFORE any test runs in parallel.
//
// Two things go wrong without this. First, whichever test happens to need a
// std module first pays its whole cold cost: measured on this machine a cold
// `lib/time7` is ~25s serially and ~41s under 8-way contention, against ~8.6s
// warm. Second, several workers compiling the SAME std module concurrently
// into the SAME directory race on its `.c`/`.o`/`.kki` -- which is why the
// Python harness gave each worker its own buildtag, at the cost of rebuilding
// std once per worker.
//
// Pre-compiling serially removes both: tests never write std objects (they only
// read them), so a warm shared cache has nothing left to race on.
//
// It also makes DIAGNOSTICS match upstream. Warnings are emitted when a module
// is compiled, not when it is loaded from cache, so a cold run carries warnings
// upstream's (warm) fixtures never recorded -- `medium/allsamples` differs from
// its fixture for exactly this reason and matches once warm.
fun std-imports(tests: list<path>): io list<string>
  val names = tests.flatmap fn(kk)
    kk.file/read-text-file.lines.filter-map fn(l)
      val t = l.trim
      if t.starts-with("import ").bool then
        val rest = t.list.drop(7).string.trim
        val nm = rest.split(" ").head.default("").trim
        if nm.starts-with("std/").bool then Just(nm) else Nothing
      else Nothing
  names.foldl([]) fn(acc, n) if acc.any(fn(x) x == n) then acc else acc ++ [n]

// Compile one synthetic module importing everything the suite imports from
// std, serially, into the shared build directory.
fun precompile(bin: string, common: list<string>, tests: list<path>): io ()
  val mods = std-imports(tests)
  // inside `.koka/` so it is gitignored and lands next to the build it warms;
  // std has no file-delete, so it is simply overwritten each run
  val warm = (test-root() / ".koka".path / "warmup.kk".path)
  // `std/core` comes in regardless; the rest is whatever the suite reaches for
  val body = mods.map(fn(m) "import " ++ m).join("\n") ++ "\n\npub fun main() ()\n"
  warm.file/write-text-file(body)
  println("pre-compiling " ++ mods.length.show ++ " std modules...")
  val argv = [bin] ++ common ++ [warm.string]
  // std's own build warnings (e.g. rbtree-bu's fip notes) are not this
  // runner's business; a real failure still surfaces via the Error branch
  val cmd = argv.map(fn(a) if a.contains(" ") then "\"" ++ a ++ "\"" else a).join(" ") ++ " 2>/dev/null"
  match run-system-read(cmd)
    Ok(_)    -> println("ok.")
    // a std module that will not compile here is not fatal: the tests that
    // need it will report it themselves, with a real diagnostic
    Error(e) -> println("warning: pre-compile incomplete: " ++ e.message)

// ---------------------------------------------------------------------------
// running a GROUP of tests as one build (the compiler as a library)
// ---------------------------------------------------------------------------

// Every test in a group shares one flag set, so one build can serve all of
// them. They also share a dependency closure -- std, and any sibling helpers --
// which is then discovered and loaded ONCE for the group rather than once per
// test. Measured per test on a warm cache: `discover` 400ms + `load-modules`
// 993ms, against 4ms of actual type-checking. That redundancy is what this
// removes; only genuinely INCOMPATIBLE configs need their own build.
//
// `evaluate = False`: the compiler must not run the programs itself. Under `-e`
// it runs the executable inside code-gen and prints to a shared stdout, which
// is exactly what makes a test's output unattributable in a shared build. The
// runner runs each root's executable itself instead, capturing that test's
// stdout on its own.
// effect INFERRED: the row duplicates `exn` (mentioned both explicitly and
// through an open tail, the same way the driver documents for `colors`/`div`),
// so writing it out by hand means writing a doubled label
fun build-group(fl: flags, files: list<path>, sess: session): _ (session, list<root-result>)
  // `comp-flags` has a default handler, but it is not auto-applied inside an
  // explicitly annotated row -- install it as the driver does
  with @default-comp-flags
  with val colors = ColorScheme()
  with no-vfs
  // quiet: the runner reports, not the compiler
  with with-console-phase(0, False)
  // the OUTER emitter. Each root captures its own output through
  // `isolate-diagnostics`; anything reaching here belongs to no single root.
  with with-console-emit
  // the abort value carries the INCOMING session back out: losing it here would
  // silently undo the sharing below
  with handler
    final ctl parse-error(_e: string, _r: range) (sess, [])
  with collapse-div
  with handler
    final ctl add-errors(_errs: errors) (sess, [])
    fun add-warnings(_w: warnings) ()
    fun add-infos(_w: warnings) ()
  build-roots-isolated(fl(evaluate = False), files.map(fn(p) p.string), sess)

// Compose one root's result the way the CLI would have printed it:
//
//   errors -> PROGRAM OUTPUT -> emitted -> warnings
//
// `compileShowInfo` runs AFTER `code-gen`, and `code-gen` is what runs the
// program under `-e`, so the signature listing follows the program's output.
// Pinned by `algeff/cps1.kk.out`: `[1,3]`, then the listing.
//
// Concatenated with NO separator between the program's output and what follows:
// `cgen/rec4`'s main is `print`, not `println`, and its fixture reads
// `1test/cgen/rec4@kk(2,13): type warning: ...`.
fun compose(r: root-result, wants-run: bool): io string
  val prog = if !wants-run then "" else
    match r.exe
      Just(e) -> match run-system-read(e.string ++ " 2>/dev/null")
        Ok(o)    -> o
        Error(_) -> ""
      Nothing -> ""
  fun lines(xs: list<string>): string
    xs.map(fn(x) x ++ "\n").join
  lines(r.messages) ++ prog ++ lines(r.emitted) ++ lines(r.warns)

// ---------------------------------------------------------------------------
// running one test
// ---------------------------------------------------------------------------

// `compute` demands `ioc`, which excludes `exn` -- and containing failures per
// test is right regardless: one unreadable file should not abort the run.
fun run-one(bin: string, common: list<string>, kk: path): ioc outcome
  match try({ run-one-raw(bin, common, kk) })
    Ok(o)    -> o
    Error(e) -> Outcome(kk.string, "ERROR", e.message)

fun run-one-raw(bin: string, common: list<string>, kk: path): <exn,ioc> outcome
  if is-excluded(kk.basename, dir-excludes(kk.dirname.path)) then
    return Outcome(kk.string, "SKIP", "")
  val flagsFile = (kk.string ++ ".flags").path
  val caseFlags = if flagsFile.dir/is-file
                    then flagsFile.file/read-text-file.replace-all("\"", " ").split(" ").map(trim).filter(fn(s) !s.is-empty)
                    else []
  val argv = [bin] ++ common ++ dir-flags(kk.dirname.path) ++ caseFlags ++ [kk.string]
  // stdout ONLY: stderr (e.g. `trace()`) is discarded, which is what the
  // fixtures were recorded against. Without the redirect a test program's
  // stderr interleaves into the RUNNER's own output.
  val cmd = argv.map(fn(a) if a.contains(" ") then "\"" ++ a ++ "\"" else a).join(" ") ++ " 2>/dev/null"
  match run-system-read(cmd)
    Error(e) -> Outcome(kk.string, "ERROR", e.message)
    Ok(out) ->
      val actual = sanitize(out)
      val expected = sanitize((kk.string ++ ".out").path.file/read-text-file)
      if actual == expected then Outcome(kk.string, "PASS", "")
      else
        val low = out.to-lower
        val kind = if low.contains("parse error") || low.contains("type error") || low.contains("cannot be found")
                     then "COMPILEFAIL" else "MISMATCH"
        Outcome(kk.string, kind, failure-detail(actual, expected))

// ---------------------------------------------------------------------------

extern import
  c include-inline "#include <time.h>"

// WALL time. `clock()` measures process CPU, which under threads reported
// 0.58s for a 313s run -- useless for measuring the runner's own speedup.
extern wall-ms(): ndet int
  c inline "kk_integer_from_int((kk_intx_t)(kk_timer_ticks(kk_context()).seconds*1000 + kk_timer_ticks(kk_context()).attoseconds/1000000000000000LL), kk_context())"

// Which harness shape to run.
//
//   subprocess (default) -- one `koka -c` process per test, workers in
//     parallel. This is what the Python harness did, and it is both
//     the faster and the more faithful of the two: a test gets a pristine
//     compiler process, so nothing leaks between tests.
//   inprocess -- drive the compiler as a LIBRARY, one build per flag group.
//     Shares discovery and interface loading across a group, but currently
//     disagrees with the subprocess path on many tests.
fun subprocess-mode(): ndet bool
  match get-env-value("KOKA_TEST_MODE")
    Just(m) -> m != "inprocess"
    Nothing -> True

// KOKA_TEST_DIFF=1 records the FULL sanitized expected and actual for every
// failure instead of a 300-char excerpt, and prints all of it. This is what
// the Python harness's separate diff/classify passes did --
// re-running the failures to capture their diffs -- except nothing has to be
// re-run, because the comparison already had both strings in hand.
// A worker's build directory is PERSISTENT across runs, which is what makes
// the sweep fast -- but a `.o` left by an OLDER compiler can still link, and
// then reports a MISMATCH that does not reproduce in a fresh buildtag. It is a
// false failure, and it lands on a different innocent test each run (seen on
// `cgen/specbox`, then `cgen/mpat`).
//
// So: drop a worker directory only when the COMPILER IS NEWER THAN IT. That is
// exactly the stale condition, it keeps the cache across ordinary re-runs, and
// it is now nearly free to check -- `file-mtime` is a `stat(2)` rather than a
// forked shell.
fun refresh-worker-dirs(bin: string, n: int): io ()
  val bin-t = bin.path.file/file-mtime
  val kdir = (test-root() / ".koka".path)
  if !kdir.dir/is-directory then () else
    val stale = kdir.dir/list-directory.filter fn(d)
      val nm = d.path/basename
      nm.contains("-test-w") && d.file/file-mtime < bin-t
    if stale.is-nil then () else
      println("dropping " ++ stale.length.show ++ " stale worker dir(s) (compiler is newer)")
      // no recursive-delete primitive in std; one spawn per stale dir, once per
      // run, is not the per-module shell-out that mattered
      stale.foreach fn(d)
        run-system-read("rm -rf '" ++ d.string ++ "'").ignore

fun diff-mode(): ndet bool
  get-env-value("KOKA_TEST_DIFF").is-just

// The detail stored on a failing outcome: an excerpt normally, both full texts
// under KOKA_TEST_DIFF.
fun failure-detail(actual: string, expected: string): ndet string
  if !diff-mode() then actual.first(300).string
  else "--- expected ---\n" ++ expected ++ "\n--- actual ---\n" ++ actual

fun share-mods(): ndet bool
  get-env-value("KOKA_TEST_SHARE_MODS").is-just

fun jobs(): io int
  match get-env-value("KOKA_TEST_JOBS")
    Just(s) -> s.parse-int.default(8)
    Nothing -> 8

// Deal the tests ROUND-ROBIN across `n` workers, one strand per worker, each
// running its share sequentially.
//
// Two things are being traded off. Taking `n` at a time and `interleaved`-ing
// each batch puts a barrier after every batch, so each batch waits on its
// slowest member -- measured 313s wall for 793s CPU (2.5x) on a machine that
// sustains ~6.7x. So: one barrier at the end, not one per batch.
//
// But CONTIGUOUS blocks then imbalance badly, because `discover` walks the tree
// in sorted order and cost per directory is wildly uneven: whichever block got
// `lib/time*` dominated the run (7 of 8 strands finished long before the last,
// and the whole run came in at 477s against the Python harness's 216s).
// Dealing round-robin spreads every directory across all workers, keeping the
// single-barrier structure. A shared work queue would balance better still, but
// needs cross-thread mutable state -- the exact shape that has produced
// use-after-free crashes here before.
fun chunks(n: int, xs: list<a>): div list<list<a>>
  val indexed = xs.map-indexed(fn(i, x) (i, x))
  list(0, n - 1).map fn(w)
    indexed.filter(fn((i, _)) i % n == w).map(snd)

// The flags that decide whether two groups can share a warmed dependency
// closure: the target and the optimization level. `build-out-dir` already keys
// the output directory by those (via `build-variant`), so two groups differing
// only elsewhere read and write exactly the same std artifacts.
// The target a group compiles for. `deps` (the import graph) is scanned against
// `fl.tpl`, so conditional imports differ per target and a `deps` cache may only
// be reused among groups sharing one.
fun target-key(key: list<string>): list<string>
  key.filter(fn(f) f.starts-with("--target=").bool)

fun variant-key(key: list<string>): list<string>
  key.filter fn(f)
    f.starts-with("--target=").bool || (f.starts-with("-O").bool && f != "-O")

// One group, with its own failure contained: a group that dies must cost only
// its own tests, not the whole run.
//
// TWO `try`s, not one. `run-group`'s row carries `exn` TWICE -- once explicitly
// and once through the open tail, the same doubling `build-group` documents for
// `colors`/`div` -- and each `try` discharges one label. With a single `try` the
// row still shows `exn` and will not fit the closed `<async,ioc>` a spawned
// worker runs under.
fun safe-group(common: list<string>, key: list<string>, files: list<path>, sess: session): <async,ioc> (session, list<outcome>)
  fun failed(e: exception): (session, list<outcome>)
    // a group that threw contributes no new modules: hand the INCOMING session
    // on, so one bad group does not reset the sharing for the rest of the chunk
    (sess, files.map(fn(kk) Outcome(kk.string, "ERROR", e.message)))
  fun once(): <exn,async,ioc> (session, list<outcome>)
    match try({ run-group(common, key, files, sess) })
      Ok(rs)   -> rs
      Error(e) -> failed(e)
  match try(once)
    Ok(rs)   -> rs
    Error(e) -> failed(e)

// Split a flag group's files so one big group cannot pin the whole run.
//
// A group is ONE build over many roots, and `test/algeff` alone holds 61 tests
// (~103s). With parallelism at group granularity the largest group is a hard
// floor on wall time no matter how many workers there are -- 17 lumpy units
// against the subprocess path's 442 even ones, which is why in-process
// achieved ~1.75x of 8 where subprocess achieved ~7.9x.
//
// Sub-batches of one group share its flags by construction, so they are
// exactly the "compatible configs" that may share a build directory. What is
// lost is only that discovery is redone per sub-batch rather than once per
// group -- and after the session fix that is cheap.
fun split-group(target: int, key: list<string>, files: list<path>): div list<(list<string>, list<path>)>
  if files.length <= target then [(key, files)]
  else
    val (head-files, rest) = files.split(target)
    Cons((key, head-files), split-group(target, key, rest.pretend-decreasing))

// Run a chunk's groups in order, THREADING THE SESSION through them.
//
// This is where the sharing actually happens. `build-roots-isolated` takes a
// session and returns the updated one; discarding it (the `.snd` this used to
// do) made every group re-discover the whole std closure from scratch --
// measured on `test/type`: discover 32.7s of a 48.3s run, against 0.24s of
// typechecking. The session is threaded PER CHUNK rather than shared across
// all of them: one session mutated from several threads is exactly the
// cross-thread hazard this project has crashed on before.
fun run-chunk(common: list<string>, chunk: list<(list<string>, list<path>)>): <async,ioc> list<outcome>
  fun step(acc: (session, list<outcome>), g: (list<string>, list<path>)): <async,ioc> (session, list<outcome>)
    val (sess, outs) = acc
    val (key, files) = g
    // Carry `deps` ACROSS groups, never `mods`.
    //
    // `deps` is the import GRAPH -- module -> (source, declared name, imports).
    // What imports what does not depend on the flags a module is compiled
    // with, so it is safe to reuse, and it is where the win is: rebuilding it
    // per group cost 32.7s of a 48.3s run on `test/type` (78x).
    //
    // `mods` is compiled INTERFACES, which very much do depend on their flags.
    // Sharing those across flag sets silently miscompiled two tests
    // (`optc/cctx-context-path`, `lazy/indirect-compress`) -- each passes
    // alone, and failed only when another group's modules were in the session.
    // Dropping `mods` per group costs little: `load-modules` gained only 1.9x
    // from sharing, against discover's 78x.
    //
    // `deps` IS target-dependent though -- conditional imports resolve against
    // `fl.tpl` -- so it only carries while the target is unchanged (this repo
    // has already had one bug from scanning with the wrong target).
    // KOKA_TEST_SHARE_MODS=1 carries `mods` too. It is OFF by default because
    // doing so miscompiles `optc/cctx-context-path` and
    // `lazy/indirect-compress` (each passes alone, both fail when another
    // group's modules are in the session) -- and those two share the same
    // compilation-affecting flag variant, so flag-keying alone does not
    // explain it. The knob exists to reproduce that under control, because
    // sharing compiled modules per flag-variant is exactly what the
    // persistent-orchestrator design depends on.
    val carried = if share-mods() then sess else Session(deps = sess.deps)
    val (sess', more) = safe-group(common, key, files, carried)
    (sess', outs ++ more)
  // groups are bucketed by target before chunking, so every group in a chunk
  // scans against the same `fl.tpl` and one `deps` cache is valid for all of them
  chunk.foldl((Session(), []), step).snd

// Groups run on REAL WORKER THREADS. Safe only because `precompile` has already
// emitted the shared closure -- see the note at the call site.
//
// `spawn-thread`, not `compute` and not `interleaved`. A group needs `async`
// itself, because `build-roots-isolated`'s orchestrator awaits on channels:
// `compute` fixes its body to `ioc`, which has neither `async` nor `exn`, so a
// group cannot run there at all. `interleaved` types fine but buys nothing --
// groups only overlap at the orchestrator's own await points, which its worker
// threads already occupy (measured: 767s serial vs 755s interleaved, 1.6%).
// `spawn-thread` gives each worker its OWN async loop, so a group is a real
// async context on a real thread.
//
// Groups are dealt ROUND-ROBIN into `jobs()` chunks rather than one thread per
// group: it bounds the thread count (each group's orchestrator spawns workers
// of its own) and spreads the uneven per-directory cost, the same trade
// `chunks` was written for.
//
// The worker is DETACHED -- process exit does not wait for it -- so the main
// loop must receive one message per chunk before returning, which is also how
// the results get back.
fun run-groups(common: list<string>, groups: list<(list<string>, list<path>)>): <async,ioc|_e> list<outcome>
  // Bucket by target FIRST, then chunk within each bucket, so a chunk's groups
  // all scan against the same `fl.tpl` and the `deps` cache threaded through
  // them stays valid.
  val targets = groups.foldl([]) fn(acc: list<list<string>>, (key, _))
    val t = target-key(key)
    if acc.any(fn(a) a == t) then acc else acc ++ [t]
  // Split first, THEN chunk: aim for a few sub-batches per worker so the
  // longest one cannot dominate. Sub-batches keep their group's flags, so a
  // chunk still only ever holds compatible work.
  val total = groups.foldl(0, fn(acc, (_, fs)) acc + fs.length)
  val batch = max(4, total / max(1, jobs() * 3))
  val split = groups.flatmap(fn((key, fs)) split-group(batch, key, fs))
  val n = max(1, min(jobs(), split.length) / max(1, targets.length))
  val cs = targets.flatmap fn(t)
    chunks(n, split.filter(fn((key, _)) target-key(key) == t))
  .filter(fn(c) !c.is-nil)
  if cs.is-nil then []
  else
    val done : xchannel<list<outcome>> = xchannel()
    val snd = done.sender
    cs.foreach fn(chunk)
      spawn-thread fn()
        // explicit row for the same reason as orchestrate.kk's `work-loop`:
        // `spawn-thread` fixes its body CLOSED, so inference has to be forced
        // rather than left to unify with the enclosing (open) row
        fun body(): <async,ioc> ()
          snd.xemit(run-chunk(common, chunk))
        body()
    val rs = cs.map(fn(_) done.xreceive)
    // An xchannel is a live uv handle: leave it open and the main loop never
    // drains, so `main` never returns and the process hangs with every result
    // already in hand. (Reproduced with a SINGLE group, where no thread is even
    // spawned -- the open channel alone was enough.)
    done.close
    rs.concat

// Separate function for the same reason as the driver's `dispatch-wave`:
// `compute` fixes each thunk's row to a CLOSED `<async,ioc>` and `interleaved`
// unifies the enclosing row with it, which would pin `main` closed and leave no
// room for the `div`/`exn`/`fsys` its own work needs.
// Each chunk gets its OWN buildtag (`test-w0`, `test-w1`, ...), matching the
// Python harness this replaces. Worker PROCESSES writing .c/.o/.kki for the
// same shared std module into ONE buildtag directory race; a per-worker tag
// keeps within-worker runs safe (only one process ever writes to it) while
// preserving cross-worker parallelism.
//
// `spawn-thread`, NOT `compute`. `compute` dispatches onto libuv's threadpool,
// which defaults to FOUR threads no matter how many chunks are handed to it --
// so with 8 chunks only half ever ran, and the sweep took 249s against the
// Python harness's 129s. Setting UV_THREADPOOL_SIZE=16 brought it to 127.5s,
// confirming the cap was the whole difference. `spawn-thread` gives each
// worker a real OS thread and its own async loop, so the worker count is what
// we asked for rather than what libuv felt like providing.
fun run-chunks(bin: string, common: list<string>, cs: list<list<path>>): <async,ioc> list<list<outcome>>
  if cs.is-nil then []
  else
    val done : xchannel<list<outcome>> = xchannel()
    val snd = done.sender
    cs.map-indexed(fn(i, chunk) (i, chunk)).foreach fn((i, chunk))
      spawn-thread fn()
        // explicit row: `spawn-thread` fixes its body closed, so inference has
        // to be forced rather than unified with the enclosing open row
        fun body(): <async,ioc> ()
          // per-worker buildtag: concurrent processes must never write the
          // same std artifacts (see the note above)
          val tagged = common ++ ["--buildtag=test-w" ++ i.show]
          snd.xemit(chunk.map(fn(kk) run-one(bin, tagged, kk)))
        body()
    val rs = cs.map(fn(_) done.xreceive)
    // a live uv handle keeps the main loop from draining -- see run-groups
    done.close
    rs

// Every test's effective flags: the cascaded directory config plus its own
// `<test>.kk.flags`. Tests sharing this list can share a build; only genuinely
// incompatible configs need their own.
fun test-flags(kk: path): io list<string>
  val flagsFile = (kk.string ++ ".flags").path
  val caseFlags = if flagsFile.dir/is-file
                    then flagsFile.file/read-text-file.replace-all("\"", " ").split(" ").map(trim).filter(fn(s) !s.is-empty)
                    else []
  dir-flags(kk.dirname.path) ++ caseFlags

// Bucket the tests by flag set, preserving first-seen order so a run is
// reproducible.
fun group-by-flags(tests: list<path>): io list<(list<string>, list<path>)>
  tests.foldl([]) fn(acc: list<(list<string>, list<path>)>, kk)
    val key = test-flags(kk)
    if acc.any(fn((k, _)) k == key)
      then acc.map(fn((k, fs)) if k == key then (k, fs ++ [kk]) else (k, fs))
      else acc ++ [(key, [kk])]

// Compile one group and compare each of its tests.
fun run-group(common: list<string>, key: list<string>, files: list<path>, sess: session): _ (session, list<outcome>)
  // `process-initial-options` reads the compiler version (for the installed
  // share/lib layout), so this runner installs the same defaults the driver does
  with @default-comp-flags
  val skipped = files.filter(fn(kk) is-excluded(kk.basename, dir-excludes(kk.dirname.path)))
  val live = files.filter(fn(kk) !is-excluded(kk.basename, dir-excludes(kk.dirname.path)))
  val wants-run = key.any(fn(f) f == "-e")
  val (sess', results) = match process-initial-options(flags-default, common ++ key)
    Left(err) -> (sess, live.map(fn(kk) Outcome(kk.string, "ERROR", err)))
    Right((fl, _mode)) ->
      val (sessB, roots) = build-group(fl, live, sess)
      // Match results to tests BY SOURCE PATH, never by position: an
      // unparseable root is reported before any compiled one, so the result
      // order does not track `live`. Pairing positionally silently mismatched
      // every test after the first parse failure and dropped the tail.
      val outs = live.map fn(kk)
        match roots.find(fn(r) r.rsrc.string == kk.string)
          Nothing -> Outcome(kk.string, "ERROR", "no result returned for this root")
          Just(r) ->
            val actual = sanitize(compose(r, wants-run))
            val expected = sanitize((kk.string ++ ".out").path.file/read-text-file)
            if actual == expected then Outcome(kk.string, "PASS", "")
            else
              val low = actual.to-lower
              val kind = if low.contains("parse error") || low.contains("type error") || low.contains("cannot be found")
                           then "COMPILEFAIL" else "MISMATCH"
              Outcome(kk.string, kind, failure-detail(actual, expected))
      (sessB, outs)
  (sess', skipped.map(fn(kk) Outcome(kk.string, "SKIP", "")) ++ results)

pub fun main()
  val args = get-args()
  val bin = match args.find(fn(a) a.contains("driver"))
    Just(b) -> b
    Nothing -> newest-driver()
  // The TESTS' include path, not this script's. A test resolves its sibling
  // imports out of the upstream test tree, so that -- and only that -- is what
  // upstream's Spec.hs (`-itest`) and the Python harness both pass. Passing
  // this script's own build includes instead left sibling imports unresolvable.
  // NO --buildtag here: the subprocess path appends a per-worker one, and the
  // in-process path adds its own single shared tag below.
  // NO --no-buildhash: the build directory is keyed by the flags hash, so
  // groups differing only in OUTPUT flags (--showtypesigs and friends) share
  // one std build while -O2 groups correctly get their own. Disabling the hash
  // collapsed every variant into one directory -- which is how an -O1
  // interface came to be reused by the -O2 `cgen/specbox` tests.
  // -O1 is NOT an oversight and must not be "fixed" to -O2: upstream's
  // `test/Spec.hs` sets "-O1" as the suite default ("for cgen/specialize"),
  // with per-test `.kk.flags` files overriding it (`cgen/specbox.kk.flags` is
  // -O2, `cgen/mutualspec.kk.flags` is "-O1 --fno-trmc"). The sweep compares
  // against upstream's recorded `.kk.out`, so it has to run upstream's
  // configuration. The BENCHMARK scripts are a different matter -- those use
  // -O2, which is what the port ships.
  // `--sharedir` is not optional: the compiler under test may be a COPY outside
  // this repository (the sweep usually runs one), and it would then sniff an
  // install layout and find no standard library at all.
  val common0 = ["-c", "-v0", "--console=raw", "-O1",
                 "--sharedir=" ++ test-root().string,
                 "--target=c", "--include=" ++ corpus-test().string]
  val common = if subprocess-mode() then common0
               else common0 ++ ["--buildtag=ktest"]
  // A substring filter narrows a run to one directory or test, so a failing
  // group can be reproduced in seconds instead of re-running all 442.
  val filt = args.filter(fn(a) !a.contains("driver") && !a.starts-with("-").bool)
  val all = discover(corpus-test())
  val tests = if filt.is-nil then all
              else all.filter(fn(kk) filt.any(fn(f) kk.string.contains(f)))
  println("discovered " ++ tests.length.show ++ " tests; jobs=" ++ jobs().show ++ "; bin=" ++ bin)
  val t0 = wall-ms()
  // Drive the compiler as a LIBRARY, one build per flag set. Tests sharing a
  // config share the discovery and interface loading their dependency closure
  // needs, instead of each paying it in its own process.
  // grouping and precompiling are IN-PROCESS setup only: a subprocess run gives
  // each test its own compiler process, which shares nothing and so needs
  // neither. Precompiling in particular is several full std builds.
  val groups = if subprocess-mode() then [] else group-by-flags(tests)
  if subprocess-mode() then
    println("mode: subprocess (" ++ jobs().show ++ " workers)")
    refresh-worker-dirs(bin, jobs())
  else println("mode: in-process; grouped into " ++ groups.length.show ++ " flag sets")
  // Warm the SHARED dependency closure before any group runs.
  //
  // This is what makes running groups concurrently safe. Groups share one build
  // directory, and the hazard there was never the test modules -- those are
  // group-local -- it was std: whichever group reached a std module first
  // EMITTED it, renumbering symbols under every concurrent reader (measured: 7
  // tests pass serially, 5 fail run 7-at-once). Compiling std up front means no
  // group emits it, and the race has nothing left to race over.
  //
  // Once per VARIANT, not once per group: only the target and the optimization
  // level change what is emitted for the shared closure. The rest of a test's
  // flags (--showtypesigs, -e, -l, ...) change what is REPORTED. That is the
  // "only genuinely incompatible configs need their own build" line, made
  // concrete -- 3 or so precompiles instead of one per flag set.
  val variants = groups.foldl([]) fn(acc: list<list<string>>, (key, _))
    val v = variant-key(key)
    if acc.any(fn(a) a == v) then acc else acc ++ [v]
  if !subprocess-mode() then
    println("std closure variants: " ++ variants.length.show)
    variants.foreach(fn(v) precompile(bin, common ++ v, tests))
  // ONE FILE runs on the main thread before any fan-out -- not, as before, the
  // whole first group, which was `algeff` (61 tests, ~103s) purely because
  // `discover` sorts and it comes first alphabetically. That was ~103s of
  // serialization for a warm-up that needs a single compile.
  //
  // A warm-up is still needed: `precompile` shells out, so it warms the build
  // DIRECTORY but none of THIS process's lazy state, and concurrent
  // first-touch of that (the lexer tables above all) crashes.
  val results = if subprocess-mode()
                  then run-chunks(bin, common, chunks(max(1, min(jobs(), tests.length)), tests)
                                                .filter(fn(c) !c.is-nil)).concat
                elif jobs() <= 1
                  then run-chunk(common, groups)
                  else match groups
                    Nil -> []
                    Cons((k0, f0), rest) -> match f0
                      Nil -> run-groups(common, rest)
                      Cons(warm, more) ->
                        // one file on the main thread, then everything else fans out
                        safe-group(common, k0, [warm], Session()).snd ++
                          run-groups(common, Cons((k0, more), rest))
  val ms = wall-ms() - t0
  val counts = ["PASS", "SKIP", "MISMATCH", "COMPILEFAIL", "ERROR"].map fn(st)
    (st, results.filter(fn(r) r.status == st).length)
  println("")
  counts.foreach fn((st, n))
    if n > 0 then println(st.pad-right(12) ++ ": " ++ n.show)
  println("wall: " ++ (ms / 1000).show ++ "." ++ (ms % 1000).show.pad-left(3, '0') ++ "s")
  results.filter(fn(r) r.status != "PASS").foreach fn(r)
    println("  " ++ r.status ++ " " ++ r.file.replace-all(corpus-test().string ++ "/", ""))
    // the detail is what says WHY; without it a whole directory of ERRORs
    // looks identical to a whole directory of unrelated failures
    if r.detail.is-empty then () else
      val ls = r.detail.split("\n")
      (if diff-mode() then ls else ls.take(2)).foreach(fn(l) println("      | " ++ l))
  // a failing exit code, so CI can gate on the run
  if results.any(fn(r) r.status != "PASS" && r.status != "SKIP") then exit(1)

fun newest-driver(): io string
  val d = ".koka/v3.2.7".path
  val cands = d.dir/list-directory.filter(fn(p) p.stemname.starts-with("clang-").bool)
                .map(fn(p) p / "compiler_main_driver__main".path).filter(dir/is-file)
  // newest by MTIME -- sorting by name picks whichever hash sorts last, which
  // silently selected a stale binary
  match cands.map(fn(p) (p.file/file-mtime, p)).sort(fn((a, _), (b, _)) a > b).map(snd)
    Cons(p, _) -> p.string
    Nil -> throw("no port binary found under .koka/v3.2.7")
