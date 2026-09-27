// `workspace/executeCommand` -- the custom commands the VS Code extension calls.
//
// Ports upstream `LanguageServer/Handler/Commands.hs`. These are what make the
// extension's "run debug | optimized" code lenses work: the lens is produced
// CLIENT-side (a regex in `code-lens.ts`), and clicking it starts a debug
// session whose adapter (`debugger.ts`) asks the server to build an executable
// and hands back its path, which the adapter then runs.
//
//   koka/compile         [filePath, extraArgs]               -> exe path | null
//   koka/compileFunction [filePath, funName, extraArgs]      -> exe path | null
//   koka/set-colors      [{mode: "dark"|"light"}]            -> null
//
// The reply must be the executable path as a bare JSON string (the adapter does
// `path.join(cwd, resp)` and then `fs.existsSync`), or null to mean "compilation
// failed, look at the problems tab".
module compiler/lsp/commands

import std/os/path
import std/data/rb-map
import std/async
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/parse
import compiler/common/color-scheme
import compiler/common/file
import compiler/compile/options
import compiler/compile/build
import compiler/compile/build-context
import compiler/compile/vfs
import compiler/lib/json
import compiler/lib/log
import compiler/lsp/jsonrpc
import compiler/lsp/stdio
import compiler/lsp/conversions
import compiler/lsp/state
import compiler/lsp/diagnostics
import compiler/lsp/util

// The commands we advertise in `executeCommandProvider`. A client only sends
// what the server claims to support, so this list IS the feature switch.
pub val command-names: list<string> =
  ["koka/compile", "koka/compileFunction", "koka/set-colors",
   "koka/signature-help/set-context"]

// Build `filePath` as an EXECUTABLE with `entry` as its entry point and answer
// with the linked path. Distinct from the ordinary check in three ways, all of
// which follow from the client wanting something runnable:
//   - `library = False` and `evaluate = False`: link an entry point, but do not
//     run it here (the client's debug adapter runs it, so that it owns stdio)
//   - `mainEntryName = entry`: `koka/compileFunction` runs `test/...` functions,
//     not just `main`
//   - the entry module is INVALIDATED in the analysis session, and the rest of
//     that session is reused. Every import has already been type-checked (and
//     code-generated -- `library` only suppresses the ENTRY, not codegen) by the
//     checks that answer hover and diagnostics, so all that is left is the entry
//     module's own compile plus the link. Starting from an empty session instead
//     re-did the whole graph on every click of the run lens.
fun compile-entry(st: server-state, fpath: string, entry: string, extra: string): _ (server-state, json)
  val fl0 = st.flags
  // client-supplied flags (`-O2` from the "optimized" lens) layer onto the
  // flags this server started with
  val fl1 = match process-extra-options(fl0, extra)
    // `process-extra-options` re-derives from `baseFlags` -- the snapshot taken
    // by `process-initial-options`, BEFORE `server/run` appended its own
    // buildTag. Left alone it therefore loses that tag, and the entry build
    // lands in a different output directory from every module this session has
    // already compiled: nothing can be shared, the whole graph is rebuilt, and
    // the returned executable sits somewhere the analysis knows nothing about.
    // Re-apply the server's own output settings on top.
    Right((f, _mode)) -> f(buildTag = fl0.buildTag, buildDir = fl0.buildDir)
    Left(_err) -> fl0
  val entry' = if entry == "" then "main" else entry
  val p = fpath.path
  // Upstream compiles a SYNTHETIC expression module for `compileFunction`, so a
  // function entry naturally lands on its own executable. This port reuses the
  // file's own compile with a different entry name, which would make the `main`
  // and `test/...` lenses in one file overwrite each other's binary; give a
  // non-`main` entry its own output path instead.
  // No `mainEntryName`/`outFinalPath` juggling any more: the entry is compiled
  // as an EXPRESSION against a synthetic module, so each entry naturally gets
  // its own output rather than overwriting the file's own executable.
  val fl = fl1(evaluate = False)
  // a `ref`, not a `var`: `on-exe` is handed to the build, whose row has no
  // `local<h>` -- `read`/`write<global>` are already part of io (the same
  // reason `diagnostics-for` uses refs for its captures)
  val exe : ref<global,maybe<path>> = ref(Nothing)
  var msgs : errors := []
  // Upstream wraps the same command in `withProgress`. The build reports
  // (done, total, module) as it goes -- the same callback the REPL's `:l` uses
  // -- and each report becomes a `$/progress` notification. Writing from inside
  // the handler is safe: the work strand is the only writer (the reader strand
  // only ever reads), so nothing can interleave with these frames.
  val token = "koka/compile"
  // Only when the percentage actually MOVES. A build reports once per module,
  // which on the std lib is ~1000 notifications for one click of the run lens --
  // pure noise to the client, and enough traffic to fill the stdout pipe.
  // Just the counter: the phase handler is the single thing that WRITES a
  // progress report, so a module completing and a phase starting cannot
  // overwrite each other in the UI.
  val last-pct : ref<global,int> = ref(0)
  fun report(done: int, total: int, _nm: name): _ ()
    last-pct.set(if total <= 0 then 0 else (100 * done) / total)
  fun build-it(): _ ()
    with with-lsp-progress(fl0.verbose, token, last-pct)
    with no-vfs
    // the buffer, not the file on disk: the user hits "run" on what they see
    with with-vfs(st.overlay)
    with handler
      final ctl parse-error(e: string, r: range)
        msgs := msgs ++ [ErrorMsg(r, e.text, SevError, ErrGeneral)]
        ()
    with handler
      final ctl add-errors(errs: errors)
        msgs := msgs ++ errs
        ()
      fun add-warnings(w: errors) msgs := msgs ++ w
      fun add-infos(w: errors) msgs := msgs ++ w
    // Reuse the analysis session ONLY when the client's extra flags leave the
    // build output in the same place. `-O2` from the "optimized" lens changes
    // the build variant, so those cached modules were compiled for a DIFFERENT
    // directory and reusing them builds against the wrong artifacts.
    if timing-on() then println("CMD st.sess: " ++ st.sess.mods.list.length.show ++ " modules; outdir-same=" ++ (build-out-dir(fl).string == build-out-dir(fl0).string).show)
    val sess0 = if build-out-dir(fl).string == build-out-dir(fl0).string
                  then st.sess.session-invalidate(p) else Session()
    // Both commands go through COMPILE-EXPR: an entry point is the expression
    // `"<name>()"`. That needs the file's own module name to `@open import`, so
    // the file is checked first (cheap -- it reuses the session) and the name
    // captured; then the entry is compiled as an expression against it.
    // `module-name-of` is a lenient header parse, NOT a build: the file itself is
    // compiled as a dependency of the synthetic module anyway, so checking it
    // separately first just to learn its name doubled the work.
    // `add-show = False`: an entry point is run for its effects, not to print
    // its result.
    // The entry is QUALIFIED with the file's module: `@open import` also brings
    // in that module's own user imports, so a bare `main()` is ambiguous as soon
    // as the file imports another module with a `main` (samples/all).
    match try({ val root = module-name-of(fl, p)
                val qentry = if entry'.new-name.is-qualified then entry'.new-name else qualify(root, entry'.new-name)
                compile-expr(fl, sess0, qentry.show-plain ++ "()", [root], "",
                             add-show = False, on-progress = report) })
      Error(exn) ->
        msgs := msgs ++ [ErrorMsg(exn.message.error-position(p), exn.message.strip-location.text, SevError, ErrGeneral)]
      Ok(Expr-result(_s2, _tp, mbexe)) -> exe.set(mbexe)
  write-bytes(progress-create(token).frame)
  write-bytes(progress-begin(token, "Koka: compiling " ++ p.basename).frame)
  build-it()
  write-bytes(progress-end(token, if (!exe).is-just then "done" else "failed").frame)
  val items = msgs.map(to-diagnostic)
  // republish this file's diagnostics so a failed run points at the reason:
  // the reply is only "null", so without them a failed build shows nothing
  val uri = p.path-to-uri
  write-bytes(publish-diagnostics(uri, items).frame)
  val st2 = match st.find-doc(uri)
    Just(d) -> st.put-doc(d(diags = items))
    Nothing -> st
  match !exe
    Just(e) -> (st2, JSString(e.string))
    Nothing -> (st2, JSNull)

// Answer one `workspace/executeCommand`. Returns the (possibly updated) state
// and the result value; an unknown command is the caller's error to report.
pub fun execute-command(st: server-state, ps: json): _ maybe<(server-state, json)>
  val cmd = ps.field("command").as-string.default("")
  val args = match ps.field("arguments")
    Just(JSList(xs)) -> xs
    _ -> []
  fun arg(i: int): string
    args.drop(i).head.as-string.default("")
  match cmd
    "koka/compile" -> Just(st.compile-entry(arg(0), "main", arg(1)))
    "koka/compileFunction" -> Just(st.compile-entry(arg(0), arg(1), arg(2)))
    // the client tells us its theme so diagnostics can be coloured; this port
    // renders no colour codes into LSP messages, so accept and ignore
    "koka/set-colors" -> Just((st, JSNull))
    // Sent by the extension's `executeCommand` middleware right after a
    // completion is accepted, naming the overload it chose; it then asks the
    // editor to pop parameter hints. Remembering it is what makes the following
    // `textDocument/signatureHelp` show THAT overload rather than the first.
    "koka/signature-help/set-context" ->
      val fn-name = match args.head
        Just(JSObj(kvs)) -> kvs.lookup(fn(k) k == "functionName").as-string
        _ -> args.head.as-string
      Just((st(sig-context = fn-name), JSNull))
    _ -> Nothing
