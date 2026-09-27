// Command-line entry point: upstream Main/Run.hs plus Main/plain/Main.hs.
//
// Everything that used to live here has moved to where upstream keeps it:
//   * per-module compilation  -> compile/build.kk        (Build.hs)
//   * the build entry surface -> compile/build-context.kk (BuildContext.hs)
//   * parallel orchestration  -> compile/orchestrate.kk   (PORT-SPECIFIC: upstream
//     uses green threads inside one process; see that file's header)
//
// The remaining KOKA_* debugging hooks are opt-in and inert unless set; see
// `docs/debug-hooks.md`. The default target is C/libc; `--target=` is the
// only way to change it.
module compiler/main/driver

import std/os/path
import std/os/file
import std/os/env
import std/os/process
import std/core/undiv
import std/async
import std/async/thread
import compiler/compile/phase
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/error
import compiler/common/color-scheme
import compiler/common/unique
import compiler/common/nice
import compiler/common/parse
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/assumption
import compiler/kind/pretty
import compiler/kind/synonyms
import compiler/kind/import-map
import compiler/kind/newtypes
import compiler/kind/unify
import compiler/syntax/range-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/assumption
import compiler/type/pretty
import compiler/syntax/syntax
import compiler/syntax/parse
import compiler/core/core
import compiler/core/pretty
import compiler/compile/module
import compiler/lib/log
import compiler/compile/options
import compiler/compile/type-check
import compiler/compile/optimize
import compiler/compile/code-gen
import compiler/compile/link
import std/os/dir
import compiler/common/file
import compiler/static/binding-groups
import compiler/lib/pprint
import std/data/rb-map
import compiler/common/name-collections
import compiler/compile/rpc
import compiler/compile/build
import compiler/compile/build-context
import compiler/compile/vfs
import compiler/interpreter/interpret
import compiler/lsp/server


// upstream `showVersion`/`showHelp` (Options.hs)
fun show-version(): _ ()
  with @default-comp-flags
  // Upstream's `versionMessage` shape. The `version: X.Y.Z` line is not
  // decoration: the VS Code extension parses exactly that with
  // /version: ([0-9]+\.[0-9]+\.[0-9]+)/ to decide which compiler it has, and
  // treats a miss as "no/old Koka installed" and offers to download one.
  println(comp-flags.programName ++ " " ++ comp-flags.version)
  println("")
  println("version: " ++ comp-flags.version)

fun show-help(): _ ()
  println(koka-flags/usage())

// compile each file in `files` under `fl`, with the same error/parse-error/
// div handling upstream installs around every compile
fun compile-files(fl: flags, files: list<string>): _ ()
  // `cwd <- getCwd`, threaded into the terminal's
  // error printer so a diagnostic under the working directory prints its
  // path relative to it.
  val cwd = cwd()
  // Exit nonzero when any file failed. Every failure path below PRINTS and
  // continues -- every file's errors are reported -- but the
  // process exit code must still reflect failure: build scripts and the
  // incremental cache logic were treating silently-failed compiles as
  // successes (exit 0 with nothing written).
  val results = files.map fn(fname)
    // upstream carries warnings alongside the error in its `Error` monad
    // (`Err err warnings`) and prints them at the very END of the compile --
    // AFTER errors, and after any program execution output (`-e`); buffer
    // them here and flush last rather than printing at raise time
    var warnings : warnings := []
    fun flush-warnings()
      warnings.foreach fn(e) println(e.err/show(cwd))
      warnings := []
    with handler
      final ctl parse-error(e: string, r: range)
        println(r.show-range(cwd, False) ++ ": parse error: " ++ e)
        flush-warnings()
        False
    with collapse-div
    // print messages via the upstream pretty format:
    // `<file>(<line>, <col>): <kind> <severity>: <message>` (e.g. "type warning:")
    with handler
      final ctl add-errors(errs: errors)
        errs.take(fl.maxErrors).foreach fn(e) println(e.err/show(cwd))
        flush-warnings()
        False
      fun add-warnings(warns: warnings)
        warnings := warnings ++ warns
      fun add-infos(infos: warnings)
        warnings := warnings ++ infos
    // parse errors are raised as exceptions carrying an already-formatted
    // message (syntax/parse.kk `show-parse-error`); print them plainly --
    // letting them escape would add the runtime's "uncaught exception: " prefix
    val ok = match try({check-file(fl, fname)})
      Error(exn) ->
        println(exn.message)
        False
      Ok(_) -> True
    flush-warnings()
    ok
  if results.any(fn(ok) !ok) then exit(1)

pub fun main()
  with val colors = ColorScheme()
  // Env-var-derived options come first (so explicit
  // CLI args can override them), then the actual argv; `process-initial-options`
  // additionally runs the environment
  // probe -- CC-toolchain detection, editor/package discovery, koka-dir
  // resolution -- on top of plain flag parsing.
  // no in-memory source overlay for a batch compile; the REPL layers one on
  // top of this with `with-vfs` (compiler/compile/vfs.kk)
  with no-vfs
  val opts = get-env-options() ++ get-args()
  match process-initial-options(flags-default, opts)
    // upstream `runWithLSArgs` prints the option error and exits with failure
    Left(err) -> { println(err); exit(1) }
    Right((fl, mode)) ->
      // upstream builds its `Terminal` with `termPhase` active only when
      // `verbose flags > 0`. The language server installs its own handler (it
      // logs to the client, not the console), so it opts out here.
      with with-console-phase(fl.verbose, fl.console == "ansi")
      // `--showtypesigs` / `--showcore` output goes straight to stdout for the
      // CLI; a library caller installs its own
      // handler to capture it per root instead.
      with with-console-emit
      match mode
        ModeHelp -> show-help()
        ModeVersion -> show-version()
        ModeCompiler(files) -> compile-files(fl, files)
        // ModeInteractive runs the REPL, loading any
        // files given on the command line first
        ModeInteractive(files) -> interpret(fl(evaluate = True), files)
        // upstream Main/langserver: JSON-RPC over stdio
        ModeLanguageServer(_files) -> server/run(fl)
