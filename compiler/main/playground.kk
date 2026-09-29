// Entry point for the web playground's standalone compiler (upstream
// Main/playground/Main.hs), built as a WASI module with `--target=wasm`.
//
// The playground runs it as a WASI command: the argument list is the usual
// flags followed by the module name, the module's source arrives on stdin, and
// every other file (the standard library, precompiled interfaces) is in the
// WASI file system. The last line on stdout is the result as JSON,
// `{"success": true}` or `{"success": false, "errors": [..]}`; the build log goes
// to stderr so the playground can stream it.
//
// Upstream compiles the source from an in-memory module; this writes it to
// `/<module>.kk` instead, since the playground's file system is itself in memory
// and the build then needs no second way to find a source.
module compiler/main/playground

import std/os/path
import std/os/file
import std/os/dir
import std/os/env
import std/data/json
import compiler/common/error
import compiler/common/range
import compiler/common/parse
import compiler/common/color-scheme
import compiler/compile/options
import compiler/compile/build-context
import compiler/compile/vfs
import compiler/lib/log

extern import
  c file "playground-inline.c"

// the whole of stdin: the playground passes the module's source there
extern read-stdin(): io string
  c "kk_playground_read_stdin"

extern eprintln(s: string): console ()
  c "kk_playground_eprintln"

fun result-json(errs: list<string>): string
  val fields = if errs.is-nil then [("success", JSBool(True))]
               else [("success", JSBool(False)), ("errors", JSList(errs.map(JSString)))]
  JSObj(fields).show

fun compile-module(fl: flags, module-name: string, source: string): _ list<string>
  val src = ("/" ++ module-name ++ ".kk").path
  ensure-dir(src.dirname.path)
  write-text-file(src, source)
  with handler
    final ctl parse-error(e: string, r: range)
      [r.show-range("/".path, False) ++ ": parse error: " ++ e]
  with handler
    final ctl add-errors(es: errors)
      es.take(fl.maxErrors).map(fn(e) e.err/show("/".path))
    fun add-warnings(_ws: warnings) ()
    fun add-infos(_is: warnings) ()
  match try({ check-file(fl, src.string) })
    Error(exn) -> [exn.message]
    Ok(_) -> []

pub fun main()
  with val colors = ColorScheme()
  with no-vfs
  match process-initial-options(flags-default, get-args())
    Left(err) -> println(result-json([err]))
    Right((fl, mode)) ->
      val module-name = match mode
        ModeCompiler(Cons(m, _)) -> m
        _ -> "main"
      val source = read-stdin()
      // the build log and any emitted listing go to stderr, keeping stdout for
      // the JSON result
      val errs =
        with fun log-phase(level, p, msg)
          if fl.verbose >= level then
            eprintln(if fl.console == "ansi" then phase-line-ansi(ColorScheme(), p, msg).trim-right
                     else phase-line(p, msg))
        with fun emit-line(s) eprintln(s)
        compile-module(fl, module-name, source)
      println(result-json(errs))
