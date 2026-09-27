// Type-check one module the way the language server does on an edit
// (compiler/lsp/diagnostics.kk `diagnostics-for`: type check only, no code
// generation), so its cost can be profiled on its own:
//
//   <port> -O2 --cclinkopts=-Wl,-no_deduplicate --output=.koka/typecheck-probe scripts/typecheck-probe.kk
//   xctrace record --template 'Time Profiler' --launch -- .koka/typecheck-probe compiler/type/infer.kk
//
// Build the target once first so its imports load from interfaces; the run is
// then dominated by the module's own type check.
module typecheck-probe

import std/os/path
import std/os/env
import std/core/undiv
import std/data/rb-map
import compiler/common/range
import compiler/common/error
import compiler/common/parse
import compiler/common/color-scheme
import compiler/platform/config
import compiler/compile/options
import compiler/compile/vfs
import compiler/compile/build
import compiler/compile/build-context
import compiler/lib/log

fun main()
  val target = get-args().head.default("compiler/type/infer.kk")
  with @default-comp-flags
  with val colors = ColorScheme()
  with no-vfs
  with with-console-phase(0, False)
  with with-console-emit
  with handler
    final ctl parse-error(e: string, _r: range) println("parse error: " ++ e)
  with collapse-div
  with handler
    final ctl add-errors(es: errors) println(es.length.show ++ " errors")
    fun add-warnings(_w: warnings) ()
    fun add-infos(_w: warnings) ()
  match process-initial-options(flags-default, ["-c", "-v0", "--console=raw", "-O2", "--target=c", "--buildtag=probe"])
    Left(err) -> println("options: " ++ err)
    Right((fl, _mode)) ->
      val t0 = wall-ms()
      val s = check-file-session(fl(evaluate = False, library = True, typeCheckOnly = True), target, Session())
      println("type-checked " ++ target ++ " in " ++ (wall-ms() - t0).show ++ "ms (" ++ s.mods.list.length.show ++ " modules)")
