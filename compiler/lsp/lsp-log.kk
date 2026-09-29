// The language server's handlers for the `log` effect (compiler/lib/log.kk):
// each phase line becomes a `window/logMessage` notification, and during a
// build also a `$/progress` report. They live here rather than beside the
// console handler because they write through the language server's stdio
// transport, which every module that logs would otherwise link.
module compiler/lsp/lsp-log

import compiler/common/color-scheme
import compiler/lib/json
import compiler/lib/log
import compiler/lsp/jsonrpc
import compiler/lsp/stdio

// The language server, DURING A BUILD: the phase also becomes a `$/progress`
// report on the build's work-done token, which is what the editor renders while
// the user waits. Upstream splits these across two Terminal fields -- `termPhase`
// to `window/logMessage`, `termProgress` to `$/progress` -- and the progress one
// is the only one shown without opening an output channel.
//
// Nested inside `with-lsp-phase`, so it wins for the duration of a build and the
// plain log-only handler takes over again afterwards.
// `pct` is how far the build has got, maintained by the caller's `on-progress`.
// Upstream sends percentage and phase text in ONE `termProgress` report; keeping
// them as two feeds means each overwrites the other's message in the UI.
pub fun with-lsp-progress(verbose: int, token: string, pct: ref<global,int>,
                          action: () -> <log,ioc|e> a): <ioc|e> a
  with fun log-phase(level, p, msg)
    if verbose >= level then
      val line = phase-line(p, msg)
      // level 0 is reserved for failures (see the effect declaration): send
      // those at MessageType Error so the client can filter and highlight them
      write-bytes((if level <= 0 then log-diagnostic(line, True)
                   else log-info(phase-line-ansi(ColorScheme(), p, msg))).frame)
      // the progress UI is a plain status string: no ANSI, no newline
      write-bytes(progress-report(token, line, !pct).frame)
  action()

// The language server: one `window/logMessage` per message, the same
// notification upstream's language-server Terminal emits. Installed inside
// `server/run`, so it shadows the console handler the driver put up.
pub fun with-lsp-phase(verbose: int, action: () -> <log,ioc|e> a): <ioc|e> a
  with fun log-phase(level, p, msg)
    if verbose >= level then
      write-bytes(log-info(phase-line-ansi(ColorScheme(), p, msg)).frame)
  action()

// `window/logMessage`, MessageType 3 = Info.
pub fun log-info(text: string): string
  notification("window/logMessage", JSObj([("type", JSInt(3)), ("message", JSString(text))]))

// `window/logMessage` at MessageType 1 = Error / 2 = Warning. Upstream routes
// compile diagnostics here through `termError`, which is also what makes the
// extension focus its terminal: its `appendLine` calls `terminal.show()` when
// the appended text matches /error/i, and diagnostics that never reach this
// channel can never trigger it.
pub fun log-diagnostic(text: string, is-error: bool): string
  notification("window/logMessage",
    JSObj([("type", JSInt(if is-error then 1 else 2)), ("message", JSString(text ++ "\n"))]))
