// Phase logging: the running commentary a build emits about what it is doing.
//
// Upstream carries this in the `Terminal` record it threads through the build
// (`termPhase`, `termTrace`), constructed differently per front end: the CLI
// prints to the console gated on `--verbose`, and the language server turns
// each message into a `window/logMessage` notification so the editor can show
// what a slow compile is working on. This port had NO equivalent -- the
// `load :` / `check :` lines a Koka user recognises come from the reference
// compiler, and the port printed nothing at any verbosity.
//
// An EFFECT rather than a Terminal record threaded through every signature, or
// a global sink. Two things fall out of that which neither alternative gives:
//
//   - the handler is scoped, so "the front end installs this before the build
//     starts" is enforced by the type checker instead of by a comment; and
//   - a worker thread cannot silently reach for the main strand's handler. A
//     `spawn-thread` closure is typed `<async,ioc>` -- a closed row with no
//     user effects -- so a module compile that logged without a local handler
//     would not compile, rather than looking up evidence belonging to the
//     spawning thread and crashing in `kk_evv_at`.
//
// `isolate-diagnostics` (orchestrate.kk) installs the worker-side handler,
// collecting phase lines into the same `mod-outcome` message list it already
// uses for diagnostics -- so worker output is ordered by the orchestrator
// rather than interleaved from several threads at once.
module compiler/lib/log

import std/pretty/printer
import compiler/common/color-scheme

// Compiler OUTPUT that is part of the observable RESULT rather than commentary
// about progress: `--showtypesigs`' signature listing, the `--showcore` /
// `--showasm` dumps. Upstream prints these straight to stdout, which is fine
// when one process compiles one program -- but it makes them unattributable the
// moment several compiles share a process, which is exactly what driving the
// compiler as a LIBRARY does. A test runner batching many roots into one build
// cannot tell which root printed what.
//
// Same reasoning as `log` below, and the same two properties: the handler is
// scoped (so "the front end installs this" is type-checked, not a convention),
// and a worker cannot silently reach for the main strand's handler.
//
// Distinct from `log` because the two are routed differently: phase logging is
// gated on verbosity and may go to the LSP as `window/logMessage`, whereas this
// IS the program's output and must be reproduced verbatim.
pub effect emit
  // `fun`, not `ctl`: emitting output never alters control flow.
  fun emit-line(s: string): ()

// The CLI front end: straight to stdout.
pub fun with-console-emit(action)
  with fun emit-line(s) println(s)
  action()

pub effect log
  // `fun`, not `ctl`: reporting progress never needs to alter control flow, and
  // a tail-resumptive operation costs no continuation capture.
  //
  // `level` is upstream's `phaseVerbose` level: 1 is the default running
  // commentary (parse/check/load/linking), 2 is per-pass detail
  // (codegen/optimize/scan), 3 is done-markers and shell commands. Level 0 is
  // this port's own addition for things that must never be silenced -- a link
  // failure is not progress, and `-v0` must not swallow it.
  fun log-phase(level: int, p: string, msg: string): ()

// upstream `phase` == `phaseVerbose 1`
pub fun phase(p: string, msg: string): <log> ()
  log-phase(1, p, msg)

pub fun phase-verbose(level: int, p: string, msg: string): <log> ()
  log-phase(level, p, msg)

// `sfill 8 phase ++ ":"`, then the message.
pub fun phase-line(p: string, msg: string): string
  p.pad-right(7) ++ " : " ++ msg

fun ansi(c: color): string
  ansi-escape(seq-color(False, c))

val ansi-reset = ansi-escape("0")

// The same line with upstream's colours: the phase in `colorInterpreter`, the
// message in `colorSource` (`phaseShowIO`).
//
// The TRAILING NEWLINE is load-bearing. The extension renders this channel
// through a pseudo-terminal that wraps each chunk as
// `\r${text.split(/(\r?\n)/g).join("\r")}\r` -- so a chunk with no newline is
// carriage-return, print, carriage-return, and the NEXT message overwrites it.
// Without it the terminal shows only the phase currently running and no
// history at all. Upstream's `writePrettyLn` ends its lines the same way.
pub fun phase-line-ansi(cs: colorScheme, p: string, msg: string): string
  ansi(cs.colorInterpreter) ++ p.pad-right(7) ++ " :" ++ ansi-reset ++ " " ++
  ansi(cs.colorSource) ++ msg ++ ansi-reset ++ "\n"

// Discard.
pub fun with-no-phase(action: () -> <log|e> a): e a
  with fun log-phase(_lvl, _p, _msg) ()
  action()

// The CLI. Upstream gates `termPhase` on `verbose > 0`; the gate is INSIDE the
// handler rather than a choice between two handlers, so the effect is
// discharged the same way either way and the caller's row does not change with
// the verbosity.
//
// Colour follows `--console`: an ANSI printer for the CLI unconditionally,
// with `--console=raw` to turn it off. There is deliberately NO tty
// auto-detection: the reference compiler has none, so
// adding it would make redirected output differ between the two compilers.
pub fun with-console-phase(verbose: int, ansi: bool, action: () -> <log,console|e> a): <console|e> a
  with fun log-phase(level, p, msg)
    if verbose >= level then
      println(if ansi then phase-line-ansi(ColorScheme(), p, msg).trim-right
              else phase-line(p, msg))
  action()

