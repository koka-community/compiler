// Koka binding for isocline (vendored under `isocline/`, BSD-licensed, see
// isocline/LICENSE). Upstream koka reaches the same C library through the
// Haskell `isocline` package from `Platform/cpp/Platform/ReadLine.hs`.
//
// Threading model. `ic_readline` blocks and owns the terminal: it puts the tty
// in raw mode and runs its own read loop, and exposes no way to feed it bytes
// from outside. So it must NOT run on the event loop. Callers run it under
// `std/async/thread`'s `compute`, which hands it to a libuv worker thread and
// leaves the loop free; `ic-async-stop` is isocline's own thread-safe lever to
// unblock that read from anywhere (it behaves as if ctrl-C were pressed, so the
// blocked `ic-readline` returns `Nothing`).
module compiler/lib/isocline

import std/num/int32

// isocline is not in vcpkg or conan, so there is no `vcpkg=`/`conan=` key to
// fall back on: `scripts/install-isocline.sh` builds the vendored source
// (vendor/isocline) into a static library under a prefix the compiler's own
// `search-c-library` already looks in, and this finds it there. Same shape as
// std/text/regex.kk's pcre2 dependency.
extern import
  c { library="isocline" }

extern import
  c file "isocline-inline.c"

// Read a line, with editing, history and (once installed) completion and
// highlighting. `Nothing` on EOF (ctrl-D) or when unblocked by `async-stop`.
pub extern readline(prompt: string): ioc maybe<string>
  c "kk_ic_readline"

// Thread-safe: unblock a `readline` that is currently blocked on another
// thread, as if the user pressed ctrl-C. Returns whether the event was
// delivered (isocline documents this as unsupported on some platforms).
pub extern async-stop(): ioc bool
  c "kk_ic_async_stop"

// Persist history to `fname` (empty disables the file), keeping at most
// `max-entries`.
pub extern set-history(fname: string, max-entries: int32): ioc ()
  c "kk_ic_set_history"

pub extern history-add(entry: string): ioc ()
  c "kk_ic_history_add"

// Drop the entry `readline` just added (isocline adds the returned line
// automatically; the REPL re-adds it itself so blank/duplicate input can be
// filtered first).
pub extern history-remove-last(): ioc ()
  c "kk_ic_history_remove_last"

pub extern enable-auto-tab(enable: bool): ioc ()
  c "kk_ic_enable_auto_tab"

pub extern enable-color(enable: bool): ioc ()
  c "kk_ic_enable_color"

// Define a named style used by the bbcode-ish markup isocline accepts, e.g.
// `style-def("ic-bracematch", "underline")`.
pub extern style-def(name: string, fmt: string): ioc ()
  c "kk_ic_style_def"

// The marker printed before the prompt text, and before continuation lines.
pub extern set-prompt-marker(marker: string, cont-marker: string): ioc ()
  c "kk_ic_set_prompt_marker"

// History file under the build dir, plus the styles
// ReadLine.hs sets for brace matching and emphasis.
pub fun with-readline(history-dir: string, action: () -> <ioc|e> a): <ioc|e> a
  set-history(if history-dir.is-empty then "" else history-dir ++ "/.koka-history", 200.int32)
  enable-auto-tab(True)
  style-def("ic-bracematch", "underline")
  style-def("ic-emphasis", "italic")
  style-def("ic-diminish", "")
  action()
