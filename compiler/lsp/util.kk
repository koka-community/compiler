// Small helpers shared by several LSP handlers.
//
// Split out of `server.kk` to mirror upstream's one-file-per-handler
// `LanguageServer/Handler/` layout.
module compiler/lsp/util

import std/os/path
import std/core/undiv
import compiler/common/name
import compiler/common/range
import compiler/common/error
import compiler/common/file
import compiler/compile/options
import compiler/compile/build-context
import compiler/syntax/range-map
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/type/assumption
import compiler/type/pretty
import compiler/kind/pretty
import compiler/kind/kind
import compiler/lib/pprint
import compiler/lib/json
import compiler/lsp/jsonrpc
import compiler/lsp/conversions
import compiler/lsp/state

// `show-parse-error` formats as `<path>(<line>, <col>): parse error: ...`.
// Recover that position; fall back to the start of the file if the shape is
// not what we expect, which is no worse than what we had.
pub fun error-position(msg: string, src: path): range
  val line1 = msg.lines.head.default("")
  match line1.split(")").head
    Nothing -> range/null
    Just(before) ->
      match before.split("(").reverse.head
        Nothing -> range/null
        Just(nums) ->
          val parts = nums.split(",").map(fn(x) x.trim.parse-int)
          match parts
            [Just(l), Just(c)] ->
              val pos = Pos(Source(src.string, ""), 0, l, c)
              Range(pos, pos, False)
            _ -> range/null

// The editor renders the location itself, so the `path(line, col): ` prefix
// `show-parse-error` bakes into the message is duplication in a diagnostic.
pub fun strip-location(msg: string): string
  match msg.split("): ")
    Cons(_, Cons(rest, more)) -> Cons(rest, more).joinsep/join("): ")
    _ -> msg

pub fun to-location(st: server-state, r: range): _ json
  JSObj([("uri", JSString(st.client-uri(r.start.source.name.path))),
         ("range", r.range/to-lsp)])
