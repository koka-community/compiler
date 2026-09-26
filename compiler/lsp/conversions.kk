// Conversions between LSP wire types and the compiler's own (upstream
// `LanguageServer/Conversions.hs`).
//
// The one rule everything here exists to enforce: **LSP positions are 0-based
// in both line and character; Koka's `pos` is 1-based in both.** Getting that
// wrong is an off-by-one that shows up as diagnostics and hovers landing one
// line or column away, so the conversion lives in exactly one place rather than
// at every call site that happens to need it.
module compiler/lsp/conversions

import std/os/path
import compiler/common/range
import compiler/common/error
import compiler/lib/json
import compiler/lsp/jsonrpc

//----------------------------------------------------------------------
// compiler -> LSP
//----------------------------------------------------------------------

pub fun pos/to-lsp(p: pos): json
  JSObj([("line", JSInt(max(0, p.line - 1))), ("character", JSInt(max(0, p.col - 1)))])

// Koka range ends are INCLUSIVE (they point at the last character) while LSP
// range ends are EXCLUSIVE, so the end column gets a +1 -- upstream `toLspRange`
// does the same. Without it every diagnostic squiggle and highlight is one
// character short.
pub fun range/to-lsp(r: range): json
  val e = r.end
  JSObj([("start", r.start.pos/to-lsp),
         ("end", JSObj([("line", JSInt(max(0, e.line - 1))),
                        ("character", JSInt(max(0, e.col - 1) + 1))]))])

// LSP DiagnosticSeverity: 1 Error, 2 Warning, 3 Information, 4 Hint
pub fun severity/to-lsp(s: error-severity): int
  match s
    SevError -> 1
    SevWarning -> 2
    SevInfo -> 3

//----------------------------------------------------------------------
// LSP -> compiler
//----------------------------------------------------------------------

// A `position` object (`{line, character}`) against the given source.
pub fun pos/from-lsp(j: maybe<json>, src: source): pos
  Pos(src, 0,
      j.field-of("line").as-int.default(0) + 1,
      j.field-of("character").as-int.default(0) + 1)

pub fun range/from-lsp(j: maybe<json>, src: source): range
  Range(j.field-of("start").pos/from-lsp(src), j.field-of("end").pos/from-lsp(src), False)

//----------------------------------------------------------------------
// uris
//----------------------------------------------------------------------

// `file:///a/b.kk` -> `/a/b.kk`. Only the `file:` scheme is supported; anything
// else passes through unchanged so the failure surfaces as "cannot find file"
// rather than as a silently wrong path.
pub fun uri-to-path(uri: string): div path
  match uri.starts-with("file://")
    Just(rest) -> rest.string.percent-decode.path
    Nothing -> uri.path

// A `file:` URI must carry an ABSOLUTE path. Compiler ranges routinely hold a
// path relative to the working directory (`.koka/v3.2.3-.../x.kki`), and
// `file://` + a relative path is read by the editor as a HOST name -- VS Code
// reports `Unable to read file '//.koka/...'`. Absolutize first.
pub fun path-to-uri(p: path): io string
  val abs = if p.is-absolute then p else cwd() / p
  "file://" ++ abs.string

fun percent-decode(s: string): div string
  fun go(cs: list<char>, acc: list<char>): div list<char>
    match cs
      Cons('%', Cons(a, Cons(b, r))) ->
        match (a.hex-val, b.hex-val)
          (Just(x), Just(y)) -> go(r, Cons((x * 16 + y).char, acc))
          _ -> go(Cons(a, Cons(b, r)), Cons('%', acc))
      Cons(c, r) -> go(r, Cons(c, acc))
      Nil -> acc.reverse
  go(s.list, []).string

fun hex-val(c: char): maybe<int>
  val v = c.char/int
  if c.is-digit then Just(v - '0'.char/int)
  elif c >= 'a' && c <= 'f' then Just(v - 'a'.char/int + 10)
  elif c >= 'A' && c <= 'F' then Just(v - 'A'.char/int + 10)
  else Nothing

// `json`'s field lookup lifted over `maybe`, so a nested path reads as a chain
pub fun field-of(mj: maybe<json>, key: string): maybe<json>
  match mj
    Just(j) -> j.field(key)
    Nothing -> Nothing
