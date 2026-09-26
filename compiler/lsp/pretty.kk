// Rendering doc comments and code for hover, completion and signature help.
//
// Ports upstream `LanguageServer/Handler/Pretty.hs`, plus the `removeComment`
// it borrows from `Syntax/Colorize.hs`.
//
// Everything here produces MARKDOWN, because that is what the three LSP
// payloads that carry documentation accept: a signature or type goes inside a
// ```koka fence so the client highlights it, and the doc comment follows as
// prose.
module compiler/lsp/pretty

import std/core/undiv
// `remove-comment` lives in its upstream home, `syntax/colorize.kk`
import compiler/syntax/colorize

// Nothing at all for a blank comment, otherwise a
// horizontal rule and then the prose. A line ending in `\` is a madoko line
// break, which becomes markdown's two-trailing-spaces break.
pub fun pp-comment(s: string): string
  if s.list.all(char/is-white) then ""
  else
    val ls = remove-comment(s).lines.drop-while(fn(l) l.is-empty)
    "\n* * *\n" ++ ls.map(fmt-line).join

fun fmt-line(line: string): string
  if line.is-empty then "\n"
  elif line.ends-with("\\").bool then line.list.init.string ++ "  \n"
  else line ++ "\n"

// A fenced block the client highlights as Koka.
pub fun as-koka-code(code: string): string
  "```koka\n" ++ code ++ "\n```"

// The documentation payload the LSP hands back for a name: its signature as
// Koka code, then its doc comment.
pub fun code-with-doc(code: string, doc: string): string
  as-koka-code(code) ++ pp-comment(doc)
