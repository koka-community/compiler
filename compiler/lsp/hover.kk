// `textDocument/hover`.
//
// Split out of `server.kk` to mirror upstream's one-file-per-handler
// `LanguageServer/Handler/` layout.
module compiler/lsp/hover

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
import compiler/lsp/pretty
import compiler/lsp/state

// Answer `textDocument/hover` from the range map the last check produced.
// Upstream `Handler/Hover.hs`: snap the requested position to the enclosing
// lexeme, look the range up, and render the `RangeInfo` as Koka code.
pub fun hover(st: server-state, ps: json): _ json
  // one place to install the pretty-printing environments the range-map
  // renderers need; every future feature that formats types wants the same
  with with-pretty-env
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Nothing -> JSNull
    Just(d) ->
      val p = ps.field("position").pos/from-lsp(Source(duri.uri-to-path.string, ""))
      val lexemes = lexer(duri.uri-to-path.string, 1, d.text)
      match d.rmap.find-at(p, lexemes)
        Nothing -> JSNull
        Just((r, ri)) ->
          val (code, doc) = ri.hover-text
          if code.is-empty then JSNull
          else JSObj([
            // The signature as Koka code, then
            // the definition's doc comment as prose after a rule
            ("contents", JSObj([("kind", JSString("markdown")),
                                ("value", JSString(code-with-doc(code, doc)))])),
            ("range", r.range/to-lsp)])
// The signature, then any extra docs the type
// checker attached. For a literal those docs are the alternate renderings
// (`dec=`, `hex64=`, `bit64=`, `unicode=`, `count=`), which is the whole point
// of hovering one.
// (code, doc comment). The code goes in a ```koka fence, the comment as prose
// after it -- upstream keeps the same split.
pub fun hover-text(ri: range-info): _ (string, string)
  match ri
    RIDecl(kind, nm, _, mbtp) ->
      (kind ++ " " ++ nm.show-plain ++ (match mbtp { Just(tp) -> " : " ++ tp.ktp/pretty-string; Nothing -> "" }), "")
    RIBlock(str) -> (str, "")
    RIId(nm, ninfo, docs, _) ->
      val sig = ninfo.info-text(nm)
      // the extra docs are the type checker's own annotations (for a literal,
      // the alternate renderings `dec=`/`hex64=`/...), so they belong INSIDE the
      // code block; the definition's comment belongs after it
      val code = if docs.is-nil then sig
                 else Cons(sig, docs.map(fn(d) d.pprint/show)).joinsep/join("\n")
      (code, ninfo.info-comment)
    // errors and warnings already reach the editor as diagnostics; repeating
    // them in a hover popup is noise
    RIError -> ("", "")
    RIWarning -> ("", "")
    RIImplicits -> ("", "")
    RIInlayHint -> ("", "")

// the doc comment the type checker captured for this name, if any
pub fun info-comment(ninfo: range-map/name-info): string
  match ninfo
    NIValue(comment=c) -> c
    NICon(comment=c) -> c
    NITypeCon(comment=c) -> c
    _ -> ""

pub fun info-text(ninfo: range-map/name-info, nm: name): _ string
  match ninfo
    NIValue(sort, tp) -> (if sort.is-empty then "" else sort ++ " ") ++ nm.show-plain ++ " : " ++ tp.ktp/pretty-string
    NICon(tp) -> "con " ++ nm.show-plain ++ " : " ++ tp.ktp/pretty-string
    NITypeCon(k) -> (if k == kindEffect || k == kindLabel then "effect" else "type") ++ " " ++ nm.show-plain ++ " :: " ++ k.kind/show
    NITypeVar(k) -> "type " ++ nm.show-plain ++ " :: " ++ k.kind/show
    NIModule -> "module " ++ nm.show-plain
