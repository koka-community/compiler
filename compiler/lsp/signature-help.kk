// `textDocument/signatureHelp`.
//
// Ports upstream `LanguageServer/Handler/SignatureHelp.hs`: find the function
// whose argument list the cursor sits in, and show every overload's signature
// and documentation.
//
// The name is recovered from the LEXEMES before the cursor, not from the range
// map, because the call being typed is usually incomplete -- `foo(1,` does not
// parse -- so there is no range-map entry to look up. `get-function-name-reverse`
// classifies the finished shapes and `get-function-incomplete-reverse` handles
// the half-typed argument list by dropping back to the nearest unmatched `(`.
//
// The client can name the overload it just accepted from a completion, via the
// `koka/signature-help/set-context` command; that overload is then the active
// signature rather than the first.
module compiler/lsp/signature-help

import std/os/path
import compiler/common/name
import compiler/common/range
import compiler/type/type
import compiler/type/assumption
import compiler/type/pretty
import compiler/syntax/range-map
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/lib/json
import compiler/lsp/jsonrpc
import compiler/lsp/conversions
import compiler/lsp/pretty
import compiler/lsp/state

// The name at the head of a call chain.
fun first-id(f: fn-syntax): maybe<name>
  match f
    FnValue(Lexeme(_, LexId(id))) -> Just(id)
    FnChained(Lexeme(_, LexId(id))) -> Just(id)
    FnIncomplete(chain) -> chain.first-id
    _ -> Nothing

pub fun signature-help(st: server-state, ps: json): _ json
  with with-pretty-env
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Nothing -> JSNull
    Just(d) ->
      val p = ps.field("position").pos/from-lsp(Source(duri.uri-to-path.string, ""))
      val lexemes = lexer(duri.uri-to-path.string, 1, d.text)
      val prior = lexemes.previous-lexemes-reversed(p)
      // upstream: the identifier immediately before the cursor wins; failing
      // that the head of the completed call chain; failing that the head of the
      // INCOMPLETE one (we are inside a half-typed argument list)
      val nm = match prior
        Cons(Lexeme(_, LexId(id)), _) -> Just(id)
        _ -> match prior.get-function-name-reverse.first-id
          Just(id) -> Just(id)
          Nothing -> prior.get-function-incomplete-reverse.first-id
      match nm
        Nothing -> JSNull
        Just(n) ->
          val sigs = d.gam.gamma-lookup(n).map(fn((qn, ninfo)) (qn, ninfo.to-signature))
          if sigs.is-nil then JSNull
          else
            // the overload the client says it just completed, if any
            // `list/index-of` answers -1 when absent, which is not a valid
            // `activeSignature`; fall back to the first overload.
            val found : int = match st.sig-context
              Nothing -> -1
              Just(want) -> sigs.map(fst).index-of(fn(qn) qn.show-plain == want)
            val active = if found < 0 then 0 else found
            JSObj([("signatures", JSList(sigs.map(snd))),
                   ("activeSignature", JSInt(active)),
                   ("activeParameter", JSNull)])

// Label is the canonical name, and the
// documentation is the signature as Koka code followed by the doc comment.
// Externals and imports have no signature to show.
fun to-signature(ninfo: assumption/name-info): _ json
  val label = ninfo.info-name.show-plain
  val code = label ++ " : " ++ ninfo.scheme.ktp/pretty-string
  JSObj([("label", JSString(label)),
         ("documentation", JSObj([("kind", JSString("markdown")),
                                  ("value", JSString(code-with-doc(code, ninfo.doc)))]))])

fun info-name(ninfo: assumption/name-info): name
  match ninfo
    InfoCon(conInfo=ci) -> ci.name
    InfoVal(cname=cn) -> cn
    InfoFun(cname=cn) -> cn
    InfoExternal(cname=cn) -> cn
    InfoImport(fullName=fn') -> fn'


