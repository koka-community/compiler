// `textDocument/definition`.
//
// Split out of `server.kk` to mirror upstream's one-file-per-handler
// `LanguageServer/Handler/` layout.
module compiler/lsp/definition

import std/os/path
import std/data/rb-map
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
import compiler/lsp/util

// Answer `textDocument/definition`: the same
// range-map lookup as hover, then resolve the name to where it was DEFINED.
pub fun definition(st: server-state, ps: json): _ json
  with with-pretty-env
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Nothing -> JSNull
    Just(d) ->
      val p = ps.field("position").pos/from-lsp(Source(duri.uri-to-path.string, ""))
      val lexemes = lexer(duri.uri-to-path.string, 1, d.text)
      match d.rmap.find-at(p, lexemes)
        Nothing -> JSNull
        Just((_, ri)) ->
          match ri.def-ranges(d.gam, st.sess)
            Nil -> JSNull
            rs -> JSList(rs.map(fn(r) st.to-location(r)))

// Which ranges count as "the definition" depends on
// what kind of name is under the cursor.
pub fun def-ranges(ri: range-info, g: gamma, sess: session): _ list<range>
  match ri
    RIId(qname, ninfo) ->
      match ninfo
        // a value, function or constructor: every gamma entry for that exact
        // qualified name (an overloaded name legitimately has several)
        NIValue -> g.lookupQ(qname).map(fn(i) i.range)
        NICon -> g.lookupQ(qname).map(fn(i) i.range)
        // type constructors resolve through synonyms/newtypes, which this
        // server does not carry yet; a type variable and a kind have no
        // definition site at all
        NITypeCon -> []
        NITypeVar -> []
        // an import: jump to the top of that module's source. The dependency
        // scan already maps module name -> source path, so no extra lookup
        // machinery is needed (upstream uses its own module-path table).
        NIModule ->
          match sess.deps.lookup(qname)
            Just((src, _, _, _)) ->
              val top = Pos(Source(src.string, ""), 0, 1, 1)
              [Range(top, top, False)]
            Nothing -> []
        NIKind -> []
    // a declaration IS its own definition, so jumping is a no-op rather than
    // an error -- report nothing and let the editor stay put
    _ -> []
