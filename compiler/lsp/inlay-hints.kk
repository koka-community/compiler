// `textDocument/inlayHint`.
//
// Split out of `server.kk` to mirror upstream's one-file-per-handler
// `LanguageServer/Handler/` layout.
module compiler/lsp/inlay-hints

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
import std/os/env
import compiler/lib/json
import compiler/lsp/jsonrpc
import compiler/lsp/conversions
import compiler/lsp/state

// Answer `textDocument/inlayHint`: the
// range map already carries everything needed, so this is a rendering pass over
// the entries that fall inside the requested range.
//
// Implemented: inferred types on unannotated definitions, and the general hints
// the type checker emits directly (`RIInlayHint`, e.g. eta-expanded parameter
// names). Not implemented: qualifier hints (need `missingQualifier`) and
// implicit-argument hints (need `RIImplicits`' shorten callback rendered
// against a pretty env) -- both are additive.
pub fun inlay-hints(st: server-state, ps: json): _ json
  with with-pretty-env
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Nothing -> JSList([])
    Just(d) ->
      val src = Source(duri.uri-to-path.string, "")
      val rng = ps.field("range").range/from-lsp(src)
      val lexemes = lexer(duri.uri-to-path.string, 1, d.text)
      val hits = d.rmap.find-in(rng, True)
      // the module this file declares, for deciding which qualifiers are
      // redundant (upstream passes `modname` down the same way)
      val modname = d.uri.uri-to-path.stemname.new-module-name
      val opts = (st.hint-qualifiers, st.hint-types, st.hint-implicits)
      // The range map can carry the same entry twice (a `var` read records two
      // identical Id entries), which would render the same hint stacked on
      // itself -- `buffer(?hdiv=..)(?hdiv=..)`. Upstream computes exactly this
      // `hintsDistinct` and then leaves it unused; dropping only EXACT duplicates
      // is strictly weaker than its nub-by-position and cannot hide a real hint.
      // `KOKA_LSP_TRACE_HINTS=1` dumps what the range map offered, which is the
      // only way to tell a mis-anchored hint from a mis-RECORDED range.
      if get-env-value("KOKA_LSP_TRACE_HINTS").is-just then
        hits.foreach fn((r, ri))
          trace("HINT " ++ r.range/show ++ " " ++ ri.ri-kind)
      JSList(hits.flatmap(fn((r, ri)) hints-for(r, ri, lexemes, modname, opts)).distinct-hints)

// The lexeme list every hint function looks at is
// anchored ONCE at the END of the range-map range (`lexemesFromPos (rangeEnd
// rng)`), so its head is the lexeme the range covers. Anchoring at the start
// instead would be equivalent for well-formed ranges, but some range-map ranges
// are a character short (a `var` read records (13,17) for a `buffer` whose
// lexeme is (13,18)), and only the end-anchored, lexeme-based form survives that.
pub fun hints-for(r: range, ri: range-info, lexemes0: list<lexeme>, modname: name,
                  // (qualifiers, types, implicits) -- upstream guards each kind
                  // separately in `createInlayHints`
                  opts: (bool, bool, bool)): _ list<json>
  val lexemes = lexemes0.lexemes-from-pos(r.end)
  val (want-qual, want-types, want-impl) = opts
  if lexemes.is-nil then [] else
    (if want-qual then qualifier-hints(r, ri, lexemes, modname) else []) ++
    (if want-impl then implicit-hints(r, ri, lexemes) else []) ++
    (if want-types then type-hints(r, ri, lexemes) else [])

pub fun type-hints(r: range, ri: range-info, lexemes: list<lexeme>): _ list<json>
  match ri
    // an inferred type on a definition the user did NOT annotate
    RIId(_, NIValue(_, tp, _, isAnnotated), _, isDef)
        | isDef && !isAnnotated && !r.has-annotation(lexemes) ->
      val str = tp.ktp/pretty-string
      // for `-> eff res` types upstream drops the leading arrow
      val body = match str.starts-with("->")
        Just(rest) -> rest.string.trim
        Nothing -> str
      [new-hint(r.end, " : " ++ body, False)]
    // hints the type checker emitted directly (eta-expanded parameter names)
    RIInlayHint(after, doc) ->
      [new-hint(if after then r.end else r.start, doc.pprint/show, !after)]
    _ -> []

// When a name resolved to something qualified that
// the user did not write out, show the missing qualifier just before it.
pub fun qualifier-hints(r: range, ri: range-info, lexemes: list<lexeme>, modname: name): _ list<json>
  match ri
    RIId(qname) | qname != qname.unqualify-full ->
      val qual = match lexemes
        Cons(Lexeme(_, LexId(nm)), _) | qname.unqualify-full == nm.unqualify-full ->
          missing-qualifier(modname, nm, qname)
        // an operator needs a space so the hint does not run into the token
        Cons(Lexeme(_, LexOp(nm)), _) | qname.unqualify-full == nm.unqualify-full ->
          val q = missing-qualifier(modname, nm, qname)
          if q.is-empty then "" else " " ++ q
        Cons(Lexeme(_, LexIdOp(nm)), _) | qname.unqualify-full == nm.unqualify-full ->
          val q = missing-qualifier(modname, nm, qname)
          if q.is-empty then "" else " " ++ q
        _ -> ""
      if qual.is-empty then [] else [new-hint(r.just-before.end, qual, False)]
    _ -> []

// The implicit arguments inference supplied, shown at
// the end of the call.
pub fun implicit-hints(r: range, ri: range-info, lexemes: list<lexeme>): _ list<json>
  match ri
    RIId(_, NIValue, idocs) | !idocs.is-nil ->
      val (at, wrap) = lexemes.final-call-range
      val body = idocs.map(fn(d) d.pprint/show).joinsep/join(",")
      [new-hint(at, wrap(body), False)]
    _ -> []

// Where the implicit list belongs, and whether it
// needs parentheses (a dot-call has no argument list yet) or a leading comma
// (an existing non-empty argument list).
pub fun final-call-range(lexemes: list<lexeme>): _ (pos, (string) -> string)
  match lexemes
    Cons(lex1, rest) ->
      // upstream `erange = endOfRange (getRange lex1)` -- the LEXEME's range,
      // which is reliable where the range-map's own range is not
      val eend = lex1.range.end-of-range.end
      // Upstream tests for the specific lexemes that can follow a dot-call with
      // no argument list -- `.`, `;`, and its two layout-inserted tokens. That
      // list is not exhaustive for THIS lexer (a call at the end of a block is
      // followed by an inserted `}`, which upstream never sees), and when the
      // test wrongly said "there is an argument list", `find-call-end` scanned
      // on past the end of the statement and anchored the hint inside the NEXT
      // definition's parameter list. Ask the question that actually decides it:
      // an argument list exists only if `(` comes next.
      val is-dot = match lex1
        Lexeme(_, LexOp) -> True     // an operator always needs parenthesising
        _ -> match rest
          Cons(Lexeme(_, LexSpecial("("))) -> False
          _ -> True
      if is-dot then (eend, fn(t) "(" ++ t ++ ")")
      else
        val empty-args = match rest
          Cons(Lexeme(_, LexSpecial("(")), Cons(Lexeme(_, LexSpecial(")")), _)) -> True
          _ -> False
        (rest.find-call-end(0, eend), if empty-args then fn(t) t else fn(t) "," ++ t)
    Nil -> (Pos(Source("", ""), -1, 1, 1), fn(t) t)

pub fun find-call-end(lexemes: list<lexeme>, depth: int, fallback: pos): div pos
  match lexemes
    // never scan out of the statement the call is in
    Cons(Lexeme(_, LexInsSemi), _) | depth <= 0 -> fallback
    Cons(Lexeme(_, LexInsRCurly), _) | depth <= 0 -> fallback
    Cons(Lexeme(_, LexSpecial(";")), _) | depth <= 0 -> fallback
    Cons(Lexeme(_, LexSpecial("(")), rest) -> rest.find-call-end(depth + 1, fallback)
    Cons(Lexeme(rr, LexSpecial(")")), rest) ->
      if depth > 1 then rest.find-call-end(depth - 1, fallback) else rr.just-before.end
    Cons(_, rest) -> rest.find-call-end(depth, fallback)
    Nil -> fallback

// A `:` in the next couple of lexemes means the user wrote
// the type themselves, so showing an inferred one would be noise.
//
// Upstream looks at the two lexemes after the range, because its `vrng` is the
// range ENDING AT `)` (its own comment says so) -- so a `:` right after the
// parameter list is the annotation. The PORT's parser puts the NAME's range in
// that binder field instead, so the lexemes after it are `(`, the first
// parameter -- and the check could never fire, leaving a redundant hint on
// every annotated definition. Rather than depend on that, skip a balanced
// parameter list first and then apply upstream's test. (The `vrng` divergence
// itself is a parser fidelity bug; see docs/parity-checklist.md.)
pub fun has-annotation(r: range, lexemes: list<lexeme>): bool
  // the lexeme list strictly shrinks, so the recursion below terminates
  pretend-no-div
    val after = lexemes.drop-while(fn(l) l.range.start < r.end)
    match after
      Cons(Lexeme(_, LexSpecial("(")), rest) -> rest.skip-parens(1).starts-with-colon
      _ -> after.starts-with-colon

pub fun skip-parens(lexemes: list<lexeme>, depth: int): div list<lexeme>
  if depth <= 0 then lexemes
  else match lexemes
    Nil -> Nil
    Cons(Lexeme(_, LexSpecial("(")), rest) -> rest.skip-parens(depth + 1)
    Cons(Lexeme(_, LexSpecial(")")), rest) -> rest.skip-parens(depth - 1)
    Cons(_, rest) -> rest.skip-parens(depth)

pub fun starts-with-colon(lexemes: list<lexeme>): bool
  match lexemes.take(2)
    Cons(Lexeme(_, LexKeyword(":")), _) -> True
    Cons(_, Cons(Lexeme(_, LexKeyword(":")), _)) -> True
    _ -> False

pub fun distinct-hints(hints: list<json>): _ list<json>
  hints.foldl(([], []), fn(acc: (list<json>, list<string>), h)
    val k = h.show
    if acc.snd.any(fn(s) s == k) then acc else (Cons(h, acc.fst), Cons(k, acc.snd))
  ).fst.reverse

pub fun new-hint(p: pos, text: string, padding: bool): _ json
  // upstream places the hint one column past the range end
  val at = Pos(p.source, p.off, p.line, p.col + 1).pos/to-lsp
  JSObj([("position", at), ("label", JSString(text)), ("kind", JSInt(1)),
         ("paddingLeft", JSBool(padding)), ("paddingRight", JSBool(padding))])

// a one-word tag for the trace above
fun ri-kind(ri: range-info): _ string
  match ri
    RIId(nm, _, docs, isDef) ->
      "Id " ++ nm.show ++ (if isDef then " def" else "") ++ " idocs=" ++ docs.length.show
    RIDecl(k, nm) -> "Decl " ++ k ++ " " ++ nm.show
    RIBlock(k) -> "Block " ++ k
    RIError -> "Error"
    RIWarning -> "Warning"
    RIImplicits -> "Implicits"
    RIInlayHint(after) -> "InlayHint after=" ++ after.show
