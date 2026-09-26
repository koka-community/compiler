// `textDocument/completion`.
//
// Ports upstream `LanguageServer/Handler/Completion.hs`. Two halves:
//
//   `completion-info` -- read the lexemes BEFORE the cursor to decide what is
//     being completed. `get-function-name-reverse` already classifies the shapes
//     that matter (`a.`, `a.b.`, a bare identifier, ...); a `.` means the
//     receiver's type is known, and that type filters the candidates.
//
//   `find-completions` -- walk gamma (and, in a type position, the newtypes)
//     for names matching the search term, and turn each into a CompletionItem.
//
// A function completion is emitted as a SNIPPET (`foo($1,$2)`) so accepting it
// leaves the cursor in the first argument, with one argument dropped for a
// dot-call because the receiver already supplies it.
module compiler/lsp/completion

import std/os/path
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/common/unique
import compiler/kind/kind
import std/data/rb-map
import compiler/common/name-collections
import compiler/kind/newtypes
import compiler/kind/synonyms
import compiler/type/type
import compiler/type/typevar
import compiler/type/assumption
import compiler/type/operations
import compiler/type/unify
import compiler/type/pretty
import compiler/syntax/range-map
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/syntax/lex
import compiler/lib/pprint
import compiler/lib/json
import compiler/lsp/jsonrpc
import compiler/lsp/conversions
import compiler/lsp/state

// LSP CompletionItemKind
val ciFunction = 3
val ciConstructor = 4
val ciModule = 9
val ciInterface = 8
val ciKeyword = 14
val ciSnippet = 15
val ciReference = 18
val ciEnumMember = 20
val ciConstant = 21

// What is being completed at the cursor.
pub type completion-kind
  CKFunction        // after a `.` -- the receiver's type filters candidates
  CKValue           // a bare identifier
  CKType            // after a `:`
  CKTypeOrEffect    // after `) :`

fun ck/is-type(k: completion-kind): bool
  match k
    CKType -> True
    CKTypeOrEffect -> True
    _ -> False

fun ck/(==)(k1: completion-kind, k2: completion-kind): bool
  match (k1, k2)
    (CKFunction, CKFunction) -> True
    (CKValue, CKValue) -> True
    (CKType, CKType) -> True
    (CKTypeOrEffect, CKTypeOrEffect) -> True
    _ -> False

pub type completion-info
  CompletionInfo(
    full-line: string,
    search: string,
    // the range an accepted item REPLACES: the partial name already typed, or
    // an empty range just after the `.` when nothing is typed yet
    search-range: range,
    // the receiver's type in a dot-call; candidates whose first parameter it
    // cannot match are dropped
    argument-type: maybe<ktype>,
    kind: completion-kind)

fun completion-info-at(d: state/doc, p: pos, lexemes: list<lexeme>): _ maybe<completion-info>
  // start one column BEFORE the insertion point: the cursor sits where the
  // completion goes, and we want the token that precedes it
  val posx = p(col = p.col - 1)
  val prior = lexemes.previous-lexemes-reversed(posx)
  val line = d.text.lines.drop(max(0, p.line - 1)).head.default("")
  // an empty range just past the `.`, for when nothing has been typed yet
  val end-rng = match prior
    Nil -> range/null
    Cons(Lexeme(r, _), _) ->
      val e = r.extend(1).end
      make-range(e, e)
  fun dot(partial: string, ins: range, recv: range, chained: bool): _ maybe<completion-info>
    // the receiver's type comes out of the range map; for `a.b.` the useful
    // type is b's RESULT, not b itself
    val tp = match d.rmap.find-types(recv)
      Nil -> Nothing
      Cons(t, _) ->
        if !chained then Just(t)
        else match t.split-fun-scheme
          Just((_, _, _, res)) -> Just(res)
          Nothing -> Just(t)
    Just(CompletionInfo(line, partial, ins, tp, CKFunction))
  fun lit(partial: string, ins: range, tp: ktype): _ maybe<completion-info>
    Just(CompletionInfo(line, partial, ins, Just(tp), CKFunction))
  match prior.get-function-name-reverse
    // `a.` / `a.b.` -- nothing typed after the dot yet
    FnIncomplete(FnValue(Lexeme(r, LexId))) -> dot("", end-rng, r, False)
    FnIncomplete(FnChained(Lexeme(r, LexId))) -> dot("", end-rng, r, True)
    // `a.pre` / `a.b.pre` -- a partial name to replace
    FnChained(Lexeme(r0, LexId(partial)), FnValue(Lexeme(r2, LexId))) ->
      dot(partial.show-plain, r0, r2, False)
    FnChained(Lexeme(r0, LexId(partial)), FnChained(Lexeme(r2, LexId))) ->
      dot(partial.show-plain, r0, r2, True)
    // a literal receiver: its type is known outright
    FnIncomplete(FnValue(Lexeme(_, LexString))) -> lit("", end-rng, typeString)
    FnChained(Lexeme(r0, LexId(p1)), FnValue(Lexeme(_, LexString))) -> lit(p1.show-plain, r0, typeString)
    FnIncomplete(FnValue(Lexeme(_, LexInt))) -> lit("", end-rng, typeInt)
    FnChained(Lexeme(r0, LexId(p1)), FnValue(Lexeme(_, LexInt))) -> lit(p1.show-plain, r0, typeInt)
    FnIncomplete(FnValue(Lexeme(_, LexFloat))) -> lit("", end-rng, typeFloat)
    FnChained(Lexeme(r0, LexId(p1)), FnValue(Lexeme(_, LexFloat))) -> lit(p1.show-plain, r0, typeFloat)
    FnIncomplete(FnValue(Lexeme(_, LexChar))) -> lit("", end-rng, typeChar)
    FnChained(Lexeme(r0, LexId(p1)), FnValue(Lexeme(_, LexChar))) -> lit(p1.show-plain, r0, typeChar)
    // a LIST LITERAL receiver (`[1,2].`): upstream `completeList`. Its element
    // type is unknown, so the filter type is `forall<a> list<a>` -- the skolem
    // keeps `match-arguments` from unifying `a` with something specific and
    // narrowing the list to one element type.
    FnIncomplete(FnValue(Lexeme(_, LexSpecial("]")))) -> lit("", end-rng, type-any-list())
    FnChained(Lexeme(r0, LexId(p1)), FnValue(Lexeme(_, LexSpecial("]")))) ->
      lit(p1.show-plain, r0, type-any-list())
    // a bare identifier
    FnValue(Lexeme(r, LexId(partial))) ->
      Just(CompletionInfo(line, partial.show-plain, r, Nothing, CKValue))
    FnChained(Lexeme(r, LexId(partial)), _) ->
      Just(CompletionInfo(line, partial.show-plain, r, Nothing, CKValue))
    _ ->
      // not a value position: a `:` before the cursor means a type is wanted
      match prior.drop-auto-gen-closing
        Cons(Lexeme(_, LexKeyword(":")), Cons(Lexeme(_, LexSpecial(")")), _)) ->
          Just(CompletionInfo(line, "", end-rng, Nothing, CKTypeOrEffect))
        Cons(Lexeme(r0, LexId(partial)), Cons(Lexeme(_, LexKeyword(":")), Cons(Lexeme(_, LexSpecial(")")), _))) ->
          Just(CompletionInfo(line, partial.show-plain, r0, Nothing, CKTypeOrEffect))
        Cons(Lexeme(_, LexKeyword(":")), _) ->
          Just(CompletionInfo(line, "", end-rng, Nothing, CKType))
        Cons(Lexeme(r0, LexId(partial)), Cons(Lexeme(_, LexKeyword(":")), _)) ->
          Just(CompletionInfo(line, partial.show-plain, r0, Nothing, CKType))
        _ -> Nothing

fun type-any-list(): ktype
  val tv = TypeVar(-1, kindStar, Skolem)
  TForAll([tv], TApp(typeList, [TVar(tv)]))

// the types the range map recorded at exactly this range (upstream
// `rangeMapFind rng rmap` then `rangeInfoType`)
fun find-types(rm: range-map, r: range): _ list<ktype>
  rm.filter-map fn((rng, ri))
    if rng == r then ri.ri-type else Nothing

// Can `tp` be applied to a value of type `arg`? Used to
// keep a dot-completion list to functions the receiver could actually feed.
// `run-unique(0)`: the unifier mints fresh metas, and this is a throwaway
// context, so the counter starts from scratch.
fun type-unifies(tp: ktype, arg: maybe<ktype>): _ bool
  match arg
    Nothing -> True
    Just(a) ->
      with run-unique(0)
      val (res, _sub) = run-unify({ match-arguments(True, range/null, tvs/empty, tp, [a], [], Nothing) })
      res.is-right

// An infix (not prefix) match, and never a name the
// user did not write -- except handler constructors, which are how `handler`
// itself is offered.
fun matches(n: name, search: string): bool
  search.is-empty || n.show-plain.string/contains(search)

pub fun completions-for(d: state/doc, p: pos, lexemes: list<lexeme>, modname: name): _ json
  match d.completion-info-at(p, lexemes)
    Nothing -> JSObj([("isIncomplete", JSBool(False)), ("items", JSList([]))])
    Just(ci) ->
      val items = d.find-completions(ci, modname)
      // `isIncomplete` true: the list is filtered by the term typed so far, so
      // the client must re-ask rather than filter our answer itself
      JSObj([("isIncomplete", JSBool(True)), ("items", JSList(items))])

fun find-completions(d: state/doc, ci: completion-info, modname: name): _ list<json>
  val vals = d.gam.value-completions(ci, modname)
  // upstream `synonymCompletions`/`datatypeCompletions`: types and synonyms are
  // only meaningful where a type is being written
  val tps = if ci.kind.is-type then
              d.ntypes.datatype-completions(modname) ++ d.syns.synonym-completions(ci, modname)
            else []
  val kws = if ci.kind == CKValue then keyword-completions(modname) else []
  kws ++ vals ++ tps

fun value-completions(g: gamma, ci: completion-info, modname: name): _ list<json>
  val rng = ci.search-range.range/to-lsp
  g.assumption/list.filter-map fn((n, ninfo))
    if !n.matches(ci.search) || n.is-hidden-name then Nothing
    else
      val tp = ninfo.scheme
      if !type-unifies(tp, ci.argument-type) then Nothing
      else
        val detail = tp.ktp/pretty-string
        match ninfo
          // a function: offer it as a call snippet, with the receiver's
          // argument already accounted for in a dot-call
          InfoFun -> Just(fun-item(modname, n, detail, tp, ci, rng))
          InfoVal ->
            match tp.split-fun-scheme
              Just(_) -> Just(fun-item(modname, n, detail, tp, ci, rng))
              Nothing -> Just(item(modname, n, ciConstant, detail))
          InfoExternal -> Just(item(modname, n, ciReference, detail))
          InfoImport -> Just(item(modname, n, ciModule, detail))
          InfoCon(conInfo=cinfo) ->
            Just(item(modname, n, if cinfo.params.is-nil then ciEnumMember else ciConstructor, detail))

fun datatype-completions(nts: newtypes, modname: name): _ list<json>
  nts.rb-map/list.map fn((_, di))
    item(modname, di.name, ciInterface, di.name.show-plain)

fun synonym-completions(sy: synonyms, ci: completion-info, modname: name): _ list<json>
  sy.rb-map/list.filter-map fn((_, si))
    if !si.name.matches(ci.search) then Nothing
    else Just(item(modname, si.name, ciInterface, si.tp.ktp/pretty-string))

fun keyword-completions(modname: name): _ list<json>
  reserved-name-list.map fn(s)
    JSObj([("label", JSString(s)), ("kind", JSInt(ciKeyword)),
           ("sortText", JSString("1" ++ s))])

// upstream `makeCompletionItem`. `sortText` is what puts the current module's
// own names above everything imported.
fun item(modname: name, n: name, kind: int, detail: string): _ json
  val label = n.nameStem
  JSObj([
    ("label", JSString(label)),
    ("kind", JSInt(kind)),
    ("detail", JSString(detail)),
    ("documentation", JSString(n.nameModule)),
    ("sortText", JSString((if modname.nameModule == n.nameModule then "0" else "2") ++ label)),
    ("commitCharacters", JSList([JSString("\t")]))])

// A snippet that types the parentheses
// and leaves tab stops in the arguments.
fun fun-item(modname: name, n: name, detail: string, tp: ktype, ci: completion-info, rng: json): _ json
  val label = n.nameStem
  val pars = match tp.split-fun-scheme
    Just((_, ps, _, _)) -> ps.length
    Nothing -> 0
  // a dot-call already supplies the first argument
  val nargs = max(0, pars - (if ci.kind == CKFunction then 1 else 0))
  val args = if nargs == 0 then ""
             else "(" ++ list(1, nargs).map(fn(i) "$" ++ i.show).joinsep/join(",") ++ ")"
  JSObj([
    ("label", JSString(label)),
    ("kind", JSInt(ciSnippet)),
    ("detail", JSString(detail)),
    ("filterText", JSString(label)),
    ("insertTextFormat", JSInt(2)),          // 2 = Snippet
    ("textEdit", JSObj([("range", rng), ("newText", JSString(label ++ args))])),
    ("sortText", JSString((if modname.nameModule == n.nameModule then "0" else "2") ++ label)),
    ("commitCharacters", JSList([JSString("\t")]))])
