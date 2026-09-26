// Document symbols and folding ranges.
//
// Ports upstream `LanguageServer/Handler/DocumentSymbol.hs` and
// `LanguageServer/Handler/Folding.hs`. Both are pure walks over the PARSED
// program -- no types, no core -- so they answer from `doc/prog`, which the
// check captures alongside the range map (upstream reads it back out of its
// module cache with `lookupProgram`; this port's `bmodule` keeps only core).
//
// Upstream expresses each walk as a `HasSymbols` / `HasFoldingRanges` class with
// one instance per syntax node. Koka has no such classes, so each instance
// becomes a `<node>/symbols` or `<node>/foldings` function; the call graph is
// otherwise one-to-one with upstream's.
module compiler/lsp/symbols

import std/core/undiv
import std/num/float64
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/syntax/syntax
import compiler/lsp/conversions
import compiler/lib/json
import compiler/lsp/jsonrpc
import compiler/lsp/state

//----------------------------------------------------------------------
// document symbols
//----------------------------------------------------------------------

// LSP SymbolKind. Koka uses only this subset (upstream's comment lists it).
val symFunction = 12
val symVariable = 13
val symConstant = 14
val symString = 15
val symNumber = 16
val symConstructor = 9
val symEnum = 10
val symInterface = 11
val symStruct = 23
val symEnumMember = 22
val symField = 8

// `range` is what folds/highlights, `selectionRange`
// is what the editor reveals -- and both are suppressed for names the user never
// wrote (hidden/compiler-generated), which would otherwise litter the outline.
fun make-symbol-select(n: name, kind: int, r: range, sel: range, cs: list<json>): _ list<json>
  // `sel.is-null` is a port addition: a symbol with no source position (the
  // implicit `True` guard the parser inserts for an unguarded branch carries
  // `range/null`) would send the editor to 0:0. Upstream emits it.
  if n.nameStem == "" || n.is-hidden-name || sel.is-null then []
  else [JSObj([
    ("name", JSString(n.nameStem)),
    ("detail", JSString(n.nameModule)),
    ("kind", JSInt(kind)),
    ("tags", JSList([])),
    ("deprecated", JSBool(False)),
    ("range", r.range/combine(sel).range/to-lsp),
    ("selectionRange", sel.range/to-lsp),
    ("children", JSList(cs))])]

fun make-symbol(n: name, kind: int, r: range, cs: list<json>): _ list<json>
  make-symbol-select(n, kind, r, r, cs)

pub fun program/symbols(p: user-program): _ list<json>
  p.typedefs.flatmap(tdg/symbols) ++ p.defs.flatmap(dg/symbols)

fun tdg/symbols(g: user-typedef-group): _ list<json>
  match g
    TypeDefRec(ds) -> ds.flatmap(td/symbols)
    TypeDefNonRec(d) -> d.td/symbols

fun td/symbols(td: user-typedef): _ list<json>
  match td
    Synonym(b, params, _, r) ->
      make-symbol-select(b.name, symInterface, r, b.name-range, params.flatmap(tb/symbols))
    DataType(b, params, constrs, r) ->
      // more than one constructor reads as an enum, one as a struct
      val kind = if constrs.length > 1 then symEnum else symStruct
      val cs = if constrs.length > 1 then constrs.flatmap(con/symbols) ++ params.flatmap(tb/symbols)
               else params.flatmap(tb/symbols)
      make-symbol-select(b.name, kind, r, b.name-range, cs)

// upstream reports no symbol for a type parameter (the instance body is
// commented out there); kept as its own function so the shape stays comparable
fun tb/symbols(^b: user-type-binder): list<json>
  []

fun con/symbols(c: user-user-con): _ list<json>
  val kind = if c.params.is-nil then symEnumMember else symConstructor
  make-symbol-select(c.name, kind, c.range, c.name-range,
                     c.params.flatmap(conpar/symbols) ++ c.existentials.flatmap(tb/symbols))

fun conpar/symbols((_vis, b): (visibility, value-binder<user-type, maybe<user-expr>>)): _ list<json>
  make-symbol-select(b.name, symField, b.range, b.name-range, b.expr.maybe/symbols)

fun maybe/symbols(m: maybe<user-expr>): _ list<json>
  match m
    Nothing -> []
    Just(e) -> e.expr/symbols

fun dg/symbols(g: user-def-group): _ list<json>
  match g
    DefRec(ds) -> ds.flatmap(def/symbols)
    DefNonRec(d) -> d.def/symbols

fun def/symbols(d: user-def): _ list<json>
  val kind = match d.sort
    DefFun -> symFunction
    DefVal -> symConstant
    DefVar -> symVariable
  make-symbol-select(d.binder.name, kind, d.range, d.binder.name-range, d.binder.expr.expr/symbols)

fun lambinder/symbols(b: value-binder<maybe<user-type>, maybe<user-expr>>): _ list<json>
  make-symbol-select(b.name, symConstant, b.range, b.name-range, b.expr.maybe/symbols)

fun expr/symbols(ex: user-expr): _ list<json>
  match ex
    Lam(bs, e) -> bs.flatmap(lambinder/symbols) ++ e.expr/symbols
    Let(d, e) -> d.dg/symbols ++ e.expr/symbols
    Bind(d, e) -> d.def/symbols ++ e.expr/symbols
    App(e, args) -> e.expr/symbols ++ args.flatmap(fn((_, a)) a.expr/symbols)
    Ann(e) -> e.expr/symbols
    Case(e, bs) -> e.expr/symbols ++ bs.flatmap(branch/symbols)
    Parens(e) -> e.expr/symbols
    Handler(localPars=ps, initially=i, hReturn=rt, finally=f, branches=hbs) ->
      ps.flatmap(hpar/symbols) ++ i.maybe/symbols ++ rt.maybe/symbols ++ f.maybe/symbols ++
      hbs.flatmap(hb/symbols)
    Inject(e=e) -> e.expr/symbols
    Var(n, _, r) -> make-symbol(n, symVariable, r, [])
    Literal(l) -> l.lit/symbols

fun hpar/symbols(b: value-binder<maybe<user-type>, ()>): _ list<json>
  make-symbol-select(b.name, symConstant, b.range, b.name-range, [])

fun lit/symbols(l: lit): _ list<json>
  val (s, kind) = match l
    LitChar(c) -> (c.show, symConstant)
    LitInt(i) -> (i.show, symNumber)
    LitFloat(f) -> (f.float64/show, symNumber)
    LitString(v) -> (v.show, symString)
  val rng = l.range.range/to-lsp
  [JSObj([("name", JSString(s)), ("kind", JSInt(kind)),
          ("range", rng), ("selectionRange", rng)])]

fun hb/symbols(hb: user-handler-branch): _ list<json>
  val sel = hb.branchNameRange
  make-symbol-select(hb.branchName, symFunction, sel.range/combine(hb.branchExpr.range), sel,
                     hb.branchPars.flatmap(hpar/symbols) ++ hb.branchExpr.expr/symbols)

fun branch/symbols(b: user-branch): _ list<json>
  b.branchPattern.pat/symbols ++ b.branchGuard.flatmap(guard/symbols)

fun guard/symbols(g: user-guard): _ list<json>
  g.guardTest.expr/symbols ++ g.guardExpr.expr/symbols

fun pat/symbols(p: user-pattern): _ list<json>
  match p
    PatVar(b) -> make-symbol(b.name, symConstant, b.range, [])
    PatAnn(p') -> p'.pat/symbols
    PatCon(args=as') -> as'.flatmap(fn((_, q)) q.pat/symbols)
    PatParens(p') -> p'.pat/symbols
    PatLit(l) -> l.lit/symbols
    PatWild -> []

//----------------------------------------------------------------------
// folding ranges
//----------------------------------------------------------------------

// A fold that starts and ends on the same line is
// not a fold, and clients render it as a stray marker
fun spans-line(r: range): bool
  r.start.line != r.end.line

fun make-folding-no-name(r: range): _ list<json>
  if !r.spans-line then []
  else [JSObj([("startLine", JSInt(max(0, r.start.line - 1))),
               ("startCharacter", JSInt(max(0, r.start.col - 1))),
               ("endLine", JSInt(max(0, r.end.line - 1))),
               ("endCharacter", JSInt(max(0, r.end.col - 1) + 1)),
               ("kind", JSString("region"))])]

fun make-folding(r: range, n: name): _ list<json>
  if !r.spans-line then []
  else [JSObj([("startLine", JSInt(max(0, r.start.line - 1))),
               ("startCharacter", JSInt(max(0, r.start.col - 1))),
               ("endLine", JSInt(max(0, r.end.line - 1))),
               ("endCharacter", JSInt(max(0, r.end.col - 1) + 1)),
               ("kind", JSString("region")),
               ("collapsedText", JSString(n.nameStem))])]

pub fun program/foldings(p: user-program): _ list<json>
  p.typedefs.flatmap(tdg/foldings) ++ p.defs.flatmap(dg/foldings)

fun tdg/foldings(g: user-typedef-group): _ list<json>
  match g
    TypeDefRec(ds) -> ds.flatmap(td/foldings)
    TypeDefNonRec(d) -> d.td/foldings

fun td/foldings(td: user-typedef): _ list<json>
  make-folding(td.range, td.binder.name)

fun dg/foldings(g: user-def-group): _ list<json>
  match g
    DefRec(ds) -> ds.flatmap(def/foldings)
    DefNonRec(d) -> d.def/foldings

fun def/foldings(d: user-def): _ list<json>
  make-folding(d.range, d.binder.name) ++ d.binder.expr.expr/foldings

fun lambinder/foldings(b: value-binder<maybe<user-type>, maybe<user-expr>>): _ list<json>
  make-folding(b.range, b.name) ++ b.expr.maybe/foldings

fun hpar/foldings(b: value-binder<maybe<user-type>, ()>): _ list<json>
  make-folding(b.range, b.name)

fun maybe/foldings(m: maybe<user-expr>): _ list<json>
  match m
    Nothing -> []
    Just(e) -> e.expr/foldings

fun expr/foldings(ex: user-expr): _ list<json>
  match ex
    Lam(bs, e, _, r) -> bs.flatmap(lambinder/foldings) ++ e.expr/foldings ++ make-folding-no-name(r)
    Let(d, e) -> d.dg/foldings ++ e.expr/foldings
    Bind(d, e, r) -> d.def/foldings ++ e.expr/foldings ++ make-folding(r, d.binder.name)
    App(e, args) -> e.expr/foldings ++ args.flatmap(fn((_, a)) a.expr/foldings)
    Ann(e, _, r) -> e.expr/foldings ++ make-folding-no-name(r)
    Case(e, bs, _, r) -> e.expr/foldings ++ bs.flatmap(branch/foldings) ++ make-folding-no-name(r)
    Parens(e) -> e.expr/foldings
    Handler(localPars=ps, initially=i, hReturn=rt, finally=f, branches=hbs, range=r) ->
      ps.flatmap(hpar/foldings) ++ i.maybe/foldings ++ rt.maybe/foldings ++ f.maybe/foldings ++
      hbs.flatmap(hb/foldings) ++ make-folding-no-name(r)
    Inject(e=e) -> e.expr/foldings
    _ -> []

fun hb/foldings(hb: user-handler-branch): _ list<json>
  val r = hb.branchNameRange.range/combine(hb.branchExpr.range)
  make-folding(r, hb.branchName) ++ hb.branchPars.flatmap(hpar/foldings) ++ hb.branchExpr.expr/foldings

fun branch/foldings(b: user-branch): _ list<json>
  b.branchGuard.flatmap(guard/foldings)

fun guard/foldings(g: user-guard): _ list<json>
  g.guardTest.expr/foldings ++ g.guardExpr.expr/foldings

// Both handlers answer from the last check's parsed program; before the first
// check completes there is none, and `null` is the correct LSP answer.
pub fun with-program(st: server-state, ps: json, f: (user-program) -> _ list<json>): _ json
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Just(d) -> match d.prog
      Just(pr) -> JSList(f(pr))
      Nothing -> JSNull
    Nothing -> JSNull
