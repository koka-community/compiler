// API documentation (`--html`): the `.xmp.html` file.
//
// Ports upstream `Syntax/GenDoc.hs`. Where `colorize.kk` renders a module's
// SOURCE, this renders its INTERFACE: a module heading, its public imports, a
// table of contents, and an entry per public type and definition carrying its
// signature and doc comment.
//
// It works from CORE rather than the syntax tree, because core is what carries
// resolved types and the visibility that decides what is public.
//
// The structural work upstream does, and this reproduces:
//   * externals are turned into ordinary defs so they document like functions
//   * every def is ASSOCIATED with a type when it mentions that type in its
//     name, its first parameter, or its result -- so `push`/`pop` nest under
//     `stack` instead of drifting into a flat alphabetical list
//   * the table of contents is split into columns by a size heuristic
//   * the module doc splits at its first blank line into a synopsis and a body
//
// All HTML primitives come from `colorize.kk`.
module compiler/syntax/gen-doc

import std/core/undiv
import std/data/sort
import compiler/common/name
import compiler/common/name-prim
import compiler/common/syntax
import compiler/common/range
import compiler/kind/kind
import compiler/kind/pretty
import compiler/type/type
import compiler/type/assumption
import compiler/kind/assumption
import compiler/type/pretty
import compiler/core/core
import compiler/syntax/highlight
import compiler/syntax/range-map
import compiler/syntax/colorize
import compiler/lib/pprint

//----------------------------------------------------------------------
// small helpers
//----------------------------------------------------------------------

// Upstream's GenDoc SHADOWS `Colorize.doctag`/`Colorize.atag` with versions
// that do NOT prepend the `doc ` class -- so a declaration is `class="decl"`
// here where a doc comment (rendered by Colorize's `showDoc`) is
// `class="doc koka comment"`.  Koka has no shadowing across modules, so they
// get their own names.
fun dtag(t: string, cls: string, content: string): string
  ptag(t, cls, content)

fun dlink(link: string, content: string): string
  dtag("a", "link\" href=\"" ++ link, content)

fun nice-name-id(nm: name): _ string
  fmt-name(nm.unqualify)

fun nice-type-name(nm: name): _ string
  fmt-type-name(nm.unqualify)

// The anchor for this name in its module's own
// rendered source page.
fun link-to-source(mname: name): _ string
  if !mname.is-qualified then ""
  else mname.nameModule.list.map(fn(c) if c == '/' then "_" else c.string).join ++
       "-source.html#" ++ link-encode(mname.name/local)

// upstream sorts on `show . defName`, and `show` is `showExplicit`, which
// writes a LOCALLY QUALIFIED name with `/#` (`doc/#stack/items`). The `#`
// sorts before any letter, so a type's accessors come before its other
// definitions -- `show-plain` would order them alphabetically instead.
fun sort-on-name(xs: list<a>, f: (a) -> e name): e list<a>
  xs.sort(?(<) = fn(x, y) f(x).name/name/show < f(y).name/name/show)

//----------------------------------------------------------------------
// types, rendered
//----------------------------------------------------------------------

// A rendered type is itself Koka, so it goes back
// through the highlighter with a TYPE context -- and through `fmtLiterate`, so
// each name in it is resolved against kgamma/gamma and linked to its
// definition.
// what `show-doc` and the literate formatter need, as one value
fun lit-env(): _ maybe<(html-env, gamma, kGamma)>
  Just((genv, ggamma, gkgamma))

fun doc/show-doc(doc: string): _ string
  colorize/show-doc(doc, lit-env())

fun highlight-type(s: string): _ string
  highlight-fragment-literate(genv, ggamma, gkgamma, CtxType([], ":"), html/compress(s))

// One shared nice-name environment across the whole list,
// so `a` means the same thing in a type header and in its constructors.
fun show-types(tps: list<ktype>): _ list<string>
  tps.nice-types-default.map(fn(d) highlight-type(d.pprint/show))

fun angled(xs: list<string>): string
  if xs.is-nil then "" else "&lt;" ++ xs.join(",") ++ "&gt;"

fun parenthesized(xs: list<string>): string
  if xs.is-nil then "" else "(" ++ xs.join(",&nbsp;") ++ ")"

// A field name is synthesized, so it is not shown.
fun show-param((nm, _tp): (name, ktype), tps: list<string>, idx: int): _ string
  val tdoc = match tps.drop(idx) { Cons(s) -> s; Nil -> "" }
  (if nm.is-field-name then ""
   else cspan("param", fmt-name(nm)) ++ " " ++ cspan("type special", ":") ++ "&nbsp;") ++ tdoc

// The signature written the way it is DECLARED --
// parameters broken out with their own names, rather than as one arrow type.
fun show-decl-type(pinfos: list<param-info>, tp: ktype): _ string
  val colon = cspan("type special", ":") ++ "&nbsp;"
  fun hl-param(nm: name)
    if nm.is-nil || nm.is-field-name || nm.is-hidden-name then ""
    else cspan("type typeparam", fmt-name(nm)) ++ " " ++ colon
  fun hl-borrow(pinfo: param-info)
    match pinfo
      Borrow -> highlight-type("^")
      _ -> ""
  with with-pretty-env
  match tp.pp-decl-type(pinfos)
    (Nothing, _pre, res) -> colon ++ highlight-type(res.pprint/show)
    (Just(params), _pre, res) ->
      val ps = params.map fn((nm, pinfo, tdoc))
        hl-borrow(pinfo) ++ hl-param(nm) ++ highlight-type(tdoc.pprint/show)
      (if ps.is-nil then "()" else "( " ++ ps.join(", ") ++ " )") ++ " " ++ colon ++
        highlight-type(res.pprint/show)

//----------------------------------------------------------------------
// module documentation (upstream `splitModuleDoc` / `showModuleDoc`)
//----------------------------------------------------------------------

// A module's doc comment is two parts: everything up to the first BLANK line is
// a one-line synopsis (shown next to the module in an import table), and the
// rest is the body.
fun split-module-doc(doc: string): _ (string, string)
  fun extract(acc: list<char>, cs: list<char>): div (string, string)
    match cs
      Nil -> (acc.reverse.string, "")
      Cons('\n', rest) ->
        match rest.drop-while(fn(c) c == ' ' || c == '\t')
          Cons('\n', rest') -> (acc.reverse.string, rest'.string)
          _ -> extract(Cons('\n', acc), rest)
      Cons(c, rest) -> extract(Cons(c, acc), rest)
  val (pre, post) = extract([], doc.remove-comment.list.drop-while(is-white))
  (pre.html/capitalize,
   Cons('.', post.list.reverse.drop-while(fn(c) c == '.' || c.is-white)).reverse.string)

fun show-module-doc(doc: string): _ string
  val (pre, post) = doc.split-module-doc
  doc/show-doc(dtag("h1", "synopsis", pre) ++ "\n\n" ++ post)

fun synopsis(doc: string): _ string
  doc/show-doc(doc.split-module-doc.fst)

//----------------------------------------------------------------------
// imports (upstream `fmtImports` and its root-sharing walk)
//----------------------------------------------------------------------

fun indent-span(n: int, s: string): _ string
  span("nested" ++ n.show, s)

fun limit(n: int, s: string): string
  if s.count <= n then fmt-name-string(s)
  else fmt-name-string(s.first(n).string) ++ "&hellip;"

// The import table shares common path prefixes down the rows: after a row for
// `std/core/list`, a following `std/core/vector` prints only its last segment
// under the same `std/core` heading. `root` is the prefix the previous row
// established.
fun fmt-import-entries(root: list<string>, imps: list<kimport>): _ list<string>
  match imps
    Nil -> []
    Cons(imp, rest) ->
      val (root', entry) = fmt-import-entry(root, imp)
      Cons(entry, fmt-import-entries(root', rest))

fun fmt-import-entry(root: list<string>, imp: kimport): _ (list<string>, string)
  // walk `root` against the import's path segments: either they agree all the
  // way to the last segment (emit the row) or they diverge, and the divergent
  // segment needs its own heading row first.
  fun common(rootc: list<string>, rt: list<string>, parts: list<string>): div either<(list<string>, string), (list<string>, string)>
    match parts
      Cons(nm, Nil) -> Right((rootc, nm))
      Cons(pre, post) ->
        match rt
          Nil -> Left((rootc, pre))
          Cons(rpre, rpost) ->
            if rpre == pre then common(rootc ++ [rpre], rpost, post)
            else Left((rootc, pre))
      Nil -> Right((rootc, ""))
  match common([], root, imp.importName.show-plain.split("/"))
    Right((root-common, nm)) -> (root-common ++ [nm], fmt-import(root-common, nm, imp))
    Left((root-common, pre)) ->
      val (root', entry) = fmt-import-entry(root-common ++ [pre], imp)
      (root', dtag("tr", "", dtag("td", "code", indent-span(root-common.length, pre))) ++ "\n" ++ entry)

fun fmt-import(root: list<string>, nm: string, imp: kimport): _ string
  dtag("tr", "",
    dtag("td", "code",
      indent-span(root.length,
        dlink(link-from-mod-name(genv, imp.importName, ""), span("module", limit(15, nm))))) ++
    dtag("td", "", synopsis(imp.doc)))

fun fmt-imports(imps: list<kimport>): _ string
  dtag("table", "index",
    fmt-import-entries([], imps.sort-on-name(fn(i) i.importName)).unlines)

fun fmt-import-module-name(qname: name): _ string
  genv.signature(True, True, "module", qname, qname.qualify(name/nil),
                  span("module", fmt-module-name(qname)),
                  cspan("namespace", fmt-module-name(qname)))

fun fmt-private-imports(imps: list<kimport>): _ string
  if imps.is-nil then ""
  else dtag("div", "decl\" id=\"-private-imports",
    dtag("div", "header code",
      dtag("span", "def",
        cspan("keyword", "private import") ++ "&nbsp;" ++
        imps.map(fn(i) dtag("span", "code", fmt-import-module-name(i.importName))).join(", "))))

//----------------------------------------------------------------------
// table of contents
//----------------------------------------------------------------------

fun toc-link(anchor: name, content: string): _ string
  dtag("a", "link\" href=\"#" ++ link-encode(anchor.name/local), content)

fun fmt-def-toc(nested: bool, d: def): _ string
  dtag("li", if nested then "nested" else "",
    toc-link(mangle(d.def-name, d.ktype),
      cspan("keyword", d.sort.defsort/show) ++ "&nbsp;" ++ nice-name-id(d.def-name)))

fun fmt-con-toc(ci: con-info): _ string
  dtag("li", "nested",
    toc-link(ci.name.mangle-con-name,
      cspan("keyword", "con") ++ "&nbsp;" ++ cspan("constructor", nice-name-id(ci.name))))

fun fmt-type-def-toc((td, ds): (typedef, list<def>)): _ list<string>
  match td
    Synonym(info) ->
      Cons(dtag("li", "",
             toc-link(info.name.mangle-type-name,
               cspan("keyword", "alias") ++ "&nbsp;" ++ cspan("type", nice-type-name(info.name))) ++ "\n"),
           ds.map(fn(d) fmt-def-toc(True, d)))
    Data(info) ->
      if info.is-struct then
        Cons(dtag("li", "",
               toc-link(info.name.mangle-type-name,
                 cspan("keyword", "struct") ++ "&nbsp;" ++ cspan("type", nice-type-name(info.name))) ++ "\n"),
             ds.map(fn(d) fmt-def-toc(True, d)))
      else
        Cons(dtag("li", "",
               toc-link(info.name.mangle-type-name,
                 cspan("keyword", info.data-keyword-plain) ++ "&nbsp;" ++ span("type", nice-type-name(info.name))) ++ "\n"),
             info.public-constrs.map(fmt-con-toc) ++ ds.map(fn(d) fmt-def-toc(True, d)))

// upstream's column heuristic: keep the table of contents roughly square, and
// never taller than `max-rows`.
fun toc-split(fmts: list<string>): _ list<list<string>>
  fun split(n: int, xs: list<string>): div list<list<string>>
    if xs.is-nil then []
    else Cons(xs.take(n), split(n, xs.drop(n)))
  val n = fmts.length
  val nice-rows = 20
  val nice-col = 4
  val max-rows = 31
  if n <= nice-col * nice-rows then
    if 2 * n <= nice-rows then [fmts]
    elif n <= nice-rows then split((n / 2) + 1, fmts)
    elif n <= 2 * nice-rows then split((n / 3) + 1, fmts)
    else split(nice-rows, fmts)
  else split(max-rows, fmts)

//----------------------------------------------------------------------
// declarations
//----------------------------------------------------------------------

fun data-keyword-plain(info: data-info): string
  if info.kind.has-kind-label-result then "effect" else info.sort.datakind/show

fun data-keyword(info: data-info): string
  if info.kind.has-kind-label-result then "effect"
  else info.sort.datakind/show ++
       (if info.is-extend then "&nbsp;extend" elif info.is-open then "&nbsp;open" else "")

// a single-constructor inductive type whose constructor shares its name is a
// `struct`, and prints as one
fun is-struct(info: data-info): bool
  match (info.sort, info.constrs)
    (Inductive, Cons(ci, Nil)) -> ci.name == info.name
    _ -> False

fun public-constrs(info: data-info): list<con-info>
  info.constrs.filter(fn(ci) !ci.name.is-hidden-name)

fun fmt-defs(ds: list<def>): _ string
  if ds.is-nil then "" else dtag("div", "nested", ds.map(fmt-def).join)

fun fmt-def(d: def): _ string
  val mname = mangle(d.def-name, d.ktype)
  dtag("div", "decl\" id=\"" ++ link-encode(mname.name/local),
    dtag("div", "header code",
      dtag("span", "def",
        cspan("keyword", d.sort.defsort/show) ++ "&nbsp;" ++
        dtag("a", "link\" href=\"" ++ link-to-source(mname), nice-name-id(d.def-name))) ++
      show-decl-type(d.param-infos, d.ktype)) ++
    doc/show-doc(d.doc))

fun fmt-constructor(ci: con-info): _ string
  // the existentials and the field types share one nice-name environment
  val tps = (ci.existentials.map(TVar) ++ ci.params.map(snd)).show-types
  val nex = ci.existentials.length
  dtag("div", "con-decl\" id=\"" ++ link-encode(ci.name.mangle-con-name.name/local),
    dtag("div", "header code",
      dtag("span", "def",
        cspan("keyword", "con") ++ "&nbsp;" ++
        dtag("a", "link\" href=\"" ++ link-to-source(ci.name.mangle-con-name),
               cspan("constructor", nice-name-id(ci.name)))) ++
      angled(tps.take(nex)) ++
      parenthesized(ci.params.map-indexed(fn(i, p) show-param(p, tps, nex + i)))) ++
    doc/show-doc(ci.doc))

fun type-anchor(nm: name, knd-html: string, content: string): _ string
  genv.signature(False, True, "kind", nm, nm.mangle-type-name, knd-html, content)

fun fmt-type-def((td, ds): (typedef, list<def>)): _ string
  match td
    Synonym(info) ->
      val tps = Cons(info.tp, info.params.map(TVar)).show-types
      dtag("div", "decl\" id=\"" ++ link-encode(info.name.mangle-type-name.name/local),
        dtag("div", "header code",
          dtag("span", "def",
            cspan("keyword", "alias") ++ "&nbsp;" ++
            cspan("type", type-anchor(info.name, show-kind(info.kind),
                                      cspan("type", nice-type-name(info.name))))) ++
          cspan("type", angled(tps.drop(1))) ++
          "&nbsp;" ++ cspan("keyword", "=") ++ "&nbsp;" ++
          (match tps { Cons(t) -> t; Nil -> "" })) ++
        doc/show-doc(info.doc) ++
        fmt-defs(ds))
    Data(info) ->
      if info.is-struct then
        val ci = match info.constrs { Cons(c) -> c; Nil -> return "" }
        val tps = (info.params.map(TVar) ++ ci.params.map(snd)).show-types
        val np = info.params.length
        dtag("div", "decl\" id=\"" ++ link-encode(info.name.mangle-type-name.name/local),
          dtag("div", "header code",
            dtag("span", "def",
              cspan("keyword", "struct") ++ "&nbsp;" ++
              cspan("type", type-anchor(info.name, show-kind(info.kind),
                                        cspan("type", nice-type-name(info.name))))) ++
            cspan("type", angled(tps.take(np))) ++
            parenthesized(ci.params.map-indexed(fn(i, p) show-param(p, tps, np + i)))) ++
          doc/show-doc(info.doc) ++
          fmt-defs(ds))
      else
        val tps = info.params.map(TVar).show-types
        dtag("div", "decl\" id=\"" ++ link-encode(info.name.mangle-type-name.name/local),
          dtag("div", "header code",
            dtag("span", "def",
              cspan("keyword", info.data-keyword) ++ "&nbsp;" ++
              cspan("type", genv.signature(info.is-extend, True, "kind", info.name,
                                            info.name.mangle-type-name, show-kind(info.kind),
                                            cspan("type", nice-type-name(info.name))))) ++
            cspan("type", angled(tps))) ++
          doc/show-doc(info.doc) ++
          info.public-constrs.map(fmt-constructor).join ++
          fmt-defs(ds))

//----------------------------------------------------------------------
// associating definitions with their types
//----------------------------------------------------------------------

// upstream's three association tests, applied in order (name, then first
// argument, then result). A def that matches a type is documented UNDER that
// type rather than in the flat list.
fun self-name(tc: type-con, d: def): bool
  tc.type-con/name == d.def-name

fun head-tcon(tp: ktype): maybe<type-con>
  match tp
    TCon(tc) -> Just(tc)
    TApp(TCon(tc), _) -> Just(tc)
    _ -> Nothing

fun self-arg(tc: type-con, d: def): _ bool
  val (_, rho) = d.ktype.split-type-scheme
  match rho.split-fun-type
    Just((Cons((_, ptp), _), _, _)) -> ptp.head-tcon == Just(tc)
    Just(_) -> False
    Nothing -> rho.head-tcon == Just(tc)   // for constant values

fun self-result(tc: type-con, d: def): _ bool
  val (_, rho) = d.ktype.split-type-scheme
  match rho.split-fun-type
    Just((_, _, res)) ->
      match res
        TCon(rtc) -> rtc == tc && !TCon(rtc).is-type-unit
        TApp(TCon(rtc), _) -> rtc == tc
        _ -> False
    Nothing -> False

fun tcon-of(td: typedef): type-con
  match td
    Data(info) -> TypeCon(info.name, info.kind)
    Synonym(info) -> TypeCon(info.name, info.kind)

// One association pass: each typedef claims, in order, the defs that satisfy
// `f`; whatever no typedef claims stays in the flat list.
fun assoc-pass(f: (type-con, def) -> _ bool, st: (list<def>, list<(typedef, list<def>)>)): _ (list<def>, list<(typedef, list<def>)>)
  val (ds0, tdds0) = st
  fun step((td, owned): (typedef, list<def>), (ds, tdds): (list<def>, list<(typedef, list<def>)>))
    val tc = td.tcon-of
    val (mine, rest) = ds.partition(fn(d) f(tc, d))
    (rest, Cons((td, owned ++ mine), tdds))
  tdds0.foldr((ds0, []), step)

//----------------------------------------------------------------------
// the document
//----------------------------------------------------------------------

// Upstream threads its `Env` record through every formatter. The port makes it
// an effect value instead, so the formatters below read it without each taking
// a parameter it only forwards.
effect val genv: html-env

// upstream threads `kgamma`/`gamma` alongside `Env` through every formatter;
// they are what turn a name inside a rendered type into a link.
effect val ggamma: gamma
effect val gkgamma: kGamma

pub fun gen-doc(c: core, kgam: kGamma, gam: gamma, env: html-env = Html-env(name/nil),
                css: list<string> = [], js: string = ""): _ list<string>
  with val genv = env
  with val ggamma = gam
  with val gkgamma = kgam
  // externals document exactly like functions, so make them defs
  val ext-defs = c.externals.flatmap fn(e)
    match e
      External(nm, tp, params, _fmt, evis, _fip, rng, edoc) ->
        [Def(nm, tp, exprUnit, evis, DefFun(params), InlineAuto, rng, edoc)]
      _ -> []
  val all-defs = (c.defs.flatten ++ ext-defs)
                   .filter(fn(d) d.vis.is-public && !d.def-name.is-hidden-name)
  val all-tdefs = c.typedefs.flatten
                    .filter(fn(td) td.vis.is-public && !td.td/name.is-hidden-name)
                    .map(filter-con)
                    .sort-on-name(td/name)
  val no-declarations = all-defs.is-nil && all-tdefs.is-nil

  // three association passes, applied result-first so that the LAST one to run
  // (self-name) has the final say
  val (flat0, grouped0) =
    assoc-pass(self-result, assoc-pass(self-arg, assoc-pass(self-name,
      (all-defs, all-tdefs.map(fn(td) (td, []))))))
  val other-defs = flat0.sort-on-name(def-name)
  val type-defs = grouped0.map(fn((td, ds)) (td, ds.sort-on-name(def-name)))

  val (pub-imports, priv-imports) = c.imports.partition(fn(i) i.visibility.is-public)

  val toc-fmts =
    type-defs.flatmap(fmt-type-def-toc) ++
    (if other-defs.is-nil || type-defs.is-nil then [] else [dtag("li", "", "&nbsp;")]) ++
    other-defs.map(fn(d) fmt-def-toc(False, d))

  val body =
    [ptag("h1", "",
       dlink(link-from-mod-name(genv, c.coreName, "-source"),
            span("module", fmt-module-name(c.coreName))) ++
       dlink("toc.html", span("toc-link", "&#x25b2;toc")))] ++
    (if pub-imports.is-nil then [] else [fmt-imports(pub-imports)]) ++
    (if no-declarations then []
     else [dtag("div", "toc code",
             toc-fmts.toc-split.filter(fn(col) !col.is-nil)
               .map(fn(col) dtag("ul", "toc", col.join)).join)]) ++
    [show-module-doc(c.doc)] ++
    type-defs.map(fmt-type-def) ++
    other-defs.map(fmt-def) ++
    [fmt-private-imports(priv-imports)]

  html-header(c.coreName.show-plain, css, js) ++ body ++ html-footer

fun filter-con(td: typedef): _ typedef
  match td
    Data(info) ->
      Data(info(constrs = info.constrs.filter(fn(ci) ci.vis.is-public).sort-on-name(fn(ci) ci.name)))
    _ -> td
