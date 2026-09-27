// Syntax-highlighted HTML output (`--html`).
//
// Ports upstream `Syntax/Colorize.hs`. The heavy lifting -- deciding what KIND
// each lexeme is in context (a type variable? a constructor? a keyword that is
// really an operator?) -- already lives in `syntax/highlight.kk`; this module
// only decides how to render each classified token.
//
// Upstream passes that renderer as a `fmtFun` argument; the port makes it the
// `fmt` EFFECT, so a different rendering is just a different handler. The
// console highlighter installs one that writes ANSI colours, and this module
// installs one that writes HTML spans.
//
// Upstream's `removeComment` is in `lsp/pretty.kk` instead, which is where the
// language server needs it.
module compiler/syntax/colorize

import std/core/undiv
import std/os/path
import compiler/common/name
import compiler/common/name-prim
import compiler/common/file
import compiler/platform/config
import compiler/syntax/lexeme
import compiler/syntax/highlight
import compiler/common/range
import compiler/kind/kind
import compiler/kind/pretty
import compiler/type/type
import compiler/type/pretty
import compiler/common/name-collections
import compiler/kind/assumption
import compiler/type/assumption
import compiler/syntax/range-map
import compiler/lib/pprint

//----------------------------------------------------------------------
// HTML primitives (upstream's `tag`/`span`/`escape` family)
//----------------------------------------------------------------------

pub fun escape(c: char): string
  match c
    '<' -> "&lt;"
    '>' -> "&gt;"
    '&' -> "&amp;"
    // escaped for markdown inside <code>
    '*' -> "&#42;"
    '_' -> "&#95;"
    '`' -> "&#96;"
    _   -> c.string

pub fun escapes(s: string): string
  s.list.map(escape).join

// upstream shortens class names because it saves a LOT: std/core's source went
// from 1.4mb to about 1mb on this alone.
// upstream `shorthands` (Colorize.hs:603), verbatim. Note it deliberately does
// NOT shorten every class -- `comment`, `number` and others stay as they are.
val shorthands: list<(string, string)> = [
  ("keyword", "kw"),
  ("operator", "op"),
  ("type", "tp"),
  ("string", "st"),
  ("module", "mo"),
  ("identifier", "id"),
  ("namespace", "mo"),
  ("constructor", "co"),
  ("typeparam", "tpp"),
  ("typevar", "tv"),
  ("special", "sp"),
  ("delimiter", "dl"),
  ("localqualifier", "lq")]

// upstream is `unwords (map shortenWord (words classnames))`. `words` DROPS
// empty fields, so the trailing space `class-prefix` adds (`"koka "`) is
// trimmed here rather than emitted as `class="koka "`. Splitting on `" "`
// keeps that empty field, so filter it out.
fun shorten(classnames: string): string
  fun short(w: string): string
    match shorthands.lookup(fn(k) k == w)
      Just(sh) -> sh
      Nothing -> w
  classnames.split(" ").filter(fn(w) !w.is-empty).map(short).join(" ")

fun start-tag(nm: string, cls: string): string
  "<" ++ nm ++ (if cls.is-empty then "" else " class=\"" ++ cls.shorten ++ "\"") ++ ">"

fun end-tag(nm: string): string
  "</" ++ nm ++ ">"

pub fun tag(nm: string, cls: string, content: string): string
  start-tag(nm, cls) ++ content ++ end-tag(nm)

pub fun ptag(t: string, cls: string, content: string): string
  tag(t, cls, content)

pub fun span(cls: string, content: string): string
  tag("span", cls, content)

// Syntax highlighting only, so no program-name prefix -- that
// is deliberate, to keep the generated HTML small
pub fun cspan(cls: string, content: string): string
  tag("span", cls, content)

pub fun atag(link: string, content: string): string
  doctag("a", "link\" href=\"" ++ link, content)

// upstream's `prefix`, renamed because `prefix` is a reserved word in Koka.
// A function, not a value: it reads the program name from `comp-flags`.
pub fun class-prefix(): _ string
  comp-flags.programName ++ " "

//----------------------------------------------------------------------
// token -> HTML
//----------------------------------------------------------------------

pub fun fmt-html(token: token<lexeme>, s: string): _ string
  match token
    // upstream routes every NAME through `fmtNameString` (which escapes, and
    // wraps `-`/`_`/`/` in their own spans) and operators through
    // `fmtOpString`. Emitting `s` raw left `<` and `&` unescaped, so a type
    // operator like `<$` produced broken HTML.
    TokId -> fmt-name-string(s)
    TokOp -> cspan("operator", fmt-op-string(s))
    TokTypeVar -> cspan("type typevar", fmt-name-string(s))
    TokTypeId -> cspan("type", fmt-name-string(s))
    TokTypeOp -> cspan("type operator", fmt-name-string(s))
    TokTypeKeyword ->
      if !s.is-keyword-op then cspan("type keyword", s) else cspan("type keyword operator", s)
    TokTypeSpecial -> cspan("type special", s.escapes)
    TokTypeParam -> cspan("type typeparam", fmt-name-string(s))
    TokModule -> cspan("namespace", fmt-name-string(s))
    TokCons -> cspan("constructor", fmt-name-string(s))
    TokNumber -> cspan("number", s)
    TokString -> cspan("string", s.escapes)
    TokSpecial -> s.escapes
    TokKeyword ->
      if !s.is-keyword-op then cspan("keyword", s) else cspan("keyword operator", s)
    TokComment -> cspan("comment", s.escapes)
    TokWhite -> s
    TokError -> s.escapes
    TokRichComment -> cspan("comment", s.escapes)

//----------------------------------------------------------------------
// name formatting (upstream `fmtName` / `fmtNameString`)
//----------------------------------------------------------------------

// Each separator gets its own span so the stylesheet can render a
// non-breaking hyphen, a raised slash, and so on.
pub fun fmt-name-string(s: string): string
  fun show-char(c: char): string
    match c
      '-' -> cspan("dash", "-")
      '_' -> cspan("underscore", "_")
      '/' -> cspan("fslash", "/")
      _   -> c.string
  s.escapes.list.map(show-char).join

pub fun fmt-op-string(s: string): string
  match s
    "/" -> cspan("divide", "/")
    "-" -> cspan("minus", "-")
    _   -> s.escapes

pub fun fmt-name(nm: name): _ string
  if nm.is-implicit-param-name then
    cspan("localqualifier", "?") ++ fmt-name(nm.from-implicit-param-name)
  else
    val lqual = nm.nameLocalQual
    val stem = fmt-name-string(nm.unqualify-full.show)
    (if lqual.is-empty then "" else cspan("localqualifier", fmt-name-string(lqual ++ "/"))) ++ stem

pub fun fmt-module-name(nm: name): _ string
  fmt-name-string(nm.show-plain)

pub fun fmt-type-name(nm: name): _ string
  fmt-name-string(nm.show-plain)

//----------------------------------------------------------------------
// links and popups (upstream `linkBase` / `popup` / `signature`)
//----------------------------------------------------------------------

// What the rendered page needs to know about its own context: which module it
// is (so a link to that module is a bare anchor) and any configured link
// prefixes for other packages.
pub struct html-env
  // `context` upstream; renamed because it is a reserved word in Koka
  ctx-module: name
  html-bases: list<(string, string)> = []
  literate: bool = False

// `postfix` is a reserved word in Koka, hence `suffix`
pub fun link-base-x(env: html-env, modname: string, suffix: string): string
  val base = match env.html-bases.filter(fn((p, _)) modname.starts-with(p).bool)
    Cons((_, base), _) -> base
    Nil -> ""
  base ++ ascii-encode(modname, True) ++ suffix ++ ".html"

pub fun link-encode(s: string): string
  ascii-encode(s, False)

// The page for another module (`""`), or that
// module's rendered source (`"-source"`).
pub fun link-from-mod-name(env: html-env, qname: name, suffix: string): string
  env.link-base-x(qname.show-plain, suffix)

// The content, with the signature tucked in a `pc` span that
// the stylesheet reveals on hover.
fun popup(link: string, pop: string, content: string): string
  tag("a", "pp" ++ (if link.is-empty then "" else "\" href=\"" ++ link), content ++ tag("span", "pc", pop))

// upstream `signature env toLit isLiterate knd qname mname scontent content`.
// `is-literate` is a genuine PARAMETER upstream, not a property of the env:
// the source colorizer passes `env.literate`, but GenDoc always passes `True`
// so a documentation page links to the module's rendered SOURCE rather than
// emitting a bare same-page anchor.
pub fun signature(env: html-env, to-lit: bool, is-literate: bool, knd: string, qname: name, mname: name,
              scontent: string, content: string): _ string
  val desc = if knd == "module" then "" else
    (if qname.is-qualified
       then cspan("namespace", fmt-name-string(qname.nameModule) ++ cspan("fslash last", "/")) ++ fmt-name(qname.unqualify)
       else fmt-name(qname)) ++ ": "
  val link-to =
    if !mname.is-qualified then ""
    else
      (if env.ctx-module == qname.qualifier && to-lit == is-literate then ""
       else link-base-x(env, mname.nameModule, if to-lit then "" else "-source")) ++
      // upstream `linkEncode (nameLocal mname)` -- `nameLocal` keeps the LOCAL
      // QUALIFIER (`string/println`), which encodes to `string_fs_println`.
      // Using the bare stem produced an anchor that matches nothing.
      (if mname.is-nil then "" else "#" ++ link-encode(mname.name/local))
  popup(link-to, desc ++ scontent, content)

//----------------------------------------------------------------------
// the literate formatter
//----------------------------------------------------------------------

// `fmt-html` renders a classified token; this renders it AND resolves the name
// it carries, so a type or function mentioned in a signature becomes a link to
// its definition with a type popup.
//
// It is what `--html` uses for the text INSIDE a rendered type, where there is
// no range map to consult -- the type was printed from `core`, not lexed from
// the file, so the only way to know what `int` refers to is to look it up.
pub fun fmt-literate(env: html-env, gam: gamma, kgam: kGamma,
                     token: token<lexeme>, s: string): _ string
  val f = fmt-html(token, s)
  match token
    TokId(qid, tp) | qid.is-qualified || !tp.is-empty -> link-from-id(env, gam, qid, tp)
    TokOp(qid, tp) | qid.is-qualified || !tp.is-empty -> link-from-id(env, gam, qid, tp)
    TokTypeId(id) -> link-from-type-id(env, kgam, id, f)
    TokTypeOp(id) -> link-from-type-id(env, kgam, id, f)
    TokModule(mid) -> popup(link-from-mod-name(env, mid, ""), f, f)
    TokCons(qid) -> link-from-id(env, gam, qid, "")
    _ -> f

fun link-from-type-name-x(env: html-env, qname: name): string
  env.link-base-x(qname.nameModule, "") ++ "#" ++ link-encode(qname.name/local)

fun link-from-type-name(env: html-env, qname: name): string
  env.link-from-type-name-x(qname.mangle-type-name)

fun link-from-id-name(env: html-env, qname: name): string
  env.link-from-type-name-x(if qname.is-constructor-name then qname.mangle-con-name else qname)

pub fun link-from-type-id(env: html-env, kgam: kGamma, nm: name, content: string): _ string
  match kgam.qname-map/lookup(env.ctx-module, nm)
    Found((qname, TypeNameInfo(k, _doc))) ->
      env.signature(True, True, "kind", qname, qname.mangle-type-name, show-kind(k), content)
    _ -> if nm.is-qualified then atag(env.link-from-type-name(nm), content) else content

pub fun link-from-id(env: html-env, gam: gamma, nm: name, tp: string): _ string
  fun sig-for((qname, info): (name, type/assumption/name-info)): _ string
    match info
      InfoImport(fullName=_) ->
        env.signature(True, True, "module", qname, qname.qualify(name/nil),
                      show-module(qname), cspan("namespace", fmt-name(qname.unqualify)))
      InfoCon(conInfo=_) ->
        env.signature(True, True, "type", qname, qname.mangle-con-name,
                      show-type(info.scheme), cspan("constructor", fmt-name(qname.unqualify)))
      _ ->
        env.signature(True, True, "type", qname, mangle(qname, info.scheme),
                      show-type(info.scheme), fmt-name(qname.unqualify))
  // upstream falls back to a plain anchor (or bare text) when the name is
  // AMBIGUOUS -- there is no single definition to point at. The `tp` string
  // carried on the token is the printed type the highlighter recorded, and it
  // is what disambiguates an overload.
  fun unresolved(): _ string
    // `con` is a reserved word in Koka
    val as-con = fn(x: string) if nm.is-constructor-name then cspan("constructor", x) else x
    if nm.is-qualified then atag(env.link-from-id-name(nm), as-con(fmt-name(nm)))
    else as-con(fmt-name(nm.unqualify))
  match gam.gamma-lookup(nm)
    Cons(hit, Nil) -> sig-for(hit)
    results ->
      val filtered = if tp.is-empty then results
                     else results.filter(fn((_, i)) i.scheme.ktp/pretty-string == tp)
      match filtered
        Cons(hit, Nil) -> sig-for(hit)
        _ -> unresolved()

// `highlight-fragment`, but with names resolved to links.
pub fun highlight-fragment-literate(env: html-env, gam: gamma, kgam: kGamma,
                                    hctx: highlight-ctx, str: string): _ string
  var out := ""
  with handler
    val source-file = ""
    fun fmt(token, _lex, s)
      out := out ++ fmt-literate(env, gam, kgam, token, s)
      token
  highlight(id, hctx, 1, str)
  out

//----------------------------------------------------------------------
// rendering a type or kind INTO the popup
//----------------------------------------------------------------------

// Collapse runs of whitespace so a signature fits on the
// one line a popup gives it.
pub fun html/compress(s: string): div string
  fun go(acc: list<char>, cs: list<char>): div list<char>
    match cs
      Nil -> acc.reverse
      Cons(c, rest) ->
        if c.is-white then go(Cons(' ', acc), rest.drop-while(is-white))
        else go(Cons(c, acc), rest)
  go([], s.list).string

// The signature is itself Koka, so it goes back through the highlighter -- with
// a TYPE context, so `:`/`->` are classified as type syntax.
// `ctx` is a reserved word in Koka, hence `hctx`
pub fun highlight-fragment(hctx: highlight-ctx, str: string): _ string
  var out := ""
  with handler
    val source-file = ""
    fun fmt(token, _lex, s)
      out := out ++ fmt-html(token, s)
      token
  highlight(id, hctx, 1, str)
  out

pub fun show-type(tp: ktype): _ string
  highlight-fragment(CtxType([], ":"), html/compress(tp.ktp/pretty-string))

pub fun show-kind(k: kind): _ string
  // upstream `prettyKind`, not the raw `show`: the latter prints a kind arrow
  // as a prefix application (`(->) V V`) instead of infix (`V -> V`).
  highlight-fragment(CtxType([], "::"), html/compress(k.pretty-kind.pprint/show))

fun show-module(qname: name): _ string
  cspan("module", fmt-module-name(qname))

fun span-effect(k: kind, content: string): _ string
  if k == kindLabel || k == kindEffect then span("effect", content) else content

//----------------------------------------------------------------------
// the range-map transform
//----------------------------------------------------------------------

// Wrap one lexeme's HTML with whatever the range map says about it: a link and
// type popup for an identifier, an anchor for a declaration, an error/warning
// marker. Returns the ranges whose closing `</span>` is still owed.
fun transform1(env: html-env, lex: lexeme, acc: (list<range>, string),
               entry: (range, range-info)): _ (list<range>, string)
  val (ranges, content) = acc
  val (range, rinfo) = entry
  match rinfo
    RIId(qname, info, docs, isdef) ->
      // a definition site in ordinary source links back to the documentation
      val to-lit = env.literate || (qname.is-qualified && isdef)
      val pcontent = lex.highlight/show.escapes
      fun pdocs(str: string): _ string
        str ++ docs.map(fn(d) "<br>" ++ d.pprint/show).join
      val is-kw = match lex
        Lexeme(_, LexKeyword) -> True
        _ -> False
      val body = match info
        NIValue(_, tp) ->
          signature(env, to-lit, env.literate, "type", qname, mangle(qname, tp), pdocs(show-type(tp)),
                    if is-kw then cspan("keyword", pcontent) else pcontent)
        NICon(tp) ->
          signature(env, to-lit, env.literate, "type", qname, qname.mangle-con-name, pdocs(show-type(tp)),
                    cspan("constructor", pcontent))
        NITypeVar(k) ->
          signature(env, to-lit, env.literate, "kind", qname, qname, pdocs(show-kind(k)),
                    cspan("type typevar", span-effect(k, pcontent)))
        NITypeCon(k) ->
          signature(env, to-lit, env.literate, "kind", qname, qname.mangle-type-name, pdocs(show-kind(k)),
                    cspan("type", if is-kw then cspan("keyword", pcontent) else span-effect(k, pcontent)))
        NIModule ->
          signature(env, to-lit, env.literate, "module", qname, qname, pdocs(show-module(qname)),
                    cspan("namespace", pcontent))
        NIKind -> span("kind", content)
      (ranges, body)
    // a declaration opens a span that stays open until its range ends
    RIDecl(str, _nm, mname) ->
      (Cons(range, ranges),
       start-tag("span", "decl-" ++ str ++ "\" id=\"" ++ link-encode(mname.name/local)) ++ content)
    RIBlock(str) -> (Cons(range, ranges), start-tag("span", str) ++ content)
    RIError(d) ->
      (Cons(range, Cons(range, ranges)),
       start-tag("span", "error") ++ start-tag("span", "popup") ++
       tag("span", "popup-content", cspan("keyword", "error: ") ++ d.pprint/show) ++ content)
    RIWarning(d) ->
      (Cons(range, Cons(range, ranges)),
       start-tag("span", "warning") ++ start-tag("span", "popup") ++
       tag("span", "popup-content", cspan("keyword", "warning: ") ++ d.pprint/show) ++ content)
    // should not reach the colorizer
    RIImplicits -> (ranges, content)
    RIInlayHint -> (ranges, content)

// Has `r1` finished before `r2` starts?
fun ends-before(r1: range, r2: range): bool
  r1.end <= r2.start


//----------------------------------------------------------------------
// doc comments (upstream `showDoc` / `fmtComment` / `removeComment`)
//----------------------------------------------------------------------

// Strip the comment syntax from a
// captured doc comment so what is left is the prose the author wrote.
pub fun remove-comment(s: string): string
  val t = s.list.drop-while(is-white).string
  if t.starts-with("//").bool then s.remove-line-comments.align
  elif t.starts-with("/*").bool then s.drop-open-block.remove-block-comment.align
  else s

fun drop-open-block(s: string): string
  // `/*` has already been detected on the trimmed text; drop up to and
  // including it
  match s.list.span(fn(c) c != '*')
    (pre, cs) -> match cs
      Cons('*', rest) -> rest.string
      _ -> pre.string

fun remove-line-comment(line: string): string
  val (pre, post) = line.list.span(is-white)
  match post
    Cons('/', Cons('/', cs)) -> pre.string ++ "  " ++ cs.string
    _ -> line

fun remove-line-comments(s: string): string
  s.lines.map(remove-line-comment).unlines

// upstream drops a TRAILING `*/` (it reverses, matches, and reverses back)
fun remove-block-comment(s: string): string
  val r = s.list.reverse
  match r
    Cons('/', Cons('*', cs)) -> cs.reverse.string
    _ -> s

// Drop the common leading indentation, measured over the
// non-blank lines only, so a comment indented to its definition does not
// render as a markdown code block.
fun align(s: string): string
  val ls = s.lines
  val indents = ls.filter(fn(l) !l.list.drop-while(is-white).is-nil)
                  .map(fn(l) l.list.take-while(is-white).length)
  val n = indents.foldl(100, min)
  ls.map(fn(l) l.list.drop(n).string).unlines



pub fun html/capitalize(s: string): string
  match s.list
    Cons(c, cs) -> c.string.to-upper ++ cs.string
    Nil -> s

// Documentation synopses read as sentences
pub fun end-with-dot(s: string): string
  val r = s.list.reverse.drop-while(is-white)
  match r
    Cons(c, _) | !([".", "?", "!"].any(fn(d) d == c.string)) -> Cons('.', r).reverse.string
    _ -> s

fun prefix-span(cls: string, content: string): _ string
  span(if cls.is-empty then "" else class-prefix() ++ cls, content)

fun prefix-block-tag(t: string, cls: string, content: string): _ string
  // the blank lines keep the surrounding markdown intact
  "\n" ++ ptag(t, if cls.is-empty then "" else class-prefix() ++ cls, content) ++ "\n"

// Render a comment's inline code, then `dropColon`.
//
// A doc comment writes a TYPE as `` `:shape` ``, and the leading `:` is
// notation for the reader, not part of what should be displayed -- so the
// rendered `:` and the whitespace after it are dropped. Same for the `module`
// keyword in an entry like `` `module std/num/float64` ``.
//
// PORT GAP: upstream's `showLexemes` also runs `fmtQualify`, which resolves a
// bare type name in a comment against the kgamma so it can be linked. That
// needs the literate formatter the port does not have yet.
// upstream `showLexemes`'s `fmtQualify`: a doc comment writes names as the
// AUTHOR typed them, so `` `fun ask` `` carries a bare `ask`. `fmt-literate`
// only links a name it can resolve, so each identifier is first looked up and
// replaced by its qualified form.
fun fmt-qualify(env: html-env, gam: gamma, kgam: kGamma, lexs: list<lexeme>): _ list<lexeme>
  fun try-qualify-type(mk: (name) -> lex, nm: name): _ lex
    match kgam.qname-map/lookup(env.ctx-module, nm)
      Found((qname, _)) -> mk(qname)
      _ -> mk(nm)
  fun try-qualify(mk: (name) -> lex, nm: name): _ lex
    match gam.gamma-lookup(nm)
      [(qname, InfoCon)] | nm.unqualify.name-case-equal(qname.unqualify) -> LexCons(qname)
      [(qname, _)] | nm.unqualify.name-case-equal(qname.unqualify) -> mk(qname)
      [(_, InfoImport(fullName=qname))] -> LexModule(nm, qname)
      _ -> mk(nm)
  fun qualify-id(l: lexeme): _ lexeme
    match l
      Lexeme(r, LexId(nm)) -> Lexeme(r, try-qualify(fn(n) LexId(n), nm))
      Lexeme(r, LexOp(nm)) -> Lexeme(r, try-qualify(fn(n) LexOp(n), nm))
      _ -> l
  match lexs
    // a type entry: `` `:shape` ``
    [Lexeme(r0, LexKeyword(":", d)), Lexeme(r1, LexId(nm))] ->
      [Lexeme(r0, LexKeyword(":", d)), Lexeme(r1, try-qualify-type(fn(n) LexId(n), nm))]
    [Lexeme(r0, LexKeyword(":", d)), Lexeme(r1, LexOp(nm))] ->
      [Lexeme(r0, LexKeyword(":", d)), Lexeme(r1, try-qualify-type(fn(n) LexOp(n), nm))]
    [Lexeme(r0, LexKeyword(":", d)), Lexeme(r1, LexSpecial("(")), Lexeme(_r2, LexSpecial(")"))] ->
      [Lexeme(r0, LexKeyword(":", d)), Lexeme(r1, LexId(nameSystemCore.qualify(new-name("()"))))]
    // a module entry: `` `module std/num/float64` ``
    [l0 as Lexeme(_, LexKeyword("module", _)), l1 as Lexeme(_, LexWhite), Lexeme(r2, LexId(nm))] ->
      [l0, l1, Lexeme(r2, LexModule(nm, nm))]
    // `name : type` -- the type text becomes the token's disambiguating `tp`
    Cons(Lexeme(r1, LexId(nm)), Cons(Lexeme(_r2, LexKeyword(":", _)), rest)) ->
      [Lexeme(r1, LexTypedId(nm, rest.map(highlight/show).join))]
    _ -> lexs.map(qualify-id)

fun fmt-lexs(lexs: list<lexeme>, lit: maybe<(html-env, gamma, kGamma)>): _ string
  val qlexs = match lit
    Just((env, gam, kgam)) -> fmt-qualify(env, gam, kgam, lexs)
    Nothing -> lexs
  var out := []
  with handler
    val source-file = ""
    fun fmt(token, _lex, str)
      val rendered = match lit
        Just((env, gam, kgam)) -> fmt-literate(env, gam, kgam, token, str)
        Nothing -> fmt-html(token, str)
      out := Cons(rendered, out)
      token
  highlight-lexemes(id, CtxNormal, qlexs)
  drop-colon(qlexs, out.reverse).join

fun drop-colon(lexs: list<lexeme>, fmts: list<string>): list<string>
  match (lexs, fmts)
    (Cons(Lexeme(_, lx), ls), Cons(_, rest)) | lx.is-drop-colon-keyword ->
      rest.drop(ls.take-while(fn(l) l.is-white).length)
    _ -> fmts

fun is-drop-colon-keyword(lx: lex): bool
  match lx
    LexKeyword(":") -> True
    LexKeyword("module") -> True
    _ -> False

// A doc comment is not plain text -- it carries urls,
// emphasis, inline code and code blocks, and the code parts are highlighted
// like any other Koka.
pub fun fmt-comment(com: token-comment<lexeme>, lit: maybe<(html-env, gamma, kGamma)> = Nothing): _ string
  match com
    ComText(f) -> f
    ComUrl(url) -> "<a href=\"" ++ url ++ "\">" ++ url.escapes ++ "</a>"
    ComLine -> prefix-span("line", "")
    ComEmph(f) -> prefix-span("emph", f)
    ComPre(f) -> prefix-span("pre", f.escapes)
    ComPreBlock(f) -> prefix-block-tag("pre", "preblock", f.escapes)
    ComCode(lexs) -> ptag("code", class-prefix(), fmt-lexs(lexs, lit))
    ComCodeBlock(cls, lexs, str) ->
      prefix-block-tag("pre", "source unchecked " ++ cls,
                       span("plaincode", str.escapes) ++ span("nicecode", fmt-lexs(lexs, lit)))
    ComCodeLit(_lit, lexs, str) ->
      prefix-block-tag("pre", "source", span("plaincode", str.escapes) ++ span("nicecode", fmt-lexs(lexs, lit)))

// `lex-comment` needs a SOURCE NAME, which it reads from the `fmt` effect --
// it lexes fenced code blocks inside the comment, and their lexemes carry
// ranges. Upstream passes the empty string explicitly (`lexComment "" 1 ...`)
// rather than the enclosing file, so this installs its own handler instead of
// inheriting the colorizer's. The `fmt` operation is never reached from here:
// `fmt-lexs` installs the handler that actually renders those lexemes.
fun lex-doc-comment(doc: string): _ list<token-comment<lexeme>>
  with handler
    val source-file = ""
    fun fmt(token, _lex, _s) token
  lex-comment(1, remove-comment(doc))

// A definition's documentation, rendered.
// `lit` carries what a name inside an inline code span needs to become a
// link (upstream's `fmtComment env kgamma gamma`). Omitting it renders the
// comment without links, which is what a caller with no gamma in hand wants.
pub fun show-doc(doc: string, lit: maybe<(html-env, gamma, kGamma)> = Nothing): _ string
  if doc.is-empty then ""
  else
    doctag("div", class-prefix() ++ "comment",
      doctag("xmp", "",
        html/capitalize(end-with-dot(lex-doc-comment(doc).map(fn(c) fmt-comment(c, lit)).join))))

pub fun doctag(t: string, cls: string, content: string): string
  ptag(t, if cls.is-empty then "" else "doc " ++ cls, content)

//----------------------------------------------------------------------
// the document
//----------------------------------------------------------------------

fun link-css(css-path: string): string
  "<link rel=\"stylesheet\" type=\"text/css\" href=\"" ++ css-path ++ "\" />"

pub fun html-header(title: string, css: list<string>, js: string): _ list<string>
  ["<!DOCTYPE html>",
   "<html>",
   "<head>",
   "<meta http-equiv=\"content-type\" content=\"text/html; charset=UTF-8\" />",
   "<meta name=\"viewport\" content=\"initial-scale=1.0\" />",
   "",
   "<style type=\"text/css\">.koka .plaincode, .koka a.pp .pc { display: none; } .koka a.pp { color: inherit; text-decoration: none; }</style>"]
  // upstream has this as ONE element built with `unlines`, so its trailing
  // newline lands inside the joined document and shows up as a blank line
  // ONE element ending in a newline: Haskell's `unlines` appends a trailing
  // newline (Koka's does not), and upstream's shows up as a blank line after
  // the stylesheet links once the header is joined.
  ++ [css.map(link-css).join("\n") ++ "\n"] ++
  ["<link rel=\"stylesheet\" type=\"text/css\" href=\"https://fonts.googleapis.com/css?family=Nunito:400,400italic,700,700italic\" />",
   "<link rel=\"stylesheet\" type=\"text/css\" href=\"https://fonts.googleapis.com/css?family=Roboto+Mono:400,500,700,400italic\" />",
   (if js.is-empty then ""
    else "<script type=\"text/javascript\" data-main=\"" ++ js.path.basename ++ "\" src=\"" ++ js ++ "\"></script>"),
   "<title>" ++ title ++ " documentation</title>",
   "</head>",
   "",
   "<body class=\"" ++ class-prefix() ++ "doc body madoko\">"]

pub val html-footer: list<string> = ["</body>", "</html>"]

// Render `input` as syntax-highlighted HTML.
//
// `full-html` wraps the result in a complete document;
// otherwise just the `<pre>` block is produced, for embedding.
//
// NOT yet ported: the range-map pass, which turns
// identifiers into links to their definitions and attaches type popups. That
// needs the module's range map, kgamma and gamma; this is the plain
// `highlightLexemes id fmtHtml CtxNormal` path upstream falls back to when it
// has no range map.
pub fun colorize(source-name: path, line-no: int, input: string,
                 rmap: maybe<range-map> = Nothing, env: html-env = Html-env(name/nil),
                 full-html: bool = False, css: list<string> = [], js: string = ""): _ string
  var out := ""
  // ranges whose `</span>` is still owed, innermost first
  var rctx : list<range> := []
  var rm : maybe<range-map> := rmap.map(rm/sort)
  val body =
    with handler
      val source-file = source-name.string
      fun fmt(token, lex, s)
        // close every range that finished before this lexeme (upstream's
        // `scan` does this before formatting each one)
        fun close-ended(): _ ()
          val open-now : list<range> = rctx
          match open-now
            Cons(r, rest) | r.ends-before(lex.range) ->
              out := out ++ end-tag("span")
              rctx := rest
              close-ended()
            _ -> ()
        close-ended()
        val content = fmt-html(token, s)
        match rm
          // no range map: plain highlighting, upstream's fallback path
          Nothing -> out := out ++ content
          Just(r0) ->
            val (rinfos, r1) = r0.range-map/lookup(lex.range)
            rm := Just(r1)
            val (ranges, content') = rinfos.reverse.foldl(([], content), fn(acc, e) transform1(env, lex, acc, e))
            rctx := ranges ++ rctx
            out := out ++ content'
        token
    highlight(id, CtxNormal, line-no, input)
    // anything still open at end of input
    val still-open : list<range> = rctx
    still-open.foreach(fn(_r) out := out ++ end-tag("span"))
    out
  val pre = "<pre class=\"" ++ class-prefix() ++ "source\">" ++ body ++ "</pre>\n"
  if !full-html then pre
  else (html-header(source-name.basename.escapes, css, js) ++ [pre] ++ html-footer).unlines ++ "\n"
