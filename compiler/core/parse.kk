// Updated as of 7/23/26: Commit 7369a3a
module compiler/core/parse

import std/core/debug
import std/os/path
import std/os/file
import compiler/common/parse
import compiler/common/id
import compiler/syntax/lexeme
import compiler/syntax/builders
import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/name-prim
import compiler/common/syntax
import compiler/common/failure
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/import-map
import compiler/type/type
import compiler/type/assumption
import compiler/platform/config
import compiler/core/core
import compiler/type/typevar
import std/data/rb-map

// BACKTRACKING, and how much of it: upstream's `Core/Parse.hs` uses Parsec,
// where `<|>` does NOT backtrack and `try` is the explicit opt-in. It reaches
// for `try` at 12 of ~115 choice points. This port had that inverted -- 26
// `parse-choices` and 36 `parse-maybe` (both backtracking) against 7 and 1 of
// the `-nb` forms -- so the interface parser, the hottest module in a warm
// build, was saving and restoring the lexeme list at nearly every decision.
// Each site converted below has a specific upstream line (`<|> return d` or
// `option d`) justifying it; a site whose alternative can consume input before
// failing must KEEP the backtracking form.
//
// `syns0` seeds the parser's synonym environment with synonyms from modules
// that are already loaded. The interface's own `local alias` section covers
// MOST imported synonyms, but not all: the emitter (upstream's too) misses
// e.g. std/core/types/ctx in trmc-lifted signatures, and a synonym parsed
// without its definition degrades to a bare TCon that backend passes then
// look up as a data type and fail on (Core.Parc.getDataDefInfo). Dependencies
// always load before dependents, so their synonyms are available to seed.
pub fun parse-core(fname: path, tpl: target-platform = target-platform-default, syns0: synonyms = synonyms/empty)
  val input = read-text-file(fname)
  lex-parse(True, False, core-preprocess, {parse-program(fname, Source(fname.string, input), syns0)}, tpl, fname.string, input)

// Filter whitespace and comments, but keep the `//.inline-section` marker as a special token so the inline
// definition section can be detected reliably.
fun core-preprocess(lexes: list<lexeme>): pure list<lexeme>
  lexes.filter-map fn(l)
    match l.lex
      // note: the lexer strips the `.` from `//.inline-section`
      LexComment(c) | c.starts-with("//.inline-section").bool || c.starts-with("//inline-section").bool ->
        Just(Lexeme(l.range, LexSpecial("//.inline-section")))
      _ -> if l.is-white then Nothing else Just(l)

fun requalify(lexes: list<lexeme>): _ list<lexeme>
  match lexes
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexId(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(new-name(modName.show-plain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexIdOp(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(new-name(modName.show-plain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexOp(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(new-name(modName.show-plain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexCons(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexCons(qualify(new-name(modName.show-plain), nm))), lexx))
    Cons(lex, lexx)
      -> Cons(lex, requalify(lexx))
    [] -> []

fun allow-dot-ids(lexes: list<lexeme>): _ list<lexeme>
  match lexes
    // Identifier
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexId(nm)), lexx)) -> allow-dot-ids(Cons(Lexeme(r1.combine(r2), LexId(prepend(".", nm))), lexx))
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexWildCard(nm)), lexx))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r2),  LexWildCard (".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexId(nm)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r3), LexId (nm.postpend("." ++ i.show))), lexx))
    // operator
    Cons(Lexeme(r1, LexKeyword(".")),Cons(Lexeme(r2, LexOp(nm)), lexx))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r2), LexId(".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexOp(nm)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r3), LexId(nm.postpend("." ++ i.show))), lexx))

    // constructor
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexCons(nm)), lexx))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r2), LexCons(".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexCons(nm)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r3), LexCons(nm.postpend("." ++ i.show))), lexx))

    // (-.4), (++.2)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(nm)), Cons(Lexeme(_,LexInt(i)), Cons(Lexeme(r5,LexSpecial(")")), lexx)))) // | last (nmId nm) == '.'
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r5), LexId(nm.postpend(i.show))), lexx))
    // (/.4)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(nm)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r5, LexSpecial(")")), lexx))))) // | last (nmId nm) == '.'
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r5), LexId(nm.postpend("." ++ i.show))), lexx))
    // ([].1)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")),Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(_, LexKeyword(".")),Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r2, LexSpecial(")")), lexx))))))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r2), LexId("[]".new-name.postpend("." ++ i.show))), lexx))
    // ([])
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")), Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(r2, LexSpecial(")")), lexx))))
      -> allow-dot-ids(Cons(Lexeme(r1.combine(r2), LexId("[]".new-name)), lexx))
    Cons(l, lx) -> Cons(l, allow-dot-ids(lx))
    Nil -> Nil

fun parse-inlines(prog: core, s: source, env: envv, inlines: list<lexeme>, gamma: gamma, tpl: target-platform = target-platform-default)
  with parse-lexemes(s, inlines, tpl)
  with with-env-initial(prog.coreName, "".path, imports-empty, synonyms/empty)
  set-env(env(gamma=gamma))
  val idefs = parse-many("inline", parse-inline-def)
  peof()
  idefs

fun parse-program(src-path: path, s: source, syns0: synonyms = synonyms/empty)
  parse-many("semis", parse-semicolon)
  val (prog, env, inlines) = parse-module(src-path, syns0)
  peof()
  (prog, fn(gamma) parse-inlines(prog, s, env, inlines, gamma))

fun parse-module(src-path: path, syns0: synonyms = synonyms/empty)
  val (_, doc) = parse-doc-keyword("module")
  parse-keyword("interface")
  val (name0, _) = parse-module-path()
  parse-many("semis", parse-semicolon)
  braced
    val (imps, impAliases) = semis("import", parse-import-declaration).filter-map(fn(x) x).unzip
    val impMap = impAliases.foldr(imports-empty) fn((asname, name'), m) 
      match m.extend(asname, name')
        Just(imp') -> imp'
        Nothing -> m
    val externImports = semis("extern imports", parse-external-import-decl)
    val fixs = semis("fix decls", parse-fixity-declaration)
    with with-env-initial(name0, src-path, impMap, syns0)
    // `local kind` declares a type constructor's kind ONCE; its occurrences then
    // carry no `:: kind` annotation and `env-type` recovers it from here. The
    // annotation stays legal, so an interface written by an older compiler (or
    // by upstream) still reads.
    // Read BEFORE the aliases: alias bodies mention those constructors.
    val impkinds = semis("import kinds", parse-local-kind)
    impkinds.foreach(fn((n, k)) env-extend-declared-kind(n, k))
    val impsyns = semis("import synonyms", parse-local-alias)
    if kind-trace-on() then
      trace("KIND read " ++ name0.show-plain ++ ": parsed " ++ impkinds.length.show
            ++ " [" ++ impkinds.take(4).map(fn((n,_)) n.show-plain).join(", ") ++ "]")
    val tdefs = semis("type decls", parse-type-declaration)
    val defs = semis("fun decls", pDefDecl)
    val externs = semis("externs", parse-extern-decl)
    val inlines = parse-maybe("inlines", {parse-special("//.inline-section"); val rest = take-all(); put-all([]); rest}).default([])
    val tdef-groups = tdefs.map(fn(tdef) [tdef])
    val def-groups = defs.map(DefNonRec)
    (Core(name0, imps, fixs.concat, tdef-groups, def-groups, externImports ++ externs, doc), get-env(), inlines)

fun parse-local-alias()
  parse-try({parse-special-id("local"); parse-keyword("alias")})
  val qname = parse-qualified-type-id().fst
  val range = parse-range()
  val name = env-qualify(qname)
  val params = parse-type-params()
  val kind = parse-kind-annot-full()
  parse-keyword("=")
  val tp = parse-type()
  val rank = parse-maybe-nb("", {parse-keyword("="); parse-integer().fst}).default(0)
  val syn = SynInfo(name, kind, params, tp, rank, range, Private, "")
  env-extend-synonym(syn)
  syn

fun parse-local-kind(): _ (name, kind)
  parse-try({parse-special-id("local"); parse-special-id("kind")})
  val qname = parse-qualified-type-id().fst
  val k = parse-kind-annot-full()
  (env-qualify(qname), k)

fun default/parse-visibility()
  parse-maybe-nb("visibility", {parse-keyword("pub"); Public}).default(Private)

fun parse-import-declaration(): _ maybe<(compiler/core/core/kimport, (name, name))>
  val (vis, doc) = parse-try({(parse-visibility(), parse-doc-keyword("import").snd)})
  match parse-import-alias()
    Nothing -> Nothing
    Just((asname, name, _, nameRng)) ->
      // import provenance: pub | type | inline | (none)
      val prov = parse-choices("import provenance", [
        {parse-keyword("pub"); ImportPub},
        {parse-keyword("type"); ImportTypes},
        {parse-special-id("inline"); ImportCompiler},
        {ImportUser}
      ])
      val pkg = parse-maybe-nb("=", {parse-keyword("="); parse-string-literal().fst}).default("")
      Just((compiler/core/core/Kimport(name, pkg, vis, doc, nameRng, prov), (asname, name)))

fun parse-fixity-declaration()
  val fix = parse-fixity()
  val op = parse-identifier().fst
  [FixDef(op, fix)]

fun parse-fixity()
  val assoc = parse-choices-nb("assoc", [
    {parse-keyword("infixl"); AssocLeft},
    {parse-keyword("infixr"); AssocRight},
    {parse-keyword("infix"); AssocNone}
  ])
  val (prec, _) = parse-integer()
  FixInfix(prec, assoc)

fun parse-type-declaration()
  parse-choices("type decl", [
    {
      val (vis, (ddef, isRec, dataEff, sort, doc)) = parse-try({(parse-visibility(), parse-type-sort())})
      val tn = if ddef.is-extend then
          parse-qualified-type-id().fst
        else
          qualify(modname, parse-choices-nb("identifier", [parse-type-binder-id, parse-op-id]).fst)
      val range = parse-range()
      val params = parse-type-params()
      val kind = parse-kind-annot-full()
      val cons = parse-maybe-nb("constructor", {parse-semi-braces("contructor args", {parse-constructor-declaration(tn, params, sort)})}).default([])
      val cons1 = match cons
        [con1] -> [con1(singleton=True)]
        _ -> cons
      val dataInfo = DataInfo(sort, tn, kind, params, cons1, range, ddef, dataEff, isRec, vis, doc)
      Data(dataInfo)
    },{
      val (vis, doc) = parse-try({(parse-visibility(), parse-doc-keyword("alias").snd)})
      val name = parse-type-binder-id().fst
      val range = parse-range()
      val params = parse-type-params()
      val kind = parse-kind-annot-full()
      parse-keyword("=")
      val tp = parse-type()
      val rank = parse-maybe-nb("rank", {parse-keyword("="); parse-integer().fst}).default(0)
      val qname = qualify(modname, name)
      val syn = SynInfo(qname, kind, params, tp, rank, range, vis, doc)
      env-extend-synonym(syn)
      Synonym(syn)
    }
  ])

fun parse-constructor-declaration(tname0: name, foralls: list<type-var>, sort: data-kind)
  val (vis, mbLazy) = parse-try
    val vis = parse-visibility()
    val mbLazy = parse-maybe-nb("lazy")
      parse-special-id("lazy")
      val (fip, _) = parse-tail-fip()
      fip
    parse-keyword("con")
    (vis, mbLazy)
  val (name, (_, doc)) = parse-doccon-id()
  val range = parse-range()
  val exists0 = parse-type-params()
  val params = parse-parameters()
  val vrepr = parse-value-repr()
  val tp = parse-type-annotation()
  val params2 = params.zip(list(1, params.length)).map(fn(((n, t), i)) (if n.nameStem == "" then i.new-field-name else n, t))
  val orderedFields = []
  parse-keyword("=")
  val (tag, _) = parse-integer()
  ConInfo(
    qualify(modname, name), tname0, 
    foralls, exists0, 
    params2, tp, sort, range, 
    params2.map(fn(_) range), 
    params2.map(fn(_) Public), False, 
    orderedFields, vrepr, mbLazy, tag, vis, doc)

fun parse-type-sort()
  val isRec = parse-maybe-nb("recursive", {parse-special-id("recursive")}).is-just
  val (ddef, sort, dataEff) = parse-type-modifier()
  val doc = parse-doc-keyword("type").snd
  (ddef, isRec, dataEff, sort, doc)

fun parse-type-modifier()
  parse-choices("type modifier", [
    {parse-special-id("open"); (DataDefOpen(False), Inductive, DataNoEffect)},
    {parse-special-id("extend"); (DataDefOpen(True), Inductive, DataNoEffect)},
    // upstream: `specialId "lazy"; (fip,_) <- parseTailFip` (lazy datatypes,
    // e.g. samples/learn/lazycons round-tripped through a .kki)
    {parse-special-id("lazy"); val (fip, _) = parse-tail-fip(); (DataDefLazy(fip), Inductive, DataNoEffect)},
    {parse-special-id("value"); (DataDefValue(parse-value-repr()), Inductive, DataNoEffect)},
    { val dataEff = parse-data-effect()
      parse-choices("type modifier", [
        {parse-special-id("co"); (DataDefNormal, CoInductive, dataEff)},
        // upstream parses `div` here (matching prettyDataInfo's "div type")
        {parse-special-id("div"); (DataDefNormal, Retractive, dataEff)},
        {(DataDefNormal, Inductive, dataEff)}
      ])
    }
  ])

fun parse-data-effect()
  parse-maybe("data effect", {
    val is-named = parse-maybe-nb("named effect", {parse-keyword("named"); True}).default(False)
    val is-linear = parse-maybe-nb("linear effect", {parse-special-id("linear", []); True}).default(False)
    parse-keyword("effect")
    DataEffect(is-named, is-linear)
    }).default(DataNoEffect)

fun parse-value-repr()
  braced
    val rraw = parse-integer().fst
    parse-comma()
    val scan = parse-integer().fst
    parse-comma()
    val align = parse-integer().fst
    ValueRepr(rraw, scan, align)

fun pDefDecl()
  val (vis, sort0, inl, doc) = parse-try({val vis = parse-visibility(); val (sort, inl, _, doc) = pDefSort(); (vis, sort, inl, doc)})
  val (name, _) = parse-choices-nb("decl name", [parse-fun-id, parse-op-id])
  val range = parse-range()
  parse-keyword(":")
  val (tp, pinfos) = parse-def-type()
  val sort = match sort0
    DefFun(_, fipT) -> DefFun(pinfos, fipT)
    _ -> sort0
  Def(qualify(modname, name), tp, exprUnit, vis, sort, inl, range, doc)

fun pDefSort()
  val isRec = parse-maybe-nb("recursive", {parse-special-id("recursive")}).is-just
  val inl = parse-inline()
  parse-choices("fip info", [
    {
      val (fipT, _) = parse-try(parse-tail-fip)
      val (_, doc) = parse-doc-keyword("fun")
      parse-choices-nb("specialization", [{parse-special-op("**"); ()}, {parse-special-op("*"); ()}, {()}])
      (def-fun-ex([], fipT), inl, isRec, doc)
    },
    {(DefVal, inl, False, parse-doc-keyword("val").snd)}
  ])

fun parse-inline-def()
  val (sort, inl, isRec, specArgs, _) = parse-inline-def-sort()
  val (name, _) = parse-fun-id()
  val e = parse-body()
  InlineDef(env-qualify(name), e, isRec, inl, if inl.is-inlineAlways then 0 else e.cost, sort, specArgs)

fun parse-extern-decl()
  val (vis, fipT, doc) = parse-try({(parse-visibility(), parse-tail-fip().fst, parse-doc-keyword("extern").snd)})
  val (name, _) = parse-fun-id()
  val rng = parse-range()
  parse-keyword(":")
  val (tp, pinfos) = parse-def-type()
  val format = match parse-external-body()
    Just(f) -> f
    Nothing ->
      // upstream `externDecl` emits a warning here before falling back
      // (`pwarningMessage ("unsupported external " ++ show name) range`)
      pwarning-message("unsupported external " ++ name.show, rng)
      unsupported-external(name.show)
  External(qualify(modname, name), tp, pinfos, format, vis, fipT, rng, doc)

fun parse-external-body(): _ maybe<string>
  parse-choices("external body", [
    {parse-keyword("="); parse-external-entry()},
    {firstof(parse-semi-braces("external entry", parse-external-entry))}
  ])

fun parse-external-entry(): _ maybe<string>
  val matches = parse-target-guard()
  parse-maybe("external inline", {parse-special-id("inline")})
  val s = parse-string-literal().fst
  if matches then Just(s) else Nothing

fun parse-external-import-decl()
  parse-try({parse-keyword("extern"); parse-keyword("import")})
  ExternalImport(parse-external-import-body(), null)

fun parse-external-import-keyval()
  val key = parse-string-literal().fst
  parse-keyword("=")
  val v = parse-string-literal().fst
  (key, v)

fun parse-external-import-entry(): _ maybe<list<(string, string)>>
  val matches = parse-target-guard() // todo: core files should have no target platform guard anymore
  val keyvals = parse-semi-braces("external key value", parse-external-import-keyval)
  if matches then Just(keyvals) else Nothing

fun parse-external-import-body(): _ list<(string, string)>
  parse-choices("external import body", [
    {
      parse-keyword("=")
      parse-external-import-entry().default([])
    },
    {
      parse-semi-braced("external import entries", parse-external-import-entry).default([])
    }
  ])

fun parse-inline-def-sort()
  val isRec = parse-maybe("inline recursive", {parse-special-id("recursive")}).is-just
  val inl = parse-inline()
  val spec = parse-maybe("inline specialize", {parse-special-id("specialize"); val (s,_) = parse-string-literal(); s.list.map(_ == '*')}).default([])
  val pinfos = parse-maybe("inline borrow", {parse-special-id("borrow"); val (s, _) = parse-string-literal(); s.list.map(fn(c) if c == '^' then Borrow else Own)}).default([])
  parse-choices("fun or val inline", [
    {
      val (fip, doc) = parse-try
        val (f, _) = parse-tail-fip()
        val (_, doc) = parse-doc-keyword("fun")
        (f, doc)
      (DefFun(pinfos, fip), inl, isRec, spec, doc)
    },
    {
      val (_, doc) = parse-doc-keyword("val")
      (DefVal, inl, False, spec, doc)
    }
  ])

fun parse-body()
  parse-keyword("=")
  val e = parse-expression()
  parse-maybe-nb("semis", parse-semicolon)
  e

fun parse-expression()
  parse-choices-nb("expr", [pare-fun, parse-forall, parse-match, parse-let, parse-app])

fun parse-app(): _ expr
  val expr = parse-atomic()
  fun parseApplies(e)
    parse-choices("app", [
      {
        val args = parse-parens-commas(parse-expression)
        parseApplies(App(e, args))
      },
      {
        val tps = angles({parse-sep-by("expr args", parse-type, parse-comma)})
        parseApplies(TypeApp(e, tps))
      },
      {e}
    ])
  parseApplies(expr)

fun parse-atomic()
  // same idea as `parse-lit`: the first token picks the alternative, so peek
  // rather than try-and-catch each in turn. `@cpath` is the optional prefix of
  // a constructor occurrence, so it routes to `parse-con` too. Anything not
  // listed falls through to the original choice unchanged.
  match peek().lex
    LexCons          -> parse-con()
    LexInt           -> ELit(parse-lit())
    LexFloat         -> ELit(parse-lit())
    LexString        -> ELit(parse-lit())
    LexChar          -> ELit(parse-lit())
    LexSpecial("(")  -> parens(parse-expression)
    LexId(n) | n.show-plain == "@cpath" -> parse-con()
    LexId            -> parse-var()
    LexOp            -> parse-var()
    LexIdOp          -> parse-var()
    _ -> parse-choices-nb("atom", [parse-con, parse-var, {ELit(parse-lit())}, {parens(parse-expression)}])

fun parse-let()
  val dgs = parse-def-groups()
  Let(dgs, parse-expression())

fun parse-forall()
  parse-keyword("forall")
  val tvars = parse-type-params1()
  TypeLam(tvars, parse-expression())

fun semi-braced(n, p)
  parse-left-curly()
  parse-many(n, parse-semicolon)
  val x = p()
  parse-many(n, parse-semicolon)
  parse-right-curly()
  x

fun pare-fun()
  parse-keyword("fn")
  val eff = parse-maybe("type parameters", {angles(parse-type)}).default(typeTotal)
  val params = parse-parameters()
  val body = semi-braced("fun", parse-expression)
  Lam(params.map(fn((n, t)) TName(n, t)), eff, body)

fun parse-match()
  parse-keyword("match")
  val args = parse-parens-commas(parse-expression)
  val branches = parse-semi-braces("match branches", parse-branch)
  Case(args, branches)

fun parse-con()
  // `@cpath("<field>")` before a constructor marks a node of a constructor
  // context, with <field> the field on the path to the hole -- the conCtxPath
  // stamped on this occurrence's repr by AnalysisCCtx/CTail, which the global
  // constructor info does not carry (koka-lang/koka#922; mirrors `@skip`)
  val cpath = parse-maybe("@cpath", {parse-special-id("@cpath"); parens({parse-string-literal().fst})})
  val name = pQualifiedConId()
  val InfoCon(_, typ, repr) = env-lookup-parse-con(name)
  val repr1 = match cpath
    Just(s) -> if repr.con-repr-has-ctx-path
                 then repr.update-ctx-path(CtxField(TName(s.qualified/read, typeAny)))
                 else repr
    Nothing -> repr
  Con(TName(name, typ), repr1)

fun parse-var()
  val (name, _) = parse-choices("var identifier", [parse-qualified-var-id, parse-qualified-op-id])
  if name.is-qualified then
    env-lookup-var(name)
  else
    val tp = env-lookup-local(name)
    Var(TName(name, tp), InfoNone)

// PROTOTYPE: dispatch on the next token instead of trying alternatives.
//
// `parse-choices-nb` installs a `final ctl parse-error` frame PER ALTERNATIVE
// and every miss is an install / raise / unwind round trip -- a string literal
// used to cost two of those (Int fails, Float fails, String matches). The token
// already says which alternative applies, so peek and go straight there. The
// alternatives here are disjoint on the token, so this is not a heuristic.
//
// The `_` arm keeps the old path, so anything not covered behaves exactly as
// before rather than turning into a new error.
fun parse-lit()
  match peek().lex
    LexInt    -> LitInt(parse-integer().fst)
    LexFloat  -> LitFloat(parse-float().fst)
    LexString -> LitString(parse-string-literal().fst)
    LexChar   -> LitChar(parse-char-literal().fst.string)
    _ -> parse-choices-nb("literal", [
           {LitInt(parse-integer().fst)},
           {LitFloat(parse-float().fst)},
           {LitString(parse-string-literal().fst)},
           {LitChar(parse-char-literal().fst.string)},
         ])

fun parse-def-groups()
  val dg = parse-def-group()
  val dgs = parse-def-groups0()
  Cons(dg, dgs)

fun parse-def-groups0()
  parse-maybe("def groups", {parse-def-groups()}).default([])  

fun parse-def-group(): _ def-group
  val (sort, inl, _, doc) = pDefSort()
  val (name, _) = parse-choices-nb("def group", [{parse-fun-id()}, {parse-wildcard(); (nil, null)}])
  val rng = parse-range()  // local defs in interface bodies carry a source range
  val tp = parse-type-annotation()
  val expr = parse-body()
  env-extend-local(name, tp)
  DefNonRec(Def(name, tp, expr, Private, sort, inl, rng, doc))

fun parse-range()
  fun parse-linecol()
    parse-integer().fst
  parse-special("[")
  val l1 = parse-linecol()
  parse-special(",")
  val c1 = parse-linecol()
  parse-special(",")
  val l2 = parse-linecol()
  parse-special(",")
  val c2 = parse-linecol()
  parse-special("]")
  env-range(l1, c1, l2, c2)

fun parse-branch()
  val patts = parse-patterns1()
  val guards = parse-many1("guard", parse-guard)
  Branch(patts, guards)

fun parse-patterns1()
  val pat = parse-pattern()
  parse-maybe("pattern comma", {parse-comma(); Cons(pat, parse-patterns1())}).default([pat])

fun parse-guard()
  val grd = parse-maybe("guard expr", {parse-vertical-bar(); parse-try(parse-expression)}).default(exprTrue)
  parse-keyword("->")
  Guard(grd, parse-expression())

fun parse-pattern()
  val pat = parse-patternBasic()
  parse-maybe("as", {parse-keyword("as"); pPatVar(pat)}).default(pat)

fun parse-patternBasic()
  parse-choices-nb("pattern", [pPatCon, {pPatVar(PatWild)}, pPatLit, pPatWild, {parens(parse-pattern)}])

fun pPatCon()
  val skip = parse-maybe("@skip", {parse-special-id("@skip")}).is-just  // upstream Core/Pretty writes "@skip"
  val cname = pQualifiedConId()
  val exists0 = parse-type-params()
  val args = parse-try({parse-left-paren(); val x = parse-patternArgs0(); parse-right-paren(); x})
  val (patArgs, argTypes) = args.unzip
  val resTp = parse-type-annotation()
  val InfoCon(_, typ, repr, cons) = env-lookup-parse-con(cname)
  PatCon(TName(cname, typ), patArgs, repr, argTypes, exists0, resTp, cons, skip)

fun parse-patternArgs0(): _ list<(pattern, ktype)>
  parse-maybe("pattern args", {parse-patternArgs1()}).default([])

fun parse-patternArgs1()
  val pattp = parse-patternArg()
  parse-maybe("pattern args", {parse-comma(); Cons(pattp, parse-patternArgs1())}).default([pattp])

fun parse-patternArg()
  val pat = parse-pattern()
  val tp = parse-type-annotation()
  (pat, tp)

// upstream Core/Parse parsePatVar = (qvarid <|> qidop) requalified locally;
// a pattern variable may be an operator id, e.g. the `(@uniq-x51+)` bound by
// `@OptArg(((@uniq-x51+): (a, a) -> a) : ...)` in an inline section.
fun pPatVar(pat: pattern)
  val (qname, _) = parse-choices("pattern variable", [parse-qualified-var-id, parse-qualified-op-id])
  val name = qname.requalify-locally
  val tp = parse-type-annotation()
  env-extend-local(name, tp)
  PatVar(TName(name, tp), pat)

fun pPatLit()
  PatLit(parse-lit())

fun pPatWild()
  parse-wildcard()
  PatWild

fun pQualifiedConId()
  parse-choices("constructor id", [
    {
      parse-module-path()
      parse-special-op("/")
      parse-special("(")
      val cs = parse-many("comma", parse-comma)
      parse-special(")")
      name-tuple(cs.length + 1)
    },
    {parse-qualified-constructor-id().fst}
  ])

fun parse-parameters()
  val iparams = parse-maybe("parameters", {parse-parens-commas({parse-parameter(False)})}).default([])
  val (params, _) = iparams.unzip
  params.map(fn((n, t)) env-extend-local(n, t))
  params

// core parameter names may be locally qualified (e.g. `@implicit/cmp`);
// upstream Core/Parse parameterId = (qvarid <|> qidop requalified) <|> paramid
fun parse-parameter-name(): _ (name, range)
  parse-choices("parameter name", [
    {
      val (qname, r) = parse-choices("qparam", [parse-qualified-var-id, parse-qualified-op-id])
      (qname.requalify-locally, r)
    },
    {parse-param-id()}
  ])

fun parse-parameter(allowBorrow: bool)
  val (name, pinfo) = parse-maybe("parameter info", {
    val pinfo = if allowBorrow then parse-param-info() else Own
    val (name, _) = parse-parameter-name()
    parse-keyword(":")
    (name, pinfo)
  }).default((nil, Own))
  parse-choices("optional type", [
    {
      parse-special-op("?")
      ((name, make-optional(parse-type())), pinfo)
    },
    {
      ((name, parse-type()), pinfo)
    }
  ])

fun parse-type-annotation()
  parse-keyword(":")
  parse-type()

fun parse-type-annotationFull()
  parse-special-op("::")
  parse-type()

fun parse-type-params()
  parse-maybe("type parameters", parse-type-params1).default([])

fun parse-type-params1()
  angles(pTBinders)

fun pTBinders()
  val bs = parse-sep-by("quantifiers", pTBinder, parse-comma)
  bs.map fn(((name, _), kind)) 
    env-extend(name, kind)
    match env-type(name, kind)
      TVar(tv) -> tv
      _ -> failure/fail("core/parse pTBinders: expecting type variable")

fun pTBinder()
  parse-choices("quantifier", [
    {
      val id = parse-choices("type parameter", [parse-var-id, parse-wildcard])
      val kind = parse-kind-annot-full()
      (id, kind)
    },
    {
      parens(pTBinder)
    }
  ])

fun parse-kind-annot-full()
  parse-kind-annot()

fun parse-kind-annot()
  parse-maybe("kind annotation", {parse-special-op("::"); pKind()}).default(kindStar)

fun parse-type(): _ ktype
  parse-typex(False).tuple2/fst

fun parse-def-type()
  val (tp, pinfos) = parse-typex(True)
  (tp, if pinfos.all(is-own) then [] else pinfos)

fun parse-typex(allowBorrow: bool)
  parse-try
    val quantify = parse-tforall()
    val (tp, pinfos) = parse-type-arrow(allowBorrow)
    (quantify(tp), pinfos)

fun parse-tforall()
  val params = parse-maybe("type forall") 
    parse-keyword("forall")
    parse-type-params1()
  fn(rho) 
    match params 
      Just(ps) -> TForall(ps, rho)
      _ -> rho

fun parse-type-arrow(allowBorrow: bool)
  val etp = parse-type-atom-params(allowBorrow)
  match etp
    Left((params, pinfos)) ->
      parse-choices("function type", [
        {
          parse-keyword("->")
          (parse-type-result(params), pinfos)
        },
        {
          val tp = extract(params, "unexpected parameters not followed by an ->")
          (parse-type-app(tp), pinfos)
        }
      ])
    Right(tp) -> (tp, [])

fun parse-type-result(params)
  val tp1 = parse-type-atom()
  val res = parse-maybe("result type")
    TFun(params, tp1, parse-type-atom())
  match res
    Just(tp) -> tp
    Nothing -> TFun(params, typeTotal, tp1)

fun parse-type-atom(): _ ktype
  val etp = parse-type-atoms-paramsx(False, False)
  match etp
    Left((params, _)) -> parse-type-app(extract(params, "expecting single type"))
    Right(tp) -> tp

fun extract(params, msg)
  match params
    Nil -> typeUnit
    [(name, tp)] | name == nil -> tp
    _ -> 
      if params.all(_.fst == nil) then
        TApp(type-tuple(params.length), params.map(snd))
      else
        failure/fail(msg)

fun parse-type-atom-params(allowBorrow: bool)
  parse-type-atoms-paramsx(True, allowBorrow)

fun parse-type-atoms-paramsx(allowParams: bool, allowBorrow: bool)
  parse-choices("type atom", [
    {
      parse-special("(")
      parse-choices("type parameters", [
        {
          val iparams = parse-sep-by("type params", {parse-parameter(allowBorrow)}, parse-comma)
          parse-special(")")
          val (params, pinfos) = iparams.unzip
          Left((params, pinfos))
        },
        {
          val cs = parse-many1("tuple commas", parse-comma)
          parse-special(")")
          val tp = parse-type-app(type-tuple(cs.length + 1))
          Right(tp)
        }
      ])
    },
    {val tp1 = pTId(); val tp2 = parse-type-app(tp1); Right(tp2)},
    {Right(parse-type-effect())},
    {parse-special-op("?"); Right(make-optional(parse-type-atom()))}
  ])

fun parse-type-app(tp)
  val tps = parse-maybe("type application", {angles({parse-sep-by("type params", parse-type, parse-comma)})}).default([])
  parse-synonym(tp, tps)

fun parse-synonym(tp, tps): _ ktype
  val res = parse-maybe("Env")
    parse-special-op("==")
    val rank = parse-maybe("synonym rank", {parse-integer().fst}).default(0)
    val body = parse-type()
    match tp
      TCon(TypeCon(name, kind)) ->
        match synonyms-lookup(name)
          Just(info as SynInfo(_, kind', _, _, rank')) ->
            TSyn(TypeSyn(name, kind', rank', Just(info)), tps, body)
          _ -> TSyn(TypeSyn(name, kind, rank, Nothing), tps, body)
      TSyn(_, _) | tps.is-empty -> tp
      _ -> failure/fail("illegal type alias expression " ++ tp.show)
  match res
    Just(t) -> t
    Nothing -> env-type-app(tp, tps)

fun parse-type-effect()
  with parse-try
  parse-left-angle()
  val labels = parse-sep-by("effect type", pTLabel, parse-comma)
  val ext = pTExtend()
  parse-right-angle()
  labels.foldr(ext, shallow-effect-extend)

fun pTExtend(): _ ktype
  parse-maybe("effect extend", {parse-vertical-bar(); parse-type-atom()}).default(effectEmpty)

fun pTLabel()
  parse-type-app(parse-type-atom())

fun pTId(): _ ktype
  val (name, _) = parse-choices("type id", [parse-qualified-var-id, parse-qualified-op-id, parse-wildcard])
  val kind = parse-maybe("type kind", parse-kind-annot-full).default(kindStar)
  env-type(name, kind)

fun pKind()
  parse-choices("kind", [
    {val params = parse-parens-commas(pKind); parse-keyword("->"); val res = pKind(); params.foldr(res, kind-fun)},
    {val k = pKatom(); parse-choices("kind arrow", [{parse-keyword("->"); val res = pKind(); kind-fun(k, res)}, {k}])}
  ])

fun pKatom()
  // `parens` fails on its first token when the input is not "(", and once it
  // HAS consumed "(" committing is correct -- so non-backtracking is both
  // cheaper and more faithful here.
  parse-choices-nb("kind", [
    {parens(pKind)},
    {parse-special-con-id("V"); kindStar},
    {parse-special-con-id("X"); kindLabel},
    {parse-special-con-id("E"); kindEffect},
    {parse-special-con-id("H"); kindHeap},
    {parse-special-con-id("S"); kindScope},
    {parse-special-con-id("HX"); kindHandled},
    {parse-special-con-id("HX1"); kindHandled1},
  ])

fun env-range(l1: int, c1: int, l2: int, c2: int): <eenv,exn> range
  make-source-range(src-path, l1, c1, l2, c2)

effect eenv
  fun env-extend(name: name, kind: kind): ()
  fun env-type(name: name, kind: kind): ktype
  fun env-qualify(name: name): name
  fun env-extend-synonym(syn-info: syn-info): ()
  fun env-extend-declared-kind(name: name, kind: kind): ()
  fun env-type-app(tp: ktype, args: list<ktype>): ktype
  fun env-extend-local(name: name, tp: ktype): ()
  fun env-lookup-local(name: name): ktype
  fun env-lookup-parse-con(name: name): name-info
  fun env-lookup-var(name: name): expr
  val modname : name
  val src-path : path
  fun get-env(): envv;
  fun set-env(env: envv): ()

struct envv
  bound: name-map<type-var>
  imports: import-map
  unique: int
  gamma: gamma
  locals: name-map<ktype>
  synonyms: name-map<syn-info>
  // the interface's `local kind` declarations; must travel with the env so the
  // deferred inline-section parse (a FRESH `with-env-initial`) still sees them
  declared: name-map<kind>

fun with-env-initial(modName: name, srcPath: path, imports0, syns0: synonyms = synonyms/empty, f: () -> _ a): _ a
  with with-synonyms(syns0)
  var bound := rb-map/empty()
  var imports := imports0
  var unique := 1000
  var gamma := assumption/empty
  var locals := rb-map/empty()
  // from the interface's `local kind` section; consulted when a type
  // constructor occurrence carries no `:: kind` annotation
  var declared-kinds : name-map<kind> := rb-map/empty()
  fun qualify(n: name)
    if n.is-qualified then
      match imports.expand(n)
        Right((qname, _)) -> qname
        Left(amb) -> 
          trace("core/parse qualify: unable to expand name: " ++ n.show ++ ": " ++ amb.show-list(show))
          n
    else name/qualify(modName, n)
  with handler
    val src-path = srcPath
    fun get-env()
      Envv(bound, imports, unique, gamma, locals, get-synonyms(), declared-kinds)
    fun set-env(e)
      val Envv(b, i, u, g, l, s, dk) = e
      bound := b
      imports := i
      unique := u
      gamma := g
      locals := l
      set-synonyms(s)
      declared-kinds := dk
    val modname = modName
    fun env-extend(n, k)
      val id = unique.new-id
      unique := unique + 1
      val tv = TypeVar(id, k, Bound)
      bound := bound.set(n, tv)
    fun env-extend-local(n, k)
      unique := unique + 1
      locals := locals.set(n, k)
    fun env-type(n, k)
      match bound.lookup(n)
        Just(tv) -> TVar(tv)
        Nothing ->
          val qname = qualify(n)
          match synonyms-lookup(qname)
            Just(info as SynInfo(name, kind, params, tp, rank)) | params.is-empty ->
              TSyn(TypeSyn(name, kind, rank, Just(info)), [], tp)
            _ ->
              // no annotation at the use site (`k` defaulted to `kindStar`) =>
              // take the kind the interface declared for it, else keep the
              // default (V-kinded constructors are deliberately not declared)
              val k' = if k == kindStar
                         then declared-kinds.lookup(qname).default(k)
                         else k
              TCon(TypeCon(qname, k'))
    fun env-qualify(n)
      qualify(n)
    fun env-extend-synonym(syn-info)
      synonyms-extend(syn-info)
    fun env-extend-declared-kind(n, k)
      declared-kinds := declared-kinds.set(n, k)
    fun env-type-app(tp, tps) 
      match tp
        TCon(TypeCon(name0, _)) ->
          match synonyms-lookup(name0)
            Just(syn-info as SynInfo(name, kind, params, syntp, rank)) | params.length == tps.length ->
              TSyn(TypeSyn(name, kind, rank, Just(syn-info)), tps, sub(params.zip(tps)) |-> syntp)
            _ -> type-app(tp, tps)
        _ -> type-app(tp, tps)
    fun env-lookup-local(n)
      match locals.lookup(n)
        Just(tp) -> tp
        Nothing -> failure/fail("core/parse unbound local: " ++ n.show)
    fun env-lookup-parse-con(n)
      match gamma.lookup-exact-con(n)
        [c as InfoCon] -> c
        res -> failure/fail("unknown constructor " ++ n.show ++ ": " ++ res.show-list(show))
    fun env-lookup-var(n)
      // a locally-qualified name may be a local (e.g. an `@implicit/par`
      // parameter): check locals first
      val lqname = n.requalify-locally
      match locals.lookup(lqname)
        Just(tp) -> return Var(TName(lqname, tp), InfoNone)
        Nothing -> ()
      match gamma.lookup-canonical(n)
        [fnct as InfoFun] -> fnct.core-expr(n)
        [v as InfoVal] -> v.core-expr(n)
        [ex as assumption/InfoExternal] -> ex.core-expr(n)
        [] | n == nameFieldAddrOf -> 
          val a = TypeVar(0, kindStar, Bound)
          val fType = TForAll([a], TFun([(nil, TVar(a)), (nil, typeString), (nil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
          Var(TName(nameFieldAddrOf, fType), compiler/core/core/InfoExternal(""))
        res -> failure/fail("unknown identifier: " ++ n.show-plain ++ ": " ++ res.show-list(show)
                            ++ "\n  stem-bucket: " ++ gamma.lookup-candidates(n).map(show).join(", ")) 
  f()