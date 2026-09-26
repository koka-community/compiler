import std/os/path
import std/os/file
import std/data/linear-map
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

fun parse-core(fname: path)
  val input = read-text-file(fname)
  lex-parse(True, False, id, {parse-program(fname, Source(fname.string, input))}, fname.string, input)

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

fun parse-inlines(prog: core, s: source, env: envv, inlines: list<lexeme>, gamma: gamma)
  with parse-lexemes(s, inlines)
  with with-env-initial(prog.coreName, "".path, LinearMap([]))
  set-env(env(gamma=gamma))
  val idefs = parse-many("inline", parse-inline-def)
  peof()
  idefs

fun parse-program(src-path: path, s: source)
  parse-many("semis", parse-semicolon)
  val (prog, env, inlines) = parse-module(src-path)
  peof()
  (prog, fn(gamma) parse-inlines(prog, s, env, inlines, gamma))

fun parse-module(src-path: path)
  val (_, doc) = parse-doc-keyword("module")
  parse-keyword("interface")
  val (name0, _) = parse-module-path()
  parse-many("semis", parse-semicolon)
  braced
    val (imps, impAliases) = semis("import", parse-import-declaration).unzip
    val impMap = impAliases.foldr(LinearMap([])) fn((asname, name'), m) 
      match m.extend(asname, name')
        Just(imp') -> imp'
        Nothing -> m
    val externImports = semis("extern imports", parse-external-import-decl)
    val fixs = semis("fix decls", parse-fixity-declaration)
    with with-env-initial(name0, src-path, impMap)
    val impsyns = semis("import synonyms", parse-local-alias)
    val tdefs = semis("type decls", parse-type-declaration)
    val defs = semis("fun decls", pDefDecl)
    val externs = semis("externs", parse-extern-decl)
    val inlines = parse-maybe("inlines", {parse-special("//.inline-section"); val rest = take-all(); put-all([]); rest}).default([]) // TODO: Read rest
    val tdef-groups = tdefs.map(fn(tdef) [tdef])
    val def-groups = defs.map(DefNonRec)
    (Core(name0, imps, fixs.concat, tdef-groups, def-groups, externImports ++ externs, doc), get-env(), inlines)

fun parse-local-alias()
  parse-try({parse-special-id("local"); parse-keyword("alias")})
  val qname = parse-qualified-type-id().fst
  val name = env-qualify(qname)
  val params = parse-type-params()
  val kind = parse-kind-annot-full()
  parse-keyword("=")
  val tp = parse-type()
  val rank = parse-maybe("", {parse-keyword("="); parse-integer().fst}).default(0)
  val syn = SynInfo(name, kind, params, tp, rank, null, Private, "")
  env-extend-synonym(syn)
  syn

fun default/parse-visibility()
  parse-maybe("visibility", {parse-keyword("pub"); Public}).default(Private)

fun parse-import-declaration(): _ (compiler/core/core/kimport, (name, name))
  val (vis, doc) = parse-try({(parse-visibility(), parse-doc-keyword("import").snd)})
  val (asname, name, _, _) = parse-import-alias()
  val pkg = parse-maybe("=", {parse-keyword("="); parse-string-literal().fst}).default("")
  (compiler/core/core/Kimport(name, pkg, vis, doc), (asname, name))

fun parse-fixity-declaration()
  val fix = parse-fixity()
  val op = parse-identifier().fst
  [FixDef(op, fix)]

fun parse-fixity()
  val assoc = parse-choices("assoc", [
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
          qualify(modname, parse-choices("identifier", [parse-type-binder-id, parse-op-id]).fst)
      val params = parse-type-params()
      val kind = parse-kind-annot-full()
      val cons = parse-maybe("constructor", {parse-semi-braces("contructor args", {parse-constructor-declaration(tn, params, sort)})}).default([])
      val cons1 = match cons
        [con1] -> [con1(singleton=True)]
        _ -> cons
      val dataInfo = DataInfo(sort, tn, kind, params, cons1, null, ddef, dataEff, isRec, vis, doc)
      Data(dataInfo)
    },{
      val (vis, doc) = parse-try({(parse-visibility(), parse-doc-keyword("alias").snd)})
      val name = parse-type-binder-id().fst
      val params = parse-type-params()
      val kind = parse-kind-annot-full()
      parse-keyword("=")
      val tp = parse-type()
      val rank = parse-maybe("rank", {parse-keyword("="); parse-integer().fst}).default(0)
      val qname = qualify(modname, name)
      val syn = SynInfo(qname, kind, params, tp, rank, null, vis, doc)
      env-extend-synonym(syn)
      Synonym(syn)
    }
  ])

fun parse-constructor-declaration(tname0: name, foralls: list<type-var>, sort: data-kind)
  val (vis, mbLazy) = parse-try
    val vis = parse-visibility()
    val mbLazy = parse-maybe("lazy")
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
  val params2 = params.zip(list(1, params.length)).map(fn(((n, t), i)) (if n.nameStem == "" then i.new-field-name else name, t))
  val orderedFields = []
  val (tag, _) = parse-integer()
  ConInfo(
    qualify(modname, name), tname0, 
    foralls, exists0, 
    params2, tp, sort, range, 
    params2.map(fn(_) range), 
    params2.map(fn(_) Public), False, 
    orderedFields, vrepr, mbLazy, tag, vis, doc)

fun parse-type-sort()
  val isRec = parse-maybe("recursive", {parse-special-id("recursive")}).is-just
  val (ddef, sort, dataEff) = parse-type-modifier()
  val doc = parse-doc-keyword("type").snd
  (ddef, isRec, dataEff, sort, doc)

fun parse-type-modifier()
  parse-choices("type modifier", [
    {parse-special-id("open"); (DataDefOpen(False), Inductive, DataNoEffect)},
    {parse-special-id("extend"); (DataDefOpen(True), Inductive, DataNoEffect)},
    {parse-special-id("value"); (DataDefValue(parse-value-repr()), Inductive, DataNoEffect)},
    { val dataEff = parse-data-effect()
      parse-choices("type modifier", [
        {parse-special-id("co"); (DataDefNormal, CoInductive, dataEff)},
        {parse-special-id("rec"); (DataDefNormal, Retractive, dataEff)},
        {(DataDefNormal, Inductive, dataEff)}
      ])
    }
  ])

fun parse-data-effect()
  parse-maybe("data effect", {
    val is-named = parse-maybe("named effect", {parse-keyword("named"); True}).default(False)
    val is-linear = parse-maybe("linear effect", {parse-keyword("linear"); True}).default(False)
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
  val (name, _) = parse-choices("decl name", [parse-fun-id, parse-op-id])
  parse-keyword(":")
  val (tp, pinfos) = parse-def-type()
  val sort = match sort0
    DefFun(_, fipT) -> DefFun(pinfos, fipT)
    _ -> sort0
  Def(qualify(modname, name), tp, ELit(LitString("core/parse " ++ name.show ++ ": cannot get the expression from an interface core file")), vis, sort, inl, null, doc)

fun pDefSort()
  val isRec = parse-maybe("recursive", {parse-special-id("recursive")}).is-just
  val inl = parse-inline()
  parse-choices("fip info", [
    {
      val (fipT, _) = parse-try(parse-tail-fip)
      val (_, doc) = parse-doc-keyword("fun")
      parse-choices("specialization", [{parse-special-op("**"); ()}, {parse-special-op("*"); ()}, {()}])
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
  val (name, rng) = parse-fun-id()
  parse-keyword(":")
  val (tp, pinfos) = parse-def-type()
  val formats = parse-external-body()
  External(qualify(modname, name), tp, pinfos, formats, vis, fipT, rng, doc)

fun parse-external-body()
  parse-choices("external body", [
    {parse-keyword("="); [parse-external-entry()]},
    {parse-semi-braces("external entry", parse-external-entry)}
  ])

fun parse-external-entry()
  val target = parse-external-target()
  parse-maybe("external inline", {parse-special-id("inline")})
  val s = parse-string-literal().fst
  (target, s)

fun parse-external-target()
  parse-choices("external target", [
    {parse-special-id("c"); C(CDefault)},
    {parse-special-id("cs"); CS},
    {parse-special-id("js"); JS(JsDefault)},
    {DefaultTarget}
  ])

fun parse-external-import-decl()
  parse-try({parse-keyword("extern"); parse-keyword("import")})
  ExternalImport(parse-external-import-body(), null)

fun parse-external-import-keyval()
  val key = parse-string-literal().fst
  parse-keyword("=")
  val v = parse-string-literal().fst
  (key, v)

fun parse-external-import-entry()
  val target = parse-external-target()
  (target, parse-semi-braces("external key value", parse-external-import-keyval))

fun parse-external-import-body()
  parse-choices("external import body", [
    {
      parse-keyword("=")
      [parse-external-import-entry()]
    },
    {
      parse-semi-braces("external import entries",parse-external-import-entry)
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
  parse-choices("expr", [pare-fun, parse-forall, parse-match, parse-let, parse-app])

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
  parse-choices("atom", [parse-con, parse-var, {ELit(parse-lit())}, {parens(parse-expression)}])

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
  val name = pQualifiedConId()
  val InfoCon(_, typ, repr) = env-lookup-parse-con(name)
  Con(TName(name, typ), repr)

fun parse-var()
  val (name, _) = parse-choices("var identifier", [parse-qualified-var-id, parse-qualified-op-id])
  if name.is-qualified then
    env-lookup-var(name)
  else
    val tp = env-lookup-local(name)
    Var(TName(name, tp), InfoNone)

fun parse-lit()
  parse-choices("literal", [
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
  val (name, _) = parse-choices("def group", [{parse-fun-id()}, {parse-wildcard(); (nil, null)}])
  val tp = parse-type-annotation()
  val expr = parse-body()
  env-extend-local(name, tp)
  DefNonRec(Def(name, tp, expr, Private, sort, inl, null, doc))

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
  parse-maybe("pattern comma", {parse-comma(); Cons(pat, parse-patterns1())}).default([])

fun parse-guard()
  val grd = parse-maybe("guard expr", {parse-vertical-bar(); parse-try(parse-expression)}).default(exprTrue)
  parse-keyword("->")
  Guard(grd, parse-expression())

fun parse-pattern()
  val pat = parse-patternBasic()
  parse-maybe("as", {parse-keyword("as"); pPatVar(pat)}).default(pat)

fun parse-patternBasic()
  parse-choices("pattern", [pPatCon, {pPatVar(PatWild)}, pPatLit, pPatWild, {parens(parse-pattern)}])

fun pPatCon()
  val skip = parse-maybe(".skip", {parse-special-id(".skip")}).is-just
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
  parse-maybe("pattern args", {parse-comma(); Cons(pattp, parse-patternArgs1())}).default([])

fun parse-patternArg()
  val pat = parse-pattern()
  val tp = parse-type-annotation()
  (pat, tp)

fun pPatVar(pat: pattern)
  val (name, _) = parse-var-id()
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

fun parse-parameter(allowBorrow: bool)
  val (name, pinfo) = parse-maybe("parameter info", {
    val pinfo = if allowBorrow then parse-param-info() else Own
    val (name, _) = parse-param-id()
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
  parse-choices("kind", [
    {parens(pKind)},
    {parse-special-con-id("V"); kindStar},
    {parse-special-con-id("X"); kindLabel},
    {parse-special-con-id("E"); kindEffect},
    {parse-special-con-id("H"); kindHeap},
    {parse-special-con-id("S"); kindScope},
    {parse-special-con-id("HX"); kindHandled},
    {parse-special-con-id("HX1"); kindHandled1},
  ])

fun env-range(l1: int, c1: int, l2: int, c2: int): eenv range
  make-source-range(src-path, l1, c1, l2, c2)

effect eenv
  fun env-extend(name: name, kind: kind): ()
  fun env-type(name: name, kind: kind): ktype
  fun env-qualify(name: name): name
  fun env-extend-synonym(syn-info: syn-info): ()
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
  bound: linear-map<name, type-var>
  imports: import-map
  unique: int
  gamma: gamma
  locals: linear-map<name, ktype>
  synonyms: name-map<syn-info>

fun with-env-initial(modName: name, srcPath: path, imports0, f: () -> _ a): _ a
  with with-synonyms(synonyms/empty)
  var bound := LinearMap([])
  var imports := imports0
  var unique := 1000
  var gamma := assumption/empty
  var locals := LinearMap([])
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
      Envv(bound, imports, unique, gamma, locals, get-synonyms())
    fun set-env(e)
      val Envv(b, i, u, g, l, s) = e
      bound := b
      imports := i
      unique := u
      gamma := g
      locals := l
      set-synonyms(s)
    val modname = modName
    fun env-extend(n, k)
      val id = unique.new-id
      unique := unique + 1
      val tv = TypeVar(id, k, Bound)
      bound := bound.add(n, tv)
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
            _ -> TCon(TypeCon(qname, k))
    fun env-qualify(n)
      qualify(n)
    fun env-extend-synonym(syn-info)
      synonyms-extend(syn-info)
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
      match gamma.lookup-canonical(n)
        [fnct as InfoFun] -> fnct.core-expr(n)
        [v as InfoVal] -> v.core-expr(n)
        [ex as assumption/InfoExternal] -> ex.core-expr(n)
        [] | n == nameFieldAddrOf -> 
          val a = TypeVar(0, kindStar, Bound)
          val fType = TForAll([a], TFun([(nil, TVar(a)), (nil, typeString), (nil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
          Var(TName(nameFieldAddrOf, fType), compiler/core/core/InfoExternal([]))
        res -> failure/fail("unknown identifier: " ++ n.show-plain ++ ": " ++ res.show-list(show)) 
  f()