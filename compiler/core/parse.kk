import std/os/path
import std/os/file
import std/data/linearmap
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
import compiler/kind/importmap
import compiler/type/type
import compiler/type/assumption
import compiler/platform/config
import compiler/core/core
import compiler/type/typevar

fun parseCore(fname: path)
  val input = read-text-file(fname)
  lex-parse(False, fn(lexes) lexes.allowDotIds.requalify, {parse-program(Source(fname.string, input))}, fname.string, input)

fun requalify(lexes: list<lexeme>): div list<lexeme>
  match lexes
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexId(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexIdOp(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexOp(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexId(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(Lexeme(r1, LexId(modName)), Cons(Lexeme(_, LexOp(slash)), Cons(Lexeme(r2, LexCons(nm)), lexx)))  | slash.nameStem  == "/"
      -> requalify(Cons(Lexeme(r1.combine(r2), LexCons(qualify(newName(modName.showPlain), nm))), lexx))
    Cons(lex, lexx)
      -> Cons(lex, requalify(lexx))
    [] -> []

fun allowDotIds(lexes: list<lexeme>): div list<lexeme>
  match lexes
    // Identifier
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexId(nm)), lexx)) -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(prepend(".", nm))), lexx))
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexWildCard(nm)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2),  LexWildCard (".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexId(nm)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId (nm.postpend("." ++ i.show))), lexx))
    // operator
    Cons(Lexeme(r1, LexKeyword(".")),Cons(Lexeme(r2, LexOp(nm)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId(".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexOp(nm)),Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexId(nm.postpend("." ++ i.show))), lexx))

    // constructor
    Cons(Lexeme(r1, LexKeyword(".")), Cons(Lexeme(r2, LexCons(nm)), lexx))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexCons(".".prepend(nm))), lexx))
    Cons(Lexeme(r1, LexCons(nm)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(r3, LexInt(i)), lexx)))
      -> allowDotIds(Cons(Lexeme(r1.combine(r3), LexCons(nm.postpend("." ++ i.show))), lexx))

    // (-.4), (++.2)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(nm)), Cons(Lexeme(_,LexInt(i)), Cons(Lexeme(r5,LexSpecial(")")), lexx)))) // | last (nmId nm) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(nm.postpend(i.show))), lexx))
    // (/.4)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_, LexOp(nm)), Cons(Lexeme(_, LexKeyword(".")), Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r5, LexSpecial(")")), lexx))))) // | last (nmId nm) == '.'
      -> allowDotIds(Cons(Lexeme(r1.combine(r5), LexId(nm.postpend("." ++ i.show))), lexx))
    // ([].1)
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")),Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(_, LexKeyword(".")),Cons(Lexeme(_, LexInt(i)),Cons(Lexeme(r2, LexSpecial(")")), lexx))))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId("[]".new-name.postpend("." ++ i.show))), lexx))
    // ([])
    Cons(Lexeme(r1, LexSpecial("(")), Cons(Lexeme(_,LexSpecial("[")), Cons(Lexeme(_, LexSpecial("]")),Cons(Lexeme(r2, LexSpecial(")")), lexx))))
      -> allowDotIds(Cons(Lexeme(r1.combine(r2), LexId("[]".new-name)), lexx))
    Cons(l, lx) -> Cons(l, allowDotIds(lx))
    Nil -> Nil

fun parse-inlines(prog: core, s: source, env: envv, inlines: list<lexeme>, gamma: gamma)
  with parse-lexemes(s, inlines)
  with withEnvInitial(prog.coreName, emptyImports)
  setEnv(env(gamma=gamma))
  val idefs = parse-many("inline", parse-inline-def)
  peof()
  idefs

fun parse-program(s: source)
  parse-many("semis", parse-semicolon)
  val (prog, env, inlines) = parse-module()
  peof()
  (prog, fn(gamma) parse-inlines(prog, s, env, inlines, gamma))

fun parse-module()
  val (_, doc) = parse-doc-keyword("module")
  parse-keyword("interface")
  val (name0, _) = parse-module-path()
  parse-many("semis", parse-semicolon)
  braced
    val (imps, impAliases) = semis("import", parse-import-declaration).unzip
    val impMap = impAliases.foldr(emptyImports) fn((asname, name'), m) 
      match m.importsExtend(asname, name')
        Just(imp') -> imp'
        Nothing -> m
    val externImports = semis("extern imports", parse-external-import-decl)
    val fixs = semis("fix decls", parse-fixity-declaration)
    with withEnvInitial(name0, impMap)
    val impsyns = semis("import synonyms", parse-local-alias)
    val tdefs = semis("type decls", parse-type-declaration)
    val defs = semis("fun decls", pDefDecl)
    val externs = semis("externs", parse-extern-decl)
    val inlines = parse-maybe("inlines", {parse-special("//.inline-section"); val rest = take-all(); put-all([]); rest}).default([]) // TODO: Read rest
    val tdefGroups = tdefs.map(fn(tdef) [tdef])
    val defGroups = defs.map(DefNonRec)
    (Core(name0, imps, fixs.concat, tdefGroups, defGroups, externImports ++ externs, doc), getEnv(), inlines)

fun parse-local-alias()
  parse-try("local alias", {parse-special-id("local"); parse-keyword("alias")})
  val qname = pQTypeId().fst
  val name = envQualify(qname)
  val params = parse-type-params()
  val kind = parse-kind-annot-full()
  parse-keyword("=")
  val tp = parse-type()
  val rank = parse-maybe("", {parse-keyword("="); parse-integer().fst}).default(0)
  val syn = SynInfo(name, kind, params, tp, rank, rangeNull, Private, "")
  envExtendSynonym(syn)
  syn

fun default/parse-visibility()
  parse-maybe("visibility", {parse-keyword("pub"); Public}).default(Private)

fun parse-import-declaration(): <parse> (compiler/core/core/kimport, (name, name))
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
      val (vis, (ddef, isExtend, sort, doc)) = parse-try({(parse-visibility(), parse-type-sort())})
      val tn = if isExtend then
          pQTypeId().fst
        else
          qualify(modname, parse-choices("identifier", [pTBinderId, pIdOp]).fst)
      val params = parse-type-params()
      val kind = parse-kind-annot-full()
      val cons = parse-maybe("constructor", {parse-semi-braces("contructor args", {parse-constructor-declaration(tn, params, sort)}).fst}).default([])
      val cons1 = match cons
        [con1] -> [con1(singleton=True)]
        _ -> cons
      val dataInfo = DataInfo(sort, tn, kind, params, cons1, rangeNull, ddef, vis, doc)
      Data(dataInfo, isExtend)
    },{
      val (vis, doc) = parse-try({(parse-visibility(), parse-doc-keyword("alias").snd)})
      val name = pTBinderId().fst
      val params = parse-type-params()
      val kind = parse-kind-annot-full()
      parse-keyword("=")
      val tp = parse-type()
      val rank = parse-maybe("rank", {parse-keyword("="); parse-integer().fst}).default(0)
      val qname = qualify(modname, name)
      val syn = SynInfo(qname, kind, params, tp, rank, rangeNull, vis, doc)
      envExtendSynonym(syn)
      Synonym(syn)
    }
  ])

fun parse-constructor-declaration(tname0: name, foralls: list<typeVar>, sort: dataKind)
  val (vis, doc) = parse-try({(parse-visibility(), parse-doc-keyword("con").snd)})
  val name = parse-constructorId().fst
  val exists0 = parse-type-params()
  val params = parse-parameters()
  val vrepr = pValueRepr()
  val tp = parse-type-annotation()
  val params2 = params.zip(list(1, params.length)).map(fn(((n, t), i)) (if n.nameStem == "" then i.newFieldName else name, t))
  val orderedFields = []
  ConInfo(qualify(modname, name), tname0, foralls, exists0, params2, tp, sort, rangeNull, params2.map(fn(_) rangeNull), params2.map(fn(_) Public), False, orderedFields, vrepr, vis, doc)

fun parse-type-sort()
  val isRec = parse-maybe("recursive", {parse-special-id("recursive")}).is-just
  val (ddef0, isExtend, sort) = parse-type-modifier()
  val doc = parse-doc-keyword("type").snd
  val ddef = match (isRec, ddef0)
    (True, DataDefNormal) -> DataDefRec
    _ -> ddef0
  (ddef, isExtend, sort, doc)

fun parse-type-modifier()
  parse-choices("type modifier", [
    {parse-special-id("open"); (DataDefOpen, False, Inductive)},
    {parse-special-id("extend"); (DataDefOpen, True, Inductive)},
    {parse-special-id("value"); (DataDefValue(pValueRepr()), False, Inductive)},
    {parse-special-id("co"); (DataDefNormal, False, CoInductive)},
    {parse-special-id("rec"); (DataDefNormal, False, Retractive)},
    {(DataDefNormal, False, Inductive)}
  ])

fun pValueRepr()
  braced
    val rraw = parse-integer().fst
    parse-comma()
    val scan = parse-integer().fst
    parse-comma()
    val align = parse-integer().fst
    ValueRepr(rraw, scan, align)

fun pDefDecl()
  val (vis, sort0, inl, doc) = parse-try({val vis = parse-visibility(); val (sort, inl, _, doc) = pDefSort(); (vis, sort, inl, doc)})
  val (name, _) = parse-choices("decl name", [parse-fun-id, pIdOp])
  parse-keyword(":")
  val (tp, pinfos) = parse-def-type()
  val sort = match sort0
    DefFun(_, fipT) -> DefFun(pinfos, fipT)
    _ -> sort0
  Def(qualify(modname, name), tp, ELit(LitString("core/parse " ++ name.show ++ ": cannot get the expression from an interface core file")), vis, sort, inl, rangeNull, doc)

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
  InlineDef(envQualify(name), e, isRec, inl, if inl.is-inlineAlways then 0 else e.cost, sort, specArgs)

fun parse-extern-decl()
  val (vis, fipT, doc) = parse-try({(parse-visibility(), pFip(), parse-doc-keyword("extern").snd)})
  val (name, rng) = parse-fun-id()
  parse-keyword(":")
  val (tp, pinfos) = parse-def-type()
  val formats = parse-external-body()
  External(qualify(modname, name), tp, pinfos, formats, vis, fipT, rng, doc)

fun parse-external-body()
  parse-choices("external body", [
    {parse-keyword("="); [parse-external-entry()]},
    {parse-semi-braces("external entry", parse-external-entry).fst}
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
  ExternalImport(parse-external-import-body(), rangeNull)

fun parse-external-import-keyval()
  val key = parse-string-literal().fst
  parse-keyword("=")
  val v = parse-string-literal().fst
  (key, v)

fun parse-external-import-entry()
  val target = parse-external-target()
  (target, parse-semi-braces("external key value", parse-external-import-keyval).fst)

fun parse-external-import-body()
  parse-choices("external import body", [
    {
      parse-keyword("=")
      [parse-external-import-entry()]
    },
    {
      parse-semi-braces("external import entries",parse-external-import-entry).fst
    }
  ])

fun parse-inline-def-sort()
  val isRec = parse-maybe("inline recursive", {parse-special-id("recursive")}).is-just
  val inl = parse-inline()
  val spec = parse-maybe("inline specialize", {parse-special-id("specialize"); val (s,_) = parse-string-literal(); s.list.map(fn(c) c == '*')}).default([])
  val pinfos = parse-maybe("inline borrow", {parse-special-id("borrow"); val (s, _) = parse-string-literal(); s.list.map(fn(c) if c == '^' then Borrow else Own)}).default([])
  parse-choices("fun or val inline", [
    {
      val f = pFip()
      val (_, doc) = parse-doc-keyword("fun")
      (DefFun(pinfos, f), inl, isRec, spec, doc)
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

fun parse-app(): <parse,eenv,comp-flags,synonymsEff> expr
  val expr = parse-atomic()
  fun parseApplies(e)
    parse-choices("app", [
      {
        val args = parse-parens-commas(parse-expression).fst
        parseApplies(App(e, args))
      },
      {
        val tps = angles({parse-sep-by("expr args", parse-type, parse-comma)}).fst
        parseApplies(TypeApp(e, tps))
      },
      {e}
    ])
  parseApplies(expr)

fun parse-atomic()
  parse-choices("atom", [parse-con, parse-var, {ELit(parse-lit())}, {parens(parse-expression).fst}])

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
  val eff = parse-maybe("type parameters", {angles(parse-type).fst}).default(typeTotal)
  val params = parse-parameters()
  val body = semi-braced("fun", parse-expression)
  Lam(params.map(fn((n, t)) TName(n, t)), eff, body)

fun parse-match()
  parse-keyword("match")
  val args = parse-parens-commas(parse-expression).fst
  val branches = parse-semi-braces("match branches", parse-branch).fst
  Case(args, branches)

fun parse-con()
  val name = pQualifiedConId()
  val InfoCon(_, typ, repr) = envLookuparse-con(name)
  Con(TName(name, typ), repr)

fun parse-var()
  val name = parse-choices("var identifier", [parse-qualified-var-id, parse-qualified-op-id]).fst
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

fun parse-def-group(): <parse,eenv,comp-flags,synonymsEff> defGroup
  val (sort, inl, _, doc) = pDefSort()
  val (name, _) = parse-choices("def group", [{parse-fun-id(True)}, {parse-wildcard(); (nil, rangeNull)}])
  val tp = parse-type-annotation()
  val expr = parse-body()
  envExtendLocal(name, tp)
  DefNonRec(Def(name, tp, expr, Private, sort, inl, rangeNull, doc))

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
  parse-choices("pattern", [pPatCon, {pPatVar(PatWild)}, pPatLit, pPatWild, {parens(parse-pattern).fst}])

fun pPatCon()
  val skip = parse-maybe(".skip", {parse-special-id(".skip")}).is-just
  val cname = pQualifiedConId()
  val exists0 = parse-type-params()
  val args = parse-try({parse-left-paren(); val x = parse-patternArgs0(); parse-right-paren(); x})
  val (patArgs, argTypes) = args.unzip
  val resTp = parse-type-annotation()
  val InfoCon(_, typ, repr, cons) = envLookuparse-con(cname)
  PatCon(TName(cname, typ), patArgs, repr, argTypes, exists0, resTp, cons, skip)

fun parse-patternArgs0(): <parse,eenv,comp-flags,synonymsEff> list<(pattern, ktype)>
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
  envExtendLocal(name, tp)
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
  val iparams = parse-maybe("parameters", {parse-parens-commas({parse-parameter(False)}).fst}).default([])
  val (params, _) = iparams.unzip
  params.map(fn((n, t)) envExtendLocal(n, t))
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
  angles(pTBinders).fst

fun pTBinders()
  val bs = parse-sep-by("quantifiers", pTBinder, parse-comma)
  bs.map fn((name, kind)) 
    envExtend(name, kind)
    match envType(name, kind)
      TVar(tv) -> tv
      _ -> fail("core/parse pTBinders: expecting type variable")

fun pTBinder()
  parse-choices("quantifier", [
    {
      val id = parse-choices("type parameter", [parse-var-id, parse-wildcard]).fst
      val kind = parse-kind-annot-full()
      (id, kind)
    },
    {
      parens(pTBinder).fst
    }
  ])

fun parse-kind-annot-full()
  parse-kind-annot()

fun parse-kind-annot()
  parse-maybe("kind annotation", {parse-special-op("::"); pKind()}).default(kindStar)

fun parse-type(): <parse,eenv,comp-flags,synonymsEff> ktype
  parse-typex(False).tuple2/fst

fun parse-def-type()
  val (tp, pinfos) = parse-typex(True)
  (tp, if pinfos.all(is-own) then [] else pinfos)

fun parse-typex(allowBorrow: bool)
  parse-try
    val quantify = parse-tforall()
    val (tp, pinfos) = parse-type-arrow(allowBorrow)
    val preds = parse-qualifier()
    (quantify(preds, tp), pinfos)

fun parse-tforall()
  val params = parse-maybe("type forall", {parse-keyword("forall"); parse-type-params1()})
  fn(ps:list<pred>, rho)
    if ps.is-nil then rho else TForAll(params.default([]), ps, rho)

fun parse-qualifier()
  parse-maybe("qualifier", {parse-keyword("with"); parse-many1("qualifier predicates", parse-predicate)}).default([])

fun parse-predicate(): <parse,eenv,comp-flags,synonymsEff> pred
  parse-try
    val (name, _) = parse-qualified-var-id()
    val tps = parse-maybe("predicate type parameters", {angles({parse-sep-by("predicates", parse-type, parse-comma)}).fst}).default([])
    PredIFace(envQualify(name), tps)  

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

fun parse-type-atom(): <parse,eenv,comp-flags,synonymsEff> ktype
  val etp = parse-type-atoms-paramsx(False, False)
  match etp
    Left((params, _)) -> parse-type-app(extract(params, "expecting single type"))
    Right(tp) -> tp

fun extract(params, msg)
  match params
    Nil -> typeUnit
    [(name, tp)] | name == nil -> tp
    _ -> 
      if params.all(fn(n) n.fst == nil) then
        TApp(type-tuple(params.length), params.map(snd))
      else
        fail(msg)

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
  val tps = parse-maybe("type application", {angles({parse-sep-by("type params", parse-type, parse-comma)}).fst}).default([])
  parse-synonym(tp, tps)

fun parse-synonym(tp, tps): <parse,eenv,comp-flags,synonymsEff> ktype
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
      TSyn | tps.is-empty -> tp
      _ -> fail("illegal type alias expression " ++ tp.show)
  match res
    Just(t) -> t
    Nothing -> envTypeApp(tp, tps)

fun parse-type-effect()
  with parse-try
  parse-left-angle()
  val labels = parse-sep-by("effect type", pTLabel, parse-comma)
  val ext = pTExtend()
  parse-right-angle()
  labels.foldr(ext, shallow-effect-extend)

fun pTExtend(): <parse,eenv,comp-flags,synonymsEff> ktype
  parse-maybe("effect extend", {parse-vertical-bar(); parse-type-atom()}).default(effectEmpty)

fun pTLabel()
  parse-type-app(parse-type-atom())

fun pTId(): <parse,eenv,comp-flags,synonymsEff> ktype
  val (name, _) = parse-choices("type id", [parse-qualified-var-id, parse-qualified-op-id, parse-wildcard])
  val kind = parse-maybe("type kind", parse-kind-annot-full).default(kindStar)
  envType(name, kind)

fun pKind()
  parse-choices("kind", [
    {val params = parse-parens-commas(pKind).fst; parse-keyword("->"); val res = pKind(); params.foldr(res, kind-fun)},
    {val k = pKatom(); parse-choices("kind arrow", [{parse-keyword("->"); val res = pKind(); kind-fun(k, res)}, {k}])}
  ])

fun pKatom()
  parse-choices("kind", [
    {parens(pKind).fst},
    {parse-special-con-id("V"); kindStar},
    {parse-special-con-id("X"); kindLabel},
    {parse-special-con-id("E"); kindEffect},
    {parse-special-con-id("H"); kindHeap},
    {parse-special-con-id("S"); kindScope},
    {parse-special-con-id("HX"); kindHandled},
    {parse-special-con-id("HX1"); kindHandled1},
    {parse-special-con-id("P"); kindPred}
  ])


effect eenv
  fun envExtend(name: name, kind: kind): ()
  fun envType(name: name, kind: kind): ktype
  fun envQualify(name: name): name
  fun envExtendSynonym(synInfo: synInfo): ()
  fun envTypeApp(tp: ktype, args: list<ktype>): ktype
  fun envExtendLocal(name: name, tp: ktype): ()
  fun env-lookup-local(name: name): ktype
  fun envLookuparse-con(name: name): nameInfo
  fun env-lookup-var(name: name): expr
  val modname : name
  fun getEnv(): envv;
  fun setEnv(env: envv): ()

struct envv
  bound: linearMap<name, typeVar>
  imports: importmap
  unique: int
  gamma: gamma
  locals: linearMap<name, ktype>
  synonyms: name-map<synInfo>;

fun withEnvInitial(modName: name, imports0, f: () -> <eenv,parse,comp-flags,synonymsEff> a): <comp-flags,parse> a
  with withSynonyms(synonyms/empty)
  var bound := LinearMap([])
  var imports := imports0
  var unique := 1000
  var gamma := assumption/empty
  var locals := LinearMap([])
  fun qualify(n: name)
    if n.is-qualified then
      match imports.importsExpand(n)
        Right((qname, _)) -> qname
        Left(amb) -> 
          trace("core/parse qualify: unable to expand name: " ++ n.show ++ ": " ++ amb.show-list(show))
          n
    else name/qualify(modName, n)
  with handler
    fun getEnv()
      Envv(bound, imports, unique, gamma, locals, getSynonyms())
    fun setEnv(e)
      val Envv(b, i, u, g, l, s) = e
      bound := b
      imports := i
      unique := u
      gamma := g
      locals := l
      setSynonyms(s)
    val modname = modName
    fun envExtend(n, k)
      val id = newId(unique)
      unique := unique + 1
      val tv = TypeVar(id, k, Bound)
      bound := bound.add(n, tv)
    fun envExtendLocal(n, k)
      unique := unique + 1
      locals := locals.set(n, k)
    fun envType(n, k)
      match bound.maybeGet(n)
        Just(tv) -> TVar(tv)
        Nothing ->
          val qname = qualify(n)
          match synonyms-lookup(qname)
            Just(info as SynInfo(name, kind, params, tp, rank)) | params.is-empty ->
              TSyn(TypeSyn(name, kind, rank, Just(info)), [], tp)
            _ -> TCon(TypeCon(qname, k))
    fun envQualify(n)
      qualify(n)
    fun envExtendSynonym(synInfo)
      synonymsExtend(synInfo.name, synInfo)
    fun envTypeApp(tp, tps)
      match tp
        TCon(TypeCon(name0, _)) ->
          match synonyms-lookup(name0)
            Just(synInfo as SynInfo(name, kind, params, syntp, rank)) | params.length == tps.length ->
              TSyn(TypeSyn(name, kind, rank, Just(synInfo)), tps, subNew(params.zip(tps)) |-> syntp)
            _ -> typeApp(tp, tps)
        _ -> typeApp(tp, tps)
    fun env-lookup-local(n)
      match locals.maybeGet(n)
        Just(tp) -> tp
        Nothing -> fail("core/parse unbound local: " ++ n.show)
    fun envLookuparse-con(n)
      match gamma.gammaLookupExactCon(n)
        [c as InfoCon] -> c
        res -> fail("unknown constructor " ++ n.show ++ ": " ++ res.show-list(show))
    fun env-lookup-var(n)
      match gamma.gammaLookupCanonical(n)
        [fnct as InfoFun] -> fnct.coreExpr(n)
        [v as InfoVal] -> v.coreExpr(n)
        [ex as assumption/InfoExternal] -> ex.coreExpr(n)
        [] | n == nameFieldAddrOf -> 
          val a = TypeVar(0, kindStar, Bound)
          val fType = TForAll([a], [], TFun([(nil, TVar(a)), (nil, typeString), (nil, typeString)], typeTotal, TApp(typeFieldAddr, [TVar(a)])))
          Var(TName(nameFieldAddrOf, fType), compiler/core/core/InfoExternal([]))
        res -> fail("unknown identifier: " ++ n.showPlain ++ ": " ++ res.show-list(show)) 
  f()