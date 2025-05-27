//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

module compiler/syntax/parse
import std/os/path
import std/os/file
import std/data/sort
import compiler/syntax/lexeme
import compiler/syntax/layout
import compiler/syntax/syntax
import compiler/syntax/builders
import compiler/syntax/promote
import compiler/syntax/parse-type
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/parse


// Updated to commit #a22ccc2 (of Parse.hs)

pub fun parse-program-from-file(fname: path, allow-at: bool, semiInsert: bool = True): io userProgram
  val r = read-text-file(fname)
  parse-program-from-string(r, fname, allow-at, semiInsert)

pub fun parse-program-from-string(input: string, fname: path, allow-at: bool, semiInsert: bool = True): io userProgram
  with handler
    final ctl parse-error(e: string, r: range)
      throw("Parse error: " ++ e ++ " at " ++ r.show) // TODO: Transition to error
  lex-parse(allow-at, semiInsert, fn(x) x.remove-white, parse-program, fname.string, input)

fun string/lex-parse(str: string, sourceName: path, line: int, semiInsert: bool, p: () -> parse a): io a
  with handler
    final ctl parse-error(e: string, r: range)
      throw("Parse error: " ++ e ++ " at " ++ r.show) // TODO: Transition to error
  lex-parse(False, semiInsert, fn(x) x, p, sourceName.string, str)

pub fun parse-value-def(input: string, fname: path, line: int, semiInsert: bool): io userDef
  lex-parse(input, fname, line, semiInsert, parse-value-definition)

pub fun parse-type-def(input: string, fname: path, line: int, semiInsert: bool): io (userTypeDef, list<userDef>)
  lex-parse(input, fname, line, semiInsert, parse-type-definition)

pub fun lex-parse-type(input: string, fname: path, line: int, name: name, semiInsert: bool): io userTypeDef
  lex-parse(input, fname, line, semiInsert, {parse-user-type(name)})

pub fun lex-parse-expression(input: string, fname: path, line: int, name: name, semiInsert: bool): io userDef
  lex-parse(input, fname, line, semiInsert, {parse-user-expression(name)})

fun interactive(f: () -> parse a): parse a
  val x = f()
  parse-many("semicolons", parse-semicolon)
  x

fun parse-value-definition(): parse userDef
  interactive
    parse-pure-decl(False, Private)

fun parse-type-definition(): parse (userTypeDef, list<userDef>)
  interactive
    parse-choices("type definition", [
      {(parse-alias-decl(Public), [])},
      {parse-type-declaration(Public)}
    ])

fun parse-user-type(name: name): parse userTypeDef
  interactive
    val tp = parse-type()
    Synonym(TypeBinder(name, KindNone, null, null), [], tp, tp.range, Public, "")

fun parse-user-expression(name: name): parse userDef
  interactive
    val e = parse-annotated-expr()
    val r = e.range
    Def(ValueBinder(name.unqualify, (), Lam([], e, False, r), r, r), r, Public, DefFun([], noFip), InlineNever, "")

fun parse-dependencies(source: source, lexemes: list<lexeme>): io list<kimport>
  with handler
    final ctl parse-error(e: string, r: range)
      throw("Parse error: " ++ e ++ " at " ++ r.show) // TODO: Transition to error
  parse-lexemes(source, lexemes, parse-module-deps)

// Program
fun parse-program(): <parse,fsys> userProgram
  parse-many("semicolons", parse-semicolon)
  val p = parse-module()
  peof()
  p

fun parse-module-decl(fpath: path)
  parse-choices-nb("module decl", [{
    val (_, doc) = parse-doc-keyword("module")
    val (name, rng) = parse-module-path()
    (Private, doc, name, rng)
  },{
    val mname = fpath.basename.path-to-module-name
    (Public, "", mname, range/null)
  }])

fun parse-module(): <parse,fsys> userProgram
  val (vis, doc, name, namerng) = parse-module-decl(source-info.name.path)
  parse-body(vis, name, namerng, doc)

// Lex imports only; this is more lenient
fun parse-module-deps(): <parse,fsys> list<kimport>
  val (_, _, name, _) = parse-module-decl(source-info.name.path)
  val imports = parse-import-decls()
  include-std-core(name, imports)
  // no eof.. try to parse as far as possible

fun include-std-core(nm: name, imports: list<kimport>): list<kimport>
  if nm.is-system-core-name || imports.any(fn(imp:kimport) imp.name == nameSystemCore) then imports
  else Cons(Kimport(nameSystemCore, nameSystemCore, null, null, null, Private, False), imports)

fun parse-import-decls()
  parse-many("semicolons", parse-semicolon)
  parse-option-maybe("open body", parse-left-curly)
  parse-many("semicolons", parse-semicolon)
  semis("imports", parse-import-declaration)

// Program body
fun parse-body(vis: visibility, name: name, rng: range, doc: string): <parse,fsys> userProgram
  parse-many("semicolons", parse-semicolon)
  val (imports, fixDefss, topDefss) = braced
    val imps = semis("imports", parse-import-declaration)
    // trace("imports " ++ imps.show)
    val fixs = semis("fixities", parse-fixity-decl)
    // trace("fixities " ++ fixs.show)
    val tdefs = semis("topDefs", {val tdef = parse-top-def(vis); // trace(tdef.show ++ "\n\n"); 
                                  tdef})
    // trace("top defs " ++ tdefs.show)
    (imps, fixs, tdefs)
  parse-many("semicolons", parse-semicolon)
  val (defs, typeDefs, externals) = split-top-defs(topDefss.concat)
  Program(source-info, name, rng, [TypeDefRec(typeDefs)], [DefRec(defs)], include-std-core(name, imports), externals, fixDefss.concat, doc)

struct funDef
  tpars: list<typeBinder<userKind>> 
  pars: list<valueBinder<maybe<userType>, maybe<userExpr>>>
  pinfos: list<paramInfo>
  parsRng: range
  mbTres: maybe<(maybe<userType>, userType)>
  preds: list<userType>
  ann: (userExpr -> parse userExpr);

fun parse-top-def(vis): <parse,fsys> list<topDef>
  parse-choices("topDef", [
    {[DefValue(parse-pure-decl(True, vis))]},
    {[DefType(parse-alias-decl(vis))]},
    {
      val (tdef, cdefs) = parse-type-declaration(vis)
      Cons(DefType(tdef), cdefs.map(DefValue))
    },
    {parse-effect-decl(vis)},
    {parse-extern-decl(vis)}
  ])

// Import declaration
fun parse-import-declaration(): parse kimport
  val (vis, vrng, rng0, open) = parse-try
    val (vis, vrng) = parse-visibility(Private)
    val isOpen = parse-option-maybe("open", {parse-special-id("@open")}).is-just
    val rng0 = parse-keyword("import")
    (vis, vrng, rng0, isOpen)
  val (asname, name, asrng, namerng) = parse-import-alias()
  Kimport(asname, name, asrng, namerng, combine([vrng, rng0, namerng]), vis, open)

fun parse-visibility(vis: visibility = Private): parse (visibility, range)
  parse-choices-nb("visibility", [{
    val rng = parse-keyword("pub", ["public"])
    (Public, rng)
  },
  {
    val rng = parse-keyword("private")
    add-warning("using private is deprecated, only use 'pub' to make declarations public", rng)
    (Private, rng)
  },{(vis, null)}])

// External
fun parse-extern-decl(dvis: visibility): <parse,fsys> list<topDef>
  parse-choices("externDecl", [{
    val krng = parse-doc-keyword("extern").fst
    val _ = parse-choices-nb("import", [
      { parse-keyword("import"); () },
      {
        parse-special-id("include"); 
        warn-deprecated("include", "import", krng); 
      }])
    [DefExtern(parse-external-import(krng))]
  }, {
    val (vis,vrng) = parse-visibility(dvis)
    val inl = parse-inline()
    val (fip, frng) = parse-tail-fip()
    val (erng, doc) = parse-doc-keyword("extern",[])
    val krng = combine([vrng, frng, erng])
    val (name, nameRng) = parse-fun-id(True) // Top level
    val (pars, pinfos, args, tp, annotate) = parse-choices-nb("extern type", [
      {
        parse-keyword(":")
        val tp = parse-type() // No "some" allowed
        val (pars, args) = gen-parameter-args(promote-type(tp))
        (pars, [], args, tp, fn(body) Ann(body, tp, tp.range))
      },
      {
        val tpPars = parse-type-params()
        val (pars, pinfos, _) = parse-decl-params(True, !inl.is-inlineAlways)
        val (teff, tres) = parse-annotated-result()
        val tp = type-from-params(nameRng, pars, teff, tres)
        (pars.map(fn(ValueBinder(name', tp', expr, rng1, rng2)) ValueBinder(name', Just(tp'), expr, rng1, rng2)), 
                  pinfos, gen-args(pars), tp, fn(body) promote([], tpPars, [], Just((Just(teff), tres)), body))
      }
    ])
    val (exprs, rng) = parse-external-body()
    val fullRng = combine([krng, vrng, rng])
    if (inl.is-inlineAlways) then [DefExtern(External(name, tp, pinfos, nameRng, fullRng, exprs, vis, fip, doc))]
    else
      val externName = name.new-hidden-external-name
      val ext = External(externName, tp, pinfos, nameRng.before, fullRng.before, exprs, Private, fip, doc)
      val body = annotate(Lam(pars, App(Var(externName, False, null), args, fullRng), True, fullRng))
      val binder = ValueBinder(name, (), body, nameRng, fullRng)
      val extfun = Def(binder, fullRng, vis, def-fun-ex(pinfos, fip), InlineNever, doc)
      [DefExtern(ext), DefValue(extfun)]
  }
  ])

fun parse-external-import-key-val(): parse (string, string)
  val key = parse-external-import-key()
  parse-keyword("=")
  val (v, _) = parse-string-literal()
  (key, v)

fun parse-external-import-key(): parse string
  val (id, _) = parse-var-id()
  id.show

fun parse-external-includes(target: target, rng: range, (key, fname): (string, string)): <fsys,parse-error> list<(string, string)>
  val currentFile = rng.source.name
  val fpath = currentFile.path.dirname / fname
  if target.is-c && fpath.extname == "" && key == "file" then
    [("header-include-inline", pread-file(fpath.change-ext("h"))), ("include-inline", pread-file(fpath.change-ext("c")))]
  elif target.is-c && key == "header-file" then
    [("header-include-inline", pread-file(fpath))]
  elif target.is-c && key == "header-end-file" then
    [("header-end-include-inline", pread-file(fpath))]
  elif key == "file" then
    [("include-inline", pread-file(fpath))]
  else [(key, fpath.show)]

fun pread-file(fpath: path): <fsys,parse-error> string
  catch({read-text-file(fpath)}, fn(e) {
      trace("Error reading file " ++ fpath.show)
      parse-error("Unable to read external file at path: " ++ fpath.show ++ ": got error " ++ e.message, null)
    })

fun parse-external-import-entry() : <parse,fsys> (target, list<(string, string)>)
  val target = parse-external-target()
  val (key-vals, rng) = parse-choices("", [
    { val key = parse-external-import-key(); 
      val (v, rng) = parse-string-literal(); 
      ([(key, v)], rng)
    },
    { parse-semi-braces-ranged("", parse-external-import-key-val) }
    ])
  (target, key-vals.map(fn(kv) {parse-external-includes(target, rng, kv)}).concat)

fun parse-external-import(r: range): <parse,fsys> external
  parse-choices-nb("import", [
    {
      parse-keyword("=")
      val entry = parse-external-import-entry()
      ExternalImport([entry], r)
    },{
      val (entries, rng2) = parse-semi-braces-ranged("entries", parse-external-import-entry)
      ExternalImport(entries, r.combine(rng2))
    }
  ])
 
fun parse-external-body(): parse (list<(target, externalCall)>, range) 
  parse-semi-braces-ranged("external entries", parse-external-entry)

fun parse-external-entry(): parse (target, externalCall)
  val (target, inl, _) = parse-external-entry-range()
  (target, inl)

fun parse-external-entry-range(): parse (target, externalCall, range)
  val target = parse-external-target()
  val (call, rng) = parse-external-call()
  (target, call, rng)

fun parse-external-call(): parse (externalCall, range)
  val f = parse-option-maybe("inline", {parse-special-id("inline"); ExternalInline}).default(ExternalCall)
  val (s, rng) = parse-string-literal()
  (f(s), rng)

fun parse-external-target(): parse target
  parse-choices-nb("target", [
    {parse-special-id("c"); C(CDefault)},
    {parse-special-id("cs"); CS},
    {parse-special-id("js"); JS(JsDefault)},
    {DefaultTarget}
  ])

// Fixity declaration
fun parse-fixity-decl(): parse list<fixDef>
  val (vis, vrng, assoc) = parse-try
    val (vis, vrng) = parse-visibility(Private); 
    val assoc = parse-assoc-decl(); 
    (vis, vrng, assoc)
  val (prec, lex) = parse-integer()
  if prec < 0 || prec > 100 then
    parse-error("fixity must be between 0 and 100", lex.range)
  val names = parse-sep-by1("names", parse-identifier, parse-comma)
  names.map(fn((name, rng)) FixDef(name, FixInfix(prec, assoc), rng.combine(vrng), vis))

fun parse-assoc-decl(): parse assoc
  parse-choices-nb("associativity", [
    {parse-keyword("infixl"); AssocLeft},
    {parse-keyword("infixr"); AssocRight},
    {parse-keyword("infix"); AssocNone}
  ])

// Type definitions
fun parse-alias-decl(dvis: visibility): parse userTypeDef
  val (vis, vrng, trng, doc) = parse-try
    val (vis, vrng) = parse-visibility(dvis)
    val (trng, doc) = parse-doc-keyword("alias")
    (vis, vrng, trng, doc)
  val tbind = parse-type-binder-def()
  val (tpars, kind, krng) = parse-type-kind-params()
  parse-keyword("=")
  val tp = parse-type()
  val range = combine([vrng, trng, krng, tp.range])
  Synonym(tbind(kind), tpars, tp, range, vis, doc) 

fun parse-type-declaration(vis: visibility): parse (userTypeDef,list<userDef>)
  parse-choices-nb("type", [{parse-data-type-decl(vis)}, {parse-struct-decl(vis)}])

fun parse-data-type-decl(dvis: visibility): parse (userTypeDef,list<userDef>)
  val (vis, defvis, vrng, (typeSort, trng, doc, ddef)) = parse-choices-nb("type", [
    {
      val rng = parse-keyword("abstract")
      val x = parse-type-declaration-kind()
      (Public, Private, rng, x)
    },
    {
      val (vis, rng) = parse-visibility(dvis)
      val x = parse-type-declaration-kind()
      (vis, vis, rng, x)
    }
  ])
  val tbind =
    if ddef.is-extend then
      val (qid, rng) = parse-qualified-type-id()
      fn(kind) TypeBinder(qid, kind, rng, combine([vrng, trng, rng]))
    else parse-type-binder-def()
  val (tpars, k, prng) = parse-type-kind-params()
  val name = tbind(k)
  val resTp = TpApp(name.tp-con, tpars.map(tp-var), combine(Cons(name.range, tpars.map(range))))
  val (cs, crng) = parse-maybe("", {parse-semi-braces-ranged("", {parse-constructor(defvis, tpars, resTp)})}).default(([], null))
  val (constrs, creatorss) = cs.unzip
  val range = combine([vrng, trng, name.range, prng, crng])
  (DataType(name, tpars, constrs, range, vis, typeSort, ddef, DataNoEffect, doc), creatorss.concat)

fun parse-struct-decl(dvis': visibility): parse (userTypeDef,list<userDef>)
  val ((vis, defvis, ddef), (vrng, trng, doc)) = parse-try
      val (vis, defvis, rng1) = parse-choices-nb("", [
        {val rng = parse-keyword("abstract"); (Public, Private, rng)}, 
        {val (vis, rng) = parse-visibility(dvis'); (vis, vis, rng)}
      ])
      val (rng2, ddef) = parse-choices-nb("", [
        {val rng = parse-special-id("value"); (rng, DataDefValue(valuerepr/zero))},
        {val rng = parse-special-id("reference", ["ref"]); (rng, DataDefNormal)},
        {(rng1, DataDefAuto(True))}
      ])
      val (trng, doc) = parse-doc-keyword("struct")
      ((vis, defvis, ddef), (combine([rng1,rng2,trng]), trng, doc))
  val tbind = parse-type-binder-def()
  val tpars = parse-maybe("", {angles(parse-type-binders)}).default([])
  val n = tbind(KindNone)
  val resTp = TpApp(n.tp-con, tpars.map(tp-var), n.range.combine(tpars.last.map(range).default(n.range)))
  val (pars, prng) = parse-con-parameters(defvis)
  val (tid, rng) = (n.name, n.name-range)
  val conId = tid.to-constructor-name
  val (usercon, creators) = make-user-constructor(conId, tpars, resTp, [], pars, Nothing, rng, rng.combine(prng), defvis, doc)
  (DataType(n, tpars, [usercon], combine([vrng, trng, rng, prng]), vis, Inductive, ddef, DataNoEffect, doc), creators)

fun parse-type-declaration-kind(): parse (dataKind, range, string, dataDef)
  parse-choices("", [
    {
      val (rng1, kind) = parse-choices-nb("", 
        [{val rng = parse-special-id("div", ["rec"]); (rng, Retractive)},
         {val rng = parse-special-id("co"); (rng, CoInductive)}])
      val (rng2, doc) = parse-doc-keyword("type")
      (kind, rng1.combine(rng2), doc, DataDefNormal)
    },
    {
      val (rng1, ddef) = parse-choices-nb("", [
        {val rng = parse-special-id("open"); (rng, DataDefOpen(False))},
        {val rng = parse-special-id("extend"); (rng, DataDefOpen(True))},
        {val rng = parse-special-id("value"); (rng, DataDefValue(valuerepr/zero))},
        {val rng = parse-special-id("lazy"); val (f, frng) = parse-tail-fip(); (combine([rng, frng]), DataDefLazy(f))},
        {val rng = parse-special-id("reference", ["ref", "heap"]); (rng, DataDefNormal)},
        {(null, DataDefAuto(False))} // not declared as a struct
      ])
      val (rng2, doc) = parse-doc-keyword("type")
      (Inductive, combine([rng1, rng2]), doc, ddef)
    }
  ])

fun parse-type-kind-params(): parse (list<userTypeBinder>,userKind,range)
  parse-choices-nb("", [
    { val (tpars, rng) = angles-ranged(parse-type-binders); 
      val kind = parse-kind-annotation(); 
      (tpars, kind, rng.combine(kind.range))},
    { val kind = parse-kind-annotation(); 
      ([], kind, kind.range)},
    { ([], KindNone, null)}
  ])

fun parse-constructor(dvis: visibility, foralls: list<userTypeBinder>, resTp: userType)
  val (vis, vrng) = parse-visibility(dvis)
  val (mbLazyFip, lrng) = parse-option-maybe("lazy", {parse-special-id("lazy"); val (fip, rng) = parse-tail-fip(); (Just(fip), rng)}).default((Nothing, null))
  val rng0 = parse-option-maybe("", {parse-keyword("con")}).default(null)
  val (constr, (rng, doc)) = parse-doccon-id()
  val exists0 = parse-type-params()
  val (pars, prng) = parse-con-parameters(vis)
  val mbLazyExpr = 
    match mbLazyFip
      Nothing -> Nothing
      Just(fip) ->
        parse-keyword("->")
        Just((fip, parse-block-expr()))
  make-user-constructor(constr, foralls, resTp, exists0, pars, mbLazyExpr, rng, combine([vrng, rng0, rng, prng, lrng]), vis, doc) // More range

fun parse-con-parameters(dvis: visibility)
  parse-choices-nb("", [
    { parse-semi-braces-ranged("", {parse-con-binder(dvis)}) }, 
    { parse-parens-commas-ranged({parse-con-binder(dvis)}) },  // Deprecated
    { ([], null) }
  ])

fun parse-con-binder(dvis: visibility)
  val (vis, vrng) = parse-visibility(dvis)
  val (name, rng, tp) = parse-param-type()
  val (opt, drng) = parse-default-expr()
  (vis, ValueBinder(name, tp, opt, rng, vrng.combine(rng).combine(tp.range).combine(drng)))

// Effect definitions
fun parse-effect-decl(dvis: visibility): parse list<topDef>
  val ((vis,defVis,vrng,erng),(doc,singleShot,sort),isInstance,isScoped) = parse-try
    val (vis, defVis, vrng) = parse-choices("", [{val (v, vr) = parse-visibility(dvis); (v, v, vr)}, {val vr = parse-keyword("abstract"); (Public, Private, vr)}])
    val isInstance = parse-option-maybe("named", {parse-keyword("named")}).is-just
    val isScoped = parse-option-maybe("scoped", {parse-keyword("scoped")}).is-just
    val (rng1, singleShot) = parse-option-maybe("linear", {val rng = parse-keyword("linear"); (rng, True)}).default((null, False))
    val sort = parse-option-maybe("sort", {parse-special-id("rec"); Retractive}).default(Inductive)
    val (rng2, doc) = parse-doc-keyword("effect")
    val erng = rng1.combine(rng2)
    ((vis,defVis,vrng,erng),(doc,singleShot,sort),isInstance,isScoped)
  val extra = if sort.is-retractive then [TpCon(nameTpDiv, erng.combine(vrng))] else []
  make-effect-decl(parse-choices("", [{
    val (effectId, irng) = parse-type-ident()
    val (tpars, kind, prng) = parse-type-kind-params()
    val effectsExtra = 
      if !isInstance then EffectExtra(extra) 
      else parse-choices("", [
        { parse-keyword("in");
          EffectReplace(Cons(parse-type(), Cons(TpCon(nameTpPartial, irng), extra)))}, 
        { if isScoped then EffectExtra(extra) // Use regular effect type
          else EffectReplace(Cons(TpCon(nameTpPartial, irng), extra))}])
    val (operations, oprng) = parse-semi-braces-ranged("", {parse-operation-decl(singleShot, defVis)})
    EffectDecl(vis, defVis, vrng, erng, doc, sort, singleShot, isInstance, isScoped, effectId, irng, 
               tpars, kind, prng, effectsExtra, operations, oprng)
   },
   {
    val (tpars, kind, prng) = parse-type-kind-params()
    val op = parse-operation-decl(singleShot, vis)
    val effectId = op.name.to-basic-operation-name
    EffectDecl(vis, defVis, vrng, erng, op.opdoc, sort, singleShot || op.lin, False, isScoped, effectId, 
               op.namerng.extend(-1), tpars, kind, prng, EffectExtra(extra), [op], op.declrng)
   }
  ]))

fun parse-doc-keyword-effect(): parse (range, string)
  parse-doc-keyword("effect", ["context", "ambient"])

fun parse-doc-keyword-fun(): parse (range, string)
  parse-doc-keyword("fun",[])

fun parse-keyword-mask(): parse range
  parse-keyword("mask", ["inject"])

fun parse-operation-decl(lin: bool, vis: visibility)
  parse-choices-nb("op decl", [
    {parse-value-operation-decl(vis)},
    {parse-fun-operation-decl(lin, vis)}
  ])

// effect NAME {val op = ...}
// TODO: annotate the operation as "value operation" to
// (a) also constrain the definition in the handler to use `val`
// (b) constrain the use site to use it as a value
fun parse-value-operation-decl(vis: visibility): parse opDecl
  val (rng0, doc) = parse-doc-keyword("val")
  val (id, idrng) = parse-identifier()
  parse-keyword(":")
  val (mbTeff, tRes) = parse-tresult()
  if mbTeff.is-just then
    parse-error("an explicit effect in result type of an operation is not allowed (yet)", mbTeff.map(fn(t) t.range).default(rng0))
  val oprng = combine([rng0, idrng, tRes.range])
  OpDecl(doc, id.to-value-operation-name, rng0, idrng, True, OpVal, [], [], idrng, mbTeff, tRes, oprng)

fun parse-fun-operation-decl(lin: bool, vis: visibility): parse opDecl
  val ((rng0, doc), sort) = parse-choices-nb("op decl", [
    {(parse-doc-keyword-fun(), OpFun)},{
      val rdoc = parse-doc-keyword("ctl", ["control"])
      if lin then parse-error("'ctl' operations are invalid for a linear effect", rdoc.fst)
      else (rdoc, OpControl)
    },{
     val rdoc = parse-doc-keyword("final");
     parse-keyword("ctl")
     if lin then parse-error("'final ctl' operations are invalid for a linear effect", rdoc.fst)
     else (rdoc, OpExcept)
    },{ // deprecated ["except", "brk"]
     val rdoc = parse-choices-nb("",[{parse-doc-keyword("except")}, {parse-doc-keyword("brk")}])
     if lin then parse-error("'brk' (or 'final ctl') operations are invalid for a linear effect", rdoc.fst)
     else (rdoc, OpExcept)
    }
  ])
  val (id, idrng) = parse-identifier()
  val exists0 = parse-type-params()
  val (pars, _, prng) = parse-decl-params(False, True)
  parse-keyword(":")
  val (mbTeff, tRes) = parse-tresult()
  if mbTeff.is-just then // TODO: check if declared effect is part of the effect type
    parse-error("an explicit effect in result type of an operation is not allowed (yet)", mbTeff.map(fn(t) t.range).default(rng0))
  val oprng = combine([rng0, idrng, tRes.range])
  OpDecl(doc, id, rng0, idrng, False, sort, exists0, pars, prng, mbTeff, tRes, oprng)

fun parse-decl-params(allowBorrow: bool, allowDefaults: bool)
  fun parse-param-binder() 
    val pinfo = if allowBorrow then parse-param-info() else Own
    val (name, rng, tp) = parse-param-type()
    val (opt, drng) = if allowDefaults then parse-default-expr() else (Nothing, null)
    (ValueBinder(name, tp, opt, rng, combine([rng, tp.range, drng])), pinfo)
  val (ipars, rng) = parse-parens-commas-ranged(parse-param-binder)
  val (pars, pinfos) = ipars.unzip
  (pars, pinfos, rng)

// Value definitions
fun parse-pure-decl(toplevel: bool, dvis: visibility): parse userDef
  with parse-try
  val (vis, vrng) = parse-visibility(dvis)
  val inl = parse-inline()
  parse-choices-nb("", [
    { 
      val (rng, doc) = parse-doc-keyword("val"); 
      parse-val-decl(toplevel, vrng.combine(rng), doc, vis, inl)
    },
    { 
      val (f,frng) = parse-tail-fip(); 
      val (rng, doc) = parse-doc-keyword-fun(); 
      parse-fun-decl(toplevel, vrng.combine(rng).combine(frng), doc, vis, inl, f)
    },
    {
      parse-keyword("fn"); 
      parse-error("hint: use 'fun' to start a named function definition (and 'fn' for anonymous functions)", peek().range)}
  ])

fun parse-function-decl(toplevel: bool, vrng: range, vis: visibility): parse userDef
  with parse-try
  val inl = parse-inline()
  val (f,frng) = parse-tail-fip()
  val (rng, doc) = parse-doc-keyword-fun()
  parse-fun-decl(toplevel, vrng.combine(rng).combine(frng), doc, vis, inl, f)

fun parse-variable-declaration(): parse userDef
  val (vrng, doc) = parse-doc-keyword("var")
  val bind = parse-value-binder(False, vrng)
  parse-keyword(":=")
  val body = parse-block-expr()
  Def(bind(body), vrng.combine(body.range), Private, DefVar, InlineNever, doc)

fun parse-val-decl(toplevel: bool, rng: range, doc: string, vis: visibility, inl: defInline): parse userDef
  val bind = parse-value-binder(toplevel, rng)
  parse-keyword("=")
  val body = parse-block-expr()
  Def(bind(body), rng.combine(body.range), vis, DefVal, inl, doc)

fun parse-fun-decl(toplevel: bool, rng: range, doc: string, vis: visibility, inl: defInline, f: fipT): parse userDef
  val spars = parse-s-quantifier()
  // trace("parsing function " ++ toplevel.show ++ "\n" ++ doc ++ "\n")
  val (name, nameRng) = parse-fun-id(toplevel)
  // trace("parsing function " ++ name.show ++ "\n")
  val FunDef(tpars, pars, pinfos, _, mbTres, preds, ann) = parse-fun-def(True, True)
  val body = parse-body-expr() // TODO: Incorporate the paramter rnge
  val fnct = promote(spars, tpars, preds, mbTres, Lam(pars, body, toplevel, rng.combine(body.range)))
  Def(ValueBinder(name, (), ann(fnct), nameRng, nameRng), rng.combine(fnct.range), vis, def-fun-ex(pinfos, f), inl, doc)

fun parse-fun-def(allowBorrow: bool, allowImplicits: bool)
  val tpars = parse-type-params()
  val (pars, pinfos, transform, rng) = parse-parameters(allowBorrow, True, allowImplicits)
  val resultTp = parse-annot-result()
  val preds = parse-maybe("predicates", {parse-keyword("with"); parens({parse-many1("", parse-predicate)})}).default([])
  FunDef(tpars, pars, pinfos, rng, resultTp, preds, transform)

fun parse-annot-result(): parse maybe<(maybe<userType>, userType)>
  parse-maybe("")
    val (teff, tres) = parse-annotated-result()
    (Just(teff), tres)

fun parse-annotated-result(): parse (userType, userType)
  parse-keyword(":")
  parse-result-type()

fun parse-type-params(): parse list<userTypeBinder>
  parse-maybe-list({angles(parse-type-binders)})

fun parse-parameters(allowBorrow: bool, allowDefaults: bool, allowImplicits: bool)
  val (results, rng) = parse-parens-commas-ranged({parse-parameter(allowBorrow, allowDefaults, allowImplicits)})
  val (binders, pinfos, transforms) = results.unzip3
  fun transform(e: userExpr): parse userExpr
    transforms.foldr(e, fn(f, e') f(e'))
  // TODO: Check correct parameter order: normal, named, implicit
  (binders, pinfos, transform, rng)

fun parse-parameter(allowBorrow: bool, allowDefaults: bool, allowImplicits: bool)
  val pinfo = if allowBorrow then parse-param-info() else Own
  val (binder, transform) = if allowImplicits then parse-choices("parameter", [parse-parameter-implicit, {parse-parameter-normal(allowDefaults)}]) else parse-parameter-normal(allowDefaults)
  (binder, pinfo, transform)

fun parse-parameter-normal(allowDefaults: bool)
  val pat = parse-pattern-atom()
  val mtp = parse-option-maybe("", parse-parameter-type-annotation)
  val (opt, drng) = if allowDefaults then parse-default-expr() else (Nothing, range/null)
  val rng = match pat
    PatVar(binder) -> binder.expr.range
    _ -> pat.range
  fun binder(name: name, nameRng: range)
    ValueBinder(name, mtp, opt, nameRng, combine([rng, drng, mtp.map(fn(t) t.range).default(drng)]))
  match pat
    // Treat PatVar and PatWild as special cases to avoid unnecessary match expressions
    PatVar(ValueBinder(name, Nothing, PatWild, nameRng, _)) -> (binder(name, nameRng), fn(x) x)
    PatWild(nameRng) -> (binder("_wildcard".unique-range-hidden-name(nameRng), nameRng), fn(x) x)
    _ -> // transform (fun (pattern) { body }) --> fun(.pat_X_Y) { match(.pat_X_Y) { pattern -> body }}
      val name = "pat".unique-range-hidden-name(rng)
      fun transform(e)
        match e
          Lam(binders, body, tl, lambdaRng) -> Lam(binders, Case(Var(name, False, rng), [Branch(pat, [Guard(guardTrue, body)])], False, rng), tl, lambdaRng)
          Ann(body, tp', rng') -> Ann(body.transform, tp', rng')
          Parens(body, pname, pre, prng) -> Parens(body.transform, pname, pre, prng)
          _ -> parse-error("Syntax.Parse.parameter: unexpected function expression in parameter match transform", rng)
      (binder(name, rng), transform)

fun parse-parameter-implicit()
  val (unpack, qname, rng) = parse-try
    val unpack = parse-maybe("unpack", {parse-keyword(".")}).is-just
    val (qname, rng) = parse-qualified-identifier()
    if !qname.is-implicit-param-name then
      parse-error("unexpected implicit parameter name", rng)
    else (unpack, qname, rng)
  val tp = parse-option-maybe("", parse-type-annot)
  val unpackExpr = if unpack then Just(Parens(Var(qname.unqualify-full, False, rng), nil, "", rng)) // Encode . as a default value assuming it is a type name
                   else Nothing
  (ValueBinder(qname, tp, unpackExpr, combine([rng, tp.map(fn(t) t.range).default(rng)]), rng), id)

fun parse-default-expr()
  parse-option-maybe("default", {val krng = parse-keyword("="); val e = parse-expression(); (Just(e), krng.combine(e.range))}).default((Nothing, null))

fun parse-block(): parse userExpr
  val rng1 = parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val stmts1 = semis("statements", parse-statement)
  val stmts2_0 = parse-option-maybe("") 
      val rng2 = parse-keyword("return")
      val e = parse-expression()
      parse-many("semicolons", parse-semicolon)
      [StatExpr(e.make-return(rng2))]
  val stmts2 = stmts2_0.default([])
  val rng2 = parse-right-curly()
  val localize = 
    match stmts1.any-statement-var
      Just(def) -> [StatFun(fn(e) local-scope(def, e))]; 
      Nothing -> []
  val stats = localize ++ stmts1 ++ stmts2
  match stats.reverse
    Cons(StatExpr(exp), rst) -> Parens(rst.foldr(exp, combine), nil, "", rng1.combine(rng2))
    [] -> Var(nameUnit, False, rng1.combine(rng2))
    _ -> parse-error("Last statement in a block must be an expression", rng1.combine(rng2))

fun parse-statement(): parse statement
  parse-choices-nb("statement", [
   {
    val funs = parse-many1("", {parse-function-decl(False, null, Private)})
    StatFun(fn(body) Let(DefRec(funs), body, combine(Cons(body.range, funs.map(range)))))
   },
   {StatFun(parse-local-value-declaration())},
   {StatVar(parse-variable-declaration())},
   {
    val f = parse-with-statement()
    parse-maybe("", {parse-keyword("in"); StatExpr(f(parse-block-expr()))}).default(StatFun(f))
   },
   {StatExpr(parse-choices("", [parse-basic-expr, parse-return-expr]))} 
  ]) 

fun parse-local-value-declaration(): parse (userExpr -> parse userExpr)
  val krng = parse-keyword("val")
  val pat = parse-pattern()
  parse-keyword("=")
  val e = parse-block-expr()
  fun bindVar(binder:valueBinder<maybe<userType>, pattern<userType>>, mbTyp: maybe<userType>, rng: range): parse (userExpr -> parse userExpr)
    val annExpr = match mbTyp
      Just(tp) -> Ann(e, tp.promote-type, rng)
      Nothing -> e
    val vBinder = ValueBinder(binder.name, (), annExpr, binder.name-range, binder.range)
    fn(b) Bind(Def(vBinder, rng, Private, DefVal, InlineAuto, ""), b, krng.combine(b.range))
  match pat.un-parens
    PatVar(binder as ValueBinder(expr=PatWild)) -> bindVar(binder, binder.binderType, binder.range) 
    PatAnn(PatVar(binder as ValueBinder(expr=PatWild)), tp, rng) -> bindVar(binder, Just(tp), rng)
    _ -> fn(b) Case(e, [Branch(pat, [Guard(guardTrue, b)])], False, krng.combine(b.range))

fun parse-with-statement()
  fun promote-value-binder(binder)
    match binder.binderType
      Just(tp) -> binder(binderType=Just(tp.promote-type))
      _ -> binder
  val krng = parse-keyword("with")
  parse-choices("", [
    {
      val (par, _, transform) = parse-parameter(False, False, False)
      parse-keyword("=")
      parse-keyword("<-")
      val e = parse-choices("", [parse-basic-expr, {parse-handler-stat(krng, HandlerInstance)}])
      fn(b:userExpr) apply-to-continuation(krng, [par.promote-value-binder], e.transform, b)
    },
    {
      val e = parse-choices("", [parse-basic-expr, {parse-handler-stat(krng, HandlerNormal)}])
      fn(b:userExpr) apply-to-continuation(krng, [], e, b)
    }
  ])


fun parse-type-annotation(): parse (userExpr -> parse userExpr)
  parse-maybe("", {
    val tp = parse-type-annot()
    fn(x) Ann(x, tp, tp.range.combine(x.range))
  }).default(fn(x) x)

// Expressions
fun parse-body-expr(): parse userExpr
  parse-choices("", [parse-block-expr, {parse-keyword("->"); parse-block-expr()}])

fun parse-block-expr(): parse userExpr
  parse-choices-nb("expression", [parse-with-expr, parse-block-fun-expr, parse-return-expr, parse-val-expr, parse-basic-expr])

fun parse-expression(): parse userExpr
  parse-choices-nb("expression", [parse-with-expr, parse-fun-expr, parse-return-expr, parse-val-expr, parse-basic-expr])

fun parse-basic-expr(): parse userExpr
  parse-choices-nb("basic expression", [parse-if-expr, parse-fn-expr, parse-match-expr, parse-handler-expr, parse-op-expr])

fun parse-with-expr(): parse userExpr
  val f = parse-with-statement()
  parse-keyword("in")
  f(parse-block-expr())

fun parse-val-expr(): parse userExpr
  val f = parse-local-value-declaration()
  parse-keyword("in")
  f(parse-expression())

fun parse-block-fun-expr(): parse userExpr
  parse-choices("", [parse-block, {parse-lambda(["fun"])}])

fun parse-fun-expr(): parse userExpr
  parse-choices("", [parse-fun-block, {parse-lambda(["fun"])}])

inline fun parse-fn-expr(): parse userExpr
  parse-lambda([])

fun parse-fun-block(): parse userExpr
  val exp = parse-block()
  Lam([], exp, False, exp.range)

fun parse-lambda(alts: list<string>): parse userExpr
  val rng = parse-keyword("fn")
  val spars = parse-s-quantifier()
  val FunDef(tpars, pars, _, _, mbTres, preds, ann) = parse-fun-def(False, True)
  val body = parse-body-expr()
  val f = promote(spars, tpars, preds, mbTres, Lam(pars, body, False, rng.combine(body.range)))
  ann(Parens(f, "fn".new-name, "", rng))

fun parse-if-expr(): parse userExpr
  val rng = parse-keyword("if")
  val tst = parse-non-trailing-lambda()
  val (tExpr, eExprs, eExpr) =
    parse-choices("",[
      {
        val tExpr = parse-return-expr()
        (tExpr, [], Var(nameUnit, False, tExpr.range.after))
      },
      {
        val tExpr = parse-then-expr(rng)
        val eExprs = parse-many("", parse-elif-expr)
        val eExpr = parse-option-maybe("", {parse-keyword("else"); parse-block-expr()}).default(Var(nameUnit, False, (tExpr.range).combine(eExprs.map(fn(e) e.snd.range).combine).after))
        (tExpr, eExprs, eExpr)
      }
    ])
  Cons((tst, tExpr), eExprs).foldr(eExpr) fn((tst', tExpr'), eExpr')
    Case(tst', [Branch(PatCon(nameTrue, [], null, null), [Guard(guardTrue, tExpr')]),
              Branch(PatCon(nameFalse, [], null, null), [Guard(guardTrue, eExpr')])], False, tst'.range.combine(eExpr'.range))
  
fun parse-elif-expr(): parse (userExpr, userExpr)
  val rng = parse-keyword("elif")
  val tst = parse-non-trailing-lambda()
  val tExpr = parse-then-expr(rng)
  (tst, tExpr)

fun parse-then-expr(rng: range): parse userExpr
  parse-choices-nb("then", [
    {parse-keyword("then"); parse-block-expr()},
    {
      val expr = parse-block-expr()
      add-warning("warning " ++ expr.range.before.start.show ++ ": using an 'if' without 'then' is deprecated.\n hint: add the 'then' keyword.", expr.range) 
      expr
    }
  ])

fun parse-return-expr(): parse userExpr
  val rng = parse-keyword("return")
  val exp = parse-expression()
  exp.make-return(rng)

fun parse-match-expr(): parse userExpr
  parse-choices("", [{
    val lzy = parse-option-maybe("", {parse-special-id("lazy")}).is-just
    val rng = parse-keyword("match")
    val tst = parse-non-trailing-lambda()
    val (branches, rng2) = parse-semi-braces-ranged1("match clause", parse-branch)
    Case(tst, branches, lzy, rng.combine(rng2))
  }, parse-handler-expr])

// TODO: Fix parsing of handler to match the grammar precisely
fun parse-handler-expr(): parse userExpr
  val (rng0, hsort) = parse-option-maybe("", {val rng = parse-keyword("named"); (rng, HandlerInstance)}).default((null, HandlerNormal))
  parse-choices("handle or handler", [
    {
      val rng1 = parse-keyword("handle")
      val rng = rng0.combine(rng1)
      val scoped = parse-option-maybe("", {parse-special-id("scoped"); HandlerScoped}).default(HandlerNoScope)
      val (over, mbEff) = parse-handler-override(hsort)
      val arg = parse-non-trailing-lambda()
      val expr = parse-handler-clauses(rng, mbEff, scoped, over, hsort)
      App(expr, [(Nothing, arg)], rng.combine(expr.range))
    },
    {
      val rng1 = parse-keyword("handler")
      val rng = rng0.combine(rng1)
      parse-handler-exprx(rng, hsort)
    }
  ])

fun parse-handler-stat(rng: range, hSort: handlerSort): parse userExpr
  match hSort
    HandlerNormal -> parse-handler-exprx(rng, hSort)
    HandlerInstance ->
      parse-keyword("named")
      parse-option-maybe("", {parse-keyword("handler")})
      parse-handler-exprx(rng, hSort)

fun parse-handler-exprx(rng: range, hSort: handlerSort): parse userExpr
  val scoped = parse-maybe("", {parse-keyword("scoped"); HandlerScoped}).default(HandlerNoScope)
  val (over, mbEff) = parse-handler-override(hSort)
  parse-handler-clauses(rng, mbEff, scoped, over, hSort)

fun parse-handler-override(hSort: handlerSort): parse (handlerOverride, maybe<userType>)
  val over = match hSort
    HandlerNormal -> 
      parse-maybe("", {parse-keyword("override"); HandlerOverride}).default(HandlerNoOverride)
    _ -> HandlerNoOverride
  val mbEff = parse-maybe("", {val eff = angles(parse-type); eff.promote-type})
  (over, mbEff)

fun parse-handler-clauses(rng: range, mbEff: maybe<userType>, scoped: handlerScope, over: handlerOverride, hsort: handlerSort): parse userExpr
  val (clausesAndBinders, rng2) = parse-op-clauses()
  val fullrange = rng.combine(rng2)
  val (clauses, binders) = extract-binders(clausesAndBinders)
  val (reinit, ret, finally, ops) = partition-clauses(clauses, fullrange)
  val hand = match (mbEff, ops)
    (Nothing, []) ->  // no ops and no annotation: this is not a handler; just apply return
      val retExpr = match ret // TODO: error on override/scoped/instance?
        Nothing -> fn(x) x
        Just(f) -> fn(actionExpr) App(f, [(Nothing, App(actionExpr, [], fullrange))], fullrange)
      val handlerExpr = Lam([ValueBinder("action".new-hidden-name, Nothing, Nothing, rng, rng)], retExpr(Var("action".new-hidden-name, False, rng)), False, fullrange)
      binders(handlerExpr)
    _ -> binders(Handler(hsort, scoped, over, Nothing, mbEff, [], reinit, ret, finally, ops, rng, fullrange))
  apply-maybe(fullrange, reinit, finally, hand)

fun parse-op-clauses(): parse (list<binder>, range)
  fun parse-single-op()
    val (op, bind) = parse-handler-op()
    ([(op, bind)], op.range)
  
  parse-choices("", [
    { parse-semi-braces-ranged("", parse-handler-opx)},
      parse-single-op,
    { val rng = parse-left-paren();
      parse-error("unexpected '(': local parameters are no longer supported, use a local 'var' instead", rng)},
    { ([], null)}
  ])

fun parse-handler-opx(): parse (clause, maybe<(userExpr -> userExpr)>)
  parse-choices("handler clause", [
    {
      val rng = parse-special-id("finally")
      parse-maybe("", {parens({()})})
      val expr = parse-body-expr()
      (ClauseFinally(Lam([], expr, False, rng.combine(expr.range))), Nothing)
    },{
      val rng = parse-special-id("initially")
      val (name, prng, tp) = parens
        parse-choices("", [{
          val (name,prng) = parse-param-id()
          val tp = parse-option-maybe("", parse-parameter-type-annotation)
          (name, prng, tp)
        },{
          (new-name("_"), rng, Nothing)
        }])
      val expr = parse-body-expr()
      (ClauseInitially(Lam([ValueBinder(name, tp, Nothing, prng, rng.combine(tp.map(fn(t) t.range).default(rng)))], expr, False, rng.combine(expr.range))), Nothing)
    }, parse-handler-op
  ])

fun parse-handler-op(): parse (clause, maybe<(userExpr -> userExpr)>)
  parse-choices-nb("handler clause", [
    {
      val rng = parse-keyword("return")
      val (name, prng, tp) = parse-choices("", [
        {
          val (name, prng) = parse-param-id()
          parse-warning-message("'return x' is deprecated; use 'return(x)' instead.", prng)
          (name, prng, parse-option-maybe("", parse-parameter-type-annotation))
        },
        {
          parens
            val (name, prng) = parse-param-id()
            (name, prng, parse-option-maybe("", parse-parameter-type-annotation))
        }
      ])
      val expr = parse-body-expr()
      (ClauseRet(Parens(Lam([ValueBinder(name, tp, Nothing, prng, prng.combine(tp.map(fn(t) t.range).default(prng)))], expr, False, rng.combine(expr.range)), "return".new-name, "", rng)), Nothing)
    },{ // TODO: is "raw" needed for value definitions?
      parse-keyword("val")
      val (name, nameRng) = parse-qualified-identifier()
      parse-keyword("=")
      val expr = parse-block-expr()
      val (binder, resumeExpr) = bind-expr-to-val(name, nameRng, expr)
      (ClauseBranch(HandlerBranch(name.to-value-operation-name, [], resumeExpr([]), OpVal, nameRng, nameRng)), Just(binder))
    },{
      val (opSort, (name, nameRng)) = parse-choices-nb("opSort", [
        {parse-keyword("fun"); (OpFun, parse-qualified-identifier())}, {parse-keyword("ctl", ["control"]); (OpControl, parse-qualified-identifier())}, 
        {parse-keyword("final"); parse-keyword("ctl"); (OpExcept, parse-qualified-identifier())},
        {parse-keyword("raw"); parse-keyword("ctl"); (OpControlRaw, parse-qualified-identifier())}, 
        // Deprecated
        {parse-keyword("except"); (OpExcept, parse-qualified-identifier())}, {parse-keyword("brk"); (OpExcept, parse-qualified-identifier())},
        {parse-keyword("rcontrol"); (OpControlRaw, parse-qualified-identifier())}, {parse-keyword("rawctl"); (OpControlRaw, parse-qualified-identifier())},
        {
          val (n, nr) = parse-qualified-identifier(); 
          parse-warning-message("using a bare operation is deprecated.\n hint: start with 'val', 'fun', 'final ctl', 'ctl', or 'raw ctl'", nr)
          (OpControlErr, (n, nr))
        }
      ])
      val (opPars, prng) = parse-op-params()
      val expr = parse-body-expr()
      (ClauseBranch(HandlerBranch(name, opPars, expr, opSort, nameRng, nameRng.combine(prng))), Nothing)
    }
  ])

fun parse-op-params()
  parse-maybe("", {parse-parens-commas-ranged(parse-op-param)}).default(([], null))

fun parse-op-param()
  val (name, rng) = parse-param-id()
  val tp = parse-option-maybe("", parse-type-annot)
  ValueBinder(name, tp, (), rng, rng.combine(tp.map(fn(t) t.range).default(rng)))

fun parse-handler-param()
  val (name, rng) = parse-identifier()
  val tp = parse-option-maybe("", parse-type-annot)
  ValueBinder(name, tp, (), rng, rng.combine(tp.map(fn(t) t.range).default(rng)))

fun parse-branch(): parse userBranch
  val pat = parse-pattern()
  val grds = parse-guards()
  Branch(pat, grds)

fun parse-guards(): parse list<userGuard>
  parse-choices-nb("guards", [
    {parse-many1("", parse-guard-bar)},
    {parse-keyword("->"); [Guard(guardTrue, parse-block-expr())]},
    {
      val exp = parse-block()
      parse-warning-message("use '->' for pattern matches", exp.range)
      [Guard(guardTrue, exp)]
    }
  ])

fun parse-guard-bar(): parse userGuard
  parse-vertical-bar()
  val grd = parse-guard-test()
  parse-keyword("->")
  val exp = parse-block-expr()
  Guard(grd, exp)

fun parse-guard-test()
  parse-choices-nb("guard condition or '_'", [
    {parse-special-id("otherwise"); parse-error("hint: use \"_\" instead of \"otherwise\" for the guard condition", peek().range)},
    parse-expression,
    {parse-wildcard(); guardTrue}
  ])

// Op expr
// Non trailing lambda expressions
inline fun parse-non-trailing-lambda(): parse userExpr
  parse-op-exprx(False)

inline fun parse-op-expr(): parse userExpr
  parse-op-exprx(True)

fun parse-op-exprx(allowTrailingLam: bool): parse userExpr
  val e1 = parse-prefix-expr(allowTrailingLam)
  // trace("Parsed expression " ++ e1.show ++ "\n")
  parse-choices-nb("", [
    {
      val ess = parse-many1("", {
                                  val op = parse-operator-var(); 
                                  // trace("Parsed operator " ++ op.show ++ "\n")
                                  val e2 = parse-prefix-expr(allowTrailingLam); 
                                  // trace("Parsed expression2 " ++ e2.show ++ "\n")
                                  [op, e2]})
      App(Var(nameOpExpr, True, null), 
          Cons(e1, ess.concat).map(fn(e) (Nothing, e)), 
          combine(Cons(e1.range, ess.concat.map(range))))
    }, {e1}
  ])

fun parse-operator-var(): parse userExpr
  parse-choices-nb("", [
    {val (name, rng) = parse-qualified-operator(); Var(name, True, rng)},
    {Var(nameAssign, True, parse-keyword(":="))}
  ])

fun parse-prefix-expr(allowTrailingLam: bool): parse userExpr
  val ops = parse-many("", parse-prefix-op)
  val aexp = parse-application-expression(allowTrailingLam)
  ops.foldr(aexp, fn(op, e) App(op, [(Nothing, e)], op.range.combine(e.range)))

fun parse-application-expression(allowTrailingLam: bool): parse userExpr
  val e0 = parse-atomic()
  // trace("applying " ++ e0.show ++ "\n")
  val fs = parse-many("", {parse-choices("", [parse-dot-expr, parse-applier, parse-indexer, {parse-func-applications(allowTrailingLam)}])})
  fs.foldl(e0, fn(e:userExpr, f:userExpr -> userExpr) f(e))

fun parse-dot-expr(): parse (userExpr -> userExpr)
  parse-keyword(".")
  parse-choices("", [
    {
      val e = parse-idcon()
      parse-choices("", [
        {
          val rng = parse-left-paren()
          val args = parse-sep-by("", parse-argument, parse-comma)
          val rng1 = parse-right-paren()
          fn(arg0) App(e, Cons((Nothing, arg0), args), rng.combine(arg0.range).combine(rng1))
        },
        { fn(arg0) App(e, [(Nothing, arg0)], arg0.range.combine(e.range)) }
      ])
    }, parse-applier])

fun parse-indexer(): parse (userExpr -> userExpr)
  val rng0 = parse-left-bracket()
  parse-choices-nb("", [
    {
      val crng = parse-keyword("ctx")
      val ct = parse-constructor-context(crng)
      val rng1 = parse-right-bracket()
      fn(e)
        val rng = e.range.combine(rng1)
        App(Var(nameCCtxComposeExtend, False, rng1), [(Nothing, e), (Nothing, ct)], rng1)
    },
    {
      val idxs = parse-sep-by1("", parse-expression, parse-comma)
      val rng1 = parse-right-bracket()
      fn(e) App(Var(nameIndex, False, rng0.combine(rng1)), Cons(e, idxs).map(fn(a) (Nothing, a)), rng0.combine(rng1))
    }
  ])

fun parse-applier(): parse (userExpr -> userExpr)
  val rng0 = parse-left-paren()
  val args = parse-sep-by("", parse-argument, parse-comma)
  val rng1 = parse-right-paren()
  fn(e) App(e, args, rng1.combine(e.range))

fun parse-func-application(allowTrailingLam: bool): parse userExpr
  if allowTrailingLam then parse-choices("", [parse-fun-block, {parse-lambda([])}])
  else parse-lambda([])

fun parse-func-applications(allowTrailingLam: bool): parse (userExpr -> userExpr)
  fun inject-apply(e, fs)
    match fs
      [] -> e
      _ -> 
        val nfargs = fs.map(fn(e') (Nothing, e'))
        match e
          App(f, args, rng) -> 
            val positional = args.filter(fn(a) a.fst.is-nothing) ++ nfargs
            val namedargs = args.filter(fn(a) a.fst.is-just)
            App(f, positional ++ namedargs, rng)
          _ -> App(e, nfargs, combine(Cons(e.range, fs.map(fn(a) a.range))))
  val fs = parse-many1("", {parse-func-application(allowTrailingLam)})
  fn(arg0)
    inject-apply(arg0, fs)

fun parse-argument(): parse (maybe<(name,range)>, userExpr)
  val exp = parse-annotated-expr()
  match exp
    Var(name, _, rng) ->
      val x = parse-maybe("=")
        parse-keyword("=")
        (Just((name, rng)), parse-expression())
      match x
        Just(x') -> x'
        Nothing -> (Nothing, exp)
    _ -> (Nothing, exp)

/// Atomic expression
fun parse-atomic(): parse userExpr
  parse-choices-nb("(simple) expression", [
    parse-idcon,
    parse-tuple-expression, // must be second due to '(' operator ')'
    parse-list-expr, 
    {Literal(parse-literal())}, 
    parse-constructor-context-hole, 
    parse-constructor-context-expr, 
    parse-mask-expr
  ])

fun parse-literal(): parse lit
  parse-choices-nb("", [
    {val (i, tok) = parse-integer(); LitInt(i, tok.range)},
    {val (f, tok) = parse-float(); LitFloat(f, tok.range)},
    {val (s, range) = parse-string-literal(); LitString(s, range)},
    {val (c, range) = parse-char-literal(); LitChar(c.string, range)},
  ])

fun parse-annotated-expr(): parse userExpr
  val e = parse-expression()
  parse-choices-nb("", [
    {
      parse-keyword(":"); 
      val tp = parse-type-scheme();
      Ann(e, tp, e.range.combine(tp.range))}, 
    { e }])

fun parse-tuple-expression(): parse userExpr
  val rng1 = parse-left-paren()
  val es = parse-sep-by("", parse-annotated-expr, parse-comma)
  val rng2 = parse-right-paren()
  val rng = rng1.combine(rng2)
  match es
    Nil -> Var(nameUnit, False, rng)
    [e] -> Parens(e, nil, "", rng)
    _ -> App(Var(name-tuple(es.length), False, rng), es.map(fn(e) (Nothing, e)), rng)

fun parse-list-expr(): parse userExpr
  val rng1 = parse-special("[")
  val es = parse-sep-by("",parse-annotated-expr, parse-comma)
  val rng2 = parse-special("]")
  if es.is-nil then
    make-nil(rng1.combine(rng2))
  else
    es.foldr(make-nil(rng2.after), fn(x, acc) rng1.make-cons(x, acc, userTpRange)).adjust-range(rng1.combine(rng2))

fun parse-constructor-context-expr(): parse userExpr
  parse-constructor-context(parse-keyword("ctx"))

fun parse-constructor-context(rng: range): parse userExpr
  make-app(Var(nameCCtxCreate, False, rng), [parse-non-trailing-lambda()], userTpRange)

fun parse-constructor-context-hole(): parse userExpr
  val rng = parse-choices("", [{parse-keyword("hole")}, {parse-wildcard().snd}])
  make-app(Var(nameCCtxHoleCreate, False, rng), [], userTpRange)

fun parse-mask-expr(): parse userExpr
  val (rng, mkInj) = parse-mask-type()
  parse-choices-nb("", [
    {mkInj(parens({parse-choices("", [parse-expression, parse-fun-block])}))}, // Need apply or the escape check may fail if it becomes a separate lambda
    {val name = new-hidden-name("mask-action"); Lam([ValueBinder(name, Nothing, Nothing, rng, rng)], mkInj(Var(name, False, rng)), False, rng)}
  ])

fun parse-mask-type(): parse (range, (userExpr -> div userExpr))
  val rng1 = parse-keyword-mask()
  val behind = parse-maybe("", {parse-special-id("behind")}).is-just
  parse-left-angle()
  val tp = parse-type()
  val rng2 = parse-right-angle()
  (rng1, fn(exp:userExpr) Inject(promote-type(tp), exp, behind, rng1.combine(rng2)))

fun parse-value-binder(toplevel: bool, pre: range): parse (userExpr -> parse valueBinder<(), userExpr>)
  val (name, range) = parse-locally-qualified-identifier(toplevel)
  val ann = parse-type-annotation()
  fn(e:userExpr) ValueBinder(name, (), ann(e), range, pre.combine(range))

inline fun parse-pattern(): parse userPattern
  parse-pattern-annotation()

fun parse-pattern-annotation(): parse userPattern
  val p = parse-pattern-atom()
  parse-maybe-type-annotation(p) fn(tp0)
    val tp = promote-type(tp0)
    match p
      PatVar(ValueBinder(name, Nothing, npat, rng1, rng2)) -> 
        PatVar(ValueBinder(name, Just(tp), npat, rng1, rng2))
      _ -> PatAnn(p, tp, p.range.combine(tp.range))

fun parse-pattern-atom(): parse userPattern
  parse-choices("pattern atom", [
    {
      val (name, rng) = parse-qualified-constructor()
      val (ps, r) = parse-choices-nb("", [{parse-parens-commas-ranged(parse-named-pattern)}, {([], null)}])
      PatCon(name, ps, rng, rng.combine(r))
    },
    {
      val (name, rng) = parse-identifier()
      parse-choices("", [
        {parse-keyword("as"); val p = parse-pattern(); PatVar(ValueBinder(name, Nothing, p, rng, rng.combine(p.range)))},
        {PatVar(ValueBinder(name, Nothing, PatWild(rng), rng, rng))}
      ])
    },
    {PatWild(parse-wildcard().snd)},
    {PatLit(parse-literal())},
    {parse-list-pattern()},
    {
      val (ps, rng) = parse-parens-commas-ranged(parse-named-pattern);
      match ps
        [(_, p)] -> PatParens(p, rng)
        _ -> PatCon(name-tuple(ps.length), ps, rng, rng)
    }
  ])

fun parse-named-pattern(): parse (maybe<(name,range)>, userPattern)
  parse-choices("named pattern", [
    {
      val (name, rng) = parse-identifier();
      parse-keyword("=")
      (Just((name, rng)), parse-pattern())
    },
    { (Nothing, parse-pattern()) }
  ])

fun parse-maybe-type-annotation(d: a, f: (userType) -> div a): parse a
  parse-maybe("", {f(parse-type-annot())}).default(d)

fun parse-list-pattern(): parse userPattern
  val rng1 = parse-special("[")
  val es = parse-sep-by("", parse-pattern, parse-comma)
  val rng2 = parse-special("]")
  if es.is-nil then
    make-nil-pattern(rng1.combine(rng2))
  else
    PatParens(es.foldr(make-nil-pattern(rng2.after),make-cons-pattern), rng1.combine(rng2))

fun warn-deprecated(o: string, n: string, rng: range): parse ()
  add-warning("warning " ++ rng.start.show ++ ": keyword \"" ++ o ++ "\" is deprecated, use \"" ++ n ++ "\" instead", rng)

fun parse-warning-message(msg: string, rng: range): parse ()
  add-warning("warning " ++ rng.start.show ++ ":" ++ msg, rng)

fun test()
  "Compiles!".println