//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

module compiler/syntax/parse
// Updated as of 8/3/26: Commit eb98b61d (verified: handler-grammar rework
// [4266dfbee, 22a32e7b7] and conditional-import/target-guard machinery
// [d4d66b04e et al.] were already ported)
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


// Updated to commit #b1b8078 (of Parse.hs) 7/23/26


// Render a parse error the way upstream shows Parsec errors from `fail`:
// `<file>(l,c): parse error: invalid syntax` followed by the message lines,
// each indented by a single space (matches the recorded .kk.out error tests)
fun show-parse-error(e: string, r: range): string
  val msg = e.lines.map(fn(l) " " ++ l.list.drop-while(fn(c) c == ' ').string).join("\n")
  r.show-range("".path, False) ++ ": parse error: invalid syntax\n" ++ msg

pub fun parse-program-from-file(fname: path, allow-at: bool, semiInsert: bool = True, tpl: target-platform = target-platform-default): _ user-program
  val r = read-text-file(fname)
  parse-program-from-string(r, fname, allow-at, semiInsert, tpl)

pub fun parse-program-from-string(input: string, fname: path, allow-at: bool, semiInsert: bool = True, tpl: target-platform = target-platform-default): _ user-program
  with handler
    final ctl parse-error(e: string, r: range)
      throw(show-parse-error(e, r))
  lex-parse(allow-at, semiInsert, fn(x) x.remove-white, parse-program, tpl, fname.string, input)

fun string/lex-parse(str: string, sourceName: path, line: int, semiInsert: bool, p: () -> _ a): _ a
  with handler
    final ctl parse-error(e: string, r: range)
      throw(show-parse-error(e, r))
  lex-parse(False, semiInsert, fn(x) x, p, target-platform-default, sourceName.string, str)

pub fun parse-value-def(input: string, fname: path, line: int, semiInsert: bool): _ user-def
  lex-parse(input, fname, line, semiInsert, parse-value-definition)

pub fun parse-type-def(input: string, fname: path, line: int, semiInsert: bool): _ (user-typedef, list<user-def>)
  lex-parse(input, fname, line, semiInsert, parse-type-definition)

pub fun lex-parse-type(input: string, fname: path, line: int, name: name, semiInsert: bool): _ user-typedef
  lex-parse(input, fname, line, semiInsert, {parse-user-type(name)})

pub fun lex-parse-expression(input: string, fname: path, line: int, name: name, semiInsert: bool): _ user-def
  lex-parse(input, fname, line, semiInsert, {parse-user-expression(name)})

fun interactive(f: () -> _ a): _ a
  val x = f()
  parse-many("semicolons", parse-semicolon)
  peof() // `interactive` requires eof: reject trailing garbage
  x

fun parse-value-definition(): _ user-def
  interactive
    parse-pure-decl(False, Private)

fun parse-type-definition(): _ (user-typedef, list<user-def>)
  interactive
    parse-choices("type definition", [
      {(parse-alias-decl(Public), [])},
      {parse-type-declaration(Public)}
    ])

fun parse-user-type(name: name): _ user-typedef
  interactive
    val tp = parse-type()
    Synonym(TypeBinder(name, KindNone, null, null), [], tp, tp.range, Public, "")

fun parse-user-expression(name: name): _ user-def
  interactive
    val e = parse-annotated-expr()
    val r = e.range
    Def(ValueBinder(name.unqualify, (), Lam([], e, False, r), r, r), r, Public, DefFun([], noFip), InlineNever, "")

fun parse-dependencies(source: source, lexemes: list<lexeme>, tpl: target-platform = target-platform-default): _ (name, range, list<kimport>)
  with handler
    final ctl parse-error(e: string, r: range)
      throw(show-parse-error(e, r))
  parse-lexemes(source, lexemes, tpl, parse-module-deps)

// Program
fun parse-program(): _ user-program
  parse-many("semicolons", parse-semicolon)
  val p = parse-module()
  peof()
  p

fun parse-module-decl(fpath: path)
  parse-choices("module decl", [{
    val (_, doc) = parse-doc-keyword("module")
    val (name, rng) = parse-module-path()
    (Private, doc, name, rng)
  },{
    val mname = fpath.stemname.path-to-module-name
    (Public, "", mname, range/null)
  }])

fun parse-module(): _ user-program
  val (vis, doc, name, namerng) = parse-module-decl(source-info.name.path)
  parse-body(vis, name, namerng, doc)

// Lex imports only; this is more lenient
fun parse-module-deps(): _ (name, range, list<kimport>)
  val (_, _, name, namerng) = parse-module-decl(source-info.name.path)
  val imports = parse-import-decls()
  (name, namerng, include-std-core(name, imports))
  // no eof.. try to parse as far as possible

fun include-std-core(nm: name, imports: list<kimport>): list<kimport>
  if nm.is-system-core-name || imports.any(fn(imp:kimport) imp.name == nameSystemCore) then imports
  else Cons(Kimport(nameSystemCore, nameSystemCore, null, null, null, Private, False), imports)

fun parse-import-decls()
  parse-many("semicolons", parse-semicolon)
  parse-maybe-nb("open body", parse-left-curly)
  parse-many("semicolons", parse-semicolon)
  semis("imports", parse-import-declaration).filter-map(fn(x) x)

// Program body
fun parse-body(vis: visibility, name: name, rng: range, doc: string): _ user-program
  parse-many("semicolons", parse-semicolon)
  val (imports, fix-defss, topDefss) = braced
    val imps = semis("imports", parse-import-declaration).filter-map(fn(x) x)
    // trace("imports " ++ imps.show)
    val fixs = semis("fixities", parse-fixity-decl)
    // trace("fixities " ++ fixs.show)
    val tdefs = semis("topDefs", {val tdef = parse-top-def(vis); // trace(tdef.show ++ "\n\n"); 
                                  tdef})
    // trace("top defs " ++ tdefs.show)
    (imps, fixs, tdefs)
  parse-many("semicolons", parse-semicolon)
  val (defs, typedefs, externals) = split-top-defs(topDefss.concat)
  Program(source-info, name, rng, [TypeDefRec(typedefs)], [DefRec(defs)], include-std-core(name, imports), externals, fix-defss.concat, doc)

type fun-def
  FunDef(
    tpars: list<type-binder<user-kind>>,
    pars: list<value-binder<maybe<user-type>, maybe<user-expr>>>,
    pinfos: list<param-info>,
    parsRng: range,
    mbTres: maybe<(maybe<user-type>, user-type)>,
    preds: list<user-type>,
    ann: (user-expr -> <parse> user-expr)
  )

fun parse-top-def(vis): _ list<top-def>
  // no backtracking: each alternative's own
  // internal `try` already peeks only far enough to disambiguate its keyword,
  // so once one commits (matches its keyword), a later failure inside it must
  // propagate hard rather than fall through to try the next declaration kind
  // (see `parse-pure-decl`)
  parse-choices-nb("topDef", [
    {[DefValue(parse-pure-decl(True, vis))]},
    {[DefType(parse-alias-decl(vis))]},
    {
      val (tdef, cdefs) = parse-type-declaration(vis)
      Cons(DefType(tdef), cdefs.map(DefValue))
    },
    {parse-effect-decl(vis)},
    {parse-extern-decl(vis)}
  ])

// Import declaration; returns `Nothing` for a conditional import with no matching target
fun parse-import-declaration(): _ maybe<kimport>
  val (vis, vrng, rng0, open) = parse-try
    val (vis, vrng) = parse-visibility(Private)
    val isOpen = parse-maybe-nb("open", {parse-special-id("@open")}).is-just
    val rng0 = parse-keyword("import")
    (vis, vrng, rng0, isOpen)
  parse-import-alias().map fn((asname, name, asrng, namerng))
    Kimport(asname, name, asrng, namerng, combine([vrng, rng0, namerng]), vis, open)

fun parse-visibility(vis: visibility = Private): _ (visibility, range)
  parse-choices("visibility", [{
    val rng = parse-keyword("pub", ["public"])
    (Public, rng)
  },
  {
    val rng = parse-keyword("private")
    add-warning("using private is deprecated, only use 'pub' to make declarations public", rng)
    (Private, rng)
  },{(vis, null)}])

// External
fun parse-extern-decl(dvis: visibility): _ list<top-def>
  parse-choices("externDecl", [{
    val krng = parse-doc-keyword("extern").fst
    val _ = parse-choices("import", [
      { parse-keyword("import"); () },
      {
        parse-special-id("include");
        warn-deprecated("include", "import", krng);
      }])
    match parse-external-import(krng)
      Just(ext) -> [DefExtern(ext)]
      Nothing -> []
  }, {
    val (vis,vrng) = parse-visibility(dvis)
    val inl = parse-inline()
    val (fip, frng) = parse-tail-fip()
    val (erng, doc) = parse-doc-keyword("extern",[])
    val krng = combine([vrng, frng, erng])
    val (name, nameRng) = parse-fun-id() // Top level
    val (pars, pinfos, args, tp, annotate) = parse-choices("extern type", [
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
    val (expr, rng) = match parse-external-body()
      Nothing ->
        pwarning-message("unsupported external: " ++ name.show, nameRng)
        val fname = name.show.show // string literal of the name
        val call-str = match ptarget-platform.tpl-target
          JS(_) -> "$std_core_types.kk_unsupported_external(" ++ fname ++ ")"
          CS -> "Primitive.UnsupportedExternal(" ++ fname ++ ")"
          C(_) -> "kk_unsupported_external(" ++ fname ++ ")"
          _ -> "kk_unsupported_external(" ++ fname ++ ")"
        (ExternalInline(call-str), nameRng)
      Just(res) -> res
    val fullRng = combine([krng, vrng, rng])
    if (inl.is-inlineAlways) then [DefExtern(External(name, tp, pinfos, nameRng, fullRng, expr, vis, fip, doc))]
    else
      val externName = name.new-hidden-external-name
      val ext = External(externName, tp, pinfos, nameRng.before, fullRng.before, expr, Private, fip, doc)
      val body = annotate(Lam(pars, App(Var(externName, False, null), args, fullRng), True, fullRng))
      val binder = ValueBinder(name, (), body, nameRng, fullRng)
      val extfun = Def(binder, fullRng, vis, def-fun-ex(pinfos, fip), InlineNever, doc)
      [DefExtern(ext), DefValue(extfun)]
  }
  ])

fun parse-external-import-key-val(): _ (string, string)
  val key = parse-external-import-key()
  parse-keyword("=")
  val (v, _) = parse-string-literal()
  (key, v)

fun parse-external-import-key(): _ string
  val (id, _) = parse-var-id()
  id.show

fun parse-external-includes(target: target, rng: range, (key, fname): (string, string)): _ list<(string, string)>
  // guard the path-joining branch on
  //   key == "file" || key == "header-file" || key == "header-end-file"
  // Joining the source dir onto the value (and `show`ing it) for all keys corrupts inline content, e.g.
  //   c include-inline "#include <time.h>"
  // becomes "compiler/main/#include <time.h>" in the generated C.
  if key == "file" || key == "header-file" || key == "header-end-file" then
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
  else [(key, fname)]

fun pread-file(fpath: path): _ string
  with catch fn(e)
      trace("Error reading file " ++ fpath.show)
      parse-error("Unable to read external file at path: " ++ fpath.show ++ ": got error " ++ e.message, null)
  read-text-file(fpath)

fun parse-external-import-entry() : _ maybe<list<(string, string)>>
  val matches = parse-target-guard()
  val (key-vals, rng) = parse-choices("", [
    { val key = parse-external-import-key();
      val (v, rng) = parse-string-literal();
      ([(key, v)], rng)
    },
    { parse-semi-braces-ranged("", parse-external-import-key-val) }
    ])
  if matches then
    val target = ptarget-platform.tpl-target
    Just(key-vals.map(fn(kv) {parse-external-includes(target, rng, kv)}).concat)
  else Nothing

fun parse-external-import(r: range): _ maybe<external>
  parse-choices("import", [
    {
      parse-keyword("=")
      parse-external-import-entry().map(fn(entry) ExternalImport(entry, r))
    },{
      val (mbentries, rng2) = parse-semi-braces-ranged("entries", parse-external-import-entry)
      firstof(mbentries).map(fn(entry) ExternalImport(entry, r.combine(rng2)))
    }
  ])

fun parse-external-body(): _ maybe<(external-call, range)>
  firstof(parse-semi-braces("external entries", parse-external-entry))

fun parse-external-entry(): _ maybe<(external-call, range)>
  val matches = parse-target-guard()
  val (call, rng) = parse-external-call()
  if matches then Just((call, rng)) else Nothing

fun parse-external-call(): _ (external-call, range)
  val f = parse-maybe-nb("inline", {parse-special-id("inline"); ExternalInline}).default(ExternalCall)
  val (s, rng) = parse-string-literal()
  (f(s), rng)

// Fixity declaration
fun parse-fixity-decl(): _ list<fix-def>
  val (vis, vrng, assoc) = parse-try
    val (vis, vrng) = parse-visibility(Private); 
    val assoc = parse-assoc-decl(); 
    (vis, vrng, assoc)
  val (prec, lex) = parse-integer()
  if prec < 0 || prec > 100 then
    parse-error("fixity must be between 0 and 100", lex.range)
  val names = parse-sep-by1("names", parse-identifier, parse-comma)
  names.map(fn((name, rng)) FixDef(name, FixInfix(prec, assoc), rng.combine(vrng), vis))

fun parse-assoc-decl(): _ assoc
  parse-choices("associativity", [
    {parse-keyword("infixl"); AssocLeft},
    {parse-keyword("infixr"); AssocRight},
    {parse-keyword("infix"); AssocNone}
  ])

// Type definitions
fun parse-alias-decl(dvis: visibility): _ user-typedef
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

fun parse-type-declaration(vis: visibility): _ (user-typedef,list<user-def>)
  parse-choices("type", [{parse-data-type-decl(vis)}, {parse-struct-decl(vis)}])

fun parse-data-type-decl(dvis: visibility): _ (user-typedef,list<user-def>)
  val (vis, defvis, vrng, (typeSort, trng, doc, ddef)) = parse-choices("type", [
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
  val (cs, crng) = parse-maybe-nb("", {parse-semi-braces-ranged("", {parse-constructor(defvis, tpars, resTp)})}).default(([], null)) // no backtracking (a bad constructor must error, not yield a constructor-less type)
  val (constrs, creatorss) = cs.unzip
  val range = combine([vrng, trng, name.range, prng, crng])
  (DataType(name, tpars, constrs, range, vis, typeSort, ddef, DataNoEffect, doc), creatorss.concat)

fun parse-struct-decl(dvis': visibility): _ (user-typedef,list<user-def>)
  val ((vis, defvis, ddef), (vrng, trng, doc)) = parse-try
      val (vis, defvis, rng1) = parse-choices("", [
        {val rng = parse-keyword("abstract"); (Public, Private, rng)}, 
        {val (vis, rng) = parse-visibility(dvis'); (vis, vis, rng)}
      ])
      val (rng2, ddef) = parse-choices("", [
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

fun parse-type-declaration-kind(): _ (data-kind, range, string, data-def)
  parse-choices("", [
    {
      val (rng1, kind) = parse-choices("", 
        [{val rng = parse-special-id("div", ["rec"]); (rng, Retractive)},
         {val rng = parse-special-id("co"); (rng, CoInductive)}])
      val (rng2, doc) = parse-doc-keyword("type")
      (kind, rng1.combine(rng2), doc, DataDefNormal)
    },
    {
      val (rng1, ddef) = parse-choices("", [
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

fun parse-type-kind-params(): _ (list<user-type-binder>,user-kind,range)
  // no backtracking: plain <|> (a malformed `<T,,>`/kind annotation
  // must error, not silently discard the type parameters)
  parse-choices-nb("", [
    { val (tpars, rng) = angles-ranged(parse-type-binders); 
      val kind = parse-kind-annotation(); 
      (tpars, kind, rng.combine(kind.range))},
    { val kind = parse-kind-annotation(); 
      ([], kind, kind.range)},
    { ([], KindNone, null)}
  ])

fun parse-constructor(dvis: visibility, foralls: list<user-type-binder>, resTp: user-type)
  val (vis, vrng) = parse-visibility(dvis)
  val (mbLazyFip, lrng) = parse-maybe-nb("lazy", {parse-special-id("lazy"); val (fip, rng) = parse-tail-fip(); (Just(fip), rng)}).default((Nothing, null))
  val rng0 = parse-maybe-nb("", {parse-keyword("con")}).default(null)
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
  // no backtracking: (a malformed `{...}`/`(...)` field list
  // must error, not silently become a bogus zero-field constructor)
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
fun parse-effect-decl(dvis: visibility): _ list<top-def>
  val ((vis,defVis,vrng,erng),(doc,singleShot,sort),isInstance,isScoped) = parse-try
    val (vis, defVis, vrng) = parse-choices("", [{val (v, vr) = parse-visibility(dvis); (v, v, vr)}, {val vr = parse-keyword("abstract"); (Public, Private, vr)}])
    val isInstance = parse-maybe-nb("named", {parse-keyword("named")}).is-just
    val isScoped = parse-maybe-nb("scoped", {parse-special-id("scoped", [])}).is-just
    val (rng1, singleShot) = parse-maybe-nb("linear", {val rng = parse-special-id("linear", []); (rng, True)}).default((null, False))
    val sort = parse-maybe-nb("sort", {parse-special-id("div", ["rec"]); Retractive}).default(Inductive)
    val (rng2, doc) = parse-doc-keyword("effect")
    val erng = rng1.combine(rng2)
    ((vis,defVis,vrng,erng),(doc,singleShot,sort),isInstance,isScoped)
  val extra = if sort.is-retractive then [TpCon(nameTpDiv, erng.combine(vrng))] else []
  make-effect-decl(parse-choices-nb("", [{ // no backtracking (errors inside the effect body must propagate)
    val (effectId, irng) = parse-type-ident()
    val (tpars, kind, prng) = parse-type-kind-params()
    val effectsExtra = 
      if !isInstance then EffectExtra(extra)
      // no backtracking: (a malformed type after
      // `in` must error, not be silently discarded as if `in` were absent)
      else parse-choices-nb("", [
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

fun parse-doc-keyword-effect(): _ (range, string)
  parse-doc-keyword("effect", ["context", "ambient"])

fun parse-doc-keyword-fun(): _ (range, string)
  parse-doc-keyword("fun",[])

fun parse-keyword-mask(): _ range
  parse-keyword("mask", ["inject"])

fun parse-operation-decl(lin: bool, vis: visibility)
  parse-choices("op decl", [
    {parse-value-operation-decl(vis)},
    {parse-fun-operation-decl(lin, vis)}
  ])

// effect NAME {val op = ...}
// TODO: annotate the operation as "value operation" to
// (a) also constrain the definition in the handler to use `val`
// (b) constrain the use site to use it as a value
fun parse-value-operation-decl(vis: visibility): _ op-decl
  val (rng0, doc) = parse-doc-keyword("val")
  val (id, idrng) = parse-identifier()
  parse-keyword(":")
  val (mbTeff, tRes) = parse-tresult()
  if mbTeff.is-just then
    parse-error("an explicit effect in result type of an operation is not allowed (yet)", mbTeff.map(kut/range).default(rng0))
  val oprng = combine([rng0, idrng, tRes.range])
  OpDecl(doc, id.to-value-operation-name, rng0, idrng, True, OpVal, [], [], idrng, mbTeff, tRes, oprng)

fun parse-fun-operation-decl(lin: bool, vis: visibility): _ op-decl
  val ((rng0, doc), sort) = parse-choices-nb("op decl", [ // no backtracking: (keeps the linear-effect diagnostics)
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
     val rdoc = parse-choices("",[{parse-doc-keyword("except")}, {parse-doc-keyword("brk")}])
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
    parse-error("an explicit effect in result type of an operation is not allowed (yet)", mbTeff.map(kut/range).default(rng0))
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
// no backtracking: ONLY visibility/inline/keyword recognition
// (to disambiguate val/fun/fn without committing); the CHOSEN decl's actual
// body/param/result-type parsing runs OUTSIDE `try` so a genuine error deep in
// e.g. a malformed result-type effect row propagates as a hard failure instead
// of backtracking into "this wasn't a val/fun/fn decl after all"
fun parse-pure-decl(toplevel: bool, dvis: visibility): _ user-def
  fun choose-decl(): _ (() -> _ user-def)
    with parse-try
    val (vis, vrng) = parse-visibility(dvis)
    val inl = parse-inline()
    parse-choices("", [
      {
        val (rng, doc) = parse-doc-keyword("val");
        fn() parse-val-decl(vrng.combine(rng), doc, vis, inl)
      },
      {
        val (f,frng) = parse-tail-fip();
        val (rng, doc) = parse-doc-keyword-fun();
        fn() parse-fun-decl(toplevel, vrng.combine(rng).combine(frng), doc, vis, inl, f)
      },
      {
        parse-keyword("fn");
        parse-error("hint: use 'fun' to start a named function definition (and 'fn' for anonymous functions)", peek().range)}
    ])
  choose-decl()()

// no backtracking: only inline/fip/keyword recognition;
// the actual `funDecl` (param/result-type/body) parse runs OUTSIDE `try` (see
// `parse-pure-decl` for why this scoping matters)
fun parse-function-decl(toplevel: bool, vrng: range, vis: visibility): _ user-def
  fun choose-decl(): _ (() -> _ user-def)
    with parse-try
    val inl = parse-inline()
    val (f,frng) = parse-tail-fip()
    val (rng, doc) = parse-doc-keyword-fun()
    fn() parse-fun-decl(toplevel, vrng.combine(rng).combine(frng), doc, vis, inl, f)
  choose-decl()()

fun parse-variable-declaration(): _ user-def
  val (vrng, doc) = parse-doc-keyword("var")
  val bind = parse-value-binder(vrng)
  parse-keyword(":=")
  val body = parse-block-expr()
  Def(bind(body), vrng.combine(body.range), Private, DefVar, InlineNever, doc)

fun parse-val-decl(rng: range, doc: string, vis: visibility, inl: def-inline): _ user-def
  val bind = parse-value-binder(rng)
  parse-keyword("=")
  val body = parse-block-expr()
  Def(bind(body), rng.combine(body.range), vis, DefVal, inl, doc)

fun parse-fun-decl(toplevel: bool, rng: range, doc: string, vis: visibility, inl: def-inline, f: fipT): _ user-def
  val spars = parse-s-quantifier()
  // trace("parsing function " ++ toplevel.show ++ "\n" ++ doc ++ "\n")
  val (name, nameRng) = parse-fun-id()
  // trace("parsing function " ++ name.show ++ "\n")
  val FunDef(tpars, pars, pinfos, parsRng, mbTres, preds, ann) = parse-fun-def(True, True)
  val body = parse-body-expr()
  val fnct = promote(spars, tpars, preds, mbTres, Lam(pars, body, toplevel, rng.combine(body.range)))
  // The binder's range spans the NAME THROUGH THE PARAMETER LIST
  Def(ValueBinder(name, (), ann(fnct), nameRng, nameRng.combine(parsRng)), rng.combine(fnct.range), vis, def-fun-ex(pinfos, f), inl, doc)

fun parse-fun-def(allowBorrow: bool, allowImplicits: bool)
  val tpars = parse-type-params()
  val (pars, pinfos, transform, rng) = parse-parameters(allowBorrow, True, allowImplicits)
  val resultTp = parse-annot-result()
  val preds = []
  FunDef(tpars, pars, pinfos, rng, resultTp, preds, transform)

fun parse-annot-result(): _ maybe<(maybe<user-type>, user-type)>
  // no backtracking: `annotResult` starts by consuming the mandatory `:` keyword
  parse-maybe-nb("")
    val (teff, tres) = parse-annotated-result()
    (Just(teff), tres)

fun parse-annotated-result(): _ (user-type, user-type)
  parse-keyword(":")
  parse-result-type()

fun parse-type-params(): _ list<user-type-binder>
  parse-maybe-list({angles(parse-type-binders)})

fun parse-parameters(allowBorrow: bool, allowDefaults: bool, allowImplicits: bool)
  val (results, rng) = parse-parens-commas-ranged({parse-parameter(allowBorrow, allowDefaults, allowImplicits)})
  val (binders, pinfos, transforms) = results.unzip3
  fun transform(e: user-expr): _ user-expr
    transforms.foldr(e, fn(f, e') f(e'))
  // TODO: Check correct parameter order: normal, named, implicit
  (binders, pinfos, transform, rng)

fun parse-parameter(allowBorrow: bool, allowDefaults: bool, allowImplicits: bool)
  val pinfo = if allowBorrow then parse-param-info() else Own
  // no backtracking: `parse-choices-nb` will try each parser in order, and only backtrack if the first one fails
  val (binder, transform) = if allowImplicits then parse-choices-nb("parameter", [parse-parameter-implicit, {parse-parameter-normal(allowDefaults)}]) else parse-parameter-normal(allowDefaults) 
  (binder, pinfo, transform)

fun parse-parameter-normal(allowDefaults: bool)
  val pat = parse-pattern-atom()
  val mtp = parse-maybe-nb("", parse-parameter-type-annotation)
  val (opt, drng) = if allowDefaults then parse-default-expr() else (Nothing, range/null)
  val rng = match pat
    PatVar(binder) -> binder.expr.range
    _ -> pat.range
  fun binder(name: name, nameRng: range)
    ValueBinder(name, mtp, opt, nameRng, combine([rng, drng, mtp.map(kut/range).default(drng)]))
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
  val tp = parse-maybe-nb("", parse-type-annot)
  val unpackExpr = if unpack then Just(Parens(Var(qname.unqualify-full, False, rng), nil, "", rng)) // Encode .? as a default value assuming it is a type name
                   else Nothing
  (ValueBinder(qname, tp, unpackExpr, combine([rng, tp.map(kut/range).default(rng)]), rng), id)

fun parse-default-expr()
  parse-maybe-nb("default", {val krng = parse-keyword("="); val e = parse-expression(); (Just(e), krng.combine(e.range))}).default((Nothing, null))

fun parse-block(): _ user-expr
  val rng1 = parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val stmts1 = semis("statements", parse-statement)
  val stmts2_0 = parse-maybe-nb("") 
      val rng2 = parse-keyword("return")
      val e = parse-expression()
      parse-many("semicolons", parse-semicolon)
      [StatExpr(e.make-return(rng2))]
  val stmts2 = stmts2_0.default([])
  val rng2 = parse-right-curly()
  val localize = 
    match stmts1.any-statement-var
      Just(def) -> [StatFun(local-scope(def, _))]; 
      Nothing -> []
  val stats = localize ++ stmts1 ++ stmts2
  match stats.reverse
    Cons(StatExpr(exp), rst) -> Parens(rst.reverse.foldr(exp, combine), nil, "", rng1.combine(rng2))
    [] -> Var(nameUnit, False, rng1.combine(rng2))
    _ -> parse-error("Last statement in a block must be an expression", rng1.combine(rng2))

fun parse-statement(): _ statement
  parse-choices("statement", [
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

fun parse-local-value-declaration(): _ (user-expr -> _ user-expr)
  val krng = parse-keyword("val")
  val pat = parse-pattern()
  parse-keyword("=")
  val e = parse-block-expr()
  fun bindVar(binder:value-binder<maybe<user-type>, pattern<user-type>>, mbTyp: maybe<user-type>, rng: range): _ (user-expr -> _ user-expr)
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
  // no backtracking:
  // EITHER binder keyword (the port required both, breaking `with x <- e`),
  val mbPar = parse-maybe("", {
    val x = parse-parameter(False, False, False)
    parse-choices-nb("", [{parse-keyword("="); ()}, {parse-keyword("<-"); ()}])
    x
  })
  match mbPar
    Just((par, _, transform)) ->
      val e = parse-choices-nb("", [parse-basic-expr, {parse-handler-with(krng, HandlerInstance)}])
      fn(b:user-expr) apply-to-continuation(krng, [par.promote-value-binder], e.transform, b)
    Nothing ->
      val e = parse-choices-nb("", [parse-basic-expr, {parse-handler-with(krng, HandlerNormal)}])
      fn(b:user-expr) apply-to-continuation(krng, [], e, b)


fun parse-type-annotation(): _ (user-expr -> _ user-expr)
  parse-maybe("", {
    val tp = parse-type-annot()
    fn(x) Ann(x, tp, tp.range.combine(x.range))
  }).default(fn(x) x)

// Expressions
// no-backtracking: consumed-input failures COMMIT (parse-choices-nb)
fun parse-body-expr(): _ user-expr
  parse-choices-nb("", [parse-block-expr, {parse-keyword("->"); parse-block-expr()}])

fun parse-block-expr(): _ user-expr
  parse-choices-nb("expression", [parse-with-expr, parse-block-fun-expr, parse-return-expr, parse-val-expr, parse-basic-expr])

fun parse-expression(): _ user-expr
  parse-choices-nb("expression", [parse-with-expr, parse-fun-expr, parse-return-expr, parse-val-expr, parse-basic-expr])

fun parse-basic-expr(): _ user-expr
  parse-choices-nb("basic expression", [parse-if-expr, parse-fn-expr, parse-match-expr, parse-handler-expr, parse-op-expr])

fun parse-with-expr(): _ user-expr
  val f = parse-with-statement()
  parse-keyword("in")
  f(parse-block-expr())

fun parse-val-expr(): _ user-expr
  val f = parse-local-value-declaration()
  parse-keyword("in")
  f(parse-expression())

fun parse-block-fun-expr(): _ user-expr
  parse-choices("", [parse-block, {parse-lambda(["fun"])}])

fun parse-fun-expr(): _ user-expr
  parse-choices("", [parse-fun-block, {parse-lambda(["fun"])}])

inline fun parse-fn-expr(): _ user-expr
  parse-lambda([])

fun parse-fun-block(): _ user-expr
  val exp = parse-block()
  Lam([], exp, False, exp.range)

fun parse-lambda(alts: list<string>): _ user-expr
  val rng = parse-keyword("fn")
  val spars = parse-s-quantifier()
  val FunDef(tpars, pars, _, _, mbTres, preds, ann) = parse-fun-def(False, True)
  val body = parse-body-expr()
  val f = promote(spars, tpars, preds, mbTres, Lam(pars, body, False, rng.combine(body.range)))
  ann(Parens(f, "fn".new-name, "", rng))

fun parse-if-expr(): _ user-expr
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
        val eExpr = parse-maybe-nb("", {parse-keyword("else"); parse-block-expr()}).default(Var(nameUnit, False, (tExpr.range).combine(eExprs.map(_.snd.range).combine).after))
        (tExpr, eExprs, eExpr)
      }
    ])
  Cons((tst, tExpr), eExprs).foldr(eExpr) fn((tst', tExpr'), eExpr')
    Case(tst', [Branch(PatCon(nameTrue, [], null, null), [Guard(guardTrue, tExpr')]),
              Branch(PatCon(nameFalse, [], null, null), [Guard(guardTrue, eExpr')])], False, tst'.range.combine(eExpr'.range))
  
fun parse-elif-expr(): _ (user-expr, user-expr)
  val rng = parse-keyword("elif")
  val tst = parse-non-trailing-lambda()
  val tExpr = parse-then-expr(rng)
  (tst, tExpr)

fun parse-then-expr(rng: range): _ user-expr
  parse-choices("then", [
    {parse-keyword("then"); parse-block-expr()},
    {
      val expr = parse-block-expr()
      add-warning("warning " ++ expr.range.before.start.show ++ ": using an 'if' without 'then' is deprecated.\n hint: add the 'then' keyword.", expr.range) 
      expr
    }
  ])

fun parse-return-expr(): _ user-expr
  val rng = parse-keyword("return")
  val exp = parse-expression()
  exp.make-return(rng)

fun parse-match-expr(): _ user-expr
  parse-choices("", [{
    val lzy = parse-maybe-nb("", {parse-special-id("lazy")}).is-just
    val rng = parse-keyword("match")
    val tst = parse-non-trailing-lambda()
    val (branches, rng2) = parse-semi-braces-ranged1("match clause", parse-branch)
    Case(tst, branches, lzy, rng.combine(rng2))
  }, parse-handler-expr])

fun parse-handler-expr(): _ user-expr
  val (rng0, hsort, over) = parse-choices("named or override", [
    {val rng = parse-keyword("named"); (rng, HandlerInstance, HandlerNoOverride)},
    {val rng = parse-keyword("override"); (rng, HandlerNormal, HandlerOverride)},
    {(null, HandlerNormal, HandlerNoOverride)}
  ])
  parse-choices("handle or handler", [
    {
      val rng1 = parse-keyword("handle")
      val rng = rng0.combine(rng1)
      val mbEff = parse-handler-effect()
      val scoped = parse-maybe-nb("", {parse-special-id("scoped"); HandlerScoped}).default(HandlerNoScope)
      val arg = parse-non-trailing-lambda()
      val expr = parse-handler-clauses(rng, mbEff, scoped, over, hsort)
      App(expr, [(Nothing, arg)], rng.combine(expr.range))
    },
    {
      val rng1 = parse-keyword("handler")
      val rng = rng0.combine(rng1)
      val mbEff = parse-handler-effect()
      val scoped = parse-maybe-nb("", {parse-special-id("scoped"); HandlerScoped}).default(HandlerNoScope)
      parse-handler-clauses(rng, mbEff, scoped, over, hsort)
    },
    {
      if rng0.is-null then parse-error("expected handler", peek().range)
      else parse-handler-clauses(rng0, Nothing, HandlerNoScope, over, hsort)
    }
  ])

fun parse-handler-with(rng: range, hSort: handler-sort): _ user-expr
  match hSort
    HandlerInstance ->
      val rng0 = parse-keyword("named")
      val rng1 = parse-keyword("handler")
      val hrng = rng0.combine(rng1)
      val mbEff = parse-handler-effect()
      val scoped = parse-maybe-nb("", {parse-special-id("scoped"); HandlerScoped}).default(HandlerNoScope)
      parse-handler-clauses(hrng, mbEff, scoped, HandlerNoOverride, HandlerInstance)
    HandlerNormal ->
      val (rng0, over) = parse-maybe-nb("", {val r = parse-keyword("override"); (r, HandlerOverride)}).default((null, HandlerNoOverride))
      val rng1 = parse-maybe-nb("", {parse-keyword("handler")}).default(null)
      val hrng = rng0.combine(rng1)
      val mbEff = parse-handler-effect()
      val scoped = parse-maybe-nb("", {parse-special-id("scoped"); HandlerScoped}).default(HandlerNoScope)
      parse-handler-clauses(hrng, mbEff, scoped, over, HandlerNormal)

fun parse-handler-effect(): _ maybe<user-type>
  parse-maybe("", {val eff = angles(parse-type); eff.promote-type})

fun parse-handler-clauses(rng: range, mbEff: maybe<user-type>, scoped: handler-scope, over: handler-override, hsort: handler-sort): _ user-expr
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

fun parse-op-clauses(): _ (list<binder>, range)
  fun parse-single-op()
    val (op, bind) = parse-handler-op()
    ([(op, bind)], op.range)
  
  parse-choices-nb("", [ // no-backtracking (keeps the lparen diagnostic)
    { parse-semi-braces-ranged("", parse-handler-opx)},
      parse-single-op,
    { val rng = parse-left-paren();
      parse-error("unexpected '(': local parameters are no longer supported, use a local 'var' instead", rng)},
    { ([], null)}
  ])

fun parse-handler-opx(): _ (clause, maybe<(user-expr -> user-expr)>)
  parse-choices-nb("handler clause", [ // no-backtracking
    {
      val rng = parse-special-id("finally")
      parse-maybe("", {parens({()})})
      val expr = parse-body-expr()
      (ClauseFinally(Lam([], expr, False, rng.combine(expr.range))), Nothing)
    },{
      val rng = parse-special-id("initially")
      // -- the parens themselves are optional; there is no `_` fallback INSIDE them
      val (name, prng, tp) = parse-maybe-nb("", {
        parens
          val (name,prng) = parse-param-id()
          val tp = parse-maybe-nb("", parse-parameter-type-annotation)
          (name, prng, tp)
      }).default((new-name("_"), rng, Nothing))
      val expr = parse-body-expr()
      (ClauseInitially(Lam([ValueBinder(name, tp, Nothing, prng, rng.combine(tp.map(kut/range).default(rng)))], expr, False, rng.combine(expr.range))), Nothing)
    }, parse-handler-op
  ])

fun parse-handler-op(): _ (clause, maybe<(user-expr -> user-expr)>)
  parse-choices-nb("handler clause", [ // no-backtracking
    {
      val rng = parse-keyword("return")
      val (name, prng, tp) = parse-choices("", [
        {
          val (name, prng) = parse-param-id()
          parse-warning-message("'return x' is deprecated; use 'return(x)' instead.", prng)
          (name, prng, parse-maybe-nb("", parse-parameter-type-annotation))
        },
        {
          parens
            val (name, prng) = parse-param-id()
            (name, prng, parse-maybe-nb("", parse-parameter-type-annotation))
        }
      ])
      val expr = parse-body-expr()
      (ClauseRet(Parens(Lam([ValueBinder(name, tp, Nothing, prng, prng.combine(tp.map(kut/range).default(prng)))], expr, False, rng.combine(expr.range)), "return".new-name, "", rng)), Nothing)
    },{ // TODO: is "raw" needed for value definitions?
      parse-keyword("val")
      val (name, nameRng) = parse-qualified-identifier()
      parse-keyword("=")
      val expr = parse-block-expr()
      val (binder, resumeExpr) = bind-expr-to-val(name, nameRng, expr)
      (ClauseBranch(HandlerBranch(name.to-value-operation-name, [], resumeExpr([]), OpVal, nameRng, nameRng)), Just(binder))
    },{
      val (opSort, (name, nameRng)) = parse-choices("opSort", [
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
  parse-maybe-nb("", {parse-parens-commas-ranged(parse-op-param)}).default(([], null)) // no-backtracking

fun parse-op-param()
  val (name, rng) = parse-param-id()
  val tp = parse-maybe-nb("", parse-type-annot)
  ValueBinder(name, tp, (), rng, rng.combine(tp.map(kut/range).default(rng)))

fun parse-handler-param()
  val (name, rng) = parse-identifier()
  val tp = parse-maybe-nb("", parse-type-annot)
  ValueBinder(name, tp, (), rng, rng.combine(tp.map(kut/range).default(rng)))

fun parse-branch(): _ user-branch
  val pat = parse-pattern()
  val grds = parse-guards()
  Branch(pat, grds)

fun parse-guard-vertical-bar(): _ range
  parse-token("guard condition \"|\"") fn(x)
    match x.lex
      LexKeyword("|", _) -> Just(x.range)
      _ -> Nothing

fun parse-guards(): _ list<user-guard>
  parse-choices-nb("guards", [ // no-backtracking (commits on `->`)
    {parse-many1("", parse-guard-bar)},
    {parse-keyword("->"); [Guard(guardTrue, parse-block-expr())]},
    {
      val exp = parse-block()
      parse-warning-message("use '->' for pattern matches", exp.range)
      [Guard(guardTrue, exp)]
    }
  ])

fun parse-guard-bar(): _ user-guard
  parse-guard-vertical-bar()
  val grd = parse-guard-test()
  parse-keyword("->")
  val exp = parse-block-expr()
  Guard(grd, exp)

fun parse-guard-test()
  parse-choices-nb("guard condition or '_'", [ // no-backtracking (otherwise-hint must fire; also `otherwise` must NOT parse as a var)
    {parse-special-id("otherwise"); parse-error("hint: use \"_\" instead of \"otherwise\" for the guard condition", peek().range)},
    parse-expression,
    {parse-wildcard(); guardTrue}
  ])

// Op expr
// Non trailing lambda expressions
inline fun parse-non-trailing-lambda(): _ user-expr
  parse-op-exprx(False)

inline fun parse-op-expr(): _ user-expr
  parse-op-exprx(True)

fun parse-op-exprx(allowTrailingLam: bool): _ user-expr
  val e1 = parse-prefix-expr(allowTrailingLam)
  // trace("Parsed expression " ++ e1.show ++ "\n")
  parse-choices-nb("", [ // no-backtracking (`x + <bad>` must error, not degrade to `x`)
    {
      val ess = parse-many1("", {
                                  val op = parse-operator-var(); 
                                  // trace("Parsed operator " ++ op.show ++ "\n")
                                  val e2 = parse-prefix-expr(allowTrailingLam); 
                                  // trace("Parsed expression2 " ++ e2.show ++ "\n")
                                  [op, e2]})
      App(Var(nameOpExpr, True, null), 
          Cons(e1, ess.concat).map((Nothing, _)), 
          combine(Cons(e1.range, ess.concat.map(range))))
    }, {e1}
  ])


fun parse-operator-var(): _ user-expr
  parse-choices("", [
    {val (name, rng) = parse-qualified-operator(); Var(name, True, rng)},
    {Var(nameAssign, True, parse-keyword(":="))}
  ])

fun parse-prefix-expr(allowTrailingLam: bool): _ user-expr
  val ops = parse-many("", parse-prefix-op)
  val aexp = parse-application-expression(allowTrailingLam)
  ops.foldr(aexp, fn(op, e) App(op, [(Nothing, e)], op.range.combine(e.range)))

fun parse-application-expression(allowTrailingLam: bool): _ user-expr
  val e0 = parse-atomic()
  // trace("applying " ++ e0.show ++ "\n")
  val fs = parse-many("", {parse-choices-nb("", [parse-dot-expr, parse-applier, parse-indexer, {parse-func-applications(allowTrailingLam)}])})
  fs.foldl(e0, fn(e:user-expr, f:user-expr -> user-expr) f(e))

fun parse-dot-expr(): _ (user-expr -> user-expr)
  parse-keyword(".")
  parse-choices("", [
    {
      val e = parse-choices("", [parse-idcon, parse-eta-hole])
      // no backtracking: (a malformed `.foo(bad args` must error, not silently become a bogus single-arg
      // call with trailing tokens left unconsumed)
      parse-choices-nb("", [
        {
          val rng = parse-left-paren()
          val args = parse-sep-by("", parse-argument, parse-comma)
          val rng1 = parse-right-paren()
          fn(arg0) App(e, Cons((Nothing, arg0), args), rng.combine(arg0.range).combine(rng1))
        },
        { fn(arg0) App(e, [(Nothing, arg0)], arg0.range.combine(e.range)) }
      ])
    }, parse-applier])

fun parse-indexer(): _ (user-expr -> user-expr)
  val rng0 = parse-left-bracket()
  parse-choices("", [
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
      fn(e) App(Var(nameIndex, False, rng0.combine(rng1)), Cons(e, idxs).map((Nothing, _)), rng0.combine(rng1))
    }
  ])

fun parse-applier(): _ (user-expr -> user-expr)
  val rng0 = parse-left-paren()
  val args = parse-sep-by("", parse-argument, parse-comma)
  val rng1 = parse-right-paren()
  fn(e) App(e, args, rng1.combine(e.range))

fun parse-func-application(allowTrailingLam: bool): _ user-expr
  if allowTrailingLam then parse-choices("", [parse-fun-block, {parse-lambda([])}])
  else parse-lambda([])

fun parse-func-applications(allowTrailingLam: bool): _ (user-expr -> user-expr)
  fun inject-apply(e, fs)
    match fs
      [] -> e
      _ -> 
        val nfargs = fs.map(fn(e') (Nothing, e'))
        match e
          App(f, args, rng) -> 
            val positional = args.filter(_.fst.is-nothing) ++ nfargs
            val namedargs = args.filter(_.fst.is-just)
            App(f, positional ++ namedargs, rng)
          _ -> App(e, nfargs, combine(Cons(e.range, fs.map(range))))
  val fs = parse-many1("", {parse-func-application(allowTrailingLam)})
  fn(arg0)
    inject-apply(arg0, fs)

fun parse-argument(): _ (maybe<(name,range)>, user-expr)
  val exp = parse-annotated-expr()
  match exp
    Var(name, _, rng) ->
      val x = parse-maybe("=")
        parse-keyword("=")
        val exp' = parse-expression()
        match exp'
          Var -> (Just((name, rng)), exp') // Don't eta-expand if the argument is just a variable
          _ -> (Just((name, rng)), exp'.eta-expand)
      match x
        Just(x') -> x'
        Nothing -> (Nothing, exp)
    _ -> (Nothing, exp.eta-expand)

/// Atomic expression
fun parse-atomic(): _ user-expr
  parse-choices-nb("(simple) expression", [ 
    parse-idcon,
    parse-tuple-expression, // must be second due to '(' operator ')'
    parse-list-expr, 
    {Literal(parse-literal())}, 
    parse-constructor-context-hole, 
    parse-eta-hole, 
    parse-constructor-context-expr, 
    parse-mask-expr
  ])

fun parse-literal(): _ lit
  parse-choices("", [
    {val (i, tok) = parse-integer(); LitInt(i, tok.range)},
    {val (f, tok) = parse-float(); LitFloat(f, tok.range)},
    {val (s, range) = parse-string-literal(); LitString(s, range)},
    {val (c, range) = parse-char-literal(); LitChar(c.string, range)},
  ])

fun parse-annotated-expr(): _ user-expr
  val e = parse-expression()
  // no backtracking: (a malformed type after `:` must error, not be silently dropped)
  parse-choices-nb("", [
    {
      parse-keyword(":");
      val tp = parse-type-scheme();
      Ann(e, tp, e.range.combine(tp.range))},
    { e }])

fun parse-tuple-expression(): _ user-expr
  val rng1 = parse-left-paren()
  val es = parse-sep-by("", parse-annotated-expr, parse-comma)
  val rng2 = parse-right-paren()
  val rng = rng1.combine(rng2)
  match es
    Nil -> Var(nameUnit, False, rng)
    [e] -> Parens(e, nil, "", rng)
    _ -> App(Var(name-tuple(es.length), False, rng), es.map((Nothing, _)), rng)

fun parse-list-expr(): _ user-expr
  val rng1 = parse-special("[")
  val es = parse-sep-by("",parse-annotated-expr, parse-comma)
  val rng2 = parse-special("]")
  if es.is-nil then
    make-nil(rng1.combine(rng2))
  else
    es.foldr(make-nil(rng2.after), fn(x, acc) rng1.make-cons(x, acc, userTpRange)).adjust-range(rng1.combine(rng2))

fun parse-constructor-context-expr(): _ user-expr
  parse-constructor-context(parse-keyword("ctx"))

fun parse-constructor-context(rng: range): _ user-expr
  make-app(Var(nameCCtxCreate, False, rng), [parse-non-trailing-lambda()], userTpRange)

fun parse-constructor-context-hole(): _ user-expr
  val rng = parse-choices("", [{parse-keyword("hole")}])
  make-app(Var(nameCCtxHoleCreate, False, rng), [], userTpRange)

fun parse-eta-hole(): _ user-expr
  val (nm, rng) = parse-wildcard()
  Var(nm, False, rng)

fun parse-mask-expr(): _ user-expr
  val (rng, mkInj) = parse-mask-type()
  // no backtracking: i.e. EITHER a
  // parenthesized expression `mask<eff>(expr)` OR a bare `{ ... }` funblock
  // `mask<eff>{ ... }` Once a body-form starts consuming
  // input, a later failure inside it must propagate hard, not silently fall
  // back to (mis-)treating `mask<eff>` as a bare, unapplied function value.
  parse-choices-nb("", [
    {mkInj(parse-choices-nb("", [{parens(parse-expression)}, parse-fun-block]))}, // Need apply or the escape check may fail if it becomes a separate lambda
    {val name = new-hidden-name("mask-action"); Lam([ValueBinder(name, Nothing, Nothing, rng, rng)], mkInj(Var(name, False, rng)), False, rng)}
  ])

fun parse-mask-type(): _ (range, (user-expr -> _ user-expr))
  val rng1 = parse-keyword-mask()
  val behind = parse-maybe("", {parse-special-id("behind")}).is-just
  parse-left-angle()
  val tps1 = parse-sep-by1("mask types", parse-type, parse-comma)
  val rng2 = parse-right-angle()
  val rng = rng1.combine(rng2)
  match tps1.reverse
    Cons(tp, tps) ->
      fun mk-inj(exp: user-expr)
        val base = Inject(promote-type(tp), exp, behind, rng)
        tps.foldl(base, fn(e, t) Inject(promote-type(t), Lam([], e, False, rng), behind, rng))
      (rng, mk-inj)
    Nil -> parse-error("expected at least one masked effect type", rng)

fun parse-value-binder(pre: range): _ (user-expr -> _ value-binder<(), user-expr>)
  val (name, range) = parse-locally-qualified-identifier()
  val ann = parse-type-annotation()
  fn(e:user-expr) ValueBinder(name, (), ann(e), range, pre.combine(range))

inline fun parse-pattern(): _ user-pattern
  parse-pattern-annotation()

fun parse-pattern-annotation(): _ user-pattern
  val p = parse-pattern-atom()
  parse-maybe-type-annotation(p) fn(tp0)
    val tp = promote-type(tp0)
    match p
      PatVar(ValueBinder(name, Nothing, npat, rng1, rng2)) -> 
        PatVar(ValueBinder(name, Just(tp), npat, rng1, rng2))
      _ -> PatAnn(p, tp, p.range.combine(tp.range))

fun parse-pattern-atom(): _ user-pattern
  parse-choices("pattern atom", [
    {
      val (name, rng) = parse-qualified-constructor()
      // no backtracking
      val (ps, r) = parse-choices-nb("", [{parse-parens-commas-ranged(parse-named-pattern)}, {([], null)}])
      PatCon(name, ps, rng, rng.combine(r))
    },
    {
      val (name, rng) = parse-locally-qualified-identifier()
      // no backtracking
      parse-choices-nb("", [
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

fun parse-named-pattern(): _ (maybe<(name,range)>, user-pattern)
  parse-choices("named pattern", [
    {
      val (name, rng) = parse-identifier();
      parse-keyword("=")
      (Just((name, rng)), parse-pattern())
    },
    { (Nothing, parse-pattern()) }
  ])

fun parse-maybe-type-annotation(d: a, f: (user-type) -> _ a): _ a
  parse-maybe("", {f(parse-type-annot())}).default(d)

fun parse-list-pattern(): _ user-pattern
  val rng1 = parse-special("[")
  val es = parse-sep-by("", parse-pattern, parse-comma)
  val rng2 = parse-special("]")
  if es.is-nil then
    make-nil-pattern(rng1.combine(rng2))
  else
    PatParens(es.foldr(make-nil-pattern(rng2.after),make-cons-pattern), rng1.combine(rng2))

fun warn-deprecated(o: string, n: string, rng: range): _ ()
  add-warning("warning " ++ rng.start.show ++ ": keyword \"" ++ o ++ "\" is deprecated, use \"" ++ n ++ "\" instead", rng)

fun parse-warning-message(msg: string, rng: range): _ ()
  add-warning("warning " ++ rng.start.show ++ ":" ++ msg, rng)

fun test()
  "Compiles!".println