// Generate JavaScript code from System-F core (port of Backend/JavaScript/FromCore.hs)
// Ported as of 2026-07-25; upstream baseline commit dd91082 of Backend/JavaScript/FromCore.hs
module compiler/backend/js/from-core

import std/data/rb-set
import std/core/undiv
import std/num/float64
import compiler/lib/pprint
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/syntax
import compiler/common/unique
import compiler/platform/config
import compiler/kind/kind
import compiler/type/type
import compiler/type/kind
import compiler/type/pretty
import compiler/core/core
import compiler/core/corevar

pub alias doc = pprint/doc

// the assembly environment
pub effect val js-module: name                    // current module
pub effect val subst-env: list<(tName, doc)>      // substituting names
pub effect val in-statement: bool                 // for generating correct function declarations in strict mode

pub alias asm-eff = <js-module, subst-env, in-statement, unique, pure, comp-flags>

// return context for statement generation
type result
  // first field carries function name if not anonymous; second the arguments (always known)
  ResultReturn(mbName: maybe<name>, params: list<tName>)
  // variable name and optional label to break
  ResultAssign(name: name, label: maybe<name>)

fun external-names(): list<(tName, doc)>
  [ (TName(nameTrue, typeBool), "true".text),
    (TName(nameFalse, typeBool), "false".text),
    (TName(nameOptionalNone, typeOptional), "undefined".text) ] // ugly but has real performance benefit

//--------------------------------------------------------------------------
// Entry point
//--------------------------------------------------------------------------

pub fun javascript-from-core(bt: buildType, mbMain: maybe<(name, bool)>, imports: kimports, core0: core): _ doc
  with val js-module = core0.coreName
  with val subst-env = external-names()
  with val in-statement = False
  with run-unique(0)
  gen-module(bt, mbMain, imports, core0)

fun gen-module(bt: buildType, mbMain: maybe<(name, bool)>, imports: kimports, core0: core): _ doc
  val externs = core0.externals.map(fn(ext) include-external(bt, ext)).concat.vcat
  val (tagDefs, defs) = core0.defs.partition(is-tag-def)
  val decls0 = gen-groups(True, tagDefs)
  val decls1 = gen-type-defs(core0.typedefs)
  val decls2 = gen-groups(True, defs)
  val mainEntry = match mbMain
    Nothing -> pprint/empty
    Just((name, _)) ->
      " ".text |-| "// main entry:".text |-|
      name.unqualify.js/pp-name |.| "($std_core.id);".text // pass id for possible cps translated main
  val externalImports = core0.externals.map(fn(ext) import-external(bt, ext)).concat
  val normalImports = imports.map(fn(imp) (imp.module-import, imp.importName.pp-mod-name))
  val importDecls = (externalImports ++ normalImports).map fn((dpath, dname))
    "import * as".text |+| dname |+| "from".text |+| (dpath |.| ".mjs".text).squotes |.| semi
  vcat([
    "// Koka generated module:".text |+| core0.coreName.show.string/pretty |.| ", koka version: 3.2.7".text,
    "\"use strict\";".text,
    " ".text,
    "// imports".text
  ] ++ importDecls ++ [
    " ".text,
    "// externals".text,
    externs,
    " ".text,
    "// type declarations".text,
    decls0,
    decls1,
    " ".text,
    "// declarations".text,
    decls2,
    mainEntry
  ])

fun is-tag-def(dg: def-group): bool
  match dg
    DefNonRec(def) -> def.def-name.is-open-tag-name
    _ -> False

fun module-import(imp: kimport): doc
  (if imp.package.is-empty then ".".text else imp.package.text) |.| "/".text |.| imp.importName.module-name-to-path.text

fun include-external(bt: buildType, ext: external): _ list<doc>
  match external-import-lookup(bt, "include-inline", ext)
    Just(content) -> [content.lines.map(text).vcat.align]
    _ -> []

fun import-external(bt: buildType, ext: external): _ list<(doc, doc)>
  match external-import-lookup(bt, "library", ext)
    Just(path) ->
      val libid = match external-import-lookup(bt, "library-id", ext)
        Just(name) -> name.text
        Nothing -> path.text
      [(path.text, libid)]
    _ -> []

//--------------------------------------------------------------------------
// Definition groups
//--------------------------------------------------------------------------

fun gen-groups(topLevel: bool, groups: list<def-group>): asm-eff doc
  with local-unique
  groups.map(fn(g) gen-group(topLevel, g)).vcat

fun gen-group(topLevel: bool, group: def-group): asm-eff doc
  match group
    DefRec(defs) -> defs.map(fn(d) gen-def(topLevel, d)).vcat
    DefNonRec(def) -> gen-def(topLevel, def)

fun gen-def(topLevel: bool, def: def): asm-eff doc
  val resDoc = def.ktype.ktp/pretty.type-comment
  val defDoc = match try-fun-def(def.def-name, resDoc, def.defExpr)
    Just(doc) -> if topLevel then pp-vis(doc) else doc
    Nothing ->
      val doc = gen-stat(ResultAssign(def.def-name, Nothing), def.defExpr)
      if topLevel then pp-vis("var".text |+| def.def-name.unqualify.js/pp-name |.| semi |--| doc)
      else doc
  val comm = def.doc.trim-right
  vcat([" ".text,
        if comm.is-empty then pprint/empty
        else (Cons(space, comm.lines.map(fn(s) ("// " ++ s).text))).vcat.align,
        defDoc])

fun pp-vis(doc: doc): doc
  "export".text |+| doc // always export due to inlined definitions

fun try-fun-def(name: name, comm: doc, ex: expr): asm-eff maybe<doc>
  match ex
    TypeApp(e) -> try-fun-def(name, comm, e)
    TypeLam(_, e) -> try-fun-def(name, comm, e)
    Lam(args, _, body) ->
      if in-statement then Nothing
      else Just(gen-fun-def(name, args, comm, body))
    _ -> Nothing

fun gen-fun-def(name: name, params: list<tName>, comm: doc, body: expr): asm-eff doc
  val args = params.map(fn(p) p.get-name.js/pp-name)
  val isTailCall = body.is-tail-calling(name)
  val bodyDoc =
    if isTailCall then
      with override val in-statement = True
      gen-stat(ResultReturn(Just(name), params), body)
    else gen-stat(ResultReturn(Just(name), params), body)
  "function".text |+| name.unqualify.js/pp-name |.| args.tupled |+| comm |+|
    (if isTailCall then bodyDoc.tco-block else bodyDoc.block)

//--------------------------------------------------------------------------
// Value constructors for each defined type
//--------------------------------------------------------------------------

fun gen-type-defs(groups: typedef-groups): asm-eff doc
  groups.map(gen-type-def-group).vcat

fun gen-type-def-group(tds: typedef-group): asm-eff doc
  tds.map(gen-type-def).vcat

fun gen-type-def(td: typedef): asm-eff doc
  match td
    Synonym -> pprint/empty
    Data(info) ->
      val (_dataRepr, conReprs) = info.data-repr(data/is-value)
      val docs = info.constrs.zip(conReprs).map fn((c, crepr))
        val args = c.params.map(fn((nm, _)) nm.js/pp-name)
        val cname = c.name.gen-name
        fun singleton-value(v: string)
          constdecl |+| cname |+| "=".text |+| v.text |.| semi |+| c.typeScheme.ktp/pretty.linecomment
        val decl =
          if c.name == nameTrue then constdecl |+| cname |+| "= true".text |.| semi
          elif c.name == nameFalse then constdecl |+| cname |+| "= false".text |.| semi
          else match crepr
            ConEnum(tag=tag) ->
              constdecl |+| cname |+| "=".text |+| tag.show.text |.| semi |+| c.typeScheme.ktp/pretty.linecomment
            ConSingleton | c.name == nameOptionalNone -> singleton-value("undefined")
            ConSingleton(repr=DataStructAsMaybe) -> singleton-value("null")
            ConSingleton(repr=DataAsMaybe) -> singleton-value("null")
            ConSingleton(repr=DataAsList) -> singleton-value("null")
            // tagless
            ConIso -> gen-constr(c, crepr, cname, args, [])
            ConSingle -> gen-constr(c, crepr, cname, args, [])
            ConAsCons -> gen-constr(c, crepr, cname, args, [])
            ConAsJust -> gen-constr(c, crepr, cname, args, [])
            ConStruct(repr=DataStructAsMaybe) -> gen-constr(c, crepr, cname, args, [])
            // normal with tag
            _ -> gen-constr(c, crepr, cname, args, [(tag-field, get-con-tag(js-module, c, crepr))])
        pp-vis(decl)
      (info.name.unqualify.show.text |+| pprint/empty).linecomment("type ".text |.| _) |-| docs.vcat |-| "".text

fun linecomment(d: doc, wrap: (doc) -> doc = fn(x) x): doc
  "//".text |+| wrap(d)

fun gen-constr(c: con-info, crepr: con-repr, nameDoc: doc, args: list<doc>, tagFields: list<(doc, doc)>): asm-eff doc
  val lazyFields = if c.mblazy.is-just then [("_kk_lazy_blocked".text, "false".text)] else []
  if args.is-empty then
    constdecl |+| nameDoc |+| "=".text |+| object(tagFields ++ lazyFields) |.| semi |+| c.typeScheme.ktp/pretty.linecomment
  else
    "function".text |+| nameDoc |.| args.tupled |+| c.typeScheme.ktp/pretty.comment |+|
      block("return".text |+|
        (if c.name == nameOptional || crepr.is-conIso then args.head.unjust
         else object(tagFields ++ lazyFields ++ args.map(fn(a) (a, a)))) |.| semi)

fun get-con-tag(modName: name, coninfo: con-info, crepr: con-repr): _ doc
  match crepr
    ConOpen ->
      val nm = coninfo.name.to-open-tag-name
      js/pp-name(if nm.qualifier == modName then nm.unqualify else nm)
    _ -> crepr.tag.show.text

//--------------------------------------------------------------------------
// Statements
//--------------------------------------------------------------------------

// Applies a return context
fun get-result(res: result, doc: doc): doc
  if doc.is-empty then "".text
  else get-result-x(res, doc, doc)

fun get-result-x(res: result, puredoc: doc, retdoc: doc): doc
  match res
    ResultReturn -> "return".text |+| retdoc |.| semi
    ResultAssign(n, ml) -> gen-assign-result(n, ml, puredoc, retdoc)

fun gen-assign-result(n: name, ml: maybe<name>, puredoc: doc, retdoc: doc): doc
  val assign =
    if n.is-wildcard then (if puredoc.is-empty then puredoc else puredoc |.| semi)
    else "var".text |+| n.unqualify.js/pp-name |+| "=".text |+| retdoc |.| semi
  val brkDoc = match ml
    Nothing -> pprint/empty
    Just(l) -> "break".text |+| l.js/pp-name |.| semi
  vcat([assign, brkDoc])

fun try-tail-call(res: result, ex: expr): asm-eff maybe<doc>
  fun matches(n: tName, info: var-info, args: list<expr>): bool
    match res
      ResultReturn(Just(m)) -> m == n.get-name && info.arity == args.length
      _ -> False
  match ex
    App(Var(n, info), args) | matches(n, info, args) ->
      match res
        ResultReturn(_, params) -> Just(block(gen-override(params, args) |-| tailcall))
        _ -> Nothing
    App(TypeApp(Var(n, info)), args) | matches(n, info, args) ->
      match res
        ResultReturn(_, params) -> Just(block(gen-override(params, args) |-| tailcall))
        _ -> Nothing
    _ -> Nothing

// overriding function arguments carefully
fun gen-override(params: list<tName>, args: list<expr>): asm-eff doc
  val (stmts, varNames) = args.map(tail-call-arg).map(gen-var-binding).unzip
  val docs1 = params.map(gen-tname)
  val docs2 = varNames.map(gen-tname)
  val assigns = docs1.zip(docs2).map fn((p, a))
    if p.show == a.show then pprint/empty
    else p |+| "=".text |+| a |.| semi
  ("tail call".text).linecomment |-| stmts.vcat |-| assigns.vcat

// if local variables are captured inside a tailcalling function argument,
// we need to capture them by value (we will overwrite the locals on a tailcall):
// wrap the argument inside another function application.
fun tail-call-arg(ex: expr): asm-eff expr
  val captured = ex.captured-var.list.filter(fn(tn) !tn.get-name.is-qualified)
  if captured.is-empty then ex
  else
    val cnames = captured.map(fn(TName(cn, tp)) TName(new-var-name(cn.show), tp))
    val sub = captured.zip(cnames.map(fn(cn) Var(cn, InfoNone)))
    App(Lam(cnames, typeTotal, sub |-> ex), captured.map(fn(arg) Var(arg, InfoNone)))

fun captured-var(ex: expr): div rbset<tName>
  match ex
    Lam -> ex.free-vars // we only care about captures inside a lambda
    Let(bgs, body) -> Cons(body.captured-var, bgs.map(captured-def-group)).unions
    Case(es, bs) -> (es.map(captured-var) ++ bs.map(captured-branch)).unions
    App(f, args) -> Cons(f.captured-var, args.map(captured-var)).unions
    TypeLam(_, e) -> e.captured-var
    TypeApp(e) -> e.captured-var
    _ -> tnames/empty

fun captured-def-group(bg: def-group): div rbset<tName>
  match bg
    DefRec(defs) -> defs.map(fn(d) d.defExpr.captured-var).unions - defs.map(dg/bound-vars-def).unions
    DefNonRec(def) -> def.defExpr.captured-var

fun dg/bound-vars-def(d: def): rbset<tName>
  tnames/empty + TName(d.def-name, d.ktype)

fun captured-branch(Branch(pat, grds): branch): div rbset<tName>
  grds.map(fn(Guard(test, e)) test.captured-var.union(e.captured-var)).unions - pat.map(pat/bound-vars).unions

// Generates a statement from an expression by applying a return context (deeply) inside
fun gen-stat(res: result, ex: expr): asm-eff doc
  match try-tail-call(res, ex)
    Just(doc) -> doc
    Nothing -> gen-expr-stat(res, ex)

fun gen-expr-stat(res: result, ex: expr): asm-eff doc
  if ex.is-inlineable-expr then
    get-result(res, gen-inline(ex))
  else match ex
    Case(exprs, branches) ->
      fun scrut-of(e: expr)
        if e.is-inlineable-expr && e.type-of.is-type-bool then ("".text, gen-inline(e))
        else
          val (sd, vn) = gen-var-binding(e)
          (sd, gen-tname(vn))
      val (docs, scrutinees) = exprs.map(scrut-of).unzip
      docs.vcat |-| gen-match(res, scrutinees, branches)
    Let(groups, body) ->
      gen-groups(False, groups) |-| gen-stat(res, body)
    _ ->
      val (statDoc, exprDoc) = gen-expr(ex)
      statDoc |-| get-result(res, exprDoc)

// Generates a statement for a match expression regarding a given return context
fun gen-match(res: result, scrutinees: list<doc>, branches: list<branch>): asm-eff doc
  match branches
    [] -> failure/fail("backend/js/from-core gen-match: no branch in match statement")
    [b] -> gen-branch(True, res, scrutinees, b).snd
    // Special handling of return related cases
    [Branch([p1], [Guard(t1, App(Var(tn), [r1]))]), Branch([p2], [Guard(t2, e2)])]
        | tn.get-name == nameReturn && is-pat(True, p1) && is-pat(False, p2) && t1.is-true && t2.is-true ->
      val scrut = scrutinees.head.unjust
      match e2
        App(Var(tn2), [r2]) | tn2.get-name == nameReturn ->
          val (stmts1, expr1) = gen-expr(r1)
          val (stmts2, expr2) = gen-expr(r2)
          "if".text |.| scrut.parens |+| block(stmts1 |-| "return".text |+| expr1 |.| semi) |-|
            "else".text |+| block(stmts2 |-| "return".text |+| expr2 |.| semi)
        _ ->
          val (stmts1, expr1) = gen-expr(r1)
          val (stmts2, expr2) = gen-expr(e2)
          ("if".text |.| scrut.parens |+| block(stmts1 |-| "return".text |+| expr1 |.| semi)) |--|
            (stmts2 |-| get-result-x(res, if e2.is-unit-con then "".text else expr2, expr2))
    [Branch([p1], [Guard(t1, e1)]), Branch([p2], [Guard(t2, e2)])]
        | t1.is-true && t2.is-true && e1.is-inlineable-expr && e2.is-inlineable-expr ->
      val nameDoc = scrutinees.head.unjust
      val test = gen-test(js-module, nameDoc, p1)
      if e1.is-true && e2.is-false then get-result(res, test.conjunction.parens)
      else
        val doc1 =
          with override val subst-env = get-substitutions(nameDoc, p1) ++ subst-env
          gen-inline(e1)
        val doc2 =
          with override val subst-env = get-substitutions(nameDoc, p2) ++ subst-env
          gen-inline(e2)
        get-result(res, test.conjunction.parens |+| "?".text |+| doc1 |+| ":".text |+| doc2)
    bs | bs.all(fn(b) b.guards.length == 1) && bs.all(fn(b) b.guards.all(fn(g) g.test.is-true)) ->
      val xs = bs.map fn(b)
        with override val in-statement = True
        gen-branch(True, res, scrutinees, b)
      match xs.reverse
        Cons(lastX, initRev) ->
          fun pp-alt((conds: list<doc>, d: doc))
            "if".text |+| conds.conjunction.parens |+| block(d) |-| "else ".text
          initRev.reverse.map(pp-alt).hcat |.| block(lastX.snd)
        Nil -> failure/fail("backend/js/from-core gen-match: no branches")
    _ ->
      val matchLabel = ("match" ++ unique-id("match").show).new-name // unique so nested match labels don't collide (illegal in JS)
      val (mbLabel, res') = match res
        ResultReturn -> (Nothing, res)
        ResultAssign(_, Just(_)) -> (Nothing, res) // wohoo, we can jump out from deep in!
        ResultAssign(n, Nothing) -> (Just(matchLabel), ResultAssign(n, Just(matchLabel)))
      match branches.reverse
        Cons(lastB, initRev) ->
          val bs = initRev.reverse.map fn(b)
            with override val in-statement = True
            gen-branch(False, res', scrutinees, b)
          val b =
            with override val in-statement = True
            gen-branch(True, res', scrutinees, lastB)
          val ds = bs.map fn((cds, stmts))
            if cds.is-empty then stmts
            else "if".text |+| cds.conjunction.parens |+| block(stmts)
          val full = ds.vcat |-| b.snd
          match mbLabel
            Just(l) -> l.js/pp-name |.| ": ".text |.| block(full)
            Nothing -> full
        Nil -> failure/fail("backend/js/from-core gen-match: no branches")

// Generates a statement for a branch with given return context
fun gen-branch(lastBranch: bool, res: result, tnDocs: list<doc>, Branch(patterns, guards): branch): asm-eff (list<doc>, doc)
  val substs = tnDocs.zip(patterns).map(fn((d, p)) get-substitutions(d, p)).concat
  val conditions = tnDocs.zip(patterns).map(fn((d, p)) gen-test(js-module, d, p)).concat
  match guards.reverse
    Cons(lastG, initRev) ->
      val gs = initRev.reverse.map fn(g)
        with override val subst-env = substs ++ subst-env
        gen-guard(False, res, g)
      val g =
        with override val subst-env = substs ++ subst-env
        gen-guard(lastBranch, res, lastG)
      (conditions, gs.vcat |-| g)
    Nil -> failure/fail("backend/js/from-core gen-branch: no guards")

fun get-substitutions(nameDoc: doc, pat: pattern): pure list<(tName, doc)>
  match pat
    PatCon(tn, args, repr, _, _, _, info) ->
      fun sub-of((pat': pattern, fname: doc))
        val fdoc = if tn.get-name == nameOptional || repr.is-conIso then pprint/empty else dot |.| fname
        get-substitutions(nameDoc |.| fdoc, pat'.pretend-decreasing)
      args.zip(info.params.map(fn((nm, _)) nm.js/pp-name)).map(sub-of).concat
    PatVar(tn, pat') -> Cons((tn, nameDoc), get-substitutions(nameDoc, pat'))
    PatWild -> []
    PatLit -> []

fun gen-guard(lastBranchLastGuard: bool, res: result, Guard(t, ex): guard): asm-eff doc
  val (testSt, testE) = gen-expr(t)
  val res' = match res
    ResultAssign(n, _) | lastBranchLastGuard -> ResultAssign(n, Nothing)
    _ -> res
  val exprSt = gen-stat(res', ex)
  if t.is-true then exprSt
  else testSt |-| "if".text |+| testE.parens |.| block(exprSt)

// Generates a list of boolish expressions for matching the pattern
fun gen-test(modName: name, scrutinee: doc, pat: pattern): pure list<doc>
  match pat
    PatWild -> []
    PatVar(_, p) -> gen-test(modName, scrutinee, p)
    PatLit(lit) -> [scrutinee |+| "===".text |+| lit.pp-lit]
    PatCon(tn, fields, repr, _, _, _, info) ->
      fun field-tests-with(scrutf: (doc) -> pure doc)
        fun test-of((field: pattern, fname: doc))
          gen-test(modName, scrutf(fname), field.pretend-decreasing)
        fields.zip(info.params.map(fn((nm, _)) nm.js/pp-name)).map(test-of).concat
      fun field-tests()
        field-tests-with(fn(fname) scrutinee |.| dot |.| fname)
      if tn.get-name == nameTrue then [scrutinee]
      elif tn.get-name == nameFalse then ["!".text |.| scrutinee]
      else match repr
        ConEnum(tag=tag) -> [scrutinee |+| "===".text |+| tag.show.text]
        ConSingleton | tn.get-name == nameOptionalNone -> [scrutinee |+| "=== undefined".text]
        ConSingleton(repr=DataStructAsMaybe) -> [scrutinee |+| "=== null".text]
        ConSingleton(repr=DataAsMaybe) -> [scrutinee |+| "=== null".text]
        ConSingleton(repr=DataAsList) -> [scrutinee |+| "=== null".text]
        ConSingleton(tag=tag) -> [scrutinee |.| dot |.| tag-field |+| "===".text |+| tag.show.text]
        ConSingle -> field-tests() // always succeeds, but need to test the fields
        ConIso -> field-tests-with(fn(_) scrutinee) // always succeeds, but need to test the fields
        ConStruct(repr=DataStructAsMaybe) ->
          if tn.get-name == nameOptional then Cons(scrutinee |+| "!== undefined".text, fields.map(fn(f) gen-test(modName, scrutinee, f)).concat)
          else Cons(scrutinee |+| "!== null".text, field-tests())
        ConAsJust ->
          if tn.get-name == nameOptional then Cons(scrutinee |+| "!== undefined".text, fields.map(fn(f) gen-test(modName, scrutinee, f)).concat)
          else Cons(scrutinee |+| "!== null".text, field-tests())
        ConAsCons -> Cons(scrutinee |+| "!== null".text, field-tests())
        _ -> Cons(scrutinee |.| dot |.| tag-field |+| "===".text |+| get-con-tag(modName, info, repr), field-tests())

// Takes a list of docs and concatenates them with logical and
fun conjunction(docs: list<doc>): doc
  match docs
    Nil -> "true".text
    _ -> docs.punctuate(" && ".text).hcat

//--------------------------------------------------------------------------
// Expressions that produce statements on their way
//--------------------------------------------------------------------------

// Generates javascript statements and a javascript expression from a core expression
fun gen-expr(ex: expr): asm-eff (doc, doc)
  if ex.is-inlineable-expr then (pprint/empty, gen-inline(ex))
  else match ex
    TypeApp(e) -> gen-expr(e)
    TypeLam(_, e) -> gen-expr(e)
    // handle not inlineable cases
    App(TypeApp(Con(name, repr)), [arg]) | name.get-name == nameOptional || repr.is-conIso -> gen-expr(arg)
    App(Con(_, repr), [arg]) | repr.is-conIso -> gen-expr(arg)
    App(Var(tname), [ELit(LitInt(i))]) | tname.get-name == nameByte && i >= 0 && i < 256 ->
      (pprint/empty, i.show.text)
    App(Var(tname), [ELit(LitInt(i))]) | [nameInt32, nameSSizeT, nameInternalInt32, nameInternalSSizeT].any(fn(nm) nm == tname.get-name) && i.is-small-int32 ->
      (pprint/empty, i.show.text)
    App(Var(tname), [ELit(LitInt(i))]) | [nameInt64, nameIntPtrT].any(fn(nm) nm == tname.get-name) && i.is-small-int64 ->
      (pprint/empty, i.show.text |.| "n".text)
    // special: .cctx-field-addr-of: create a tuple with the object and the field name as a string
    App(TypeApp(Var(cfieldOf), [_]), [Var(conName), ELit(LitString(_)), ELit(LitString(fieldName))]) | cfieldOf.get-name == nameFieldAddrOf ->
      val conDoc = gen-tname(conName)
      (pprint/empty, "{obj:".text |+| conDoc |.| ", field_name: \"".text |.| fieldName.qualified/read.unqualify.js/pp-name |.| "\"}".text)
    App(f, args) ->
      match ex.extract-list
        Just((xs, tl)) -> gen-list(xs, tl)
        Nothing -> match f.extract-extern
          Just((tname, formats)) ->
            match args
              [ELit(LitInt(i))] | tname.get-name == nameByte && i >= 0 && i < 256 -> (pprint/empty, i.show.text)
              [ELit(LitInt(i))] | [nameInt32, nameSSizeT, nameInternalInt32, nameInternalSSizeT].any(fn(nm) nm == tname.get-name) && i.is-small-int32 -> (pprint/empty, i.show.text)
              [ELit(LitInt(i))] | [nameInt64, nameIntPtrT].any(fn(nm) nm == tname.get-name) && i.is-small-int64 -> (pprint/empty, i.show.text |.| "n".text)
              _ ->
                val (decls, argDocs) = gen-exprs(args)
                val (edecls, doc) = gen-expr-external(tname, formats, argDocs)
                if tname.get-name == nameReturn then ((decls ++ edecls ++ [doc |.| semi]).vcat, "".text)
                else ((decls ++ edecls).vcat, doc)
          Nothing ->
            val (decls, fdocs) = gen-exprs(Cons(f, args.trim-optional-args))
            match fdocs
              Cons(fdoc, docs) -> (decls.vcat, fdoc |.| docs.tupled)
              Nil -> failure/fail("backend/js/from-core gen-expr: app")
    Let(groups, body) ->
      val decls1 = gen-groups(False, groups)
      val (decls2, doc) = gen-expr(body)
      (decls1 |-| decls2, doc)
    Case ->
      val (doc, tname) = gen-var-binding(ex)
      (doc, gen-tname(tname))
    _ -> failure/fail("backend/js/from-core gen-expr: invalid expression")

fun is-small-int32(i: int): bool
  i >= -2147483648 && i <= 2147483647

fun is-small-int64(i: int): bool
  i >= -9223372036854775808 && i <= 9223372036854775807

fun extract-list(e: expr): _ maybe<(list<expr>, expr)>
  fun extract(acc: list<expr>, ex: expr): div (list<expr>, expr)
    match ex
      App(TypeApp(Con(name)), [hd, tl]) | name.get-name == nameCons -> extract(Cons(hd, acc), tl.pretend-decreasing)
      _ -> (acc.reverse, ex)
  val (elems, tl) = extract([], e)
  if elems.length > 10 then Just((elems, tl)) // only use inlined array for larger lists
  else Nothing

fun gen-list(elems: list<expr>, tl: expr): asm-eff (doc, doc)
  val (decls, docs) = gen-exprs(elems)
  val (tdecl, tdoc) = gen-expr(tl)
  ((decls ++ [tdecl]).vcat, "$std_core_vector.vlist".text |.| [docs.list, tdoc].tupled)

fun gen-exprs(exprs: list<expr>): asm-eff (list<doc>, list<doc>)
  exprs.map(gen-expr).unzip

// Introduces an additional let binding in core if necessary
// The expression in the result is guaranteed to be a Var afterwards
fun gen-var-binding(ex: expr): asm-eff (doc, tName)
  match ex
    Var(tn) -> (pprint/empty, tn)
    _ ->
      val name = new-var-name("x")
      val doc = gen-stat(ResultAssign(name, Nothing), ex)
      (doc, TName(name, ex.type-of))

//--------------------------------------------------------------------------
// Pure expressions
//--------------------------------------------------------------------------

fun gen-pure(ex: expr): asm-eff doc
  match ex
    TypeApp(e) -> gen-pure(e)
    TypeLam(_, e) -> gen-pure(e)
    Var(name, InfoExternal(format)) -> gen-wrap-external(name, format) // unapplied inlined external: wrap as function
    Var(name) -> gen-tname(name)
    Con(name) -> gen-tname(name)
    ELit(l) -> l.pp-lit
    Lam(params, _, body) ->
      val args = params.map(gen-comment-tname)
      val bodyDoc = gen-stat(ResultReturn(Nothing, params), body)
      "function".text |.| args.tupled |+| block(bodyDoc)
    _ -> failure/fail("backend/js/from-core gen-pure: invalid expression")

fun is-pat(b: bool, q: pattern): bool
  match q
    PatWild -> False
    PatLit -> False
    PatVar(_, q') -> is-pat(b, q')
    PatCon(tn) -> tn.get-name == (if b then nameTrue else nameFalse)

// Generates an effect-free javascript expression
// NOTE: throws an error if the expression is not guaranteed to be effect free
fun gen-inline(ex: expr): asm-eff doc
  if ex.is-pure-expr then gen-pure(ex)
  else match ex
    TypeLam(_, e) -> gen-inline(e)
    TypeApp(e) -> gen-inline(e)
    App(TypeApp(Con(name, repr)), [arg]) | name.get-name == nameOptional || repr.is-conIso -> gen-inline(arg)
    App(Con(_, repr), [arg]) | repr.is-conIso -> gen-inline(arg)
    App(f, args) ->
      val argDocs = args.trim-optional-args.map(gen-inline)
      match f.extract-extern
        Just((tname, formats)) ->
          match args
            [ELit(LitInt(i))] | [nameInt32, nameSSizeT, nameInternalInt32, nameInternalSSizeT].any(fn(nm) nm == tname.get-name) && i.is-small-int32 -> i.show.text
            [ELit(LitInt(i))] | [nameInt64, nameIntPtrT].any(fn(nm) nm == tname.get-name) && i.is-small-int64 -> i.show.text |.| "n".text
            _ -> gen-inline-external(tname, formats, argDocs)
        Nothing ->
          match (f, args)
            (Var(tname), [ELit(LitInt(i))]) | [nameInt32, nameSSizeT, nameInternalInt32, nameInternalSSizeT].any(fn(nm) nm == tname.get-name) && i.is-small-int32 -> i.show.text
            (Var(tname), [ELit(LitInt(i))]) | [nameInt64, nameIntPtrT].any(fn(nm) nm == tname.get-name) && i.is-small-int64 -> i.show.text |.| "n".text
            _ -> gen-inline(f) |.| argDocs.tupled
    _ -> failure/fail("backend/js/from-core gen-inline: invalid expression")

fun extract-extern(ex: expr): maybe<(tName, string)>
  match ex
    TypeApp(Var(tname, InfoExternal(format))) -> Just((tname, format))
    Var(tname, InfoExternal(format)) -> Just((tname, format))
    _ -> Nothing

// not fully applied external gets wrapped in a function
fun gen-wrap-external(tname: tName, format: string): asm-eff doc
  val n = tname.type-of.type-arities.snd
  val vs = gen-var-names(n)
  val (decls, doc) = gen-expr-external(tname, format, vs)
  ("function".text |.| vs.tupled |+| block((decls ++ ["return".text |+| doc |.| semi]).vcat)).parens

// inlined external sometimes needs wrapping in an applied function block
fun gen-inline-external(tname: tName, format: string, argDocs: list<doc>): asm-eff doc
  val (decls, doc) = gen-expr-external(tname, format, argDocs)
  if decls.is-empty then doc
  else (("function()".text |+| block((decls ++ ["return".text |+| doc |.| semi]).vcat)).parens |.| "()".text).parens

// generate external: adds a try block for primitives that can throw exceptions
fun gen-expr-external(tname: tName, format: string, argDocs0: list<doc>): asm-eff (list<doc>, doc)
  val (decls, doc) = gen-expr-external-prim(tname, format, argDocs0)
  match tname.type-of.split-fun-type
    Nothing -> (decls, doc)
    Just((_, eff, _)) ->
      val (ls, _) = eff.extract-ordered-effect
      match ls.filter(fn(l) l.label-name == nameTpPartial)
        [] -> (decls, doc)
        _ -> // has an exception type, wrap it in a try handler
          val tryDoc = (("function()".text |+| block(vcat([
              "try".text |+| block((decls ++ ["return".text |+| doc |.| semi]).vcat),
              "catch(_err){ return $std_core_exn._throw_exception(_err); }".text
            ]))).parens |.| "()".text).parens
          ([], tryDoc)

fun gen-expr-external-prim(tname: tName, format: string, argDocs0: list<doc>): asm-eff (list<doc>, doc)
  // special case: .cctx-hole-create
  if tname.get-name == nameCCtxHoleCreate && argDocs0.is-empty then ([], "undefined".text)
  else
    val argDocs = argDocs0.map fn(argDoc)
      if argDoc.as-string.list.all(fn(c) c.is-alpha-num || c == '_') then argDoc
      else argDoc.parens
    match format.lines.map(fn(fmt) pp-external-f(tname, fmt.list, argDocs))
      [] -> ([], pprint/empty)
      ds -> match ds.reverse
        Cons(lastD, initRev) -> (initRev.reverse, lastD)
        Nil -> ([], pprint/empty)

fun pp-external-f(tname: tName, k: list<char>, args: list<doc>): pure doc
  match k
    Nil -> pprint/empty
    Cons('\\', Cons('#', xs)) -> '#'.char |.| pp-external-f(tname, xs, args)
    Cons('#', Cons('#', _)) -> failure/fail("backend/js/from-core: type arguments in javascript external in: " ++ tname.get-name.show)
    Cons('#', Cons(y, xs)) ->
      if y >= '1' && y <= '9' then
        val i = y.char/int - '1'.char/int
        match args.drop(i)
          Cons(arg, _) -> arg |.| pp-external-f(tname, xs, args)
          Nil -> failure/fail("illegal index in external: " ++ tname.get-name.show)
      else y.char |.| pp-external-f(tname, xs, args)
    Cons(x, xs) -> x.char |.| pp-external-f(tname, xs, args)

fun gen-tname(tname: tName): asm-eff doc
  match subst-env.find(fn((tn, _)) tn == tname)
    Nothing -> gen-name(tname.get-name)
    Just((_, d)) -> d

fun gen-name(name: name): asm-eff doc
  if name.is-qualified then
    if name.qualifier == js-module then name.unqualify.js/pp-name
    else name.js/pp-name
  else name.js/pp-name

fun new-var-name(s: string): _ name
  ("@" ++ s ++ unique-id("x").show).new-name

fun gen-var-names(i: int): _ list<doc>
  list(1, i).map(fn(_) new-var-name("x").js/pp-name)

// Generate a name with its type in comments
fun gen-comment-tname(TName(n, t): tName): _ doc
  n.js/pp-name |+| t.ktp/pretty.comment

fun trim-optional-args(args: list<expr>): list<expr>
  fun is-optional-none(arg: expr): bool
    match arg
      TypeApp(Con(tname)) -> tname.get-name == nameOptionalNone
      _ -> False
  args.reverse.drop-while(is-optional-none).reverse

fun local-unique(f: () -> <unique|e> a): <unique|e> a
  val u = get-unique()
  val x = f()
  set-unique(u)
  x

//--------------------------------------------------------------------------
// Classification
//--------------------------------------------------------------------------

fun is-fun-expr(ex: expr): bool
  match ex
    TypeApp(e) -> e.is-fun-expr
    TypeLam(_, e) -> e.is-fun-expr
    Lam -> True
    _ -> False

fun is-inlineable-expr(ex: expr): bool
  match ex
    TypeApp(e) -> e.is-inlineable-expr
    TypeLam(_, e) -> e.is-inlineable-expr
    App(Var(_, InfoExternal), args) -> args.all(is-pure-expr)
    _ -> ex.is-pure-expr

fun is-pure-expr(ex: expr): bool
  match ex
    TypeApp(e) -> e.is-pure-expr
    TypeLam(_, e) -> e.is-pure-expr
    Var(_, InfoConField) -> False
    Var(n) -> n.get-name != nameReturn // make sure return will never be inlined
    Con -> True
    ELit -> True
    Lam -> True
    _ -> False

fun is-tail-calling(ex: expr, n: name): div bool
  match ex
    TypeApp(e) -> e.is-tail-calling(n) // trivial
    TypeLam(_, e) -> e.is-tail-calling(n) // trivial
    Lam -> False // lambda body is a new context, can't tailcall
    Var -> False // a variable is not a call
    Con -> False // a constructor is not a call
    ELit -> False // a literal is not a call
    App(Var(tn, info), args) | tn.get-name == n -> info.arity == args.length // direct application can be a tail call
    App(TypeApp(Var(tn, info)), args) | tn.get-name == n -> info.arity == args.length // may be applied to types first
    App(Var(tn), [e]) | tn.get-name == nameReturn -> e.is-tail-calling(n) // return is transparent for tail calls
    App -> False
    Let(_, e) -> e.is-tail-calling(n) // tail calls can only happen in the actual body
    Case(_, bs) -> bs.any(fn(Branch(_, gs)) gs.any(fn(Guard(_, e)) e.is-tail-calling(n)))

fun is-unit-con(ex: expr): bool
  match ex
    Con(tn) -> tn.get-name == nameUnit
    _ -> False

//--------------------------------------------------------------------------
// Pretty printing
//--------------------------------------------------------------------------

fun pp-lit(lit: lit): doc
  match lit
    LitInt(i) ->
      if i.is-small-int then i.show.text
      else nameIntConst.js/pp-name |.| (i.show.text |.| "n".text).parens
    LitChar(c) -> ("0x" ++ show-hex(c.list.head.default(' ').char/int, 4, pre="")).text
    LitFloat(d) -> std/num/float64/show(d).text
    LitString(s) -> s.list.map(escape).hcat.dquotes

fun escape(c: char): doc
  if c < ' ' then
    if c == '\n' then "\\n".text
    elif c == '\r' then "\\r".text
    elif c == '\t' then "\\t".text
    else ("\\u" ++ show-hex(c.char/int, 4, pre="")).text
  elif c <= '~' then
    if c == '"' then "\\\"".text
    elif c == '\'' then "\\'".text
    elif c == '\\' then "\\\\".text
    else c.char
  elif c.char/int <= 0xFFFF then ("\\u" ++ show-hex(c.char/int, 4, pre="")).text
  elif c.char/int > 0x10FFFF then "\\uFFFD".text // error instead?
  else
    val code = c.char/int - 0x10000
    val hi = (code / 0x0400) + 0xD800
    val lo = (code % 0x0400) + 0xDC00
    ("\\u" ++ show-hex(hi, 4, pre="") ++ "\\u" ++ show-hex(lo, 4, pre="")).text

fun is-small-int(i: int): bool
  i > -9007199254740991 && i < 9007199254740991 // 2^53 - 1

pub fun js/js/pp-name(name: name): doc
  if name.is-qualified then name.qualifier.pp-mod-name |.| dot |.| name.unqualify.encode(False)
  else name.encode(False)

pub fun pp-mod-name(name: name): doc
  "$".text |.| name.encode(True)

fun encode(name: name, isModule: bool): doc
  val s = name.show
  if s.is-reserved then ("$" ++ s).text
  else s.ascii-encode(isModule).text

fun is-reserved(s: string): bool
  match s.list
    // Vacuously True when `tail s` is empty,
    // so the bare identifier "T" (no digit suffix) is ALSO reserved -- the
    // check exists to avoid collision with backend-internal `T<n>`-style
    // type-variable names, and "T" itself is such a name with n omitted.
    Cons('T', rest) | rest.all(is-digit) -> True
    _ -> reserved-words.any(fn(w) w == s)

val reserved-words: list<string> = [
  // JavaScript pseudo-keywords
  "prototype", "toString", "arguments", "eval",
  // word literals
  "null", "Infinity", "NaN",
  // JavaScript keywords
  "async", "await", "break", "case", "catch", "continue", "const", "debugger", "default",
  "delete", "do", "else", "finally", "for", "function", "if", "in", "instanceof", "let",
  "new", "return", "switch", "this", "throw", "try", "typeof", "var", "void", "while",
  "with", "yield",
  // reserved for future use
  "class", "enum", "export", "extends", "import", "super",
  // special globals
  "window", "document", "process", "exports", "module", "Date", "Error" ]

fun block(doc: doc): doc
  "{".text |--| doc.tab |--| "}".text

fun tco-block(doc: doc): doc
  "{ tailcall: while(1)".text |-| "{".text |--| doc.tab |--| "}}".text

val tailcall: doc = "continue tailcall;".text

fun object(xs: list<(doc, doc)>): doc
  "{".text |+| xs.map(fn((d1, d2)) d1 |.| colon |+| d2).punctuate(comma |.| space).hcat |+| "}".text

fun tab(doc: doc): doc
  doc.indent(2)

fun type-comment(d: doc): doc
  d.comment

fun comment(d: doc): doc
  "/*".text |+| d |+| "*/ ".text

val tag-field: doc = "_tag".text

val constdecl: doc = "const".text
