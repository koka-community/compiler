import compiler/common/name
import compiler/common/color-scheme
import compiler/common/syntax
import compiler/common/nice
import compiler/common/name-collections
import compiler/lib/pprint
import compiler/core/core
import compiler/kind/kind
import compiler/kind/pretty
import compiler/kind/synonyms
import compiler/kind/importmap
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/platform/config
import std/data/linearmap
import std/num/float64

// Show pretty names rather than numbers

val pretty-names = True

fun source(d: doc)
  d.color(colors.colorSource)

// TODO: Show instances


// Pretty printers

  // val showKinds: bool
  // val showIds: bool // show id numbers
  // val expandSynonyms: bool
  // val ranked: tvScheme
  // val moduleContext: name // module in which we pretty print
  // val importsMap: importmap // import aliases
  // val fullNames: bool

fun set-env(env: ppEnv, f: () -> <ppEnvEff|e> a): <ppEnvEff|e> a
  with override val ppEnv = env
  f()

fun no-vis(f)
  set-env(ppEnv(coreShowVis=False), f)

fun no-vis-show-def(f)
  set-env(ppEnv(coreShowVis=False, coreShowDef=True),f)

fun pretty-core(target: target, inlineDefs: list<inlineDef>, c as Core(name, imports, fixDefs, typeDefGroups, defGroups, externals, doc): core)
  val importedSyns = c.extract-imported-synonyms()
  val extraImports = extract-imports-from-synonyms(imports, importedSyns)
  val allDefs = defGroups.flatten
  val allTypeDefs = typeDefGroups.flatten
  fun separator(msg)
    if !ppEnv.coreIface then [] else [" ".text, "//----------------------".text, ("//#kki: " ++ msg).text, " ".text]
  with override
    val importsMap = importsMap.extend-import-map(extraImports)
    val ranked = ranked
    val moduleContext = moduleContext
  val p0 = ppEnv
  with override
    val ppEnv = p0(showKinds = p0.showKinds || p0.coreIface, coreShowDef = !p0.coreIface, coreShowTypes = p0.coreIface || p0.coreShowTypes)
  val p = ppEnv(expandSynonyms = False)
  val px = ppEnv(showKinds = False, expandSynonyms = True)
  val coreDoc = "module".keyword |+| (if ppEnv.coreIface then "interface".text else empty) |.|
    name.pretty-def-name |-|
    vcat([
      "import declarations".separator,
      set-env(px, {imports.map(pretty-import)}),
      "external imports".separator,
      set-env(px, {externals.map(fn(e) e.pretty-external-import(target))}),
      "fixity declarations".separator,
      set-env(px, {fixDefs.map(pretty-fix-def)}),
      "local imported aliases".separator,
      set-env(px, {importedSyns.map(pretty-imported-syn)}),
      "type declarations".separator,
      set-env(px, {allTypeDefs.map(pretty-typedef)}),
      "declarations".separator,
      set-env(p, {allDefs.map(pretty-def)}), // TODO: is this and the next env wrong?
      "external declarations".separator,
      set-env(p, {externals.map(pretty-external)}),
      "inline definitions".separator,
      (
        if !ppEnv.coreIface || inlineDefs.is-nil then [] 
        else 
          ["//.inline-section".text] ++ inlineDefs.map(pretty-inline-def)
      ) 
    ].concat)
  coreDoc.pretty-comment(doc)

fun pretty-import(Kimport(name, pkg, vis, _): kimport)
  pretty-vis(vis, "import".keyword |+| get-alias(importsMap, name).pretty |+| "=".text |+|
    name.pretty-name |+| "=".text |+| LitString(pkg).pretty-lit |.| semi
    )

fun pretty-external-import(e: external, t: target)
  match e
    External -> pprint/empty
    ExternalImport(imports) ->
      match lookup-target(t, imports)
        Nothing -> pprint/empty
        Just(kvals0) ->
          fun prettyKeyval((k, v))
            LitString(k).pretty-lit |.| "=".text |.| LitString(v).pretty-lit |.| semi
          match kvals0.filter(fn((key, _)) key != "include-inline" && key != "header-include-inline")
            [] -> pprint/empty
            keyvals ->
              "extern import".keyword |+| "{".text |-|
                tab(t.pp-target |+| "{".text |-| tab(keyvals.map(prettyKeyval).vcat) |-| "};".text) |-| "};".text
  
fun pretty-fix-def(FixDef(nm, fixity): fixDef)
  val d = match fixity
    FixInfix(f, assoc) ->
      val adoc = match assoc
        AssocLeft -> "infixl".text
        AssocRight -> "infixr".text
        AssocNone -> "infix".text 
      adoc |+| f.pretty
    FixPrefix -> "prefix".text
    FixPostfix -> "postfix".text
  d |+| nm.pretty-def-name |.| semi

fun pretty-imported-syn(si: synInfo)
  si.pp-syn-info(True, False, True) |.| semi

fun pretty-external(ex: external)
  match ex
    ExternalImport -> pprint/empty
    External(name, tp, pinfos, body, vis, _, _, doc) ->
      if ppEnv.coreIface && name.is-hidden-external-name then pprint/empty
      else
        // TODO:
        fun prettyEntry((t:target, c: string))
          t.pp-target |.| "inline".keyword |+| LitString(c).pretty-lit |.| semi
        val entriesDoc = match body
          [(DefaultTarget, content)] -> "= inline".keyword |+| LitString(content).pretty-lit |.| semi
          _ -> "{".text |-| tab(body.map(prettyEntry).vcat) |-| "};".text
        val d = "extern".keyword |+| name.pretty-def-name |+| ":".text |+| tp.pretty-def-fun-type(pinfos) |+| entriesDoc
        pretty-vis(vis, d).pretty-comment(doc)

fun pp-target(t: target)
  match t
    DefaultTarget -> pprint/empty
    CS -> "cs ".text
    JS -> "js ".text
    C -> "c ".text

fun pretty-typedef-group(tdg: typeDefGroup)
  vcat(tdg.map(pretty-typedef))

fun pretty-typedef(td: typeDef)
  match td
    Synonym(synInfo) -> synInfo.pp-syn-info(False, True, True) |.| semi
    Data(dataInfo, isExtend) -> dataInfo.pretty-data-info(True, False, isExtend) |.| semi 

fun pretty-defgroup(dg: defGroup)
  match dg
    DefNonRec(d) -> d.pretty-defX(False)
    DefRec(ds) -> "rec {".text |+| align(ds.pretty-defs) / "}".text

fun pretty-defs(defs: list<def>)
  defs.map(pretty-def).vcat

fun pretty-inline-def(InlineDef(name, expr, isRec, inlkind, cost, sort, specArgs): inlineDef)
  val rdoc = if isRec then "recursive ".keyword else empty
  val prettySpecArgs = specArgs.map(fn(s) if s then '*' else '_').string.text.dquotes
  val specdoc = if specArgs.is-nil then pprint/empty else "specialize ".keyword |.| prettySpecArgs |.| " ".text 
  val inl = if cost <= 0 || inlkind.is-inlineAlways then "inline ".keyword else empty
  val pidoc = match sort
    DefFun(pinfos) -> if pinfos.any(fn(p) p.is-borrow) then "borrow".keyword |+| dquotes(pinfos.map(fn(i) if i.is-borrow then '^' else '_').string.text) |.| " ".text else empty
    _ -> empty
  val nm = if name.is-nil then "_".text else name.pretty-def-name
  rdoc |.| specdoc |.| inl |.| pidoc |.| sort.show-full.keyword |+|
    nm |+| ("// inline size: " ++ cost.show).text |.| linebreak |.|
    ("=".text |+| no-vis-show-def({expr.pretty-expr})).indent(2) |.| semi
  
fun pretty-def(d: def)
  d.pretty-defX(True)

fun pretty-defX(Def(name, scheme, expr, _, sort, _, _, doc): def, isRec: bool)
  val ppBody = no-vis({expr.pretty-expr})
  val d = sort.show-full.keyword |+| (if name.is-nil && ppEnv.coreShowDef then "_".text else name.pretty-def-name) |+|
    ":".text |+| (match sort {DefFun(pinfos) -> scheme.pretty-def-fun-type(pinfos); _ -> scheme.pretty-type}) |.|
    (if !ppEnv.coreShowDef then empty else linebreak |.| ("=".text |+| ppBody).indent(2) |.| semi)
  d.pretty-comment(doc)

fun pretty-vis(vis: visibility, d: doc)
  if !ppEnv.coreShowVis then d
  else
    match vis
      Public -> "pub".keyword |+| d
      Private -> d

fun pretty-type(tp: ktype)
  pretty-types([tp]).head.unjust

fun pretty-types(tps: list<ktype>)
  nice-types(tps)

fun pretty-kind(pre: string, k: kind)
  if k == kindStar then pprint/empty else pre.text |.| k.pp-kind(precTypeTop)

// Expressions
fun tab(d: doc)
  d.indent(2)

// Core lambda calculus
fun pretty-expr(ex: expr)
  match ex
    Lam(tnames, eff, expr) ->
      val doc = "fn".keyword |.| (if eff.is-type-total then empty else overridePrec(precTypeTop, {"<".text |.| eff.pretty-type |.| ">".text}).color(colors.colorType)) |.|
        overridePrec(precTypeTop, {tnames.map(pretty-tname).tupled}) |.| "{".text |--|
        tab(expr.pretty-expr |.| semi) |--| "}".text
      doc.pparens(prec, precTypeArrow)
    Var(tname) ->
      tname.pretty-var
    App(a, args) ->
      overridePrec(precTypeApp, {a.pretty-expr |.| args.map(fn(e) e.pretty-expr).tupled}).pparens(prec, precTypeApp)
    // Type abstraction / application
    TypeLam(tvs, expr) ->
      if pretty-names then
        tvs.foreach(extend-nice)
      val doc = overridePrec(precTypeTop, {"forall".text |.| tvs.map(fn(tv) tv.pretty-typeVar).angled |+| ".".text |+| expr.pretty-expr})
      doc.pparens(prec, precTypeArrow)
    TypeApp(expr, tps) ->
      if !ppEnv.coreShowTypes then expr.pretty-expr
      else
        val dtps = overridePrec(precTypeTop, {tps.map(fn(tp) tp.pretty-type)}).angled
        val de = overridePrec(precTypeApp - 1, {expr.pretty-expr})
        (de |.| dtps).pparens(prec, precTypeApp)
    // Literals and Contants
    Con(tname) -> tname.pretty-var
    ELit(l) -> l.pretty-lit
    Let([DefNonRec(Def(x, tp, e))], e') ->
      val exprDoc = e.pretty-expr |.| semi
      vcat([
        "val".keyword |+| ((if x.is-nil then "_".text else x.pretty-def-name) |+| tp.pretty-type |-| "=".text |+| exprDoc).hang(2),
        e'.pretty-expr
      ]) 
    Let(defgs, e) ->
      vcat([defgs.map(pretty-defgroup).vcat.align, e.pretty-expr])
    // Case expressions
    Case(exprs, branches) -> 
      val doc = "match".keyword |+| tupled(overridePrec(precTypeAtom, {exprs.map(fn(e) e.pretty-expr)})) |+| "{".text |--|
        tab(branches.pretty-branches) |--| "}".text
      doc.pparens(prec, precTypeTop) 

fun pretty-var(tn: tName)
  tn.get-name.pretty-name

// Case branches

fun pretty-branches(bs: list<branch>)
  bs.map(pretty-branch).vcat

fun pretty-branch(Branch(patts, guards): branch)
  val pats = overridePrec(precTypeApp, {pretty-patterns(patts)})
  hsep(pats.punctuate(comma)) |.| linebreak |.| indent(vcat(guards.map(pretty-guard)), 2) |.| semi 

fun pretty-guard(Guard(test, expr): guard)
  (if test.is-true then empty else " |".text |+| overridePrec(precTop, {test.pretty-expr})) |+|
  " ->".text |+| overridePrec(precTop, {expr.pretty-expr})

fun pretty-patterns(pats: list<pattern>)
  pats.map(pretty-pattern)

fun pretty-pattern-type(pat: pattern, tp: ktype)
  val doc = overridePrec(prec - 1, {pat.pretty-pattern})
  doc |.| (if ppEnv.coreShowTypes then " :".text |+| tp.pretty-type else empty)

fun pretty-con-name(tname: tName)
  tname.get-name.pretty

fun pretty-pattern(pat: pattern)
  match pat
    PatCon(tname, args, _, targs, exists0, resTp, _, skip) ->
      exists0.foreach(extend-nice)
      val docs = args.zip(targs).foldr([], fn((a, t), l) l ++ [a.pretty-pattern-type(t)])
      parens(
        (if skip then ".skip".keyword else empty) |.|
        tname.pretty-con-name |.| (if exists0.is-nil then empty else angled(exists0.map(pp-typevar))) |.|
        tupled(docs) |+| resTp.pretty-type |.| space
      )
    PatVar(tname, PatWild) -> 
      parens(tname.pretty-tname)
    PatVar(tname, pat) ->
      parens(overridePrec(prec - 1, {pat.pretty-pattern}) |+| "as".keyword |+| tname.pretty-tname)
    PatWild -> "_".text
    PatLit(l) -> pretty-lit(l)


// Literals
fun pretty-lit(l: lit)
  match l
    LitInt(i) -> i.show.text.color(colors.colorNumber)
    LitFloat(f) -> f.show.text.color(colors.colorNumber)
    LitChar(c) -> ("'" ++ show-xchar(c.head-char.unjust) ++ "'").text.color(colors.colorString)
    LitString(s) -> ("\"" ++ s.list.map(show-xchar).join ++ "\"").text.color(colors.colorString)

fun show-xchar(c: char): string
  if c >= ' ' && c <= '~' && c != '\"' && c != '\'' && c != '\\' then c.string
  else
    val n = c.int
    if n < 256 then "\\x" ++ n.show-hex(2)
    elif n < 65536 then "\\u" ++ n.show-hex(4)
    else "\\U" ++ n.show-hex(6)

// Pretty-printers for non-core terms

fun pretty-tname(TName(nm, t): tName)
  nm.pretty-name |.| ":".text |+| t.pp-type

fun pretty-name(n: name)
  if n.is-qualified then
    (n.nameModule ++ "/").text.color(colors.colorNameQual) |.| 
      n.unqualify.pretty.color(colors.colorSource)
  else n.pretty.color(colors.colorSource)

fun pretty-def-name(n: name)
  n.unqualify.pretty.color(colors.colorSource)

fun pp-operator-name(n: name)
  n.unqualify.pretty.color(colors.colorSource)

val pretty-typeVar = pp-typevar



// Extend an import map with nice aliases for a set of new imports
fun extend-import-map(im: importmap, imps: list<kimport>): importmap
  imps.foldr(im) fn(i, im')
    val fullName = i.importName
    match im'.extend(fullName, fullName)
      Just(new) -> new
      Nothing -> im'

// extract all qualifiers in synonyms: it can be the case that a type synonym
// refers to a type defined in a non-imported module and we need to add it to the
// imports of the .kki file. (no need to add it to the generated code since
// javascript does not use types, while c-sharp does not use import declarations but fully
// qualified names all the time)

fun extract-type(tp: ktype)
  match tp
    TSyn(syn, args, body) -> Cons(syn.name.qualifier, Cons(body,args).extract-types)
    TApp(c, args) -> Cons(c, args).extract-types
    TFun(args, eff, res) -> Cons(res, Cons(eff, args.map(snd))).extract-types
    TForAll(_, _, b) -> b.extract-type
    TCon(tc) -> [tc.name.qualifier]
    TVar -> []

fun extract-types(tps: list<ktype>)
  tps.map(extract-type).concat

fun extract-imports-from-synonyms(imps: list<kimport>, syns: list<synInfo>)
  val impNames = imps.map(importName)
  fun extractSyn(syn: synInfo)
    Cons(syn.name.qualifier, syn.t.extract-type)
  val quals = syns.map(extractSyn).concat.filter(fn(nm) !impNames.any(fn(n) n == nm))
  quals.map(fn(nm) Kimport(nm, "", Private, "")) // TODO: import path?

// extract from type signatures the synonyms so we can compress .kki files
// by locally defining imported synonyms
fun extract-synonym(tp: ktype): pure name-map<synInfo>
  match tp
    TSyn(syn, args, body) ->
      val syns = Cons(body, args).extract-synonyms
      match syn.info
        Just(i) -> syns.set(i.name, i)
        Nothing -> syns
    TApp(c, args) -> Cons(c, args).extract-synonyms
    TFun(args, eff, res) -> Cons(res, Cons(eff, args.map(snd))).extract-synonyms
    TForAll(_, _, b) -> b.extract-synonym
    _ -> synonyms/empty

fun extract-synonyms(tps: list<ktype>): pure name-map<synInfo>
  tps.map(extract-synonym).foldr(synonyms/empty, fn(s1, s2) s2.union(s1))

fun extract-imported-synonyms(c: core)
  c.extract-signatures.extract-synonyms.list.map(snd).filter(fn(i:synInfo) c.coreName != i.name.qualifier)
