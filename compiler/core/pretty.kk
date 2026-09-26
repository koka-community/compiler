// Updated as of 7/23/26: Commit 8315db4
module compiler/core/pretty

import std/core/unsafe
import std/core/debug
import std/os/env
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
import compiler/kind/import-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/platform/config
import std/num/float64
import std/core/undiv
import std/data/rb-map

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
  // val importsMap: import-map // import aliases
  // val fullNames: bool

fun set-env(env: pretty-env, f: () -> _ a): _ a
  with override val pp-env = env
  f()

fun no-vis(f)
  set-env(pp-env(coreShowVis=False), f)

fun no-vis-show-def(f)
  set-env(pp-env(coreShowVis=False, coreShowDef=True),f)

pub fun pretty-core(target: target, inlineDefs: list<inline-def>, c as Core(name, imports, fix-defs, typedef-groups, def-groups, externals, doc): core)
  val importedSyns = c.extract-imported-synonyms(inlineDefs)
  // declared once, omitted at every use site (see `pp-typecon`)
  // OFF by default -- it does not read back yet (kkc-check 43/53 decls, 19/43
  // inline sections). KOKA_LOCAL_KINDS=1 turns it on for investigation;
  // KOKA_KIND_TRACE=1 traces what is declared, parsed and looked up.
  val kindUses: list<(name, kind)> =
    if pp-env.coreIface && local-kinds-on() then c.extract-kind-uses(inlineDefs) else []
  val _kt = if kind-trace-on() && !kindUses.is-nil
              then trace("KIND emit " ++ c.coreName.show-plain ++ ": " ++ kindUses.length.show
                         ++ " decls [" ++ kindUses.take(4).map(fn((n,_)) n.show-plain).join(", ") ++ "]")
              else ()
  val extraImports = extract-imports-from-synonyms(imports, importedSyns)
  val allDefs = def-groups.flatten
  val allTypeDefs = typedef-groups.flatten
  fun separator(msg)
    if !pp-env.coreIface then [] else [" ".text, "//----------------------".text, ("//#kki: " ++ msg).text, " ".text]
  val importsMap' = importsMap.extend-import-map(extraImports)
  with override
    val importsMap = importsMap'
    val ranked = ranked
    val moduleContext = moduleContext
  val p0 = pp-env
  // ONCE per interface, not once per name
  val shortMods = if p0.coreIface then importsMap'.iface-short-modules else []
  with override
    val pp-env = p0(showKinds = p0.showKinds || p0.coreIface, coreShowDef = !p0.coreIface,
                    coreShowTypes = p0.coreIface || p0.coreShowTypes, shortModules = shortMods,
                    declaredKinds = kindUses.map(fst))
  val p = pp-env(expandSynonyms = False)
  val px = pp-env(showKinds = True, expandSynonyms = True) 
  val coreDoc = "module".keyword |+| (if pp-env.coreIface then "interface".text else empty) |+|
    name.pretty-core-name(colors) |-|
    vcat([
      "import declarations".separator,
      set-env(px, {imports.map(pretty-import)}),
      "external imports".separator,
      set-env(px, {externals.map(pretty-external-import)}),
      "fixity declarations".separator,
      set-env(px, {fix-defs.map(pretty-fix-def)}),
      // kinds MUST precede the aliases: an alias BODY mentions type
      // constructors whose `:: kind` annotation this section replaces, so the
      // table has to be populated before the alias section is parsed.
      "local kinds".separator,
      set-env(px, {kindUses.map(pp-kind-decl)}),
      "local imported aliases".separator,
      set-env(px, {importedSyns.map(pretty-imported-syn)}),
      "type declarations".separator,
      set-env(px, {allTypeDefs.map(pretty-typedef)}),
      "declarations".separator,
      // fresh nice scope PER TOP-DEF. Local defs
      // nested in a body deliberately SHARE their top-def's scope.
      set-env(p, {allDefs.map(fn(d) { with nice-env; d.pretty-def })}),
      "external declarations".separator,
      set-env(p, {externals.map(pretty-external)}),
      "inline definitions".separator,
      (
        if !pp-env.coreIface || inlineDefs.is-nil then [] 
        else 
          ["//.inline-section".text] ++ inlineDefs.map(fn(d) { with nice-env; d.pretty-inline-def })
      ) 
    ].concat)
  coreDoc.pretty-comment(doc)

fun pretty-import(imp: kimport)
  val name = imp.importName
  val provDoc = match imp.provenance
    ImportUser -> pprint/empty
    ImportPub -> " pub".keyword
    ImportTypes -> " type".keyword
    ImportCompiler -> " inline".keyword
  // module names have an empty stem: print via pretty-core-name, never the stem-appending pretty-name
  pretty-vis(imp.visibility, "import".keyword |+| get-alias(importsMap, name).pretty-core-name(colors) |+| "=".text |+|
    name.pretty-core-name(colors) |.| provDoc |+| "=".text |+| LitString(imp.package).pretty-lit |.| semi
    )

fun pretty-external-import(e: external)
  match e
    External -> pprint/empty
    ExternalImport(imports) ->
      fun prettyKeyval((k, v))
        LitString(k).pretty-lit |.| "=".text |.| LitString(v).pretty-lit |.| semi
      match imports.filter(fn((key, _)) key != "include-inline" && key != "header-include-inline")
        [] -> pprint/empty
        keyvals ->
          "extern import".keyword |+| "{".text |-|
            tab("{".text |-| tab(keyvals.map(prettyKeyval).vcat) |-| "};".text) |-| "};".text
  
fun pretty-fix-def(FixDef(nm, fixity): fix-def)
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

fun pretty-imported-syn(si: syn-info)
  si.pp-syn-info(True, False, True) |.| semi

fun pretty-external(ex: external)
  match ex
    ExternalImport -> pprint/empty
    External(name, tp, pinfos, body, vis, fip, nameRng, doc) ->
      if pp-env.coreIface && name.is-hidden-external-name then pprint/empty
      else
        val d = sep-by-space([fip.show, "extern"]).keyword |+| name.pretty-def-name |.| nameRng.pretty-range |+|
                ":".text |+| tp.pretty-def-fun-type(pinfos) |+|
                "= inline".keyword |+| LitString(body).pretty-lit |.| semi
        pretty-vis(vis, d).pretty-comment(doc)

fun pp-target(t: target)
  match t
    DefaultTarget -> pprint/empty
    CS -> "cs ".text
    JS -> "js ".text
    C -> "c ".text

fun pretty-typedef-group(tdg: typedef-group)
  vcat(tdg.map(pretty-typedef))

fun pretty-typedef(td: typedef)
  match td
    // An INTERFACE declares every synonym it mentions, private ones included.
    // Its `declarations` section prints private definitions and does not expand
    // synonyms, so a private alias can appear in a signature or inline body. A
    // consumer that LOADS the interface has to be able to expand it; otherwise
    // the C backend receives it as a nominal type that no header declares. A
    // module compiled in the same run has the alias in memory, so only
    // incremental builds depend on this.
    Synonym(syn-info) -> syn-info.pp-syn-info(False, !pp-env.coreIface, True) |.| semi
    Data(dataInfo) -> dataInfo.pretty-data-info(True, False) |.| semi 

fun pretty-defgroup(dg: def-group)
  match dg
    DefNonRec(d) -> d.pretty-defX(False)
    DefRec(ds) -> "rec {".text |+| align(ds.pretty-defs) / "}".text

fun pretty-defs(defs: list<def>)
  defs.map(pretty-def).vcat

fun pretty-inline-def(InlineDef(name, expr, isRec, inlkind, cost, sort, specArgs): inline-def)
  val rdoc = if isRec then "recursive ".keyword else empty
  val prettySpecArgs = specArgs.map(fn(s) if s then '*' else '_').string.text.dquotes
  val specdoc = if specArgs.is-nil then pprint/empty else "specialize ".keyword |.| prettySpecArgs |.| " ".text 
  val inl = if cost <= 0 || inlkind.is-inlineAlways then "inline ".keyword else empty
  val pidoc = match sort
    DefFun(pinfos) -> if pinfos.any(is-borrow) then "borrow".keyword |+| dquotes(pinfos.map(fn(i) if i.is-borrow then '^' else '_').string.text) |.| " ".text else empty
    _ -> empty
  val nm = if name.is-nil then "_".text else name.pretty-def-name
  rdoc |.| specdoc |.| inl |.| pidoc |.| sort.show-full.keyword |+|
    nm |+| ("// inline size: " ++ cost.show).text |.| linebreak |.|
    ("=".text |+| no-vis-show-def({expr.pretty-expr})).indent(2) |.| semi
  
fun pretty-def(d: def)
  d.pretty-defX(True)

fun pretty-defX(Def(name, scheme, expr, vis, sort, _, nameRng, doc): def, isRec: bool)
  val ppBody = no-vis({expr.pretty-expr})
  val d = pretty-vis(vis,
    sort.show-full.keyword |+| (if name.is-nil && pp-env.coreShowDef then "_".text else name.pretty-def-name) |.| nameRng.pretty-range |+|
    ":".text |+| (match sort {DefFun(pinfos) -> scheme.pretty-def-fun-type(pinfos); _ -> scheme.pretty-type}) |.|
    (if !pp-env.coreShowDef then empty else linebreak |.| ("=".text |+| ppBody).indent(2)) |.| semi)
  d.pretty-comment(doc)

fun pretty-vis(vis: visibility, d: doc)
  if !pp-env.coreShowVis then d
  else
    match vis
      Public -> "pub".keyword |+| d
      Private -> d

// Scope each call explicitly.
fun pretty-type(tp: ktype)
  with nice-scoped
  pretty-types([tp]).head.unjust

fun pretty-types(tps: list<ktype>)
  with nice-scoped
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
      val doc = "fn".keyword |.| (if eff.is-type-total then empty else override-prec(precTypeTop, {"<".text |.| eff.pretty-type |.| ">".text}).color(colors.colorType)) |.|
        override-prec(precTypeTop, {tnames.map(pretty-tname).tupled}) |.| "{".text |--|
        tab(expr.pretty-expr |.| semi) |--| "}".text
      doc.pparens(pp-prec, precTypeArrow)
    Var(tname) ->
      tname.pretty-var
    App(a, args) ->
      // callee at decPrec (one BELOW precApp), arguments at precApp.
      // Printing the callee at precTypeApp made a type-applied callee
      // self-parenthesize -- `(f<T>)(args)` -- which the core parser rejects.
      val de = override-prec(precTypeApp - 1, {a.pretty-expr})
      val dargs = override-prec(precTypeApp, {args.map(pretty-expr)}).tupled
      (de |.| dargs).pparens(pp-prec, precTypeApp)
    // Type abstraction / application
    TypeLam(tvs, expr) ->
      // upstream extends nice only for this forall's scope (env' is local)
      with nice-scoped
      if pretty-names then
        tvs.foreach(extend-nice)
      val doc = override-prec(precTypeTop, {"forall".text |.| tvs.map(pretty-type-var).angled |+| expr.pretty-expr})
      doc.pparens(pp-prec, precTypeArrow)
    TypeApp(expr, tps) ->
      if !pp-env.coreShowTypes then expr.pretty-expr
      else
        val dtps = override-prec(precTypeTop, {tps.map(pretty-type)}).angled
        val de = override-prec(precTypeApp - 1, {expr.pretty-expr})
        (de |.| dtps).pparens(pp-prec, precTypeApp)
    // Literals and Contants
    Con(tname, repr) ->
      // serialize the constructor-context path: it is stamped on this
      // occurrence's repr (not the constructor's global info), so without
      // this marker an interface round-trip would lose it and cross-module
      // inlined context code would copy garbage at runtime (koka-lang/koka#922)
      match (if pp-env.coreIface then repr.con-repr-ctx-path else Nothing)
        Just(CtxField(fld)) ->
          "@cpath".keyword |.| parens(pretty-lit(LitString(fld.get-name.show-tupled))) |+| tname.pretty-var
        _ -> tname.pretty-var
    ELit(l) -> l.pretty-lit
    Let([DefNonRec(Def(x, tp, e, _, _, _, nameRng))], e') ->
      val exprDoc = e.pretty-expr |.| semi
      vcat([
        // the RANGE is part of the interface grammar (a null range prints as [1,0,1,0]) and the core parser requires it
        "val".keyword |+| ((if x.is-nil then "_".text else x.pretty-def-name) |.| nameRng.pretty-range |+| ":".text |+| tp.pretty-type |-| "=".text |+| exprDoc).hang(2),
        e'.pretty-expr
      ])
    Let(defgs, e) ->
      vcat([defgs.map(pretty-defgroup).vcat.align, e.pretty-expr])
    // Case expressions
    Case(exprs, branches) -> 
      val doc = "match".keyword |+| tupled(override-prec(precTypeAtom, {exprs.map(pretty-expr)})) |+| "{".text |--|
        tab(branches.pretty-branches) |--| "}".text
      doc.pparens(pp-prec, precTypeTop) 

fun pretty-var(tn: tName)
  // in coreIface mode names print in the EXPLICIT /# form
  // (prettyCoreName), which is what marks a LOCAL qualifier apart from a
  // module path segment.
  if pp-env.coreIface then tn.get-name.pretty-core-name(colors)
  else tn.get-name.pretty-name

// Case branches

fun pretty-branches(bs: list<branch>)
  bs.map(pretty-branch).vcat

fun pretty-branch(Branch(patts, guards): branch)
  val pats = override-prec(precTypeApp, {pretty-patterns(patts)})
  hsep(pats.punctuate(comma)) |.| linebreak |.| indent(vcat(guards.map(pretty-guard)), 2) |.| semi 

fun pretty-guard(Guard(test, expr): guard)
  (if test.is-true then empty else " |".text |+| override-prec(precTop, {test.pretty-expr})) |+|
  " ->".text |+| override-prec(precTop, {expr.pretty-expr})

fun pretty-patterns(pats: list<pattern>)
  pats.map(pretty-pattern)

fun pretty-pattern-type(pat: pattern, tp: ktype)
  val doc = override-prec(pp-prec - 1, {pat.pretty-pattern})
  doc |.| (if pp-env.coreShowTypes then " :".text |+| tp.pretty-type else empty)

fun pretty-con-name(tname: tName)
  tname.get-name.pretty

// upstream threads its (functional) pretty env through the PatCon argument
// fold, and every printed sub-pattern DECREMENTS the precedence (`decPrec`:
// once per argument via `prettyPatternType`, plus once per nested
// non-wildcard sub-pattern); the result type is then printed with that
// threaded, lower precedence -- so `Cons(...) : list<int>` has no parens
// while `Nil() : (list<int>)` does. Count the decrements to replicate.
fun pat-prec-decs(p: pattern): int
  match p
    PatVar(_, PatWild) -> 0
    PatVar(_, p') -> 1 + p'.pat-prec-decs
    PatCon(_, args) -> args.foldl(0, fn(acc, a) acc + 1 + a.pretend-decreasing.pat-prec-decs)
    _ -> 0

fun pretty-pattern(pat: pattern)
  match pat
    PatCon(tname, args, _, targs, exists0, resTp, _, skip) ->
      exists0.foreach(extend-nice)
      val docs = args.zip(targs).foldr([], fn((a, t), l) Cons(a.pretty-pattern-type(t), l))
      val resPrec = pp-prec - pat.pat-prec-decs
      parens(
        (if skip then "@skip ".keyword else empty) |.|
        tname.pretty-con-name |.| (if exists0.is-nil then empty else angled(exists0.map(pp-typevar))) |.|
        tupled(docs) |+| ":".text |+| override-prec(resPrec, {resTp.pretty-type}) |.| space
      )
    PatVar(tname, PatWild) -> 
      parens(tname.pretty-tname)
    PatVar(tname, pat) ->
      parens(override-prec(pp-prec - 1, {pat.pretty-pattern}) |+| "as".keyword |+| tname.pretty-tname)
    PatWild -> "_".text
    PatLit(l) -> pretty-lit(l)


// Literals
fun pretty-lit(l: lit)
  match l
    LitInt(i) -> i.show.text.color(colors.colorNumber)
    // Force a decimal point so the printed literal always re-parses as a float.
    LitFloat(f) ->
      val s = f.show
      val hasMarker = s.list.any(fn(c) c == '.' || c == 'e' || c == 'E' || c == 'n' || c == 'N')
      val s2 = if hasMarker then s else s ++ ".0"
      s2.text.color(colors.colorNumber)
    LitChar(c) -> ("'" ++ show-xchar(c.head-char.unjust) ++ "'").text.color(colors.colorString)
    LitString(s) -> ("\"" ++ s.list.map(show-xchar).join ++ "\"").text.color(colors.colorString)

fun show-xchar(c: char): string
  if c >= ' ' && c <= '~' && c != '\"' && c != '\'' && c != '\\' then c.string
  else
    val n = c.int
    // NB pre="": std's show-hex defaults to a "0x" prefix, which glued onto
    // the escape as `\x0x5C` -- unreadable by our own lexer. Upstream's
    // Haskell showHex has no prefix.
    if n < 256 then "\\x" ++ n.show-hex(2, pre="")
    elif n < 65536 then "\\u" ++ n.show-hex(4, pre="")
    else "\\U" ++ n.show-hex(6, pre="")

// Pretty-printers for non-core terms

fun pretty-tname(TName(nm, t): tName)
  // Use pretty-core-name unconditionally (the /# form)
  nm.pretty-core-name(colors) |.| ":".text |+| t.pp-type

fun pretty-name(n: name)
  if n.is-qualified then
    (n.nameModule ++ "/").text.color(colors.colorNameQual) |.| 
      n.unqualify.pretty.color(colors.colorSource)
  else n.pretty.color(colors.colorSource)

fun pretty-def-name(n: name)
  n.unqualify.pretty.color(colors.colorSource)

fun pp-operator-name(n: name)
  n.unqualify.pretty.color(colors.colorSource)

val pretty-type-var = pp-typevar



// Extend an import map with nice aliases for a set of new imports
fun extend-import-map(im: import-map, imps: list<kimport>): import-map
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
    TForAll(_, b) -> b.extract-type
    TCon(tc) -> [tc.name.qualifier]
    TVar -> []

fun extract-types(tps: list<ktype>)
  tps.map(extract-type).concat

fun extract-imports-from-synonyms(imps: list<kimport>, syns: list<syn-info>)
  val impNames = imps.map(importName)
  fun extractSyn(syn: syn-info)
    Cons(syn.name.qualifier, syn.tp.extract-type)
  val quals = syns.map(extractSyn).concat.filter(fn(nm) !impNames.any(_ == nm))
  quals.map(Kimport(_, "", Private, "")) // TODO: import path?

// extract from type signatures the synonyms so we can compress .kki files
// by locally defining imported synonyms
fun extract-synonym(tp: ktype): _ name-map<syn-info>
  match tp
    TSyn(syn, args, body) ->
      val syns = Cons(body, args).extract-synonyms
      match syn.info
        Just(i) -> rb-map/set(syns, i.name, i)
        Nothing -> syns
    TApp(c, args) -> Cons(c, args).extract-synonyms
    TFun(args, eff, res) -> Cons(res, Cons(eff, args.map(snd))).extract-synonyms
    TForAll(_, b) -> b.extract-synonym
    _ -> synonyms/empty

fun extract-synonyms(tps: list<ktype>): _ name-map<syn-info>
  tps.map(extract-synonym).foldr(synonyms/empty, fn(s1, s2) s2.union(s1))

// Types mentioned anywhere in an expression, so the interface can declare the
// synonyms its INLINE SECTION uses and not just those in top-level signatures.
//
// The inline section is rendered from `inlineDefs`, which `pretty-core` receives
// SEPARATELY from the core and which `extract-signatures` therefore never saw:
// 33 synonyms (`std/core/hnd/ev-index` in 43 interfaces, and others) were used
// there and declared nowhere. Read back without a declaration they degrade to
// bare `TCon`s, which is what forced this port to seed the parser with synonyms
// from already-loaded dependencies -- and that seeding is what made interface
// loads ORDERED. The reference compiler has the same gap, but parses inline
// sections lazily, so it bites less there.
//
// NOTE: this is not a port of upstream -- `extractSignatures` has no expression
// traversal. It is the fix for a bug both compilers have.
fun expr/all-types(e: expr): _ list<ktype>
  match e
    Lam(names, eff, b)  -> Cons(eff, names.map(type-of)) ++ b.all-types
    Var(n)              -> [n.type-of]
    App(f, args)        -> f.all-types ++ args.flatmap(all-types)
    TypeLam(_, b)       -> b.all-types
    TypeApp(f, tps)     -> tps ++ f.all-types
    Con(n)              -> [n.type-of]
    ELit                -> []
    Let(dgs, b)         -> dgs.flatten.flatmap(fn(d) Cons(d.ktype, d.defExpr.all-types)) ++ b.all-types
    Case(exprs, brs)    -> exprs.flatmap(all-types) ++ brs.flatmap(branch/all-types)

fun branch/all-types(Branch(pats, guards): branch): _ list<ktype>
  pats.flatmap(pat/all-types) ++ guards.flatmap(fn(g) g.test.all-types ++ g.body.all-types)

fun pat/all-types(p: pattern): _ list<ktype>
  match p
    PatCon(nm, subs, _, targs, _, tres) -> Cons(nm.type-of, Cons(tres, targs)) ++ subs.flatmap(pat/all-types)
    PatVar(tn, sub) -> Cons(tn.type-of, sub.pat/all-types)
    _ -> []

// Every (type constructor, kind) pair a type mentions, with `kindStar` left out
// -- the reader already defaults to it, and the emitter never wrote it.
//
// A constructor's kind never varies, but it was re-spelled at EVERY occurrence:
// 6.48MB over 748,678 occurrences across the corpus, 13.8% of all interface
// bytes, from only 485 distinct pairs (median 18 per interface). `types/handled`
// alone appears 143,951 times. Declaring them once and omitting the annotation
// is the same trick the `local alias` section already plays for synonyms.
pub val local-kinds-flag : bool = unsafe-total{ get-env-value("KOKA_LOCAL_KINDS").is-just }
pub fun local-kinds-on(): bool
  local-kinds-flag
pub val kind-trace-flag : bool = unsafe-total{ get-env-value("KOKA_KIND_TRACE").is-just }
pub fun kind-trace-on(): bool
  kind-trace-flag

fun ktype/kind-uses(tp: ktype): _ list<(name, kind)>
  match tp
    TCon(TypeCon(nm, k))  -> if k == kindStar then [] else [(nm, k)]
    TSyn(ts, args, body)  -> (if ts.kind == kindStar then [] else [(ts.name, ts.kind)])
                               ++ args.flatmap(kind-uses) ++ body.kind-uses
    TApp(t, args)         -> t.kind-uses ++ args.flatmap(kind-uses)
    TFun(args, eff, res)  -> args.flatmap(fn(a) a.snd.kind-uses) ++ eff.kind-uses ++ res.kind-uses
    TForAll(_, t)         -> t.kind-uses
    TVar                  -> []

fun extract-kind-uses(c: core, inlineDefs: list<inline-def>): _ list<(name, kind)>
  val tps = c.extract-signatures ++ inlineDefs.flatmap(fn(d) d.expr.all-types)
  val all = tps.flatmap(kind-uses)
  // dedup by name; a constructor has ONE kind, so first wins
  all.foldl([]) fn(acc: list<(name, kind)>, (nm, k))
    if acc.any(fn((n2, _)) n2 == nm) then acc else acc ++ [(nm, k)]

fun extract-imported-synonyms(c: core, inlineDefs: list<inline-def> = [])
  val tps = c.extract-signatures ++ inlineDefs.flatmap(fn(d) d.expr.all-types)
  tps.extract-synonyms.list.map(snd).filter(fn(i:syn-info) c.coreName != i.name.qualifier)

// Render an expression / definition with the default pretty environment, for
// diagnostics raised outside a pretty-printing context
pub fun expr/doc-default(ex: expr): _ doc
  with default-pretty-env
  ex.pretty-expr

pub fun def/doc-default(d: def): _ doc
  with default-pretty-env
  d.pretty-def

pub fun pat/doc-default(pat: pattern): _ doc
  with default-pretty-env
  pat.pretty-pattern

fun default-pretty-env(action)
  with nice-env
  with default-doc-env
  with default-pp-env
  with val pp-prec = precTopTop
  with val indent = 0
  with handler
    val ranked = rankedDefault
    val moduleContext = "Main".new-name
    val importsMap = imports-empty
  action()

// Render a Core expression the way UPSTREAM's `show` does.
//
// `Core/Pretty.hs` defines `instance Show Expr where show = show . prettyExpr
// defaultEnv{showKinds=True,coreShowTypes=True}` -- upstream's `show` for Core
// types IS the pretty printer. This port keeps `show` as the structural dump
// (`Lam([n],...)`), which is the more useful of the two to have available, and
// spells out the pretty rendering at the sites whose output is meant to be
// READ -- above all `core/specialize`'s provenance comment, which is written
// into every interface that has a specialization.
//
// That one site is worth 34.5MB of 85.7MB of interface text (upstream's
// equivalent comments are 16.8MB), and interface text is what a warm build
// spends its time lexing.
pub fun expr/pretty-show(ex: expr): _ string
  // supply the colour scheme here rather than demanding it from the caller:
  // `show` is available in any context and this must be too. Rendering to a
  // plain string drops the colours anyway.
  with color-scheme-default
  with nice-env
  with default-doc-env
  with handler
    val pp-env = PrettyEnv(showKinds = True, coreShowTypes = True)
  with val pp-prec = precTopTop
  with val indent = 0
  with handler
    val ranked = rankedDefault
    val moduleContext = "Main".new-name
    val importsMap = imports-empty
  ex.pretty-expr.show

// Show a pattern with the default pretty environment (for warnings/messages)
pub fun pattern/show-default(pat: pattern): _ string
  with nice-env
  with default-doc-env
  with default-pp-env
  with val pp-prec = precTopTop
  with val indent = 0
  with handler
    val ranked = rankedDefault
    val moduleContext = "Main".new-name
    val importsMap = imports-empty
  pat.pretty-pattern.show
