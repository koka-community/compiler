module compiler/type/pretty

import compiler/common/id
import std/data/rb-map
import compiler/common/name-collections
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/nice
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/lib/pprint
import std/pretty/printer
import compiler/type/type
import compiler/type/typevar
import compiler/kind/import-map
import compiler/platform/config
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/pretty
import compiler/kind/synonyms
import std/data/rb-set
import std/data/sort
import std/core/undiv
// Updated 7/23/26 to commit #045e2dc, not fully visually second checked otherwise.

alias prec = int;
pub val precTopTop = -1 // most outer level: used to suppress 'forall'
pub val precTypeTop = 0
pub val precTypeQuant = 1
pub val precTypeArrow = 2
pub val precTypeApp = 3
pub val precTypeAtom = 4
pub val precPred = 5

pub alias tv-scheme = rbmap<type-var, (prec -> doc)>;

pub val rankedDefault:tv-scheme = rb-map/empty()

pub fun keyword(s: string)
  s.text.color(colors.colorTypeKeyword)

// Find a better place for this
// Contains link bases for documentation generation (see Syntax.Colorize)
effect documentation
  val colorizing: bool
  val htmlBases: list<(string, string)>
  val htmlCss: string
  val htmlJs: string

// find a better place for this
// Signifies whether we output core for an interface or not

pub fun default-doc-env(f)
  with handler
    val colorizing = False
    val htmlBases = []
    val htmlCss = "styles/" ++ comp-flags.programName ++ ".css"
    val htmlJs = "scripts/" ++ comp-flags.programName ++ "-highlight.js"
  f()

pub fun default-pp-env(f)
  with handler
    val pp-env = PrettyEnv()
  f()

// Pretty print environment for types

pub alias pretty-eff = <pp-type-eff,indent,documentation,colors,pure,nice-eff<type-var>,comp-flags>

pub alias pp-type-eff = <pretty-type-eff,pp-env,pp-prec>

pub effect val pp-prec: prec;

pub effect val pp-env: pretty-env;

pub type pretty-env
  PrettyEnv(
    showKinds: bool = False,
    showIds: bool = False, // show id numbers
    showFlavours: bool = True,
    expandSynonyms: bool = False,
    fullNames: bool = False, // TODO: If True it can lead to .kki parse errors
    coreIface: bool = False,
    coreShowTypes: bool = False, // show types in core output
    coreShowVis: bool = True, // show visibility
    coreShowDef: bool = False, // show definition body
    // module -> shortest suffix that still names it uniquely among the
    // interface's imports, computed ONCE per interface (`iface-short-modules`).
    shortModules: list<(string, name)> = [],
    // Type constructors whose kind this interface DECLARES once, in its
    // `local kind` section: their occurrences omit the `:: kind` annotation and
    // the reader recovers it from the declaration. 6.48MB of 46.8MB was these
    // annotations repeated at 748,678 use sites from 485 distinct pairs.
    declaredKinds: list<name> = []
  )

pub fun no-full-names(f)
  with handler
    val pp-env = pp-env(fullNames=False)
  f()

pub effect val indent : int

fun trace-indent(f)
  with override val indent = type/pretty/indent + 2
  f()

pub fun trace-doc(d: () -> _ doc): _ ()
  trace(d().indent(type/pretty/indent).show)

pub fun pp-name-type((name, tp): (name, ktype)): _ doc
  name.pp-name |+| colon |+| tp.pp-type

pub fun default-indent(f)
  with val indent = 0
  f()

pub effect pretty-type-eff
  val ranked: tv-scheme
  val moduleContext: name // module in which we pretty print
  val importsMap: import-map // import aliases

pub fun override-prec(p: prec, f)
  with override 
    val pp-prec = p
  f()

fun handle-pretty-eff(f)
  with val pp-prec = precTopTop
  with val indent = 0
  with handler 
    val ranked = rankedDefault
    val moduleContext = "Main".new-name
    val importsMap = imports-empty
  f()
 
pub fun type-colon()
  ":".text.color(colors.colorSep)

fun min-canonical(tp: ktype): _ string
  tp.minimal-form.show.compress

pub fun canonical(tp: ktype): _ string
  tp.canonical-form.show.compress

pub fun string/compress(s: string): string
  s.list.compress.string

pub fun list/compress(l: list<char>): list<char>
  match l
    Nil -> Nil
    Cons(c, cs) ->
      if c == '\n' then compress(cs.drop-while(is-space).pretend-decreasing)
      elif c.is-space then  Cons(' ', compress(cs.drop-while(is-space).pretend-decreasing))
      else Cons(c, compress(cs))

pub fun nice-type(tp: ktype)
  nice-types([tp]).head.unjust

pub fun nice-types(tps: list<ktype>): _ list<doc>
  tps.niceList fn(tp)
    tp.pp-type.color(colors.colorType)

fun niceList(schemes: list<ktype>, f: (ktype) -> _ doc): _ list<doc>
  // Set, i.e. sorted by type-var id -- nice names (a, b, ..., e, e1, ...) are assigned in tid
  // order, not traversal order.
  schemes.map(free-type-vars).unions.list
    .sort(?(<) = fn(tv1: type-var, tv2: type-var) tv1.tid < tv2.tid)
    .map(extend-nice)
  schemes.map(f)

// Pretty print a type
fun ktp/ppretty(t: ktype): _ doc
  with handle-pretty-eff
  with nice-env
  t.pp-type

// `nice-types` with the default environment installed, for diagnostics raised
// outside a pretty-printing context (upstream passes an explicit `Env`).
pub fun nice-types-default(tps: list<ktype>): _ list<doc>
  with default-pp-env
  with default-doc-env
  with handle-pretty-eff
  with nice-env
  with color-scheme-default
  tps.nice-types

// Run `action` with every pretty-printing environment installed locally, for
// callers outside the compiler's own pretty-printing context (the language
// server, diagnostics built at odd moments) that would otherwise have to
// assemble the handler stack themselves.
pub fun with-pretty-env(action)
  with default-pp-env
  with default-doc-env
  with handle-pretty-eff
  with nice-env
  with color-scheme-default
  action()

// A type rendered to a plain string with every pretty-printing environment
// installed locally, AND with nice type-variable names assigned.
//
// `pp-type` alone prints type variables by their raw id, because the readable
// `a`/`b`/`e` names come from `extend-nice` over the type's free variables --
// which only `nice-types`/`niceList` performs. Anything user-facing (hover,
// diagnostics) must go through that pass, so this does.
pub fun ktp/pretty-string(t: ktype): _ string
  match [t].nice-types-default
    Cons(d) -> d.pprint/show
    Nil -> ""    // unreachable: one type in, one doc out

pub fun ktp/pretty(t: ktype): _ doc
  with default-pp-env
  with default-doc-env
  with handle-pretty-eff
  with nice-env
  with color-scheme-default
  t.pp-type

fun tv/pretty(tv: type-var): _ doc
  with handle-pretty-eff
  with nice-env
  tv.pp-typevar

fun tcon/pretty(tc: type-con): _ doc
  with handle-pretty-eff
  with nice-env
  tc.pp-typecon

fun tsyn/pretty(ts: type-syn): _ doc
  with handle-pretty-eff
  with nice-env
  ts.pp-typesyn

fun pp-schema(tp: ktype)
  tp.nice-type

fun pp-schema-effect(tp: ktype)
  match tp
    TFun([], _) -> pp-schema-effect(TForAll([], tp))
    TForAll(vars, TFun([], eff, res)) ->
      vars.foreach(extend-nice)
      with override-prec(precTypeTop)
      val fors = if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(pp-typevar).angled |.| dot |.| space
      val effDoc = if eff.is-type-total then pprint/empty else override-prec(precArrow - 1, {eff.pp-type}) |.| space
      val resDoc = res.pp-type
      (fors |.| effDoc |.| resDoc).pparens(pp-prec, precTypeQuant)
    _ -> tp.nice-type

pub fun pretty-def-fun-type(tp: ktype, pinfos: list<param-info>)
  fun pp-param((nm:name, pinfo, tpDoc))
    val x = match pinfo
      Borrow -> "^".text |+| (if nm.is-nil then "_".text else nm.pp-name) |+| ": ".text
      _ -> if nm.is-nil then pprint/empty else nm.pp-name |+| ": ".text
    x |.| tpDoc
  match tp.pp-decl-type(pinfos)
    (Just(params), pre, post) ->
      pre |.| params.map(pp-param).comma-sep.parens |+| "->".text |+| post
    (Nothing, pre, post) -> pre |+| "()".text |+| "->".text |+| post

pub fun pp-decl-type(tp: ktype, pinfos: list<param-info>)
  match tp
    TForAll(vars, rho) ->
      vars.foreach(extend-nice)
      val (args, _, res) = rho.pp-decl-type(pinfos)
      val pre = if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(pp-typevar).angled |.| space
      (args, pre, res)
    TFun(params, eff, rho) ->
      // upstream zips `pinfos ++ repeat Own` -- hardcoding Own here lost the
      // Borrow annotations so `^` never printed in def signatures
      val pinfosPadded = pinfos ++ params.drop(pinfos.length).map(fn(_) Own)
      val pparams = params.zip(pinfosPadded).map(fn(((name, tp'), pinfo)) (name, pinfo, tp'.pp-type))
      val effDoc = if eff.is-type-total then pprint/empty else override-prec(precArrow, {eff.pp-type |.| space})
      (Just(pparams), pprint/empty, effDoc |.| override-prec(precArrow, {rho.pp-type}))
    _ -> (Nothing, pprint/empty, tp.pp-type)

fun data-info/pretty(d: data-info): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with nice-env
  pp-data-info(d, True)

fun pp-data-info(d: data-info, showBody: bool)
  d.pretty-data-info(showBody, False)

fun comma-sep(d: list<doc>)
  d.punctuate(comma).hsep

pub fun pretty-data-info(d: data-info, showBody: bool, publicOnly: bool)
  if publicOnly && d.vis.is-private then pprint/empty
  else
    val vis = if publicOnly then pprint/empty else d.vis.pp-vis
    d.params.foreach(extend-nice)
    val recur = if d.is-rec then "recursive ".keyword else "".text
    val ext = if d.is-extend then "extend ".keyword else match d.def
      DataDefOpen -> "open ".keyword
      DataDefValue(v) -> ("value" ++ v.show ++ " ").keyword
      DataDefLazy(fipT) -> (["lazy", fipT.show, " "].sep-by-space ++ " ").keyword
      _ -> pprint/empty 
    val eff = match d.deffect
      DataNoEffect -> pprint/empty
      DataEffect(is-named, is-linear) ->
        (if is-named then "named ".keyword else pprint/empty) |.|
        (if is-linear then "linear ".keyword else pprint/empty) |.| "effect ".keyword
    val sort = match d.sort
      Inductive -> "type".keyword
      CoInductive -> "co type".keyword
      Retractive -> "div type".keyword // this "div" means a retractive type or non-(co)inductive type
    val params = if d.params.is-nil then pprint/empty else space |.| d.params.map(TVar).nice-types.angled
    val kind = if d.kind == kindStar then pprint/empty else " ::".text |+| d.kind.pp-kind(precTop)
    val body = if showBody && d.constrs.is-cons then 
        "{".text |-| d.constrs.map(_.pretty-con-info(publicOnly)).vcat.indent(2) |-| "}".text 
      else pprint/empty
    val data = vis |.| recur |.| ext |.| eff |.| sort |+| d.name.pp-name |.| d.range.pretty |.| params |.| kind |+| body
    data.pretty-comment(d.doc)

fun pretty-con-info(c: con-info, publicOnly: bool)
  if publicOnly && c.vis.is-private then pprint/empty
  else
    fun pp-field((_, (name, tp)))
      (if name.is-field-name then pprint/empty else name.pp-name |.| ": ".text) |.| tp.pp-type
    val vis = if publicOnly then pprint/empty else c.vis.pp-vis
    val lzy = match c.mbLazy 
      Nothing -> pprint/empty
      Just(fipT) -> ["lazy", fipT.show].sep-by-space.keyword |.| space
    c.existentials.foreach(extend-nice)
    val exists0 = if c.existentials.is-nil then pprint/empty else c.existentials.map(pp-typevar).angled
    val fields = if c.params.is-nil then pprint/empty else zip(c.paramVis, c.params).map(pp-field).comma-sep.parens
    val vrepr = c.valueRepr.show.text
    val const = vis |.| lzy |.| "con".keyword |+| c.name.pp-name |.| c.range.pretty |.| exists0 |.| fields |.| vrepr |+| ":".text |+| c.typeScheme.pp-type |+| "=".text |+| c.tag.pretty |.| semi
    const.pretty-comment(c.doc)

pub fun pretty-comment(d: doc, comment: string)
  if comment == "" then d else
    val clist = comment.list
    val cmt = if clist.last.unjust == '\n' then clist.init.string else comment
    (cmt.text |-| d).color(colors.colorComment)

fun pp-vis(v: visibility): _ doc
  match v
    Private -> pprint/empty
    Public -> "pub ".keyword

fun pp-sub(sub: sub): _ doc 
  sub.list.map(fn((tv, tp)) tv.pp-typevar |+| "|->".text |+| tp.pp-type).list

// Synonym info
fun syninfo/pretty(s: syn-info): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with nice-env
  pp-syn-info(s)

pub fun pp-syn-info(s: syn-info, isLocal: bool=False, publicOnly:bool=False, showBody:bool=True)
  if publicOnly && s.vis.is-private then pprint/empty 
  else
    val al = if isLocal then "local alias".keyword else s.vis.pp-vis |.| "alias".keyword
    val params = if s.params.is-nil then pprint/empty else s.params.map(TVar).nice-types.angled
    val kind = if s.kind == kindStar then pprint/empty else " ::".text |+| s.kind.pp-kind(precTop)
    val body = if !showBody then pprint/empty else "=".keyword |+| s.tp.nice-type
    val syn = al |+| s.name.pp-name |.| s.range.pretty-range |.| params |.| kind |+| body |+| "=".text |+| pretty(s.rank)
    syn.pretty-comment(s.doc)

// Linear-map workaround - sort by name. Nice-naming
// isn't threaded across the listing -- each entry's quantified vars start at
// 'a' again (matching `nice-types`'s own per-item convention) -- so install a
// fresh nice-env per item rather than relying on the caller's ambient one.
// noinline: prevents cross-module inlining into driver.kk, which trips a
// reference-compiler codegen bug (an effect-val read cache hoisted under a
// type/pretty-local symbol name that is not emitted in the inlining TU)
pub noinline fun pp-synonyms(syns: synonyms): _ doc
  fun pp-one(s: syn-info): _ doc
    with nice-env
    pp-syn-info(s)
  vcat(rb-map/list(syns).sort(fn((n1: name, _), (n2: name, _)) n1.show < n2.show).map(fn((_, s)) pp-one(s)))

pub fun range/pretty-range(r: range)
  if pp-env.coreIface then r.pretty else pprint/empty

pub fun pp-type(tp: ktype)
  val isCoreIface = pp-env.coreIface
  val t = match tp
    TForAll(vars, t) ->
      val p = pp-prec
      // -- the nice extension is scoped to this forall (sibling foralls
      // re-use the same letters) and the body prints at top precedence (no
      // extra parens around a function-typed body)
      with nice-scoped
      vars.foreach(extend-nice)
      val d = (if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(pp-typevar).angled |.| space)
      val d' = d |.| override-prec(precTypeTop, {t.pp-type})
      d'.pparens(p, precTypeQuant)
    TFun(args, eff, res) -> pp-fun("->".text, args, eff, res)
    TVar(tv as TypeVar(_, _, Bound)) ->
      match ranked.lookup(tv)
        Nothing -> tv.pp-typevar
        Just(f) -> f(pp-prec)
    TVar(tv) -> tv.pp-typevar
    TCon(cv) -> pp-typecon(cv)
    TApp(TCon(c), [_, _]) | c.name == nameEffectExtend ->
      val (ls, tl) = tp.shallow-extract-effect-extend
      val tldoc = if tl.match-type(effectEmpty) then pprint/empty else "|".text |.| override-prec(precTypeTop, {tl.pp-type})
      val isTailEmpty = tl.match-type(effectEmpty)
      val doc = match ls
        [l] | isTailEmpty && !isCoreIface -> override-prec(precTypeAtom, {l.pp-type})
        _ -> "<".text |.| ls.map(fn(l) override-prec(precTypeTop, {l.pp-type})).punctuate(comma).hcat |.| tldoc |.| ">".text
      doc.color(colors.colorEffect)
    TApp(TCon(c), [eff, res]) | c.name == nameTpValueOp && !isCoreIface ->
      "->".text |+| eff.pp-type |+| res.pp-type
    TApp(TCon(c), [eff, res]) | c.name == nameTpDelay ->
      "$".text |+| (if eff.is-type-total then pprint/empty else override-prec(precArrow, {eff.pp-type}) |.| space) |.|
      override-prec(precArrow, {res.pp-type})
    // guards must be total so the `coreIface` tests use the pre-bound
    // `isCoreIface` local rather than reading the pp-env effect in the guard
    TApp(TCon(c), [arg]) | c.name == nameTpOptional && !isCoreIface ->
      "?".text |+| override-prec(precTypeAtom, {arg.pp-type})
    TApp(TCon(c), [arg]) | (c.name == nameTpHandled || c.name == nameTpHandled1 || c.name == nameTpNHandled || c.name == nameTpNHandled1) && !isCoreIface ->
      arg.pp-type
    TApp(TCon(TypeCon(nm1)), args) | nm1.is-name-tp-tuple ->
      args.map(fn(t) override-prec(precTypeTop, {t.pp-type})).comma-sep.parens
    TApp(f, args) ->
      val fdoc = override-prec(precTypeAtom, {f.pp-type})
      val argsdoc = match args 
        Nil -> pprint/empty
        Cons(arg, rest) -> 
          val argsDoc = args.map(fn(a) override-prec(precTypeTop, {a.pp-type})).angled
          if rest.is-nil then argsDoc.color-by-kind(arg.kind, id) else argsDoc
      (fdoc |.| argsdoc).pparens(pp-prec, precApp)
    TSyn(syn, args, tp) ->
      override-prec(precTop, {tp.pp-type}).pp-synonym(syn, args)
  t.color(colors.colorType)

fun pp-fun(arrow, args, eff, result)
  // pparens wraps the WHOLE function type (so a function in
  // arrow-result position prints `-> ((x : a) -> b)`)
  (args.map(fn(p) override-prec(precTypeTop, {p.pp-param})).punctuate(comma).hsep.parens |+|
   (if eff.is-type-total then arrow else arrow |+| override-prec(precTypeArrow, {eff.pp-type})) |+|
   override-prec(precTypeArrow, {result.pp-type})).pparens(pp-prec, precTypeArrow)

pub fun pp-param((nm: name, tp: ktype))
  val name = if (nm.is-nil || nm.is-field-name || nm.is-wildcard || nm.is-hidden-name) then
      pprint/empty
    else
      nm.unqualify.pp-name-plain.color(colors.colorParameter) |.| " : ".text
  name |.| tp.pp-type

pub fun pp-name(nm: name)
  nm.pp-name-plain.color(colors.colorSource)

fun pp-type-name(nm: name)
  nm.pp-name-plain.color(colors.colorType)

pub fun pp-name-plain(n: name)
  // Renders through `prettyName` (plain `/` separator for
  // local qualifiers), NOT `show`/show-explicit (`/#`) -- the `#` marker must
  // never appear in user-facing type/error output.
  val pp = fn(nm: name) pretty-name(nm, colors)
  if n.is-implicit-param-name then
    "?".text |.| pp-name-plain(n.from-implicit-param-name)
  elif pp-env.fullNames || n.is-module-name then n.pp
  elif n.qualifier == moduleContext then
    n.unqualify.pp
  elif pp-env.coreIface then // emit .kki file?
    n.shorten-for-iface(pp-env.shortModules).pp
  elif n.is-system-core-name then
    n.shorten-system-core-name.pp
  else
    val n' = remove-common-prefix(moduleContext, n)
    if !(n' == n) then n'.pp
    else importsMap.get-alias(n).pp

// The SHORTEST suffix of a name's module path that still names it uniquely
// among the interface's imports: `std/core/types/bool` -> `types/bool`, and
// `compiler/core/core/def` -> `core/core/def` only because `compiler/type/type`
// and friends also end in a segment that would otherwise collide.
//
// Nothing has to be declared for this. `resolve-path` already
// resolves a written path as a SUFFIX of an import entry
// (`rpath.is-prefix(ralias)` on reversed paths), so the import section stays
// canonical and the reader expands. That also means the rule MUST be computed
// against exactly the imports the interface emits: a suffix matching nothing
// does not fail, it is silently taken as a local qualification.
//
// Module-qualified prefixes are 38.7% of interface bytes (26.9MB of 69.4MB,
// 1.57M occurrences over only 1,593 distinct prefixes), and interface text is
// what a warm build spends its time reading.
fun shorten-for-iface(n: name, short: list<(string, name)>): name
  val nmod = n.nameModule
  if nmod.is-empty then n
  else match short.lookup(fn(m) m == nmod)
    Just(m) -> qualify(m, n.unqualify)
    Nothing -> n

// Build the table: for each module in scope, the shortest suffix of its path
// that no OTHER module in scope also ends with. `std/core/types` -> `types`,
// while `compiler/core/core` needs `core/core` because other modules end in
// `core`. Modules with no unambiguous proper suffix keep their full path.
pub fun iface-short-modules(imp: import-map): list<(string, name)>
  val mods = import-map/list(imp).map(fn((_, m)) m.nameModule).filter(fn(m) !m.is-empty)
  val split = mods.map(fn(m) (m, m.split("/")))
  split.filter-map fn((m, segs))
    val hits = list(1, segs.length - 1).filter-map fn(k)
      val suffix = segs.drop(segs.length - k)
      val n-matching = split.filter(fn((_, ms)) ms.length >= suffix.length
                                      && ms.drop(ms.length - suffix.length) == suffix).length
      if n-matching == 1 then Just(suffix.join("/").new-module-name) else Nothing
    match hits
      Cons(short) -> Just((m, short))
      Nil -> Nothing

fun pp-synonym(tpdoc: doc, ts: type-syn, args: list<ktype>)
  // An interface must carry enough to rebuild what was written. A synonym
  // normally travels as a NAME here plus a `local alias` declaration in the
  // header -- but the header is built by `extract-imported-synonyms`, which can
  // only declare a synonym it has a `syn-info` for. A `TSyn` carrying `Nothing`
  // (`type-cctx` builds `std/core/types/ctx` that way, and upstream's
  // `typeCCtx` is identical) is therefore declared NOWHERE, and printing just
  // its name loses the expansion for good: read back, it degrades to a bare
  // `TCon` that `Parc.getDataDefInfo` then fails on.
  //
  // The expansion is right here in `tpdoc`, so emit it inline for exactly that
  // case. `parse-synonym` already reads `name<args> == rank body` back into a
  // `TSyn` with no table lookup at all, which is what lets an interface be read
  // without seeding synonyms from its dependencies.
  val selfDescribe = pp-env.coreIface && ts.info.is-nothing
  val nm = override-prec(precTypeTop, {TApp(TCon(TypeCon(ts.name, ts.kind)), args).pp-type}) |.| 
    (if pp-env.expandSynonyms || selfDescribe then " ==".text |+| ts.rank.pretty |+| tpdoc else pprint/empty)
  if pp-env.expandSynonyms || selfDescribe then
    nm.parens
  elif args.is-nil then
    nm
  else
    nm.pparens(pp-prec, precTypeApp)

pub fun pp-typevar(tv: type-var)
  val fl = 
    if pp-env.showFlavours then 
      match tv.flavour
        Meta -> "_".text
        Skolem -> if pp-env.coreIface then "__".text else "$".text
        _ -> pprint/empty
    else pprint/empty
  val nm = fl |.| get-nice-doc(tv) |.| (if pp-env.showIds then text("=" ++ tv.tid.show) else pprint/empty)
  nm.wrap-kind(tv.kind).color-by-kind-def(tv.kind, colorTypeVar)

pub fun pp-typecon(tc: type-con)
  val doc = if tc.name == nameTpUnit then "()".text else tc.name.pp-name-plain
  if pp-env.declaredKinds.any(fn(n) n == tc.name)
    then doc.color-by-kind-def(tc.kind, colorTypeCon)   // declared once above
    else doc.wrap-kind(tc.kind).color-by-kind-def(tc.kind, colorTypeCon)

pub fun pp-typesyn(ts: type-syn)
  if pp-env.declaredKinds.any(fn(n) n == ts.name)
    then ts.name.pp-name-plain.color-by-kind-def(ts.kind, colorTypeCon)
    else ts.name.pp-name-plain.wrap-kind(ts.kind).color-by-kind-def(ts.kind, colorTypeCon)

fun color-by-kind-def(d: doc, k: kind, defcolor: (colorScheme -> _ color))
  d.color-by-kind(k, fn(d') d'.color(defcolor(colors)))

fun color-by-kind(d: doc, k: kind, defcolor: (doc -> _ doc))
  match k.color-for-kind
    Just(c) -> d.color(c)
    Nothing -> defcolor(d)

fun color-for-kind(k: kind)
  if k == kindEffect || k == kindLabel || k == kind-fun(kindHeap, kindLabel) then
    Just(colors.colorEffect)
  elif k == kindHeap || k == kindScope then
    Just(colors.colorEffect)
  else Nothing

pub fun pp-kind-decl((nm, k): (name, kind)): _ doc
  "local kind".keyword |+| nm.pp-name-plain |+| "::".text |+| k.pp-kind(kind/pretty/precTop) |.| semi

fun wrap-kind(d: doc, k: kind)
  if pp-env.showKinds && k != kindStar then
    parens(d.color(colors.colorType) |+| "::".text |+| k.pp-kind(kind/pretty/precTop)).color(colors.colorKind)
  else d
