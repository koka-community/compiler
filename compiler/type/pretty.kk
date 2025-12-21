import compiler/common/id
import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/nice
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import compiler/type/type
import compiler/type/typevar
import compiler/kind/import-map
import compiler/platform/config
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/pretty
import std/data/linearmap
import std/data/linearset
import std/core/undiv
import std/core-extras
// Updated 11/19/25 to commit #752748d, not fully visually second checked otherwise.

alias prec = int;
val precTopTop = -1 // most outer level: used to suppress 'forall'
val precTypeTop = 0
val precTypeQuant = 1
val precTypeArrow = 2
val precTypeApp = 3
val precTypeAtom = 4
val precPred = 5

alias tv-scheme = linearMap<type-var, (prec -> doc)>;

val rankedDefault:tv-scheme = LinearMap([])

fun keyword(s: string)
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

fun default-doc-env(f)
  with handler
    val colorizing = False
    val htmlBases = []
    val htmlCss = "styles/" ++ comp-flags.programName ++ ".css"
    val htmlJs = "scripts/" ++ comp-flags.programName ++ "-highlight.js"
  f()

fun default-pp-env(f)
  with handler
    val pp-env = PrettyEnv()
  f()

// Pretty print environment for types

alias pp-type-eff = <pp-type-env,documentation,colors,pure,nice-eff<type-var>,comp-flags>

effect val pp-prec: prec;

effect val pp-env: pretty-env;

type pretty-env
  PrettyEnv(
    showKinds: bool = False,
    showIds: bool = False, // show id numbers
    showFlavours: bool = True,
    expandSynonyms: bool = False,
    fullNames: bool = False, // TODO: If True it can lead to .kki parse errors
    alwaysUnqualify: bool = False,
    coreIface: bool = False,
    coreShowTypes: bool = False, // show types in core output
    coreShowVis: bool = True, // show visibility
    coreShowDef: bool = False // show definition body
  )

effect indent 
  val indent : int

fun default-indent(f)
  with val indent = 0
  f()

alias pp-type-env = <pretty-type-eff,pp-env,pp-prec>

effect pretty-type-eff
  val ranked: tv-scheme
  val moduleContext: name // module in which we pretty print
  val importsMap: import-map // import aliases

fun override-prec(p: prec, f)
  with override 
    val pp-prec = p
  f()

fun handle-pretty-eff(f)
  with handler
    val pp-prec = precTopTop
  with handler 
    val ranked = rankedDefault
    val moduleContext = "Main".new-name
    val importsMap = LinearMap([])
  f()
 
fun type-colon()
  ":".text.color(colors.colorSep)

fun min-canonical(tp: ktype): pure string
  tp.minimal-form.show.compress

fun canonical(tp: ktype): pure string
  tp.canonical-form.show.compress

fun string/compress(s: string): string
  s.list.compress.string

fun list/compress(l: list<char>): list<char>
  match l
    Nil -> Nil
    Cons(c, cs) ->
      if c == '\n' then compress(cs.drop-while(is-space).pretend-decreasing)
      elif c.is-space then  Cons(' ', compress(cs.drop-while(is-space).pretend-decreasing))
      else Cons(c, compress(cs))

fun nice-type(tp: ktype)
  nice-types([tp]).head.unjust

fun nice-types(tps: list<ktype>): pp-type-eff list<doc>
  tps.niceList fn(tp)
    tp.pp-type.color(colors.colorType)

fun niceList(schemes: list<ktype>, f: (ktype) -> pp-type-eff doc): pp-type-eff list<doc>
  schemes.map(free-type-vars).unions.list.map(extend-nice)
  schemes.map(f)

// Pretty print a type
fun ktp/ppretty(t: ktype): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with niceEnv
  t.pp-type

fun ktp/pretty(t: ktype): <comp-flags, pure> doc
  with default-pp-env
  with default-doc-env
  with handle-pretty-eff
  with niceEnv
  with color-scheme-default
  t.pp-type

fun tv/pretty(tv: type-var): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with niceEnv
  tv.pp-typevar

fun tcon/pretty(tc: type-con): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with niceEnv
  tc.pp-typecon

fun tsyn/pretty(ts: type-syn): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with niceEnv
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

fun pretty-def-fun-type(tp: ktype, pinfos: list<param-info>)
  fun pp-param((nm:name, pinfo, tpDoc))
    val x = match pinfo
      Borrow -> "^".text |+| (if nm.is-nil then "_".text else nm.pp-name) |+| ": ".text
      _ -> if nm.is-nil then pprint/empty else nm.pp-name |+| ": ".text
    x |.| tpDoc
  match tp.pp-decl-type(pinfos)
    (Just(params), pre, post) ->
      pre |.| params.map(pp-param).comma-sep.parens |+| "->".text |+| post
    (Nothing, pre, post) -> pre |+| "()".text |+| "->".text |+| post

fun pp-decl-type(tp: ktype, pinfos: list<param-info>)
  match tp
    TForAll(vars, rho) ->
      vars.foreach(extend-nice)
      val (args, _, res) = rho.pp-decl-type(pinfos)
      val pre = if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(pp-typevar).angled |.| space
      (args, pre, res)
    TFun(params, eff, rho) ->
      val pparams = params.map(fn((name, tp')) (name, Own, tp'.pp-type))
      (Just(pparams), pprint/empty, if eff.is-type-total then pprint/empty else override-prec(precArrow, {eff.pp-type |.| space}) |.| override-prec(precArrow, {rho.pp-type}))
    _ -> (Nothing, pprint/empty, tp.pp-type)

fun pretty(d: data-info): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with niceEnv
  pp-data-info(d, True)

fun pp-data-info(d: data-info, showBody: bool)
  d.pretty-data-info(showBody, False)

fun comma-sep(d: list<doc>)
  d.punctuate(comma).hsep

fun pretty-data-info(d: data-info, showBody: bool, publicOnly: bool)
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
        if is-named then "named ".keyword else pprint/empty |.| 
        (if is-linear then "linear ".keyword else pprint/empty) |.| "effect ".keyword
    val sort = match d.sort
      Inductive -> "type".keyword
      CoInductive -> "co type".keyword
      Retractive -> "div type".keyword // this "div" means a retractive type or non-(co)inductive type
    val params = if d.params.is-nil then pprint/empty else d.params.map(TVar).nice-types.angled
    val kind = if d.kind == kindStar then pprint/empty else " ::".text |+| d.kind.pp-kind(precTop)
    val body = if showBody && d.constrs.is-cons then 
        "{".text |-| d.constrs.map(_.pretty-con-info(publicOnly)).vcat.indent(2) |-| "}".text 
      else pprint/empty
    val data = vis |.| recur |.| ext |.| eff |.| sort |+| d.name.pp-name |.| d.range.pretty |.| params |.| body
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
    val const = vis |.| lzy |.| "con".keyword |+| c.name.pp-name |.| c.range.pretty |.| exists0 |.| fields |+| vrepr |+| ":".text |+| c.typeScheme.pp-type |+| "=".text |+| c.tag.pretty |.| semi
    const.pretty-comment(c.doc)

fun pretty-comment(d: doc, comment: string)
  if comment == "" then d else
    val clist = comment.list
    val cmt = if clist.last.unjust == '\n' then clist.init.string else comment
    (cmt.text |-| d).color(colors.colorComment)

fun pp-vis(v: visibility): colors doc
  match v
    Private -> pprint/empty
    Public -> "pub ".keyword

fun pp-sub(sub: sub): _ doc 
  sub.list.map(fn((tv, tp)) tv.pp-typevar |+| "|->".text |+| tp.pp-type).list

// Synonym info
fun syninfo/pretty(s: syn-info): <documentation,pp-env,pure,comp-flags,colors> doc
  with handle-pretty-eff
  with niceEnv
  pp-syn-info(s)

fun pp-syn-info(s: syn-info, isLocal: bool=False, publicOnly:bool=False, showBody:bool=True)
  if publicOnly && s.vis.is-private then pprint/empty 
  else
    val al = if isLocal then "local alias".keyword else s.vis.pp-vis |.| "alias".keyword
    val params = if s.params.is-nil then pprint/empty else s.params.map(TVar).nice-types.angled
    val kind = if s.kind == kindStar then pprint/empty else " ::".text |+| s.kind.pp-kind(precTop)
    val body = if !showBody then pprint/empty else "=".keyword |+| s.t.nice-type
    val syn = al |+| s.name.pp-name |.| s.range.pretty-range |.| params |.| kind |+| body |+| "=".text |+| pretty(s.rank)
    syn.pretty-comment(s.doc)

fun range/pretty-range(r: range)
  if pp-env.coreIface then r.pretty else pprint/empty

fun pp-type(tp: ktype)
  val isCoreIface = pp-env.coreIface
  val t = match tp
    TForAll(vars, t) ->
      val p = pp-prec
      vars.foreach(extend-nice)
      val d = (if vars.is-nil then pprint/empty else "forall".keyword |.| vars.map(pp-typevar).angled |.| space)
      val d' = d |.| t.pp-type
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
    TApp(TCon(c), [arg]) ->
      val nm = c.name
      if nm == nameTpOptional && !isCoreIface then
        "?".text |.| override-prec(precTypeAtom, {arg.pp-type})
      elif nm == nameTpHandled || nm == nameTpHandled1 || nm == nameTpNHandled || nm == nameTpNHandled1 && !isCoreIface then
        arg.pp-type
      else
        match tp
          TApp(TCon(TypeCon(nm1)), args) | nm1.is-name-tp-tuple -> args.map(fn(t) override-prec(precTypeTop, {t.pp-type})).comma-sep.parens
          TApp(f, args) ->
            val fdoc = override-prec(precTypeAtom, {f.pp-type})
            val argsdoc = match args 
              Nil -> pprint/empty
              Cons(targ, rest) -> 
                val argsDoc = args.map(fn(a) override-prec(precTypeTop, {a.pp-type})).angled
                if rest.is-nil then argsDoc.color-by-kind(targ.kind, id) else argsDoc
            (fdoc |.| argsdoc).pparens(pp-prec, precApp)
    // TODO: this is duplicated above due to issues with limitations in guards
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
  args.map(fn(p) override-prec(precTypeTop, {p.pp-param})).punctuate(comma).hsep.parens.pparens(pp-prec, precTypeArrow) |+|
  (if eff.is-type-total then arrow else arrow |+| override-prec(precTypeArrow, {eff.pp-type})) |+|
  override-prec(precTypeArrow, {result.pp-type})

fun pp-param((nm: name, tp: ktype))
  val name = if (nm.is-nil || nm.is-field-name || nm.is-wildcard || nm.is-hidden-name) then
      pprint/empty
    else
      nm.unqualify.pp-name-plain.color(colors.colorParameter) |.| " : ".text
  name |.| tp.pp-type

fun pp-name(nm: name)
  nm.pp-name-plain.color(colors.colorSource)

fun pp-type-name(nm: name)
  nm.pp-name-plain.color(colors.colorType)

fun pp-name-plain(n: name)
  if n.is-implicit-param-name then
    "?".text |.| pp-name-plain(n.from-implicit-param-name)
  elif pp-env.fullNames || n.is-module-name then n.pretty
  elif n.qualifier == moduleContext || pp-env.alwaysUnqualify then
    n.unqualify.pretty
  elif n.is-system-core-name && !pp-env.coreIface then
    n.shorten-system-core-name.pretty
  else
    importsMap.get-alias(n).pretty

fun pp-synonym(tpdoc: doc, ts: type-syn, args: list<ktype>)
  val nm = override-prec(precTypeTop, {TApp(TCon(TypeCon(ts.name, ts.kind)), args).pp-type}) |.| 
    (if pp-env.expandSynonyms then " == ".text |.| ts.rank.pretty |+| tpdoc else pprint/empty)
  if pp-env.expandSynonyms then
    nm.parens
  elif args.is-nil then
    nm
  else
    nm.pparens(pp-prec, precTypeApp)

fun pp-typevar(tv: type-var)
  val fl = 
    if pp-env.showFlavours then 
      match tv.flavour
        Meta -> "_".text
        Skolem -> if pp-env.coreIface then "__".text else "$".text
        _ -> pprint/empty
    else pprint/empty
  val nm = fl |.| get-nice-doc(tv) |.| (if pp-env.showIds then text("=" ++ tv.tid.show) else pprint/empty)
  nm.wrap-kind(tv.kind).color-by-kind-def(tv.kind, colorTypeVar)

fun pp-typecon(tc: type-con)
  val doc = if tc.name == nameTpUnit then "()".text else tc.name.pp-name-plain
  doc.wrap-kind(tc.kind).color-by-kind-def(tc.kind, colorTypeCon)

fun pp-typesyn(ts: type-syn)
  ts.name.pp-name-plain.wrap-kind(ts.kind).color-by-kind-def(ts.kind, colorTypeCon)

fun color-by-kind-def(d: doc, k: kind, defcolor: (colorScheme -> <pretty-type-eff,colors> color))
  d.color-by-kind(k, fn(d') d'.color(defcolor(colors)))

fun color-by-kind(d: doc, k: kind, defcolor: (doc -> <pretty-type-eff,colors> doc))
  match k.color-for-kind
    Just(c) -> d.color(c)
    Nothing -> defcolor(d)

fun color-for-kind(k: kind)
  if k == kindEffect || k == kindLabel || k == kind-fun(kindHeap, kindLabel) then
    Just(colors.colorEffect)
  elif k == kindHeap || k == kindScope then
    Just(colors.colorEffect)
  else Nothing

fun wrap-kind(d: doc, k: kind)
  if pp-env.showKinds && k != kindStar then
    parens(d.color(colors.colorType) |+| "::".text |+| k.pp-kind(kind/pretty/precTop)).color(colors.colorKind)
  else d