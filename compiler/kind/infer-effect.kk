import compiler/common/range
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/name
import compiler/common/name-collections
import compiler/common/failure
import compiler/common/unique
import compiler/platform/config
import compiler/lib/pprint
import compiler/kind/kind
import compiler/kind/infer-kind
import compiler/kind/assumption
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/import-map
import compiler/type/type
import compiler/syntax/range-map
import compiler/syntax/syntax
import compiler/core/core
import compiler/common/error
import std/data/linear-map

type infer-kind-env
  InferKindEnv(
    imports: import-map,
    kGamma: kGamma,
    infgamma: inf-kgamma,
    synonyms: synonyms,
    newtypesImported: newtypes,
    newtypesExtended: newtypes,
    dataEffects: name-map<data-effect>
  )

effect val inf-kind-env: infer-kind-env

effect infer-kind-effect
  fun get-ksub(): ksub
  fun extend-ksub(s: ksub): ()
  fun get-local-syns(): synonyms
  fun get-syns(): synonyms
  fun add-synonym(syn: syn-info): ()
  fun add-external(name: name, rng: range): ()
  fun lookup-external(name: name): maybe<range>
  val platform: platform

fun allnewtypes(env: infer-kind-env)
  env.newtypesImported.compose(env.newtypesExtended)

fun run-kind-infer(platform: platform, moduleName: name, imports: import-map, kgamma: kGamma, syns: synonyms, datas: newtypes, f: () -> _ a): _ a
  with val current-error-kind = ErrKind
  val imports' = match imports.extend(moduleName, moduleName)
    Just(imp) -> imp
    Nothing -> imports // ignore
  with handler
    val inf-kind-env = InferKindEnv(imports', kgamma, LinearMap([]), syns, datas, newtypes/empty, LinearMap([]))
  var local-syns := synonyms/empty
  var ksub := LinearMap([])
  var externals: name-map<range> := LinearMap([])
  with handler
    fun get-ksub() ksub
    fun extend-ksub(s) ksub := ksub.compose(s)
    fun get-local-syns() local-syns
    fun get-syns() inf-kind-env.synonyms.compose(local-syns)
    fun add-synonym(syn) local-syns := local-syns.extend(syn)
    fun lookup-external(nm) externals.lookup(nm)
    fun add-external(nm, rng) externals := externals.add(nm, rng)
    val platform = platform
  f()

fun fresh-kind()
  KIVar(unique-id("k"))

fun fresh-typevar(TypeBinder(name, kind): type-binder<kind>, fl: flavour)
  TypeVar(unique-id(name.show), kind, fl)

fun subst(x: inf-kind)
  get-ksub() |-> x

// Extend the inference kind assumption; checks for 'shadow' definitions
fun extend-infgamma(tbinders: list<type-binder<inf-kind>>, f)
  fun check(TypeBinder(nm, infkind, nmrng, _): type-binder<inf-kind>, infgamma: inf-kgamma)
    match infgamma.lookup(nm)
      Nothing -> infgamma.add(nm, infkind)
      Just(_) ->
        add-error(nmrng, "Type".text |+| nm.pp-type |+| "is already defined".text)
        infgamma.set(nm, infkind) // replace
  val infgammaNew = tbinders.foldl(inf-kind-env.infgamma, fn(acc, tb) tb.check(acc))
  with override
    val inf-kind-env = inf-kind-env( infgamma = infgammaNew)
  f()

// Extend the kind assumption; checks for duplicate definitions
fun extend-kgamma(rngs: list<range>, dg: compiler/core/core/typedef-group, f)
  fun nameKind(tdef: compiler/core/core/typedef)
    match tdef
      core/Synonym(syn-info) -> (syn-info.name, syn-info.kind, syn-info.doc)
      core/Data(ntInfo) -> (ntInfo.name, ntInfo.kind, ntInfo.doc)
  fun check((kgamma: kGamma, tdefs: list<compiler/core/core/typedef>), (rng: range, tdef: compiler/core/core/typedef))
    if tdef.is-extension then (kgamma, tdefs)
    else
      val (nm, knd, doc) = nameKind(tdef)
      match kgamma.lookup-qualified(nm)
        Nothing -> (kgamma.extend(nm, knd, doc), Cons(tdef, tdefs))
        Just(_) ->
          add-error(rng, "Type".text |+| nm.pp-type |+| "is already defined".text)
          (kgamma, tdefs)
  val (_, tdefs) = zip(rngs, dg).foldl((inf-kind-env.kGamma, []), check)
  
  fun name-syn(tdef: compiler/core/core/typedef)
    match tdef
      core/Synonym(syn-info) -> [syn-info]
      _ -> []
  fun name-newtype(tdef: compiler/core/core/typedef)
    match tdef
      Data(dataInfo) -> [dataInfo]
      _ -> []
  val newkGamma = new-nub(tdefs.map(nameKind))
  val kSyns = tdefs.map(name-syn).concat.new
  val kNewtypes = tdefs.map(name-newtype).concat.new
  val old-env = inf-kind-env
  with override
    val inf-kind-env = old-env( 
      kGamma = old-env.kGamma.qname-map/union(newkGamma), 
      synonyms = old-env.synonyms.compose(kSyns), 
      newtypesExtended = old-env.newtypesExtended.compose(kNewtypes))  
  f()

fun member-doc(doc: string, header: string, members: list<string>): string
  val mdoc = "// " ++ header ++ ":\n// ```koka\n" ++ members.map("//" ++ _).join("\n") ++ "// ```\n"
  if doc == "" then mdoc else doc ++ "\n// * * *\n" ++ mdoc

fun check-external(name: name, range: range)
  val mbres = lookup-external(name)
  match mbres
    Just(rng0) ->
      add-error(range, "external".text |+| name.pretty-name(colors) |+| "is already defined at".text |+| rng0.start.show.text |-| "hint: use a local qualifier?".text)
    _ -> 
      add-external(name, range)

fun inf-qualified-name(nm: name, rng: range)
  if !nm.is-qualified then nm
  else
    match expand(inf-kind-env.imports, nm)
      Right((name', alias0)) ->
        if !nm.qualifier.name-case-equal-prefix-of(alias0) then
          add-error(rng, "module".text |+| nm.pp-module |+| "should be cased as".text |+| alias0.pretty.color(colors.colorModule))
          name'
        else
          name'
      Left([]) ->
        add-error(rng, "module".text |+| nm.pp-module |+| "is undefined".text)
        nm
      Left(aliases) ->
        add-error(rng, "module".text |+| nm.pp-module |+| ambiguous(aliases))
        nm

fun pp-module(nm: name)
  nm.nameModule.text.color(colors.colorModule)

fun find-infkind(nm0: name, rng: range)
  val (nm, mbAlias) = match expand(inf-kind-env.imports, nm0)
    Right((name', alias0)) -> (name', Just(alias0))
    _ -> (nm0, Nothing)
  val qname = if nm.is-qualified then nm else qualify(current-modname(), nm)
  // lookup locally
  // note: also lookup qualified since it might be recursive definition
  // TODO: check for the locally inferred names for casing too.
  val infgamma = inf-kind-env.infgamma
  match infgamma.lookup(nm)
    Just(infkind) -> (nm, infkind, "")
    Nothing ->
      match infgamma.lookup(qname)
        Just(infkind) -> (qname, infkind, "")
        _ ->
          val kgamma = inf-kind-env.kGamma  
          match kgamma.lookup(current-modname(), nm)
            Found((qname', TypeNameInfo(kind, doc))) ->
              val name' = if nm.is-qualified then qname' else qname'.unqualify
              if !name'.name-case-equal(nm) then
                add-error(rng, "type".text |+| nm0.unqualify.pp-type |+| "should be cased as".text |+| name'.unqualify.pp-type)
              else
                ()
              match mbAlias
                Just(alias0) | nm0.nameModule != alias0.nameModule ->
                  add-error(rng, "module".text |+| nm0.nameModule.text.color(colors.colorModule) |+| "should be cased as ".text |+| alias0.pretty.color(colors.colorModule))
                _ -> ()
              (qname, KICon(kind), doc)
            NotFound ->
              // trace("cannot find type: " ++ nm.pp-type(colors).show)
              add-error(rng, "Type".text |+| nm.pp-type |+| "is not defined".text |-| " hint: bind the variable using".text |+| ("forall<".text |.| nm.pp-type |.| ">".text).color(colors.colorType) |+| "?".text)
              val k = fresh-kind()
              (nm, k, "")
            Ambiguous(names) ->
              add-error(rng, "Type".text |+| nm.pp-type |+| ambiguous(names))
              val k = fresh-kind()
              (nm, k, "")

fun ambiguous(lst: list<name>)
  match lst
    [name1, name2] -> "is ambiguous.".text |-| " hint: It can refer to either".text |+| name1.pp-type |.| ", or".text |+| name2.pp-type
    [name1, name2, name3] -> "is ambiguous.".text |-| " hint: It can refer to either".text |+| name1.pp-type |.| ", ".text |+| name2.pp-type |.| ", or".text |+| name3.pp-type
    [name] -> "should be cased as:".text |+| name.unqualify.pp-type
    names -> "is ambiguous and can refer to multiple imports:".text |-| names.map(pp-type).list.indent(1)

fun pp-type(nm: name)
  nm.pretty.color(colors.colorType)

fun qualify-def(nm: name)
  qualify(current-modname(), nm)

fun find-kind(nm: name)
  match kgamma-lookup(current-modname(), nm)
    Found((qname, (kind, doc))) -> (qname, kind, doc)
    _ -> fail("kind/infer find-kind: unknown type constructor: " ++ nm.show)

fun lookup-datainfo(nm: name)
  match inf-kind-env.newtypesExtended.lookup-any(nm)
    Nothing -> inf-kind-env.newtypesImported.lookup-any(nm)
    just -> just

fun with-data-effects(effs: name-map<data-effect>, f)
  with override
    val inf-kind-env = inf-kind-env(dataEffects = effs)
  f()

fun lookup-data-effect(nm: name)
  match inf-kind-env.dataEffects.lookup(nm)
    Just(eff) -> eff
    Nothing -> 
      match lookup-datainfo(nm)
        Just(di) -> di.deffect
        Nothing -> DataNoEffect
