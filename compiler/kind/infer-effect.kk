// Updated as of 7/23/26: Commit 6dbe4e6
module compiler/kind/infer-effect

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
import std/data/rb-map

pub type infer-kind-env
  InferKindEnv(
    imports: import-map,
    kGamma: kGamma,
    infgamma: inf-kgamma,
    synonyms: synonyms,
    newtypesImported: newtypes,
    newtypesExtended: newtypes,
    dataEffects: name-map<data-effect>
  )

pub effect val inf-kind-env: infer-kind-env

pub effect infer-kind-effect
  fun get-ksub(): ksub
  fun extend-ksub(s: ksub): ()
  fun get-local-syns(): synonyms
  fun get-syns(): synonyms
  fun add-synonym(syn: syn-info): ()
  fun add-external(name: name, rng: range): ()
  fun lookup-external(name: name): maybe<range>
  // Kind errors ACCUMULATE (inference continues with a fallback) and are raised together at the end of the kind phase --
  // aborting at the first one loses upstream's follow-on errors
  fun kind-add-error(rng: range, msg: doc): ()
  // raise the accumulated errors NOW (no-op when none): called between kind phases 
  fun kind-flush-errors(): ()
  val target-platform: target-platform

pub fun allnewtypes(env: infer-kind-env)
  env.newtypesImported.compose(env.newtypesExtended)

pub fun get-platform(): _ platform
  target-platform.tpl-platform

pub fun run-kind-infer(tplatform: target-platform, moduleName: name, imports: import-map, kgamma: kGamma, syns: synonyms, datas: newtypes, f: () -> _ a): _ a
  with val current-error-kind = ErrKind
  val imports' = match imports.extend(moduleName, moduleName)
    Just(imp) -> imp
    Nothing -> imports // ignore
  with handler
    val inf-kind-env = InferKindEnv(imports', kgamma, rb-map/empty(), syns, datas, newtypes/empty, rb-map/empty())
  var local-syns := synonyms/empty
  var ksub := ksubEmpty
  var externals: name-map<range> := rb-map/empty()
  var kerrs : errors := []
  with handler
    // All phases run collecting errors (kind-add-error below); 
    // only when the whole kind phase RETURNS are they raised together
    // type inference never runs when any kind error  occurred. 
    // NOTE: raise from the `return` clause -- a statement placed
    // after this `with handler` gets miscompiled by the reference compiler
    // (same class as the `with val pp-env` mlift bug, see code-gen.kk).
    return(x)
      if !kerrs.is-nil then add-errors(kerrs) else ()
      x
    fun get-ksub() ksub
    fun extend-ksub(s) ksub := s.compose(ksub)
    fun get-local-syns() local-syns
    fun get-syns() inf-kind-env.synonyms.compose(local-syns)
    fun add-synonym(syn) local-syns := local-syns.extend(syn)
    fun lookup-external(nm) externals.lookup(nm)
    fun add-external(nm, rng) externals := rb-map/set(externals, nm, rng) // upstream M.insert overwrites
    fun kind-add-error(rng, msg) kerrs := kerrs ++ [msg.error-message(rng)]
    fun kind-flush-errors()
      if !kerrs.is-nil then add-errors(kerrs) else ()
    val target-platform = tplatform
  f()

pub fun fresh-kind()
  KIVar(unique-id("k"))

pub fun fresh-typevar(TypeBinder(name, kind): type-binder<kind>, fl: flavour)
  TypeVar(unique-id(name.show), kind, fl)

pub fun subst(x: inf-kind)
  get-ksub() |-> x

// Extend the inference kind assumption; checks for 'shadow' definitions
pub fun extend-infgamma(tbinders: list<type-binder<inf-kind>>, f)
  fun check(TypeBinder(nm, infkind, nmrng, _): type-binder<inf-kind>, infgamma: inf-kgamma)
    match infgamma.lookup(nm)
      Nothing -> infgamma.set(nm, infkind) // upstream M.insert (key absent here, but keep insert semantics)
      Just(_) ->
        kind-add-error(nmrng, "Type".text |+| nm.pp-type |+| "is already defined".text)
        infgamma.set(nm, infkind) // replace
  val infgammaNew = tbinders.foldl(inf-kind-env.infgamma, fn(acc, tb) tb.check(acc))
  with override
    val inf-kind-env = inf-kind-env( infgamma = infgammaNew)
  f()

// Extend the kind assumption; checks for duplicate definitions
pub fun extend-kgamma(rngs: list<range>, dg: compiler/core/core/typedef-group, f)
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
          kind-add-error(rng, "Type".text |+| nm.pp-type |+| "is already defined".text)
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

pub fun check-external(name: name, range: range)
  val mbres = lookup-external(name)
  match mbres
    Just(rng0) ->
      kind-add-error(range, "external".text |+| name.pretty-name(colors) |+| "is already defined at".text |+| rng0.start.show.text |-| "hint: use a local qualifier?".text)
    _ -> 
      add-external(name, range)

fun inf-qualified-name(nm: name, rng: range)
  if !nm.is-qualified then nm
  else
    match expand(inf-kind-env.imports, nm)
      Right((name', alias0)) ->
        if !nm.qualifier.name-case-equal-prefix-of(alias0) then
          kind-add-error(rng, "module".text |+| nm.pp-module |+| "should be cased as".text |+| alias0.pretty.color(colors.colorModule))
          name'
        else
          name'
      Left([]) ->
        kind-add-error(rng, "module".text |+| nm.pp-module |+| "is undefined".text)
        nm
      Left(aliases) ->
        kind-add-error(rng, "module".text |+| nm.pp-module |+| ambiguous(aliases))
        nm

fun pp-module(nm: name)
  nm.nameModule.text.color(colors.colorModule)

// Resolve a type name WITHOUT reporting errors: used by implicit-parameter
// unpacking (`.?name`), where the parameter name may not be a type at all
// (the unpack type then comes from the parameter's type annotation instead).
pub fun lookup-infkind-name(nm0: name): _ maybe<name>
  val nm = match expand(inf-kind-env.imports, nm0)
    Right((name', _)) -> name'
    _ -> nm0
  val qname = if nm.is-qualified then nm else qualify(current-modname(), nm)
  val infgamma = inf-kind-env.infgamma
  match infgamma.lookup(nm)
    Just(_) -> Just(nm)
    Nothing ->
      match infgamma.lookup(qname)
        Just(_) -> Just(qname)
        Nothing ->
          match inf-kind-env.kGamma.lookup(current-modname(), nm)
            Found((qname', _)) -> Just(qname')
            _ -> Nothing

pub fun find-infkind(nm0: name, rng: range)
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
                kind-add-error(rng, "type".text |+| nm0.unqualify.pp-type |+| "should be cased as".text |+| name'.unqualify.pp-type)
              else
                ()
              match mbAlias
                Just(alias0) | nm0.nameModule != alias0.nameModule ->
                  kind-add-error(rng, "module".text |+| nm0.nameModule.text.color(colors.colorModule) |+| "should be cased as".text |+| alias0.pretty.color(colors.colorModule))
                _ -> ()
              (qname', KICon(kind), doc)
            NotFound ->
              // trace("cannot find type: " ++ nm.pp-type(colors).show)
              kind-add-error(rng, "Type".text |+| nm.pp-type |+| "is not defined".text |-| " hint: bind the variable using".text |+| ("forall<".text |.| nm.pp-type |.| ">".text).color(colors.colorType) |+| "?".text)
              val k = fresh-kind()
              (nm, k, "")
            Ambiguous(names) ->
              kind-add-error(rng, "Type".text |+| nm.pp-type |+| ambiguous(names))
              val k = fresh-kind()
              (nm, k, "")

fun ambiguous(lst: list<name>)
  match lst
    [name1, name2] -> "is ambiguous.".text |-| " hint: It can refer to either".text |+| name1.pp-type |.| ", or".text |+| name2.pp-type
    [name1, name2, name3] -> "is ambiguous.".text |-| " hint: It can refer to either".text |+| name1.pp-type |.| ",".text |+| name2.pp-type |.| ", or".text |+| name3.pp-type
    [name] -> "should be cased as:".text |+| name.unqualify.pp-type
    names -> "is ambiguous and can refer to multiple imports:".text |-| names.map(pp-type).list.indent(1)

fun pp-type(nm: name)
  nm.pretty.color(colors.colorType)

pub fun qualify-def(nm: name)
  qualify(current-modname(), nm)

fun find-kind(nm: name)
  match kgamma-lookup(current-modname(), nm)
    Found((qname, (kind, doc))) -> (qname, kind, doc)
    _ -> failure/fail("kind/infer find-kind: unknown type constructor: " ++ nm.show)

pub fun lookup-datainfo(nm: name)
  match inf-kind-env.newtypesExtended.lookup-any(nm)
    Nothing -> inf-kind-env.newtypesImported.lookup-any(nm)
    just -> just

pub fun with-data-effects(effs: name-map<data-effect>, f)
  with override
    val inf-kind-env = inf-kind-env(dataEffects = effs)
  f()

pub fun lookup-data-effect(nm: name)
  match inf-kind-env.dataEffects.lookup(nm)
    Just(eff) -> eff
    Nothing -> 
      match lookup-datainfo(nm)
        Just(di) -> di.deffect
        Nothing -> DataNoEffect
