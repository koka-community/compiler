

import compiler/common/range
import compiler/common/name
import compiler/common/name-collections
import compiler/common/color-scheme
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import compiler/lib/pprint
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/assumption
import std/data/linearmap
// Updated to #cf4024e on 7/13/25

pub infixr 5 (|->)
// inf gamma
// Environment mapping names to type schemes. Due to overloading
// there may be multiple entries for the same name
alias infGamma = name-map<list<nameInfo>>

effect infGammaEff
  fun gamma-extend(name: name, ni: nameInfo): ()
  fun gamma-lookupx(name: name): maybe<nameInfo>
  fun gamma-set(inf: infGamma): ()
  fun gamma-get(): infGamma

fun inf-gamma(ig0: infGamma, f: () -> <infGammaEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var ig := ig0
  with handler
    fun gamma-extend(name: name, ni: nameInfo) ig := ig.inf-gamma/extend(name, ni)
    fun gamma-lookupx(name: name) Nothing // ig.lookup(name)
    fun gamma-set(inf: infGamma) ig := inf
    fun gamma-get() ig
  f()

fun ni/combine(nis: list<nameInfo>, nis2: list<nameInfo>): exn list<nameInfo>
  match nis
    [] -> nis2
    Cons(ni, nis) -> combine(nis, Cons(ni, nis2.filter(fn(ni2) ni.cname != ni2.cname)))

fun inf-gamma/delete(ig: infGamma, n : name): infGamma
  ig.remove(n)

// TODO: Update
// note: qualified names can get inserted into gamma due to recursive definitions, or
// during inference by inserting fully qualified expressions (in resolveApp-name)
// (if isQualified name then trace ("gamma-extend: insert qualified: " ++ show name) else id) $
// overwrite previous names
fun inf-gamma/extend(ig: infGamma, name: name, ni: nameInfo): <exn> infGamma
  ig.update(name.unqualify-full, [ni], ni/combine)

fun inf-gamma-eff/extends(tnames: list<(name,ktype,int,string)>)
  tnames.foreach(fn((name,tp,scope-depth,doc)) extend-tp(name, name, tp, scope-depth, doc))
// fun inf-gamma/extends(ig: gamma, tnames: list<(name,ktype,string)>)
//   tnames.foldl(ig, fn(ig', (name,tp,doc)) ig'.extend-tp(name, name, tp, doc))

fun inf-gamma-eff/extend-tp(name: name, cname: name, tp: ktype, scope-depth: int, doc: string)
  extend-x(name, cname, tp, scope-depth, range/null, False, doc)
// fun inf-gamma/extend-tp(ig: gamma, name: name, cname: name, tp: ktype, doc: string)
//   ig.extend-x(name, cname, tp, range/range/null, False, doc)

fun inf-gamma-eff/extend-x(name: name, cname: name, tp: ktype, scope-depth, rng: range, isVar: bool, doc: string)
  gamma-extend(name, InfoVal(Public, cname, tp, scope-depth, rng, isVar, False, doc))
// fun inf-gamma/extend-x(ig: gamma, name: name, cname: name, tp: ktype, rng: range, isVar: bool, doc: string)
//   ig.set(name, [InfoVal(Public, cname, tp, rng, isVar, doc)])

// fun inf-gamma-eff/lookup(name: name): <infGammaEff,exn> maybe<(name,ktype)>
//   gamma-lookupx(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))
// fun inf-gamma/lookup(ig: gamma, name: name): exn maybe<(name, ktype)>
//   ig.lookup(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))

fun inf-gamma/list(ig: infGamma): pure list<(name, ktype)>
  ig.linearmap/list.flatmap(fn((_, infos)) infos.map(fn(info) (info.cname, info.typ)))
    

fun inf-gamma-list()
  gamma-get().inf-gamma/list

val inf-gamma/empty: infGamma = LinearMap([])

fun (|->)(sub: sub, inf: infGamma): pure infGamma
  inf.map(fn(k, ni) (k, sub |-> ni))

fun ppgamma(ig: infGamma)
  val nameSchemes = ig.gammaList()
  val maxWidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(nice-types([scheme]).head.unjust)
  vcat(nameSchemes.map(fn((n, s))
    fill(n.showPlain.text |.| type-colon().color(colors.colorSep) |+| align(nice(s)), maxWidth)
  ))

fun pretty(ig: infGamma)
  // TODO: Add default env to pretty definitions?
  ppgamma(ig)

fun showgamma(ig: infGamma)
  pretty(ig).show