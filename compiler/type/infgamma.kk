

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

pub infixr 5 (|->)
// inf gamma
// Environment mapping names to type schemes. Due to overloading
// there may be multiple entries for the same name
alias infGamma = name-map<list<nameInfo>>

effect infGammaEff
  fun gamma-extend(name: name, ni: nameInfo): ()
  fun gamma-lookupx(name: name): maybe<nameInfo>
  fun gamma-set(inf: gamma): ()
  fun gamma-get(): gamma

fun inf-gamma(ig0: gamma, f: () -> <infGammaEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var ig := ig0
  with handler
    fun gamma-extend(name: name, ni: nameInfo) ig := ig.extend(name, ni)
    fun gamma-lookupx(name: name) Nothing // ig.lookup(name)
    fun gamma-set(inf: gamma) ig := inf
    fun gammaGet() ig
  f()

fun ni/combine(nis: list<nameInfo>, nis2: list<nameInfo>): exn list<nameInfo>
  match nis
    [] -> nis2
    Cons(ni, nis) -> combine(nis, Cons(ni, nis2.filter(fn(ni2) ni.cname != ni2.cname)))

// TODO: Update
// note: qualified names can get inserted into gamma due to recursive definitions, or
// during inference by inserting fully qualified expressions (in resolveApp-name)
// (if isQualified name then trace ("gamma-extend: insert qualified: " ++ show name) else id) $
// overwrite previous names
fun inf-gamma/extend(ig: gamma, name: name, ni: nameInfo): <exn> gamma
  ig.update(name.unqualify, [ni], ni/combine)

fun inf-gamma-eff/extends(tnames: list<(name,ktype,string)>)
  tnames.foreach(fn((name,tp,doc)) extend-tp(name, name, tp, doc))
// fun inf-gamma/extends(ig: gamma, tnames: list<(name,ktype,string)>)
//   tnames.foldl(ig, fn(ig', (name,tp,doc)) ig'.extend-tp(name, name, tp, doc))

fun inf-gamma-eff/extend-tp(name: name, cname: name, tp: ktype, doc: string)
  extend-x(name, cname, tp, range/range/null, False, doc)
// fun inf-gamma/extend-tp(ig: gamma, name: name, cname: name, tp: ktype, doc: string)
//   ig.extend-x(name, cname, tp, range/range/null, False, doc)

fun inf-gamma-eff/extend-x(name: name, cname: name, tp: ktype, rng: range, isVar: bool, doc: string)
  gamma-extend(name, InfoVal(Public, cname, tp, rng, isVar, doc))
// fun inf-gamma/extend-x(ig: gamma, name: name, cname: name, tp: ktype, rng: range, isVar: bool, doc: string)
//   ig.set(name, [InfoVal(Public, cname, tp, rng, isVar, doc)])

// fun inf-gamma-eff/lookup(name: name): <infGammaEff,exn> maybe<(name,ktype)>
//   gamma-lookupx(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))
// fun inf-gamma/lookup(ig: gamma, name: name): exn maybe<(name, ktype)>
//   ig.lookup(name).map(fn(InfoVal(_, cname, tp, _, _)) (cname, tp))

fun inf-gamma/list(ig: gamma): pure list<(name, ktype)>
  ig.list.map(fn((name, InfoVal(typ=tp))) (name, tp))

fun inf-gamma-eff/list()
  gammaGet().list.map(fn((name, InfoVal(typ=tp))) (name, tp))

val inf-gamma/empty: gamma = LinearMap([])

fun (|->)(sub: sub, inf: gamma): pure gamma
  inf.map(fn(k, ni) (k, sub |-> ni))

fun ppgamma(ig: gamma)
  val nameSchemes = ig.gammaList()
  val maxWidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(nice-types([scheme]).head.unjust)
  vcat(nameSchemes.map(fn((n, s))
    fill(n.showPlain.text |.| type-colon().color(colors.colorSep) |+| align(nice(s)), maxWidth)
  ))

fun pretty(ig: gamma)
  // TODO: Add default env to pretty definitions?
  ppgamma(ig)

fun showgamma(ig: gamma)
  pretty(ig).show