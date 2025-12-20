

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
fun inf-gamma/extends(ig: infGamma, tnames: list<(name,ktype,int,string)>)
  tnames.foldl(ig, fn(ig', (name,tp,scope-depth,doc)) ig'.extend-tp(name, name, tp, scope-depth, doc))

fun inf-gamma-eff/extend-tp(name: name, cname: name, tp: ktype, scope-depth: int, doc: string)
  extend-x(name, cname, tp, scope-depth, range/null, False, doc)
fun inf-gamma/extend-tp(ig: infGamma, name: name, cname: name, tp: ktype, scope-depth: int, doc: string)
  ig.extend-x(name, cname, tp, scope-depth, range/null, False, doc)

fun inf-gamma-eff/extend-x(name: name, cname: name, tp: ktype, scope-depth, rng: range, isVar: bool, doc: string)
  gamma-extend(name, InfoVal(Public, cname, tp, scope-depth, rng, isVar, False, doc))
fun inf-gamma/extend-x(ig: infGamma, name: name, cname: name, tp: ktype, scope-depth, rng: range, isVar: bool, doc: string)
  ig.extend(name, InfoVal(Public, cname, tp, scope-depth, rng, isVar, False, doc))

// Lookup any exact match in the local scope
// Note that recursive definitions add the fully qualified name to the infgamma,
// in that case we also consider it an exact match with just the stem.

fun inf-gamma/list(ig: infGamma): pure list<(name, ktype)>
  ig.linearmap/list.flatmap(fn((_, infos)) infos.map(fn(info) (info.cname, info.typ)))
    
fun inf-gamma-list()
  gamma-get().inf-gamma/list

val inf-gamma/empty: infGamma = LinearMap([])

fun pp-inf-gamma(ig: infGamma)
  val name-schemes = ig.inf-gamma/list()
  val max-width = name-schemes.map(fn((name, _)) name.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(nice-types([scheme]).head.unjust)
  vcat(name-schemes.map(fn((name, scheme))
    fill(name.show-plain.text |.| type-colon().color(colors.colorSep) |+| align(nice(scheme)), max-width)
  ))

fun infgamma/free-type-vars(ig: infGamma): pure tvs
  ig.inf-gamma/list().map(snd).free-type-vars

fun infgamma/bound-type-vars(ig: infGamma): pure tvs
  ig.inf-gamma/list().map(snd).bound-type-vars

fun infgamma/free-type-constructors(ig: infGamma): pure typeCons
  ig.inf-gamma/list().map(snd).free-type-constructors
