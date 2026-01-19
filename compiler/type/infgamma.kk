

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
import std/data/linear-map
// Updated to #cf4024e on 7/13/25

pub infixr 5 (|->)
// inf gamma
// Environment mapping names to type schemes. Due to overloading
// there may be multiple entries for the same name
alias inf-gamma = name-map<list<name-info>>

fun ni/combine(nis: list<name-info>, nis2: list<name-info>): _ list<name-info>
  match nis
    [] -> nis2
    Cons(ni, nis) -> combine(nis, Cons(ni, nis2.filter(fn(ni2) ni.cname != ni2.cname)))

fun inf-gamma/delete(ig: inf-gamma, n : name): inf-gamma
  ig.remove(n)

// TODO: Update
// note: qualified names can get inserted into gamma due to recursive definitions, or
// during inference by inserting fully qualified expressions (in resolveApp-name)
// (if isQualified name then trace ("gamma-extend: insert qualified: " ++ show name) else id) $
// overwrite previous names
fun inf-gamma/extend(ig: inf-gamma, name: name, ni: name-info): _ inf-gamma
  ig.update(name.unqualify-full, [ni], ni/combine)

fun inf-gamma/extends(ig: inf-gamma, tnames: list<(name,ktype,int,string)>)
  tnames.foldl(ig, fn(ig', (name,tp,scope-depth,doc)) ig'.extend-tp(name, name, tp, scope-depth, doc))

fun inf-gamma/extend-tp(ig: inf-gamma, name: name, cname: name, tp: ktype, scope-depth: int, doc: string)
  ig.extend-x(name, cname, tp, scope-depth, range/null, False, doc)

fun inf-gamma/extend-x(ig: inf-gamma, name: name, cname: name, tp: ktype, scope-depth, rng: range, isVar: bool, doc: string)
  ig.extend(name, InfoVal(Public, cname, tp, scope-depth, rng, isVar, False, doc))

// lookup any exact match in the local scope
// note that recursive definitions add the fully qualified name to the infgamma,
// in that case we also consider it an exact match with just the stem.
fun inf-gamma/lookup(ig: inf-gamma, name: name): _ either<list<(name, name-info)>, (name, name-info)>
  match ig.lookup-ex(fn(_) True, name)
    Left([(name', info)]) -> Right((name', info))
    other -> other

// lookup a local name: return either a list of possibly matching (locally qualified) names, or an exact match
fun inf-gamma/lookup-ex(ig: inf-gamma, guard: (name-info) -> bool, name: name): _ either<list<(name, name-info)>, (name, name-info)>
  val mbinfos = ig.map/lookup(name.unqualify-full)
  match mbinfos
    Nothing -> Left([])
    Just(infos) ->
      val lqname = name.requalify-locally
      match infos.filter(fn(info) guard(info) && info.cname == lqname)
        Cons(info, _) -> Right((info.cname, info))
        [] ->
          val matches = infos.filter(fn(info) guard(info) && match-qualifiers(name, info.cname))
          Left(matches.map(fn(info) (info.cname, info)))

fun inf-gamma/map(ig: inf-gamma, f: (ktype) -> _ ktype): _ inf-gamma
  ig.map(fn(a, infos) infos.list/map(fn(i : name-info) i.update-type(f(i.typ))))

fun inf-gamma/union(ig1: inf-gamma, ig2: inf-gamma): _ inf-gamma
  ig1.union-with(ig2, fn(nis1, nis2) ni/combine(nis2, nis1)) // right-biased

fun inf-gamma/unions(igs: list<inf-gamma>): _ inf-gamma
  igs.foldr(inf-gamma/empty, inf-gamma/union)

fun inf-gamma/is-empty(ig: inf-gamma): bool
  ig.internal.is-nil

fun inf-gamma/single(name: name, tp: ktype, scope-depth: int, doc: string): _ inf-gamma
  inf-gamma/empty.extend-tp(name, name, tp, scope-depth, doc)

fun inf-gamma/new(tnames: list<(name,ktype,int,string)>): _ inf-gamma
  inf-gamma/empty.extends(tnames)

fun inf-gamma/list(ig: inf-gamma): _ list<(name, ktype)>
  ig.linear-map/list.flatmap(fn((_, infos)) infos.map(fn(info) (info.cname, info.typ)))

val inf-gamma/empty: inf-gamma = LinearMap([])

fun pp-inf-gamma(ig: inf-gamma)
  val name-schemes = ig.inf-gamma/list()
  val max-width = name-schemes.map(fn((name, _)) name.show.count).maximum(0).min(12)
  fun nice(scheme: ktype)
    align(nice-types([scheme]).head.unjust)
  vcat(name-schemes.map(fn((name, scheme))
    fill(name.show-plain.text |.| type-colon().color(colors.colorSep) |+| align(nice(scheme)), max-width)
  ))

fun infgamma/free-type-vars(ig: inf-gamma): _ tvs
  ig.inf-gamma/list().map(snd).free-type-vars

fun infgamma/bound-type-vars(ig: inf-gamma): _ tvs
  ig.inf-gamma/list().map(snd).bound-type-vars

fun infgamma/free-type-constructors(ig: inf-gamma): _ type-cons
  ig.inf-gamma/list().map(snd).free-type-constructors

fun infgamma/substitute(s: sub, ig: inf-gamma): _ inf-gamma
  ig.inf-gamma/map(fn(tp) s.substitute(tp))