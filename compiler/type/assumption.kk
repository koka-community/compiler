module compiler/type/assumption
// Updated as of 7/23/26: Commit 9bc234e

import compiler/common/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/color-scheme
import compiler/common/name-collections
import compiler/common/failure
import compiler/platform/config
import compiler/type/type
import compiler/type/typevar
import compiler/core/core
import compiler/core/corevar
import compiler/type/pretty
import compiler/common/nice
import compiler/lib/pprint
import std/data/rb-set
import std/os/path
import std/data/sort
import std/data/rb-map
// Updated to #ddac17b on 11/19/25
pub infixr 5 (|->)

pub type name-info
  InfoVal(vis: visibility, cname: name, typ: scheme, scopeDepthX: int, range: range, isVar: bool, allowImplicitMaskX: bool, doc: string)
  InfoFun(vis: visibility, cname: name, typ: scheme, scopeDepthX: int, arity: (int, int), fipt: fipT, range: range, doc: string)
  InfoCon(vis: visibility, typ: scheme, repr: con-repr, conInfo: con-info, range: range, doc: string)
  InfoExternal(vis: visibility, cname: name, typ: scheme, format: string, fipt: fipT, range: range, doc: string)
  InfoImport(vis: visibility, typ: scheme, nameAlias: name, fullName: name, range: range)

pub fun tp/update-type(ni : name-info, tp: scheme): name-info
  match ni
    InfoVal(vis, cname, _, scopeDepthX, range, isVar, allowImplicitMaskX, doc) -> InfoVal(vis, cname, tp, scopeDepthX, range, isVar, allowImplicitMaskX, doc)
    InfoFun(vis, cname, _, scopeDepthX, arity, fipt, range, doc) -> InfoFun(vis, cname, tp, scopeDepthX, arity, fipt, range, doc)
    InfoCon(vis, _, repr, conInfo, range, doc) -> InfoCon(vis, tp, repr, conInfo, range, doc)
    InfoExternal(vis, cname, _, format, fipt, range, doc) -> InfoExternal(vis, cname, tp, format, fipt, range, doc)
    InfoImport(vis, _, nameAlias, fullName, range) -> InfoImport(vis, tp, nameAlias, fullName, range)

// Treat every Private entry as Public. Used for the module currently being
// compiled so its own (private) definitions and generated constructors
// (e.g. `@Hnd-<eff>`) resolve during its own type inference
// (upstream Compile/TypeCheck: `extractGamma isValue True coreProgram`).
pub fun info/private-as-public(ni: name-info): name-info
  match ni
    InfoVal(Private, cname, tp, s, r, iv, aim, doc) -> InfoVal(Public, cname, tp, s, r, iv, aim, doc)
    InfoFun(Private, cname, tp, s, ar, f, r, doc) -> InfoFun(Public, cname, tp, s, ar, f, r, doc)
    InfoCon(Private, tp, repr, ci, r, doc) -> InfoCon(Public, tp, repr, ci, r, doc)
    InfoExternal(Private, cname, tp, fmt, f, r, doc) -> InfoExternal(Public, cname, tp, fmt, f, r, doc)
    InfoImport(Private, tp, na, full, r) -> InfoImport(Public, tp, na, full, r)
    _ -> ni

pub fun gamma/private-as-public(g: gamma): gamma
  g.map(info/private-as-public)

pub fun scheme(ni: name-info): scheme
  match ni
    InfoVal(_, _, typ, _, _, _, _, _) -> typ
    InfoFun(_, _, typ, _, _, _, _, _) -> typ
    InfoCon(_, typ, _, _, _, _) -> typ
    InfoExternal(_, _, typ, _, _, _, _) -> typ
    InfoImport(_, typ, _, _, _) -> typ

pub fun (==)(ni1: name-info, ni2: name-info)
  range/(==)(ni1.range, ni2.range)

pub fun scope-depth(ni: name-info): int
  match ni 
    InfoVal(scopeDepthX = depth) -> depth
    InfoFun(scopeDepthX = depth) -> depth
    _ -> 0

pub fun allow-implicit-mask(ni: name-info): bool
  match ni
    InfoVal(allowImplicitMaskX = allow) -> allow
    _ -> False

pub fun show(ni: name-info): _ string
  match ni
    InfoVal(vis, cname, typ, scope, range, isVar, allowImplicitMask, doc) -> "InfoVal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show(scope) ++ ", " ++ show-full-range(range, "".path) ++ ", " ++ show(isVar) ++ "," ++ show(allowImplicitMask) ++ "," ++  show(doc) ++ ")"
    InfoFun(vis, cname, typ, scope, arity, fipt, range, doc) -> "InfoFun(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show(scope) ++ ", " ++ show-tuple(arity, show, show) ++ ", " ++ show(fipt) ++ ", " ++ show-full-range(range, "".path) ++ "," ++ show(doc) ++ ")"
    InfoCon(vis, typ, repr, conInfo, range, doc) -> "InfoCon(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(repr) ++ ", " ++ show(conInfo) ++ ", " ++ show-full-range(range, "".path) ++ "," ++ show(doc) ++ ")"
    assumption/InfoExternal(vis, cname, typ, format, fipt, range, doc) -> "InfoExternal(" ++ show(vis) ++ ", " ++ show(cname) ++ ", " ++ show(typ) ++ ", " ++ show(format) ++ ", " ++ show(fipt) ++ ", " ++ show-full-range(range, "".path) ++ "," ++ show(doc) ++ ")"
    InfoImport(vis, typ, nameAlias, fullName, range) -> "InfoImport(" ++ show(vis) ++ ", " ++ show(typ) ++ ", " ++ show(nameAlias) ++ ", " ++ show(fullName) ++ ", " ++ show-full-range(range, "".path) ++ ")"

pub fun sort(ni: name-info)
  match ni
    InfoVal -> "val"
    InfoFun -> "fun"
    assumption/InfoExternal -> "external"
    InfoCon -> "con"
    InfoImport -> "module"

pub fun canonical-name(info: name-info, name: name)
  match info
    InfoVal(cname=c) -> c
    InfoFun(cname=c) -> c
    assumption/InfoExternal(cname=c) -> c
    _ -> name

pub fun update-canonical-name(info: name-info, cname: name)
  match info
    InfoVal(vis, _, typ, scopeDepthX, range, isVar, allowImplicitMaskX, doc) -> InfoVal(vis, cname, typ, scopeDepthX, range, isVar, allowImplicitMaskX, doc)
    InfoFun(vis, _, typ, scopeDepthX, arity, fipt, range, doc) -> InfoFun(vis, cname, typ, scopeDepthX, arity, fipt, range, doc)
    assumption/InfoExternal(vis, _, typ, format, fipt, range, doc) -> assumption/InfoExternal(vis, cname, typ, format, fipt, range, doc)
    _ -> info

pub fun cname(info: name-info)
  match info
    InfoVal(cname=c) -> c
    InfoFun(cname=c) -> c
    assumption/InfoExternal(cname=c) -> c
    _ -> throw("type/assumption cname")

pub fun is-info-val-fun-ext(info)
  match info
    InfoVal(_) -> True
    InfoFun(_) -> True
    assumption/InfoExternal(_) -> True
    _ -> False

pub fun is-info-fun-or-external(info)
  match info
    InfoFun(_) -> True
    assumption/InfoExternal(_) -> True
    _ -> False

pub fun doc(info)
  match info
    InfoVal(doc=d) -> d
    InfoFun(doc=d) -> d
    InfoCon(doc=d) -> d
    assumption/InfoExternal(doc=d) -> d
    _ -> ""

pub fun fipT(info: name-info)
  match info
    InfoFun(fipt=fipt) -> fipt
    assumption/InfoExternal(fipt=fipt) -> fipt
    _ -> noFip

pub fun element(info: name-info)
  match info
    InfoCon() -> "constructor"
    InfoImport() -> "import"
    _ -> "identifier"

pub fun is-visible(info: name-info)
  info.vis.is-public

pub fun core-var-info(info: name-info)
  match info
    InfoVal -> InfoNone
    InfoFun(arity=(m,n)) -> InfoArity(m, n)
    assumption/InfoExternal(format=f) -> compiler/core/core/InfoExternal(f)

pub fun core-expr(info: name-info, qname: name)
  match info
    InfoVal(_, cname, tp) -> Var(TName(cname, tp), InfoNone)
    InfoFun(_, cname, tp, _, (m, n), _) -> Var(TName(cname, tp), InfoArity(m ,n))
    InfoCon(_, tp, repr) -> Con(TName(qname, tp), repr)
    assumption/InfoExternal(_, cname, tp, format) -> Var(TName(cname, tp), compiler/core/core/InfoExternal(format))
    _ -> impossible()

// Names to type schemes.
// Due to overloading there may be multiple entries for the same qualified name

pub alias gamma = name-map<list<(name, name-info)>>
pub val empty:gamma = rb-map/empty()

pub fun schemes(g: gamma): list<scheme>
  g.assumption/list.map(_.snd.typ)

pub fun single(name: name, ni: name-info)
  rb-map/set(assumption/empty, name, [(name, ni)])

pub fun gamma/new(xs: list<(name, name-info)>): gamma
  extends(empty, xs)

pub fun extends(g: gamma, ls: list<(name,name-info)>): gamma
  ls.foldl(g, fn(m, (name,tp)) m.extend(name, tp))

pub fun extend(g: gamma, name: name, ni: name-info)
  // note: linear-map update calls f(old, new); upstream `M.insertWith combine key [new] old`
  // computes `new ++ old` — the NEW entry comes first
  rb-map/update(g, name.unqualify-full, [(name, ni)], fn(old:list<_>, new) new ++ old) // TODO: Check for overlapping type schemes?

// a single-entry gamma keyed by the full stem
pub fun gamma/single(name: name, ni: name-info): gamma
  empty.extend(name, ni)

// Diagnostic: every entry sharing this name's unqualified stem, with full
// qualifiers, so a failed lookup can show HOW the stored names differ from
// the requested one (module vs local qualifier splits are easy to get wrong).
pub fun lookup-candidates(g: gamma, name: name): list<name>
  match g.lookup(name.unqualify-full)
    Nothing -> []
    Just(xs) -> xs.map(fst)

pub fun lookup-canonical(g: gamma, name: name)
  g.lookupQ(name).filter(_.canonical-name(nil) == name)

pub fun lookup-exact-con(g: gamma, name: name)
  g.lookupQ(name).filter(is-infoCon)

// Return exactly matching qualified names
pub fun lookupQ(g: gamma, name: name)
  match g.lookup(name.unqualify-full)
    Nothing -> []
    Just(xs) -> xs.filter(_.fst == name).map(snd)

// @lookup name gamma@ looks up a potentially (partially) qualified name and returns all matches.
pub fun gamma-lookup(g: gamma, name: name)
  val stem-name = name.unqualify-full
  match g.lookup(stem-name)
    Nothing -> []
    Just(candidates0) ->
      val candidates1 = candidates0.filter(fn((_, i)) i.is-visible)
      if stem-name == name then candidates1 // Fast path for unqualified names
      else
        val qpaths = name.split-rev-qualifiers
        candidates1.filter(fn((n,_)) match-rev-qualifier-paths(qpaths, n.split-rev-qualifiers))

// Given a user qualified name, see if the qualifiers match a resolved name.
// The user qualified name has already been de-aliased in kind inference (see `Kind/ImportMap/importsExpand`)
// Note that the user qualified name might not distinguish local qualification from module qualification,
// e.g. `std/core/int/show` vs  `std/core/#int/show`.
// ambiguities may occur, where `std/num/float32/foo` should match both `std/num/#float32/foo` and `std/num/float32/#foo`
pub fun match-qualifiers(uname: name, name: name)
  match-rev-qualifier-paths(uname.split-rev-qualifiers, name.split-rev-qualifiers)

pub fun match-rev-qualifier-paths(upaths: (list<string>,list<string>), paths: (list<string>,list<string>)): bool
  match (upaths, paths)
    (([], []), _) -> True // not qualified
    ((umpath, []), (mpath, [])) -> umpath.list/is-prefix-of(mpath) // no user specified local path
    ((umpath, []), (mpath, lpath)) -> // not (null lpath)
      umpath.list/is-prefix-of(lpath) || // user module is a postfix the local qualifier
      lpath.list/is-prefix-of(umpath) && umpath.drop(lpath.length).list/is-prefix-of(mpath) // stradle both
    ((umpath, ulpath), (mpath, lpath)) -> // not (null ulpath)
      match umpath
        [] -> ulpath.list/is-prefix-of(lpath)
        _ -> ulpath == lpath && umpath.list/is-prefix-of(mpath)

// Split out the module and local qualifier as a _reverse_ list of components
// e.g. `std/core/#int/show` -> (["core","std"],["int"])
pub fun split-rev-qualifiers(name: name): (list<string>, list<string>)
  val mpath = name.split-module-name.reverse
  val lpath = name.split-local-qual-name.reverse
  (mpath, lpath)

pub fun lookup-prefix(g: gamma, name: name): list<(name, name-info)>
  val pre = name.unqualify.show-plain ++ "_"
  fun is-prefix(nm: name)
    nm == name || nm.name/name/starts-with(pre)
  g.filter(fn(n, ni) n.is-prefix).values.concat.filter(fn((_, ni)) ni.is-visible)

pub fun map(g: gamma, f: (name-info -> name-info)): gamma
  g.map(fn(k, xs) xs.list/map(fn((n, ni)) (n, f(ni))))

pub fun list(g: gamma): list<(name, name-info)>
  rb-map/list(g).map(snd).concat.sort(?(<)=fn((n, _), (n2, _)) n.name/name/cmp(n2).is-lt)

pub fun remove(g: gamma, name: name)
  rb-map/remove(g, name.unqualify)

pub fun union(g1: gamma, g2: gamma)
  rb-map/union-with(g2, g1, fn(xs1: list<_>, xs2) xs1 ++ xs2)

pub fun unions(gs: list<gamma>)
  // O(n log n) key-sorted merge instead of the O(n^2) `foldl union` (which is a
  // hot path when combining the ~40 stdlib module gammas in defs-from-modules).
  // `union(g1,g2) = g2.union-with(g1, ++)` puts g2's entries first for a shared
  // key, so unions-with (which orders later maps first) reproduces the same order.
  rb-map/unions-with(gs, fn(xs1: list<_>, xs2) xs1 ++ xs2)

// Filter out signature belonging to a module
pub fun filter(g: gamma, mod: name)
  g.filter(fn(k, _) k.qualifier == mod)

pub fun names(g: gamma)
  g.keys

pub fun public-names(g: gamma)
  g.filter(fn(n, nis) !n.is-hidden-name && nis.all(fn((_, ni)) ni.is-visible)).keys

// Extract from core
pub fun extract-gamma-imports(imports: list<(name,name)>, modName: name): gamma
  val modAlias = modName //.nameStem.list.reverse.take-while(_ != '.').reverse.string.new-name
  imports.map(extract-import).assumption/unions.extend(modAlias, InfoImport(Private, typeVoid, modAlias, modName, null))

pub fun extract-import((name, qname))
  gamma/single(name, InfoImport(Private, typeVoid, name, qname, null))

// Extract a Gamma from a Core module
pub fun extract-gamma(isValue: (data-info -> bool), privateAsPublic: bool, c: core): _ gamma
  fun update-vis(vis)
    match vis
      Public -> Public
      _ -> if privateAsPublic then Public else vis
  assumption/unions([
    c.defs.map(_.extract-def-group(update-vis)).assumption/unions,
    c.externals.map(_.extract-external(update-vis)).assumption/unions,
    c.typedefs.map(_.extract-type-def-group(isValue, update-vis)).assumption/unions
  ])

fun extract-type-def-group(td: typedef-group, isValue: (data-info -> bool), update-vis)
  td.map(extract-type-def(isValue, update-vis, _)).assumption/unions

fun extract-type-def(isValue: (data-info -> bool), update-vis, td: typedef)
  fun extract-con-info((info, repr): (con-info, con-repr))
    gamma/single(info.name, InfoCon(update-vis(info.vis), info.typeScheme, repr, info, info.range, info.doc))
  match td
    Data(dataInfo) -> zip(dataInfo.constrs, dataInfo.data-repr(isValue).snd).map(extract-con-info).assumption/unions
    _ -> assumption/empty

fun extract-def-group(d: def-group, update-vis)
  match d
    DefRec(defs) -> defs.map(extract-def(_, update-vis)).assumption/unions
    DefNonRec(v) -> extract-def(v, update-vis)

fun extract-def(d: def, update-vis)
  gamma/single(d.def-name, create-name-infoX(update-vis(d.vis), d.def-name, 0, d.sort, d.nameRange, d.ktype, d.doc)) // specials since we cannot call isTopLevel as in coreDefInfo

pub fun core-def-info(d: def, scopeDepth)
  (d.def-name, create-name-infoX(d.vis, d.def-name, scopeDepth, if d.sort.is-defFun && !d.is-top-level then DefVal else d.sort, d.nameRange, d.ktype, d.doc))
// since we use coreDefInfo also for local definitions, we need to be careful to to use DefFun for
// things that do not get lifted to toplevel due to free type/variables. test: codegen/rec5

pub fun create-name-info(name, scopeDepth, is-val, rng, tp, doc)
  create-name-infoX(Public, name, scopeDepth, if is-val then DefVal else DefFun([]), rng, tp, doc)

pub fun create-name-infoX(vis, name, scopeDepth: int, sort, rng, tp, doc)
  create-name-infoEX(vis, name, scopeDepth, sort, False, rng, tp, doc)

pub fun create-name-infoEX(vis, name, scopeDepth: int, sort, allowImplicitMask, rng, tp, doc)
  val d = if scopeDepth == 0 && name.is-in-default-namespace then -1 else scopeDepth
  match sort
    DefFun(_, fipT) -> InfoFun(vis, name, tp, d, tp.arity, fipT, rng, doc)
    DefVar -> InfoVal(vis, name, tp, d, rng, True, False, doc)
    _ -> InfoVal(vis, name, tp, d, rng, False, allowImplicitMask, doc)

pub fun arity(tp: ktype): _ (int, int)
  match tp.expand-syn
    TForAll(tvars, t) ->
      match t.expand-syn
        TFun(pars) -> (tvars.length, pars.length)
        _ -> (tvars.length, -1)
    TFun(pars) -> (0, pars.length)

pub fun extract-external(external: external, update-vis)
  match external
    External(name, tp, _, body, vis, fipT, nameRng, doc) ->
      gamma/single(name, InfoExternal(update-vis(vis), name, tp, body, fipT, nameRng, doc))
    _ -> assumption/empty

// TODO: ftc
// Instances

pub fun gamma/substitute(sub: sub, g: gamma): _ gamma
  g.map(fn(n, nis) nis.list/map(fn((n1, ni: name-info)) (n1, sub.substitute(ni))))

pub fun gamma/free-type-vars(g: gamma): _ tvs
  g.schemes.map(free-type-vars).unions

pub fun gamma/bound-type-vars(g: gamma): _ tvs
  g.schemes.map(bound-type-vars).unions

pub fun ni/substitute(sub: sub, ni: name-info): _ name-info
  ni.map-type(sub |-> _)

pub fun ni/free-type-vars(info: name-info): _ tvs
  info.typ.free-type-vars

pub fun ni/bound-type-vars(info: name-info): _ tvs
  info.typ.bound-type-vars

pub fun map-type(ni: name-info, f: (ktype) -> e ktype): e name-info
  match ni
    InfoVal(vis, cname, typ, depth, range, isVar, allowMask, doc) -> InfoVal(vis, cname, f(typ), depth, range, isVar, allowMask, doc)
    InfoFun(vis, cname, typ, depth, arity, fipt, range, doc) -> InfoFun(vis, cname, f(typ), depth, arity, fipt, range, doc)
    InfoCon(vis, typ, repr, conInfo, range, doc) -> InfoCon(vis, f(typ), repr, conInfo, range, doc)
    assumption/InfoExternal(vis, cname, typ, format, fipt, range, doc) -> assumption/InfoExternal(vis, cname, f(typ), format, fipt, range, doc)
    InfoImport(vis, typ, nameAlias, fullName, range) -> InfoImport(vis, f(typ), nameAlias, fullName, range)

fun pp-gamma-internal(g: gamma, showHidden: bool)
  // upstream `gammaList` sorts by `compare (show n1) (show n2)` where Name's
  // Show is `showExplicit` (operators wrapped in parens, `/#` before a local
  // qualifier) -- the port's `name/show` is exactly that, so sorting by
  // `show` reproduces upstream's exact ordering (e.g. `#`-qualified locals
  // first, then `(op)`s, then capitalized constructors, then lowercase)
  val nameSchemes = g.assumption/list.filter(fn((_, i)) !i.is-infoImport).map(fn((n, i)) (n, i.typ))
                     .sort(fn((n1, _), (n2, _)) n1.show < n2.show)
  val maxWidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  // upstream calls `niceTypes` fresh per scheme (nice-naming isn't threaded
  // across the whole listing -- each entry's quantified vars start at 'a'
  // again), so install a fresh nice-env per item rather than relying on
  // whatever ambient one the caller installed
  fun nice(scheme: ktype)
    with nice-env
    align(nice-types([scheme]).head.unjust)
  vcat(nameSchemes.filter(fn((n, _)) showHidden || !n.is-hidden-name).map(fn((n, s))
    // `fill` pads only the bare NAME, not name+colon together, and prettyName
    // (the port's `pretty-name`) wraps operators in parens (`(>>=)`) and
    // prefixes implicit-parameter names with `?`
    fill(pretty-name(n, colors), maxWidth) |.| type-colon().color(colors.colorSep) |+| align(nice(s)) // TODO: Tim new color?
  ))

pub fun pp-gamma(g: gamma)
  pp-gamma-internal(g, False)

pub fun pp-gamma-hidden(g: gamma)
  pp-gamma-internal(g, True)

pub fun pretty(g: gamma): _ doc
  pp-gamma(g)

pub fun show-gamma(g: gamma): _ string
  pretty(g).show