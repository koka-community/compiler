import compiler/common/name
import compiler/common/name-collections
import compiler/common/range
import compiler/common/syntax
import compiler/syntax/syntax
import compiler/lib/scc
import std/data/linear-set
import std/data/linear-map
// Updated 7/12/25; Commit #752748d

effect val modname: name
// Program
fun program/group-bindings(program: user-program)
  with val modname = program.name
  program(typedefs=program.typedefs.group-bindings, defs=program.defs.group-bindings)

// Binding groups in type definitions
fun typedefs/group-bindings(tdGroups: list<user-typedef-group>)
  val (ds, extends) = tdGroups.flatten.partition(is-definition)
  ds.group(emptyDeps + ds.map(dependencies)) ++ extends.map(TypeDefNonRec)

fun flatten(grps: list<user-typedef-group>)
  val xs = grps.map fn(g)
    match g
      TypeDefRec(tds) -> tds
      TypeDefNonRec(td) -> [td]
  xs.concat

fun is-definition(td: user-typedef)
  match td
    DataType(ddef=ddef) -> !ddef.is-extend
    _ -> True

fun normalize(n: name)
  if n.qualifier == modname then n.unqualify else n

fun typedef/dependencies(td: user-typedef): _ (name, name-set)
  match td
    Synonym(_, _, t) -> (td.name, t.free-types.list.map(normalize).linear-set)
    DataType(_, _, c) -> (td.name, c.free-types.list.map(normalize).linear-set)

// Free type constructors
fun list/free-types(l: list<t>, ?free-types: (t) -> _ name-set): _ name-set
  l.map(free-types).unions

fun ktp/free-types(tp: user-type): _ name-set
  match tp
    TpQuan(_, _, t) -> t.free-types
    TpFun(args, eff, t) -> args.map(snd).free-types + eff.free-types + t.free-types
    TpApp(t, args) -> Cons(t, args).free-types
    TpVar -> names/empty
    TpCon(nm) -> LinearSet([]) + nm
    TpParens(t) -> t.free-types
    TpAnn(t) -> t.free-types

fun vb/free-types(vb: value-binder<t,e>, ?free-types: (t) -> pure name-set): pure name-set
  vb.binderType.free-types

fun uc/free-types(c: user-con<t,u,k>, ?free-types: (t) -> pure name-set): pure name-set
  c.params.map(snd).free-types + c.result.map(free-types).default(empty)

// Binding groups in definitions
fun defgroups/group-bindings(dgs: list<def-group<t>>): _ list<def-group<t>>
  val (defs0, deps0) = dgs.map(group-bindings).unzip
  val defs = defs0.concat
  val deps1 = deps0.unions
  val extraDefs = dgs.extract
  fun extend-name(defName: name, n: name)
    match extraDefs.lookup(n.unqualify)
      Just(extra) -> extra
      Nothing -> []
  fun extend(def-name: name, ndeps: name-set)
    ndeps.union(ndeps.list.flatmap(extend-name(def-name, _)).linear-set)
  val deps = deps1.map(fn(k, v) extend(k, v))
  group-bindings(defs, deps)

alias extraDeps = name-map<list<name>>; // maps base names (`eq`) to internally qualified names (`int/eq`, `char/eq`)

fun def-groups/extract(dgs: list<def-group<t>>): exn extraDeps
  dgs.map(ee).unions

fun defgroup/ee(d0: def-group<t>): exn extraDeps
  match d0
    DefNonRec(d) -> d.def/ee
    DefRec(defs) -> defs.map(def/ee).unions

fun def/ee(d: def<t>): extraDeps
  val nm = d.binder.name
  if nm.is-locally-qualified then LinearMap([(nm.unqualify-full, [nm])])
  else LinearMap([])

fun defgroup/group-bindings(g: def-group<t>): _ (list<def<t>>, deps)
  match g
    DefNonRec(d) ->
      val (d', deps) = d.def/dependencies
      ([d'], deps)
    DefRec(defs) -> 
      defs.dependencies

fun udefs/dependencies(defs: list<def<t>>): _ (list<def<t>>, deps)
  val (defDeps, depss) = defs.map(def/dependencies).unzip
  (defDeps, depss.unions)

fun def/dependencies(d: def<t>): _ (def<t>, deps)
  val (depBinding, deps) = d.binder.dependencies
  (d(binder=depBinding), deps)

fun binding/dependencies(vb: value-binder<(), expr<t>>): _ (value-binder<(), expr<t>>, deps)
  val (depExpr, free-var) = vb.expr.dependencies
  (vb(expr=depExpr), emptyDeps.add(vb.name, free-var))

fun fv/dependencies(d: def<t>): _ (def<t>, name-set)
  val (depDef, deps) = d.def/dependencies
  (depDef, deps.list.map(snd).unions)

fun groupfv/dependencies(dg: def-group<t>): _ (list<def-group<t>>, name-set, name-set)
  val (defs, deps) = dg.group-bindings
  val names = defs.map(_.binder.name).linear-set
  val free-vars = deps.list.map(snd).unions - names
  (defs.group-bindings(deps), free-vars, names)

fun mbexpr/dependencies(mex: maybe<expr<t>>): _ (maybe<expr<t>>, name-set)
  match mex
    Just(ex) ->
      val (ex', deps) = ex.dependencies
      (Just(ex'), deps)
    Nothing -> (Nothing, names/empty)

fun expr/dependencies(ex: expr<t>): _ (expr<t>, name-set)
  match ex
    Lam(binders, body, tl, rng) ->
      val (depBody, fv1) = body.dependencies
      val (binders', fv2) = binders.dependencies(fv1)
      (Lam(binders', depBody, tl, rng), fv2)
    Bind(def, body, rng) ->
      val (depDef, fv1) = def.fv/dependencies
      val (depBody, fv2) = body.dependencies
      (Bind(depDef, depBody, rng), fv1 + (fv2 - def.name))
    Let(dgrp, body, rng) ->
      val (depGroups, fv1, names) = dgrp.groupfv/dependencies
      val (depBody, fv2) = body.dependencies
      (depGroups.foldr(depBody, fn(g, l) Let(g, l, rng)), fv1 + (fv2 - names))
    Var(name) ->
      val uname = name.unqualify
      if uname.is-constructor-name then
        (ex, names/empty + uname + uname.new-creator-name)
      else
        (ex, names/empty + uname + uname.to-value-operation-name)
    App(f, nargs, rng) ->
      val (depF, fv1) = f.dependencies
      val (argNames, args) = nargs.unzip
      val (depArgs, fv2s) = args.map(dependencies).unzip
      val fv2 = fv2s.unions
      (App(depF, argNames.zip(depArgs), rng), fv1 + fv2)
    Ann(e, t, rng) ->
      val (depE, fv1) = e.dependencies
      (Ann(depE, t, rng), fv1)
    Case(e, brnches, lzy, rng) ->
      val (depE, fv1) = e.dependencies
      val (depBranches, fv2) = brnches.map(dependencies).unzip
      (Case(depE, depBranches, lzy, rng), fv1 + fv2.unions)
    Parens(e, nm, pre, rng) ->
      val (depE, fv) = e.dependencies
      (Parens(depE, nm, pre, rng), fv)
    Literal ->
      (ex, names/empty)
    Handler(shallow, scoped, over, allowMask, eff, pars, reinit, ret, fin, ops, hrng, rng) ->
      val (depRet, fv1) = ret.dependencies
      val (depBranches, fv2) = ops.map(dependencies).unzip
      val (depReinit, fv3) = reinit.dependencies
      val (depFin, fv4) = fin.dependencies
      val fvs = (fv1 + fv2.unions + fv3 + fv4) - (names/empty + pars.map(name))
      (Handler(shallow, scoped, over, allowMask, eff, pars, depReinit, depRet, depFin, depBranches, hrng, rng), fvs)
    Inject(tp, body, b, rng) ->
      val (depBody, fv) = body.dependencies
      (Inject(tp, depBody, b, rng), fv)

fun handler-branch/dependencies(h: handler-branch<t>): _ (handler-branch<t>, name-set)
  val (depExpr, fvExpr) = h.branchExpr.dependencies
  val uname = if h.branchName.qualifier == modname then h.branchName.unqualify else h.branchName
  (h(branchExpr=depExpr), (fvExpr - h.branchPars.map(name)) + uname)

fun branch/dependencies(Branch(patts, guards): branch<t>): _ (branch<t>, name-set)
  val (depGuards, fvGuardss) = guards.map(dependencies).unzip
  val fvsg : name-set = fvGuardss.unions
  (Branch(patts, depGuards), fvsg - patts.free-var)

fun guard/dependencies(Guard(test, expr): guard<t>): _ (guard<t>, name-set)
  val (depTest, fv1) = test.dependencies
  val (depExpr, fv2) = expr.dependencies
  (Guard(depTest, depExpr), fv1 + fv2)

fun lambinders/dependencies(binders: list<value-binder<maybe<t>, maybe<expr<t>>>>, fvs: name-set): _ (list<value-binder<maybe<t>, maybe<expr<t>>>>, name-set)
  match binders
    Nil -> (Nil, fvs)
    Cons(binder, rest) ->
      val (binders0, fv0) = rest.dependencies(fvs)
      val fv1 = fv0 - binder.name
      match binder.expr
        Nothing -> (Cons(binder, binders0), fv1)
        Just(ex) ->
          val (depEx, fv2) = ex.dependencies
          (Cons(binder(expr=Just(depEx)), binders0), fv1 + fv2)

fun lambinder/dependencies(binder: value-binder<maybe<t>, maybe<expr<t>>>): _ (value-binder<maybe<t>, maybe<expr<t>>>, name-set)
  match binder.expr
    Nothing -> (binder, names/empty)
    Just(ex) ->
      val (depEx, fv) = ex.dependencies
      (binder(expr=Just(depEx)), fv)


// Free variables

fun list/free-var(l: list<t>, ?free-var: (t) -> pure name-set): pure name-set
  l.map(?free-var).unions

fun maybe/free-var(mex: maybe<t>, ?free-var: (t) -> pure name-set): pure name-set
  match mex
    Just(ex) -> ex.free-var
    Nothing -> names/empty

fun pat/free-var(pat: pattern<t>): pure name-set
  match pat
    PatVar(binder) -> names/empty + binder.name
    PatCon(_, pats) -> pats.map(snd).map(free-var).unions
    PatParens(p) -> p.free-var
    PatAnn(p, _) -> p.free-var
    PatLit(_) -> names/empty
    PatWild -> names/empty

fun expr/free-var(ex: expr<t>): pure name-set
  match ex
    Lam(binders, body) -> binders.foldr(body.free-var, fn(b, fv) fv - b.name)
    Bind(def, bd) -> bd.free-var - def.name + def.body.free-var
    Let(group, body) ->
      val (fv, bound) = group.free-bound-var
      body.free-var - bound + fv
    Var(name) -> if name.is-constructor-name then names/empty else names/empty + name
    App(f, nargs) -> Cons(f, nargs.map(snd)).free-var
    Ann(e) -> e.free-var
    Case(e, brnches) -> e.free-var + brnches.map(free-var).unions
    Parens(e) -> e.free-var
    Literal -> names/empty
    Inject(_, body) -> body.free-var
    Handler(branches=ops, hReturn=ret, initially=init, finally=fin, localPars=pars) ->
      ret.free-var + ops.map(free-var).unions + init.free-var + fin.free-var - pars.map(name)

fun branch/free-var(Branch(patt, guards): branch<t>): pure name-set
  patt.free-var + guards.map(free-var).unions

fun guard/free-var(Guard(test, expr): guard<t>): pure name-set
  test.free-var + expr.free-var

fun hb/free-var(HandlerBranch(_, pars, expr): handler-branch<t>): pure name-set
  expr.free-var - pars.map(name)

fun dg/free-bound-var(dg: def-group<t>): pure (name-set, name-set)
  match dg
    DefNonRec(d) -> (names/empty + d.name, d.body.free-var)
    DefRec(defs) ->
      val bound = defs.map(name)
      val free = defs.map(_.body.free-var).unions
      (names/empty + bound, free - bound)

// Dependencies
alias deps = name-map<name-set>
alias free-var = name-set
val emptyDeps: linear-map<name, name-set> = LinearMap([])

// Topological sort

fun dfs/group-bindings(defs: list<def<t>>, deps: deps): pure list<def-group<t>>
  // get definition id's
  val defVars = names/empty + deps.list.map(fst)
  // constrain to the current group of id's
  val defDeps = deps.map(fn(k, fvs) fvs.intersection(defVars))
  // determine strongly connected components
  val defDepsList = defs.flatmap fn(def) 
    match defDeps.lookup(def.name)
      Just(fvs) -> [(def, fvs.list)]
      Nothing -> []
  
  val defOrderScc = scc(defDepsList.map(fn((d, ddeps)) (d.name, ddeps)))

  // create a map from definition id's to definitions
  val defMap = defs.map(fn(d) (d.name, [d])).foldl(LinearMap([])) fn(acc, (id, v))
    acc.update(id, v, fn(old: list<_>, new) old ++ new)

  // try to maintain original source order as much as possible
  // reorder the `defOrderScc` according to the (earliest) source line (of a recursive group)
  // without violating explicit dependencies. Regardless of the particular dependency order
  // returned by the `scc` algorithm (as dependency order is partial), this should always
  // result in the same canonical order (essentially making the ordering total using source lines
  // as a tie breaker). This is important since at this point in the compilation we cannot
  // yet resolve names fully:
  // 1. We may overestimate dependencies: a name like `foo` may refer to a locally qualified
  //    name `int/foo` or `bool/foo` and we don't know until type checking and assume
  //    it might refer to either one.
  // 2. We may not see all dependencies: implicit parameters are resolved at type checking
  //    and may introduce dependencies that we cannot determine yet. As a programmer, we
  //    can ensure the correct order by putting such implicit dependencies first in the source.
  fun get-line(id: name)
    defMap.find(id).map(_.range.start.line)
  fun line-of(ids: list<name>)
    match ids.flatmap(get-line)
      [] -> 0
      ls -> minimum(ls)
      
  fun insert(rdefs: list<list<name>>, idgrp: list<name>): pure list<list<name>>
    // insert `idgrp` into the reverse definitions (from most to least dependent)
    val n = line-of(idgrp)
    val idgrp-deps = idgrp.map(defDeps.find(_)).unions
    fun goes-after(x: list<name>) // don't go beyond source order
      n < x.line-of && !x.any(idgrp-deps.member(_))
    val (pre, post) = rdefs.span(goes-after)
    pre ++ Cons(idgrp, post)

  val defOrder =
    // in dependency order (from least to most)
    // fold from least to most dependent, creating a list from most to least dependent
    // and reverse to go from least to most dependent
    defOrderScc.foldl([], insert).reverse 
  
  // create a definition group from a list of mutual recursive identifiers
  fun make-group(ids:list<name>)
    match ids
      [id] -> 
        if defDeps.find(id).member(id) then
          [DefRec(defMap.get(id))]
        else
          defMap.get(id).map(DefNonRec)
      _ -> [DefRec(ids.map(defMap.get(_)).concat)]
  
  defOrder.map(make-group).concat

fun typedefs/group(tdefs: list<user-typedef>, deps: deps)
  // get type names
  val typeNames = names/empty + deps.list.map(fst)
  // constrain to current group of ids
  val typeDeps0 = deps.list.map(fn((k, fts)) (k, fts.intersection(typeNames).list))
  // determine strongly connected components
  val typeOrder0 = scc(typeDeps0)
  // create a map from type id's to type defs
  // note: due to duplicate definitions (which are checked for during kind checking), we map to a list of possible definitions
  val typeMap = tdefs.map(fn(d) (d.name, [d])).foldl(LinearMap([])) fn(acc, (id, v))
    acc.update(id, v, fn(old:list<user-typedef>, new) old ++ new)
  // create a (recursive) definition group
  fun make-group(ids: list<name>)
    match ids
      [id] ->
        if typeDeps0.find(fn((k, _)) k == id).map(snd).default([]).any(_ == id) then
          [TypeDefRec(typeMap.get(id))]
        else
          typeMap.get(id).map(TypeDefNonRec)
      _ -> [TypeDefRec(ids.map(typeMap.get(_)).concat)]
  typeOrder0.map(make-group).concat

    

// As a tribute to Doaitse Swierstra, let's leave in this code which
// was from a time when we used the Attribute Grammar system from
// Doaitse developed at the University of Utrecht.

// {--------------------------------------------------------------------
//   Group
// --------------------------------------------------------------------}
// ATTR Program TypeDefs TypeDef Def Defs Expr Pattern Lit
//      Exprs Patterns Branch Branches
//      UserType UserTypes UserKindScheme UserKind
//      Externals External
//      FixDefs FixDef
//       [ || grouped : SELF ]


// ATTR DefGroup  [ || grouped : DefGroups]
// ATTR DefGroups [ || grouped USE {++} {[]}: DefGroups]

// SEM DefGroup
//   | DefNonRec lhs.grouped = [DefNonRec @def.grouped]
//   | DefRec    lhs.grouped = group @defs.grouped @defs.deps


// ATTR TypeDefGroup  [ || grouped : TypeDefGroups]
// ATTR TypeDefGroups [ || grouped USE {++} {[]}: TypeDefGroups]

// SEM TypeDefGroup
//   | TypeDefGroup lhs.grouped = group-typedefs @typedefs.grouped @typedefs.deps


// {
// group :: Defs -> Deps -> DefGroups
// group defs deps
//   = let -- get definition id's
//         defVars  = S.fromList (M.keys deps)
//         -- constrain to the current group of id's
//         defDeps  = M.map (\fvs -> S.intersection defVars fvs) deps
//         -- determine strongly connected components
//         defOrder = scc [(id,S.toList fvs) | (id,fvs) <- M.toList defDeps]
//         -- create a map from definition id's to definitions.
//         defMap   = M.fromList [(def-name def,def) | def <- defs]
//         -- create a definition group from a list of mutual recursive identifiers.
//         make-group ids  = case ids of
//                            [id] -> if S.member id (M.find id defDeps)
//                                     then DefRec [M.find id defMap]
//                                     else DefNonRec (M.find id defMap)
//                            _    -> DefRec [M.find id defMap | id <- ids]
//     in map make-group defOrder

// group-typedefs :: TypeDefs -> Deps -> TypeDefGroups
// group-typedefs typedefs deps
//   = let -- get type names
//         typeNames = S.fromList (M.keys deps)
//         -- constrain to current group of id's
//         typeDeps  = M.map (\fts -> S.intersection typeNames fts) deps
//         -- determine strongly connected components
//         typeOrder = scc [(id,S.toList fts) | (id,fts) <- M.toList typeDeps]
//         -- create a map from type id's to type defs
//         typeMap   = M.fromList [(typedefName def,def) | def <- typedefs]
//         -- create a (recursive) definition group
//         make-group ids = TypeDefGroup [M.find id typeMap | id <- ids]
//     in map make-group typeOrder
// }

// {
// --------------------------------------------------------------------
//   Dependencies
// --------------------------------------------------------------------}
// {
// type Deps = M.NameMap S.NameSet
// }

// ATTR TypeDef TypeDefs Def Defs [ || deps USE {`M.union`} {M.empty} : Deps ]

// SEM Def
//   | Def   lhs.deps  = M.single @name @body.free-var

// SEM TypeDef
//   | Synonym lhs.deps = M.single @name @tp.free-types
//   | Newtype lhs.deps = M.single @name @tp.free-types

// {--------------------------------------------------------------------
//   Free variables (and defined variables)
// --------------------------------------------------------------------}
// ATTR DefGroups DefGroup Defs Def Expr Exprs Branch Branches    [ || free-var USE {`S.union`}{S.empty} : {S.NameSet} ]
// ATTR DefGroups DefGroup Defs Def Pattern Patterns  [ || defVar USE {`S.union`}{S.empty} : {S.NameSet} ]

// SEM DefGroup
//   | DefRec    lhs.free-var = S.difference @defs.free-var @defs.defVar
//   | DefNonRec lhs.free-var = S.difference @def.free-var @def.defVar     -- paranoia :-)

// SEM Def
//   | Def     lhs.defVar  = S.single @name

// SEM Expr
//   | Lam     lhs.free-var = S.difference @body.free-var @pat.defVar
//   | Let     lhs.free-var = S.union @defs.free-var (S.difference @body.free-var @defs.defVar)
//   | Var     lhs.free-var = S.single @name

// SEM Branch
//   | Branch  lhs.free-var = S.difference (S.union @guard.free-var @expr.free-var) @pats.defVar

// SEM Pattern
//   | PatVar  lhs.defVar  = S.single @name

// {--------------------------------------------------------------------------
//   Free types
// --------------------------------------------------------------------------}
// ATTR UserTypes UserType [ || free-types USE {`S.union`} {S.empty} : {S.NameSet} ]

// SEM UserType
//   | TpCon       lhs.free-types = S.single @name

fun test()
  "Compiles".println