// Responsibilities of the kind checker:
// - Kindcheck all types in the program
// - Translate user types to internal types
// - Collect lists of data types, synonyms and constructors
// - Expand all synonyms (i.e., replace @id(int)@ by @id(int) == int@)
// - Translate type definition groups and externals to Core.

// Updated to 7083c02 on 7/13/25 (other than lazy)
import compiler/lib/pprint
import compiler/common/failure
import compiler/common/color-scheme
import compiler/common/range
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/file
import compiler/common/error
import compiler/syntax/syntax
import compiler/syntax/range-map
import compiler/core/core
import compiler/kind/importmap
import compiler/kind/kind
import compiler/kind/assumption
import compiler/kind/constructors
import compiler/kind/newtypes
import compiler/kind/synonyms
import compiler/kind/repr
import compiler/type/type
import compiler/type/assumption
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/kind
import compiler/kind/infer-kind
import compiler/kind/infer-effect
import compiler/kind/unify
import compiler/static/binding-groups
import std/data/linearset
import std/data/linearmap
import std/data/sort

// Kindcheck a program and calculate types
// Also group recursive type and expressing bindings in order
fun inferKinds(
      isValue: (dataInfo) -> pure bool, // is this a value type
      target: platform, // target platform (x32, x64)
      mbRangeMap: maybe<range-map>, // range map for tool integration
      imports: importmap, // import aliases
      kgamma0: kGamma, // initial kind kgamma
      syns0: synonyms, // initial list of synonyms
      data0: newtypes) // initial list of data types
  // original program
  val Program(_, modName, nmrng, tdefs, defs, importdefs, externals, _, doc) = current-program
  // order and group recursive let-bindings
  with runKindInfer(platform, modName, imports, kgamma0, syns0, data0)
  val tdgroups0 = tdefs.group-bindings
  val (tdgroups, kgamma1, syns1, data1, lazyExprs) = kinfer(tdgroups0)
  val externals1 = kinfer(externals)
  val defs1 = kinfer(defs)
  val synDefs = tdgroups.syn-typedef-groups(lazyExprs)
  inf-imports(modName, nmrng, importdefs)

  val (_, dataInfos) = tdgroups.extract-infos.unzip-either
  val conInfos = dataInfos.map(constrs).concat
  val cons1 = conInfos.constructors-from-list
  val gamma1 = dataInfos.constructor-gamma(data/is-value)
  conInfos.constructor-check-duplicates
  // Now order and group definitions including newly synthesized definitions for type definitions
  val dgroups = (synDefs ++ defs1).group-bindings
  (dgroups ++ defs1, kgamma1, (syns1, data1, cons1), Core(modName, [], [], tdgroups, [], externals1, doc))
  
fun unzip-either(xs: list<either<a, b>>): (list<a>, list<b>)
  fun loop(ys: list<either<a, b>>, las: ctx<list<a>>, lbs: ctx<list<b>>): (list<a>, list<b>)
    match ys
      Nil -> (las ++. Nil, lbs ++. Nil)
      Cons(Left(a), a1) -> loop(a1, las ++ ctx Cons(a, hole), lbs)
      Cons(Right(b), b1) -> loop(b1, las, lbs ++ ctx Cons(b, hole))
  loop(xs, ctx hole, ctx hole)

fun extract-infos(groups: list<core/core/typeDefGroup>): list<either<synInfo, dataInfo>>
  fun extract-info(td: core/core/typeDef): either<synInfo, dataInfo>
    match td
      core/core/Synonym(si) -> Left(si)
      Data(di) -> Right(di)
  fun extract-group-infos(g: core/core/typeDefGroup): list<either<synInfo, dataInfo>>
    g.map(extract-info)
  groups.flatmap(extract-group-infos)

// 
alias lazyExpr = (name, syntax/syntax/expr<ktype>)

fun syn-typedef-groups(tdgs: list<core/core/typeDefGroup>, lazyExprs: list<lazyExpr>)
  tdgs.flatmap(fn(tdg) tdg.syn-typedef-group(lazyExprs))

fun syn-typedef-group(tdg: core/core/typeDefGroup, lazyExprs: list<lazyExpr>): _ syntax/syntax/defGroups<ktype>
  tdg.flatmap(_.syn-typedef(lazyExprs))

fun syn-typedef(td: core/core/typeDef, lazyExprs: list<lazyExpr>): _ list<syntax/syntax/defGroup<ktype>>
  match td
    core/core/Synonym -> []
    Data(di) | di.name.is-hidden-name -> []
    Data(di) ->
      val accessors = if !(di.is-open || di.di/is-lazy) then di.syn-accessors else []
      val copycon = if di.constrs.length == 1 && !(di.is-open || di.di/is-lazy) && !di.constrs.head.unjust.name.is-hidden-name && di.kind.has-kind-star-result then
                      [syn-copycon(di, di.constrs.head.unjust)]
                    else []
      val testers = if (di.constrs.length > 1 || di.is-open) && !di.di/is-lazy then
                      di.constrs.flatmap(syn-tester(di, _))
                    else []
      val contag = if di.is-open then di.constrs.map(syn-constr-tag) else []
      val synLazy = if di.di/is-lazy then 
                      [di.syn-lazy-tag, di.syn-lazy-eval(lazyExprs), di.syn-lazy-step, di.syn-lazy-whnf, di.syn-lazy-force]
                    else [] 
      accessors ++ testers ++ copycon ++ contag ++ synLazy

fun syn-copycon(di: dataInfo, ci: conInfo)
  val rc = ci.range.hide
  val defName = copy-name-of(di.name).unqualify
  val argName = "@this".new-name
  val fullTp = 
    val (vars, rho) = ci.typeScheme.split-type-scheme
    match rho.split-fun-type
      Just((args, eff, res)) -> TForAll(vars, TFun([(argName, res)] ++ args.map(fn((nm, t)) (nm, if !ci.has-accessor(nm, t) then t else t.make-optional)), eff, res))
      Nothing -> TForAll(vars, TFun([(argName, rho)], typeTotal, rho))
  fun vvar(n)
    Var(n, False, rc)
  fun app(x, xs)
    match xs 
      Nil -> x 
      _ -> App(x, xs.map((Nothing, _)), rc)
  val params0 = ci.params.map(fn((fldname, t)) ValueBinder(fldname, Nothing, if !ci.has-accessor(fldname, t) then Nothing else Just(app(vvar(type-qualified-name-of(di.name, fldname)), [vvar(argName)])), rc, rc))
  val body = app(vvar(ci.name), ci.params.map(fn((nm, _)) vvar(nm)))
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rc, rc)] ++ params0, body, True, rc)
  DefNonRec(Def(ValueBinder(defName, (), Ann(expr, fullTp, rc), rc, rc), rc, di.vis, def-fun([]), InlineAuto, ""))

fun has-accessor(ci: conInfo, nm: name, tp: ktype)
  val tvs = tp.free-type-vars
  !(nm.is-field-name || nm == nil) && ci.existentials.all(!tvs.member(_))

fun nub-by(xs: list<a>, f: (a, a) -> bool): list<a>
  match xs
    Cons(x1, rst) -> Cons(x1, rst.filter(!f(x1, _)))
    Nil -> Nil

fun is-alphanum(c: char)
  c.is-alpha || c.is-digit

fun syn-accessors(di: dataInfo)
  val paramss = di.constrs.map(fn(ci) ci.params.zipwith(ci.paramVis.zip(ci.paramRanges)) fn((nm, tp), (pvis, rng))
    (nm, (tp, rng, pvis, ci))
  )
  fun occurs-on-all-constrs((nm, (tp, _, _, _)))
    paramss.all(_.any(fn((n, (t, _, _, _))) n == nm && t.eq-type(tp))) // TODO: Change this to eqType
  val fields = paramss.concat.filter(fn((nm, (tp, _, _, cinfo))) cinfo.has-accessor(nm, tp)).nub-by(fn(x, y) x.fst == y.fst).filter(occurs-on-all-constrs)
  fun syn-accessor((nm, (tp, xrng, visibility, _)))
    val rng = xrng.hide
    val defName = type-qualified-name-of(di.name, nm).unqualify
    val arg = 
      val dataName = di.name.unqualify
      if dataName.show.list.all(is-alphanum) then dataName else "@this".new-name
    val fld = "@x".new-name
    val dataTp = TApp(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
    fun make-branch(ci: conInfo)
      val r = ci.range
      match zip(ci.params.map(fst), list(0, ci.params.length)).lookup(_ == nm)
        Just(i) ->
          val patterns = list(0, i - 1).map(fn(_) (Nothing, PatWild(r))) ++ [(Nothing, PatVar(ValueBinder(fld, Nothing, PatWild(r), r, r)))] ++ list(i+1, ci.params.length - 1).map(fn(_) (Nothing, PatWild(r)))
          [(ci.vis, Branch(PatCon(ci.name, patterns, r, r), [Guard(guardTrue, Var(fld, False, r))]))]
        _ -> []
    val branches = di.constrs.map(make-branch).concat
    val isPartial = branches.length < di.constrs.length || di.is-open
    val fullTp = 
      val (foralls, rho) = tp.split-type-scheme
      TForAll(di.params ++ foralls, TFun([(arg, dataTp)], if isPartial then typePartial else typeTotal, rho))
    val messages = [Literal(LitString(rng.start.source.name ++ rng.show, rng)), Literal(LitString(nm.show, rng))]
    val doc = "// Automatically generated. Retrieves the `" ++ nm.show ++ "` constructor field of the `" ++ di.name.nameLocalQual ++ "` type.\n"
    val defaultBranch = if isPartial then [Branch(PatWild(rng), [Guard(guardTrue, App(Var(namePatternMatchError, False, rng), messages.map(fn(msg) (Nothing, msg)), rng))])] else []
    val caseExpr = Case(Var(arg, False, rng), branches.map(snd) ++ defaultBranch, False, rng)
    val expr = Ann(Lam([ValueBinder(arg, Nothing, Nothing, rng, rng)], caseExpr, True, rng), fullTp, xrng)
    DefNonRec(Def(ValueBinder(defName, (), expr, xrng, xrng), rng, visibility, def-fun-ex([Borrow], noFip), InlineAlways, doc))
  fields.map(syn-accessor)

fun syn-tester(di: dataInfo, ci: conInfo)
  if ci.name.is-hidden-name || ci.coninfo/is-lazy then []
  else
    val def-name = "is-".prepend(ci.name.unqualify.to-var-name)
    val arg = di.name.unqualify
    val rc = ci.range.hide
    val patterns = ci.params.map(fn(_) (Nothing, PatWild(rc)))
    val branch1 = Branch(PatCon(ci.name, patterns, rc, rc), [Guard(guardTrue, Var(nameTrue, False, rc))])
    val branch2 = Branch(PatWild(rc), [Guard(guardTrue, Var(nameFalse, False, rc))])
    val caseExpr = Case(Var(arg, False, rc), [branch1, branch2], ci.coninfo/is-lazy, rc)
    val expr = Lam([ValueBinder(arg, Nothing, Nothing, rc, rc)], caseExpr, True, rc)
    val doc = "// Automatically generated. Tests for the `" ++ ci.name.nameLocalQual ++ "` constructor of the `:" ++ di.name.nameLocalQual ++ "` type.\n"
    [DefNonRec(Def(ValueBinder(def-name, (), expr, rc, rc), rc, ci.vis, def-fun-ex([Borrow], Fip(AllocAtMost(0))), InlineAlways, doc))]

fun syn-constr-tag(ci: conInfo)
  val nm = ci.name.unqualify.to-open-tag-name
  val rc = ci.range.hide
  val expr = Literal(LitString(ci.name.show, rc))
  DefNonRec(Def(ValueBinder(nm, (), expr, rc, rc), rc, ci.vis, DefVal, InlineNever, ""))

fun syn-lazy-tag(di: dataInfo)
  val xrng = di.range
  val rng = xrng.hide
  val defName = di.lazy-name("tag")
  val lazyTag = 
    match di.constrs.find(_.name.is-lazy-indirect-con-name)
      Nothing -> fail("kind/infer/syn-lazy-tag: no indirection constructor found: " ++ di.name.show)
      Just(ind) -> ind.tag
  val expr = App(Var(nameInternalInt32, False, rng), [(Nothing, Literal(syntax/syntax/LitInt(lazyTag, rng)))], rng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefVal, InlineAlways, "// Automatically generated tag value of lazy indirection"))

// Add lazy evaluation step:
// ```
// noinline fbip fun stream/lazy-eval( s : stream<a> ) : _ stream<a>
//   lazy-whnf-target(s)
//   match s
//     SAppRev( pre, post )
//       -> match pre
//           SNil        -> lazy-update(s,sreverse(post))
//           SCons(x,xx) -> lazy-update(s,SCons(x,SAppRev(xx,post)))
//     SIndirect(ind)
//       -> ind
//     _ -> s
// ```

fun syn-lazy-eval(di: dataInfo, lazyExprs: list<lazyExpr>)
  val xrng = di.range
  val rng = xrng.hide
  
  val defName = di.lazy-name("eval")
  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)
  
  fun rotate(xs)
    match xs
      Cons(x, xs) -> xs ++ [x]
      _ -> xs
  
  val lazyConstrs = di.constrs.filter(coninfo/is-lazy).rotate // indirect match comes last

  fun branch-expr(ci: conInfo)
    match lazyExprs.lookup(_ == ci.name)
      Just(lazyExpr) -> lazy-add-update(di, ci, defName, arg, lazyExpr)
      Nothing -> fail("kind/infer/syn-lazy-eval/branch-expr: cannot find expression for lazy constructor " ++ ci.name.show)
  // generate branch
  fun make-branch(ci: conInfo)
    if ci.name.is-lazy-indirect-con-name then
      val [(par, _)] = ci.params
      Branch(PatCon(ci.name, 
                   [(Nothing, PatVar(ValueBinder(par, Nothing, PatWild(rng), rng, rng)))], 
                   rng, rng), 
        [Guard(guardTrue, Var(par, False, rng))])
    else
      fun make-pat(par, rng)
        if par.is-wildcard then PatWild(rng)
        else PatVar(ValueBinder(par, Nothing, PatWild(rng), rng, rng))
      Branch(PatCon(ci.name,
                   ci.params.map(fn((par, _)) (Nothing, make-pat(par, rng))),
                   rng, rng),
            [Guard(guardTrue, ci.branch-expr)]
            )
  val branches = lazyConstrs.map(make-branch)
  val mark = syntax/syntax/Def(ValueBinder(nil, (), App(Var(nameLazyTarget, False, rng), [(Nothing, arg)], rng), rng, rng), rng, Private, DefVal, InlineNever, "")
  val body = Case(arg, branches ++ [Branch(PatWild(rng), [Guard(guardTrue, arg)])], True, rng)
  val expr = syntax/syntax/Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], Bind(mark, body, rng), xrng)
  val defbinder = ValueBinder(defName, (), expr, rng, rng)
  val def = syntax/syntax/Def(defbinder, rng, di.vis, DefFun([], di.lazy-fip), InlineNever, "")
  DefNonRec(def)


// Add `lazy-update(s,...)` to tail positions
// SAppRev( pre, post )
//       -> match pre
//            SNil        -> sreverse(post)
//            SCons(x,xx) -> SCons(x,SAppRev(xx,post))
// ~>
// SAppRev( pre, post )
//       -> match pre
//            SNil        -> lazy-update(s,sreverse(post))
//            SCons(x,xx) -> lazy-update(s,SCons(x,SAppRev(xx,post)))

fun add-guard(di: dataInfo, ci: conInfo, evalName, g, arg)
  match g
    syntax/syntax/Guard(test, expr) -> Guard(test, add(di, ci, evalName, expr, arg))

fun add-branch(di: dataInfo, ci: conInfo, evalName, b, arg)
  match b
    syntax/syntax/Branch(patt, guards) -> Branch(patt, guards.map(add-guard(di, ci, evalName, _, arg)))

fun is-whnf-con(di, cname: name)
  val (_, whnfConstrs) = di.constrs.partition(coninfo/is-lazy)
  di.lookup-con(whnfConstrs, cname).is-just

fun is-whnf-con-pat(di, p)
  match p
    PatParens(pat) -> di.is-whnf-con-pat(pat)
    PatAnn(pat) -> di.is-whnf-con-pat(pat)
    syntax/syntax/PatVar(v) -> di.is-whnf-con-pat(v.expr)
    syntax/syntax/PatCon(cname) -> di.is-whnf-con(cname)
    _ -> False

fun is-whnf-con-branch(di, b)
  match b
    syntax/syntax/Branch(p) -> di.is-whnf-con-pat(p)

fun add(di: dataInfo, ci: conInfo, evalName, e, arg)
  match e
    syntax/syntax/Lam(binds, expr, tl, rng) -> syntax/syntax/Lam(binds, add(di, ci, evalName, expr, arg), tl, rng)
    Let(defs, expr, rng) -> Let(defs, add(di, ci, evalName, expr, arg), rng)
    Bind(def, expr, rng) -> Bind(def, add(di, ci, evalName, expr, arg), rng)
    Ann(expr, tp, rng) -> Ann(add(di, ci, evalName, expr, arg), tp, rng)
    Case(expr, brs, lzy, rng) ->
      val brs' = brs.map(add-branch(di, ci, evalName, _, arg))
      val forceName = di.lazy-name("force")
      val exprForce = if !lzy && brs.any(di.is-whnf-con-branch(_)) then
                        App(Var(forceName, False, rng), [(Nothing, expr)], rng)
                      else
                        expr
      Case(exprForce, brs', lzy, rng)
    Parens(expr, name, pre, rng) -> Parens(add(di, ci, evalName, expr, arg), name, pre, rng)
    App(syntax/syntax/Var(cname), _, _) -> di.lazy-update-con(ci, cname, evalName, e, arg)
    syntax/syntax/Var(cname) -> di.lazy-update-con(ci, cname, evalName, e, arg)
    _ -> unknown-update(di, ci, evalName, e, arg)

fun unknown-update(di: dataInfo, ci: conInfo, evalName, expr, arg)
  val rng = expr.expr/range.hide
  update-warning(di, ci, rng, fn(_) "in-place as the result constructor is not statically known -- using an indirection instead".text)
  lazy-update(expr, arg)

fun recursive-update(di: dataInfo, ci: conInfo, ci': conInfo, evalName, expr, arg)
  val r0 = expr.expr/range.hide
  // No need to warn anymore as we don't force recursively here
  warn-update(di, ci, expr.range, ci')
  lazy-update(expr, arg)

fun warn-update(di: dataInfo, ci: conInfo, rng: range, resultCon)
  val lazySize = alloc-size(con-repr(di, ci), platform)
  val whnfSize = alloc-size(con-repr(di, resultCon), platform)
  if lazySize <= whnfSize then
    update-warning(di, resultCon, rng, fn(_) "in-place as the result constructor is larger(".text |.| lazySize.pretty |+| "vs".text |+| whnfSize.pretty |+| "bytes".text)

fun lazy-update-con(di: dataInfo, ci: conInfo, cname: name, evalName, expr, arg)
  val (lazyConstrs, whnfConstrs) = di.constrs.partition(fn(ci') ci.coninfo/is-lazy)
  match di.lookup-con(whnfConstrs, cname)
    Nothing -> match di.lookup-con(lazyConstrs, cname)
      Nothing -> unknown-update(di, ci, evalName, expr, arg)
      Just(ci') -> recursive-update(di, ci, ci', evalName, expr, arg)
    Just(whnf) ->
      warn-update(di, ci, expr.range, whnf)
      lazy-update(expr, arg)

fun lazy-update(expr, arg)
  val rng = expr.expr/range.hide
  App(Var(nameLazyMemoize, False, rng), [(Nothing, arg), (Nothing, expr)], rng)

fun update-warning(di: dataInfo, ci: conInfo, rng: range, fdoc: (name -> doc) -> doc)
  val cs = colors
  fun show-con-name(nm: name)
    nm.unqualify.pretty.color(cs.colorCons)
  add-warning(rng, "Cannot update the lazy constructor".text |+| ci.name.show-con-name |+| fdoc(show-con-name))

fun lookup-con(di: dataInfo, constrs, cname: name)
  val modName = di.name.qualifier
  constrs.find fn(ci: conInfo)
    ci.name == (if cname.is-qualified then cname else qualify(modName, cname))

fun lazy-add-update(di: dataInfo, ci: conInfo, evalName: name, arg, topExpr)
  di.add(ci, evalName, topExpr, arg)

// noinline fun stream/lazy-step( s : stream<a> ) : _ stream<a>
//   if kk-datatype-ptr-is-unique || !lazy-atomic-enter(s,stream/lazy-tag) then
//     stream/lazy-eval(s)
//   else
//     val v = stream/lazy-eval(s)
//     lazy-atomic-leave(s)
//     v

fun syn-lazy-step(di: dataInfo)
  val xrng = di.range
  val rng = xrng.hide
  val defName = di.lazy-name("step")
  val dataTp = TApp(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  val fullTp = TForAll(di.params, [], TFun([(nil, dataTp)], typePure, dataTp))

  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)
  val tst = App(Var(nameOr, False, rng), 
      [(Nothing, App(Var(nameDataTypePtrIsUnique, False, rng), [(Nothing, arg)], rng)),
       (Nothing, App(Var("std/core/types".new-qualified("not"), False, rng), 
           [(Nothing, App(Var(nameLazyEnter, False, rng), 
              [(Nothing, arg), 
               (Nothing, Var(di.lazy-name("tag"), False, rng))], rng))], rng))], rng)
  val eval = App(Var(di.lazy-name("eval"), False, rng), [(Nothing, arg)], rng)
  val atomic = 
    val v = "v".new-name
    val vdef = Def(ValueBinder(v, (), eval, rng, rng), rng, Private, DefVal, InlineNever, "")
    val bdef = Def(ValueBinder(nil, (), App(Var(nameLazyLeave, False, rng), [(Nothing, arg)], rng), rng, rng), rng, Private, DefVal, InlineNever, "")
    Bind(vdef, Bind(bdef, Var(v, False, rng), rng), rng)
  val body = Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, eval)]),
                        Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, atomic)])], 
                        False, rng)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], body, xrng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineNever, ""))

// recursive force:
// noinline fun stream/lazy-whnf(s: stream<a>): div stream<a>
//   val x = stream/step(s)
//   if lazy/datatype-is-whnf(x, stream/lazy-tag) then x else stream/lazy-whnf(x)

fun syn-lazy-whnf(di: dataInfo)
  val xrng = di.range
  val rng = xrng.hide
  val defName = di.lazy-name("whnf")
  val dataTp = TApp(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  val nameIsWhnf = 
    if di.constrs.all(fn(ci: conInfo) ci.params.length > 0)
    then nameLazyPtrIsWhnf else nameLazyIsWhnf

  val valName = "val".new-hidden-name
  val vl = Var(valName, False, rng)

  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)

  val nameStep = di.lazy-name("step")
  val stepExpr = App(Var(nameStep, False, rng), [(Nothing, arg)], rng)
  val valDef = Def(ValueBinder(valName, (), stepExpr, rng, rng), rng, Private, DefVal, InlineNever, "")
  val tst = App(Var(nameIsWhnf, False, rng), [(Nothing, vl), (Nothing, Var(di.lazy-name("lazy-tag"), False, rng))], rng)
  val whnf = App(Var(di.lazy-name("whnf"), False, rng), [(Nothing, vl)], rng)
  val body = Let(DefNonRec(valDef), Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, vl)]), Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, whnf)])], False, rng), rng)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], body, xrng)
  DefRec([Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineNever, "")])

// force is a one step unfolding of whnf and is inlined at call sites.
// inline fun stream/lazy-force(s: stream<a>): div stream<a>
//   if kk-datatype-is-whnf(s,stream/lazy-tag) then s else stream/lazy-whnf(s)
fun syn-lazy-force(di: dataInfo)
  val xrng = di.range
  val rng = xrng.hide
  val defName = di.lazy-name("force")
  val dataTp = TApp(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  val nameIsWhnf = 
    if di.constrs.all(fn(ci: conInfo) ci.params.length > 0)
    then nameLazyPtrIsWhnf else nameLazyIsWhnf
  
  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)
  val tst = App(Var(nameIsWhnf, False, rng), [(Nothing, arg), (Nothing, Var(di.lazy-name("tag"), False, rng))], rng)
  val whnf = App(Var(di.lazy-name("whnf"), False, rng), [(Nothing, arg)], rng)
  val body = Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, arg)]), 
                        Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, whnf)])], False, rng)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], body, xrng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineAlways, ""))

fun lazy-fip(di: dataInfo)
  match di.def
    DataDefLazy(fip) -> fip
    _ -> fail("kint/infer/lazy-fip: not a lazy data type? " ++ di.name.show)

// Types for constructors
fun constructor-gamma(dis: list<dataInfo>, is-value: (dataInfo) -> bool): exn gamma
  fun gamma(cis: list<(conInfo, conRepr)>)
    cis.map(fn((ci: conInfo, crepr)) (ci.name, InfoCon(ci.vis, ci.typeScheme, crepr, ci, ci.range, ci.doc))).gamma/new
  dis.flatmap(fn(di) di.constrs.zip(data-repr(di, is-value).snd)).gamma

fun constructor-check-duplicates(cis: list<conInfo>)
  fun same-name(ci1: conInfo, ci2: conInfo)
    ci1.name == ci2.name
  fun duplicate(cis': list<conInfo>)
    match cis'
      Cons(ci1, Cons(ci2)) -> 
        add-error(ci2.range, "Constructor".text |+| ci2.name.pretty.color(colors.colorSource) 
          |+| "is already defined at".text |+| ci1.range.show.text)
      _ -> ()
  cis.group-by(same-name).foreach(duplicate)

fun inf-imports(modName: name, modRange: range, imports: list<syntax/syntax/kimport>)
  add-range-info(modRange, RIId(modName, NIModule, [], True))
  imports.foreach(inf-import)

fun inf-import(imp: syntax/syntax/kimport)
  val syntax/syntax/Kimport(aliasn, qname, aliasRng, nameRange) = imp
  add-range-info(nameRange, RIId(qname, NIModule, [], True))
  add-range-info(aliasRng, RIId(aliasn, NIModule, [], True))

// Infer kinds for type definition groups
fun tdgs/kinfer(tdgs: list<syntax/syntax/typeDefGroup<userType,userKind>>)
  fun get-ranges(tdg)
    match tdg
      TypeDefRec(tdefs) -> tdefs.map(range)
      TypeDefNonRec(tdef) -> [tdef.range]
  match tdgs
    Nil -> (Nil, infKindEnv.kGamma, get-syns(), infKindEnv.allnewtypes, [])
    Cons(tdgroup, tdgroups) ->
      val (ctdgroup, lazyExprs) = kinfer(tdgroup)
      with extend-kgamma(tdgroup.get-ranges, ctdgroup)
      val (ctdgroups, kgamma1, syns1, data1, lazyExprss) = tdgs/kinfer(tdgroups)
      (Cons(ctdgroup, ctdgroups), kgamma1, syns1, data1, lazyExprs ++ lazyExprss)

fun tdg/kinfer(td: syntax/syntax/typeDefGroup<userType,userKind>)
  match td
    TypeDefRec(tdefs) -> kinfer(True, tdefs)
    TypeDefNonRec(tdef) -> kinfer(False, [tdef])

fun get-data-effect((tbind, dt))
  match dt
    DataType(deffect = deffect) ->
      if deffect.is-dataNoEffect && tbind.tb/kind.is-infkind-handled then // TODO: Add (n)handled(1) kind constructors?
        [(tbind.name, DataEffect(False, False))] // for user declared `type eff :: HX` `test/algeff/wrong/eff-rec5`
      else [(tbind.name, deffect)]
    _ -> []

fun tdl/kinfer(isRec: bool, tdefs0: list<syntax/syntax/typeDef<userType, userType, userKind>>)
  val tdefs = tdefs0.map(add-lazy-indirect)
  val xinfgamma = tdefs.map(bind-typedef) // set up recursion
  val infgamma = xinfgamma.filter(snd).map(fst)
  with with-data-effects(LinearMap([]) + infgamma.zip(tdefs).flatmap(get-data-effect)) // make effect types visible for lifting to handled
  with extend-infgamma(infgamma) // extend inference gamma, also checks for duplicates
  val names = infgamma.map(name)
  val tdefs1 = xinfgamma.map(fst).zip(tdefs).map(fn((a, b)) kinfer(a, b))
  val ctdefs' = tdefs1.map(resolve-typedef(isRec, names, _))
  check-recursion(tdefs) // check for recursive type synonym definitions rather late so we spot duplicate definitions first
  val (ctdefs, lazyExprss) = ctdefs'.unzip
  (ctdefs, lazyExprss.concat)

fun check-recursion(tdefs: list<syntax/syntax/typeDef<userType, userType, userKind>>)
  if tdefs.length <= 1 || tdefs.any(is-dataType) then
    ()
  else
    add-error(if tdefs.length > 0 then tdefs.head.unjust.range.combine(tdefs.last.unjust.range) else null, 
              "Type synonyms cannot be recursive".text)

// Setup type environment for recursive definitions
fun bind-typedef(tdef: syntax/syntax/typeDef<userType, userType, userKind>)
  val TypeBinder(name, kind, rngName, rng) = bind-typebinder(tdef.binder)
  val isExtend = 
    match tdef
      DataType(ddef=ddef) -> ddef.is-extend
      _ -> False
  val qname = if isExtend then name else name.qualify-def
  (TypeBinder(qname, kind, rngName, rng), !isExtend)

fun bind-typebinder(TypeBinder(name, userKind, rngName, rng): typeBinder<userKind>)
  val kind = to-kind(userKind)
  TypeBinder(name, kind, rngName, rng)

fun userkind/to-kind(userKind: userKind)
  match userKind
    KindCon(nm) -> KICon(KCon(nm))
    KindArrow(k1, k2) ->
      val k1' = to-kind(k1)
      val k2' = to-kind(k2)
      match (k1', k2')
        (KICon(kk1), KICon(kk2)) -> KICon(kind-fun(kk1, kk2))
        _ -> KIApp(k1', k2')
    KindParens(k) -> to-kind(k)
    KindNone -> fresh-kind()

// Infer kinds of external definitions
fun externals/kinfer(externals0: list<syntax/syntax/external>)
  fun walk(names: list<name>, externals: list<syntax/syntax/external>)
    match externals
      Nil -> Nil
      Cons(ex, exs) ->
        val (ext, names2) = ex.kinfer(names)
        val exts = walk(names2, exs)
        Cons(ext, exts)
  walk([], externals0)

fun external/kinfer(ex: syntax/syntax/external, names: list<name>)
  match ex
    syntax/syntax/External(name, tp, pinfos, nameRng, rng, calls, vis, fipT, doc) ->
      with override val uctx = Check("Externals must be values", rng)
      val tp' = tp.inf-resolve-type()
      val qname = name.qualify-def
      val cname = qname
      check-external(cname, nameRng)
      if name.is-hidden-name then ()
      else
        add-range-info(nameRng, RIId(qname, NIValue("extern", tp', doc, True), [], True))
        add-range-info(rng, RIDecl("extern", qname, cname.mangle(tp'), Just(tp')))
      (core/core/External(cname, tp', pinfos, calls.map(_.format-call(tp')), vis, fipT, nameRng, doc), Cons(qname, names))
    syntax/syntax/ExternalImport(imps, rng) -> (core/core/ExternalImport(imps, rng), names)

fun format-call((target, externalCall): (target, externalCall), tp: ktype)
  match externalCall
    ExternalInline(inl) -> (target, inl)
    ExternalCall(fname) ->
      val (foralls, rho) = tp.split-type-scheme
      val argumentCount = match rho.split-fun-type
        Just((args, _, _)) -> args.length
        _ -> 0
      val arguments = "(" ++ list(1, argumentCount).map("#" ++ _.show).join(",") ++ ")"
      val argumentsC = "(" ++ list(1, argumentCount).map("#" ++ _.show).join(",") ++ (if fname.starts-with("kk_").is-just then "kk_context()" else "") ++ ")"
      val typeArguments = if foralls.is-nil then "" else "<" ++ list(1, foralls.length).map("##" ++ _.show).join(",") ++ ">"
      match target
        CS -> (target, fname ++ typeArguments ++ arguments)
        JS -> (target, fname ++ arguments)
        C -> (target, fname ++ argumentsC)
        DefaultTarget -> (target, fname ++ arguments)

fun inf-resolve-type(tp: userType)
  val infTp = kinfer(infKindStar, tp)
  resolve-type(nameTVMapEmpty, False, infTp)

fun inf-resolve-hx(tp: userType)
  val infTp = kinfer(infKindHandled, tp)
  resolve-type(nameTVMapEmpty, False, infTp)

fun inf-resolvex(tp: userType, rng: range)
  val ikind = fresh-kind()
  val infTp = kinfer(ikind, tp)
  val skind = subst(ikind)
  // also allow effect label constructors without giving type parameters
  val (kargs, kres) = skind.inf-extract-kind-fun
  if kargs.length > 2 || kargs.is-cons && kres.is-infkind-label then
    // either user defined, or a primitive like `:local`
    val vars = list(1, kargs.length - (if kres.is-infkind-label then 0 else 2)).map(new-name("_" ++ _.show))
    val quals = vars.map(TypeBinder(_, KindNone, rng, rng))
    val tpvars = vars.map(TpVar(_, rng))
    val newTp = quals.foldr(TpApp(tp, tpvars, rng), fn(q, t) TpQuan(QSome, q, t, rng))
    newTp.inf-resolvex(rng) // recurse
  else
    // auto upgrade bare labels of HX or HX1 to X kind labels.
    val eff = match skind
      KICon(k) | k == kindLabel -> infTp
      KICon(k) | k.is-kind-handled -> get-effect-lift(infTp)(infTp, rng)
      _ -> 
        unify(rng, infKindLabel, skind)
        infTp
    resolve-type(nameTVMapEmpty, False, eff)

// Infer kinds of definitions
fun dgs/kinfer(dgs: list<syntax/syntax/defGroup<userType>>)
  dgs.map(kinfer)

fun dg/kinfer(dg: syntax/syntax/defGroup<userType>)
  match dg
    syntax/syntax/DefRec(defs) -> DefRec(defs.map(kinfer))
    syntax/syntax/DefNonRec(def) -> DefNonRec(kinfer(def))

fun def/kinfer(syntax/syntax/Def(binder, rng, vis, isVal, inl, doc): syntax/syntax/def<userType>)
  Def(binder.kinfer, rng, vis, isVal, inl, doc)

fun valuebinder/kinfer(ValueBinder(nm, u, x, nmRng, rng): valueBinder<(), syntax/syntax/expr<userType>>)
  ValueBinder(nm, u, x.kinfer, nmRng, rng)

fun lam-valuebinder/kinfer(ValueBinder(lamnm, mbTp, mbExpr, nmRng, rng): valueBinder<maybe<userType>, maybe<syntax/syntax/expr<userType>>>)
  val mbTp' = mbTp.map fn(t)
    with override val uctx = Check("Function parameters must be values", rng)
    t.inf-resolve-type()
  val isImplicit = lamnm.is-implicit-param-name
  val mbExpr' = mbExpr.map fn(e)
    match e
      Parens(Var(iname, _, nrng), nm, _, prng) | isImplicit ->
        val (qname, _, _) = find-infkind(iname, rng)
        Parens(Var(qname, False, nrng), nm, "implicit", prng)
      expr -> expr.kinfer
  ValueBinder(lamnm, mbTp', mbExpr', nmRng, rng)

fun pat-valuebinder/kinfer(ValueBinder(nm, mbTp, pat, nmRng, rng): valueBinder<maybe<userType>, syntax/syntax/pattern<userType>>)
  val mbTp' = mbTp.map(
    fn(t)
      with override val uctx = Check("Matched expressions must be values", rng)
      t.inf-resolve-type()
  )
  ValueBinder(nm, mbTp', pat.kinfer, nmRng, rng)

fun handler-valuebinder/kinfer(ValueBinder(nm, mbTp, u, nmRng, rng): valueBinder<maybe<userType>, ()>)
  val mbTp' = mbTp.map(
    fn(t)
      with override val uctx = Check("Handler parameters must be values", rng)
      inf-resolve-type(t)
  )
  ValueBinder(nm, mbTp', u, nmRng, rng)

fun expr/kinfer(ex: syntax/syntax/expr<userType>)
  match ex
    syntax/syntax/Lam(binds, expr, tl, rng) -> syntax/syntax/Lam(binds.map(kinfer), expr.kinfer, tl, rng)
    syntax/syntax/Let(defs, expr, rng) -> syntax/syntax/Let(defs.kinfer, expr.kinfer, rng)
    syntax/syntax/Bind(def, expr, rng) -> syntax/syntax/Bind(def.kinfer, expr.kinfer, rng)
    syntax/syntax/App(f, nargs, rng) -> syntax/syntax/App(f.kinfer, nargs.map(fn((nm, arg)) (nm, arg.kinfer)), rng)
    syntax/syntax/Var(nm, isOp, rng) -> syntax/syntax/Var(nm, isOp, rng) // resolve qualified term identifiers during type inference
    Literal(l) -> Literal(l)
    Ann(expr, tp, rng) -> 
      val expr' = expr.kinfer
      val tp' = 
        with override val uctx = Check("Expressions must be values", rng) 
        tp.inf-resolve-type()
      Ann(expr', tp', rng)
    syntax/syntax/Case(expr, brs, lzy, rng) -> syntax/syntax/Case(expr.kinfer, brs.map(kinfer), lzy, rng)
    syntax/syntax/Parens(expr, nm, pre, rng) -> syntax/syntax/Parens(expr.kinfer, nm, pre, rng)
    Handler(hsort, scoped, over, allowMask, meff, pars, reinit, ret, fin, ops, hrng, rng) ->
      val pars' = pars.map(kinfer)
      val meff' = meff.map() fn(eff)
        with override val uctx = Check("Handler effects must be effect constants (of kind X)", hrng)
        eff.inf-resolvex(rng)
      Handler(hsort, scoped, over, allowMask, meff', pars', reinit.map(kinfer), ret.map(kinfer), fin.map(kinfer), ops.map(kinfer), hrng, rng)
    Inject(tp, expr, b, rng) ->
      val expr' = expr.kinfer
      val tp' =
        with override val uctx = Check("Can only inject effect constants (of kind X)", tp.range)
        tp.inf-resolvex(rng)
      Inject(tp', expr', b, rng)

fun pat/kinfer(p: syntax/syntax/pattern<userType>)
  match p
    syntax/syntax/PatWild(rng) -> syntax/syntax/PatWild(rng)
    syntax/syntax/PatLit(l) -> syntax/syntax/PatLit(l)
    syntax/syntax/PatVar(binder) -> syntax/syntax/PatVar(binder.kinfer)
    syntax/syntax/PatAnn(pat, tp, rng) ->
      val pat' = pat.kinfer
      val tp' = 
        with override val uctx = Check("Patterns must be values", rng)
        tp.inf-resolve-type()
      syntax/syntax/PatAnn(pat', tp', rng)
    syntax/syntax/PatCon(name, args, r1, r2) -> syntax/syntax/PatCon(name, args.map(fn((mbNm, p')) (mbNm, p'.kinfer)), r1, r2)
    syntax/syntax/PatParens(pat, rng) -> syntax/syntax/PatParens(pat.kinfer, rng)

fun handlerbranch/kinfer(HandlerBranch(name, pars, expr, opSort, nmRng, rng): handlerBranch<userType>)
  val pars' = pars.map(kinfer)
  val expr' = expr.kinfer
  HandlerBranch(name, pars', expr', opSort, nmRng, rng)

fun branch/kinfer(syntax/syntax/Branch(pat, guards): syntax/syntax/branch<userType>)
  val pat' = pat.kinfer
  val guards' = guards.map(kinfer)
  syntax/syntax/Branch(pat', guards')

fun guard/kinfer(syntax/syntax/Guard(test, body): syntax/syntax/guard<userType>)
  val test' = test.kinfer
  val body' = body.kinfer
  syntax/syntax/Guard(test', body')

// Infer the kinds for a type definition
fun typedef/kinfer(tb: typeBinder<infKind>, td: syntax/syntax/typeDef<userType, userType, userKind>)
  match td
    syntax/syntax/Synonym(_, args, tp, rng, vis, doc) ->
      val infgamma = args.map(bind-typebinder)
      val k = fresh-kind()
      with extend-infgamma(infgamma)
      with override val uctx = Infer(rng)
      val tp' = kinfer(k, tp)
      val tbinder = unify-binder(tb, rng, infgamma, k)
      syntax/syntax/Synonym(tbinder, infgamma, tp', rng, vis, doc)
    DataType(newTp, args, constrs, rng, vis, sort, ddef, dataEff, doc) ->
      val infgamma = args.map(bind-typebinder)
      with extend-infgamma(infgamma)
      val constrs' = constrs.map(kinfer)
      // TODO: unify extended datatype kind with original
      val resKind = if ddef.is-open then infKindStar else fresh-kind()
      val tbinder' = unify-binder(tb, rng, infgamma, resKind)
      if !ddef.is-extend then ()
      else
        val (_, kd, _) = find-infkind(newTp.name, newTp.range)
        with override val uctx = Check("extended type must have the same kind as the open type", newTp.range)
        unify(newTp.range, tbinder'.tb/kind, kd)
      DataType(tbinder', infgamma, constrs', rng, vis, sort, ddef, dataEff, doc)

fun unify-binder(tb: typeBinder<infKind>, rng: range, infgamma: list<typeBinder<infKind>>, resKind: infKind)
  val kind = inf-kind-funN(infgamma.map(tb/kind), resKind)
  with override val uctx = Infer(rng)
  unify(rng, tb.tb/kind, kind)
  tb

fun tb/kind(TypeBinder(_, k, _, _): typeBinder<k>): k
  k

fun constr/kinfer(UserCon(name, exists0, params, mbresult, mblazy, rngName, rng, vis, doc): userCon<userType,userType,userKind>)
  val infgamma = exists0.map(bind-typebinder)
  with extend-infgamma(infgamma)
  val params' = params.map(kinfer)
  val result' = mbresult.map fn(t)
    with override val uctx = Check("Constructor results must be values", rng)
    kinfer(infKindStar, t)
  UserCon(name, infgamma, params', result', mblazy, rngName, rng, vis, doc)

fun con-valuebinder/kinfer((vis,ValueBinder(name, tp, mbExpr, nameRng, rng)): (visibility, valueBinder<userType, maybe<syntax/syntax/expr<userType>>>))
  with override val uctx = Check("Constructor parameters must be values", rng)
  val tp' = kinfer(infKindStar, tp)
  (vis, ValueBinder(name, tp', mbExpr, nameRng, rng))

fun usertp/kinfer(expected: infKind, userType: userType)
  match userType
    TpQuan(quant, tname, tp, r) ->
      val ikind = match quant
        QSome -> expected
        _ -> 
          unify(r, expected, infKindStar)
          expected
      val tname' = tname.bind-typebinder
      with extend-infgamma([tname'])
      with check-quant(r)
      val tp' = kinfer(ikind, tp)
      TpQuan(quant, tname', tp', r)
    TpFun(args, eff, tp, r) ->
      unify(r, expected, infKindStar)
      with check-arg(r)
      val args' = args.map(kinfer(infKindStar, _))
      // somewhat involved since we auto-wrap labels L into effects E here
      val ekind = fresh-kind()
      with check-eff(r)
      val etp = kinfer(ekind, eff)
      val skind = subst(ekind)
      val eff' = match skind
        KICon(k) | k == kindLabel -> make-effect-extend(etp, make-effect-empty)
        KICon(k) | k.is-kind-handled ->
          make-effect-extend(get-effect-lift(etp)(etp, r), make-effect-empty) 
        _ ->
          with check-eff(r)
          unify(r, KICon(kindEffect), skind)
          etp
      with check-res(r)
      val tp' = kinfer(infKindStar, tp)
      TpFun(args', eff', tp', r)
    TpApp(tp as TpCon(nm), [lab, tl], r) | nm == nameEffectExtend ->
      with check-app(r)
      val tp' = kinfer(inf-kind-funN([KICon(kindLabel), KICon(kindEffect)], expected), tp)
      with check-extend-tail(r)
      val tl' = kinfer(KICon(kindEffect), tl)
      // somewhat involved since we allow fixed effects to be used as labels
      // the append nodes are just used temporarily (see resolve-app in this file)
      val lkind = fresh-kind()
      with override val uctx = Infer(r)
      val ltp = kinfer(lkind, lab)
      val skind = subst(lkind)
      match skind
        KICon(kind) | kind == kindEffect -> make-effect-append(ltp, tl')
        KICon(kind) | kind.is-kind-handled ->
          // TODO: check effects environment if really effect?
          with check-extend-label(r)
          unify(r, KICon(kindHandled), skind)
          TpApp(tp', [get-effect-lift(ltp)(ltp, r), tl'], r)
        _ ->
          with check-extend-label(r)
          unify(r, KICon(kindLabel), skind)
          TpApp(tp', [ltp, tl'], r)
    TpApp(tp, args, rng) ->
      val kinds = args.map(fn(_) fresh-kind())
      with check-app(rng)
      val tp' = kinfer(inf-kind-funN(kinds, expected), tp)
      val args' = args.zip(kinds).map fn((arg, kind)) 
        with override val uctx = Infer(rng)
        kinfer(kind, arg)
      TpApp(tp', args', rng)
    TpVar(nm, rng) ->
      val (qname, kind, _) = find-infkind(nm, rng)
      unify(rng, expected, kind)
      TpVar(qname, rng)
    TpCon(nm, rng) ->
      val (qname, kind, _) = find-infkind(nm, rng)
      unify(rng, expected, kind)
      TpCon(qname, rng)
    TpParens(tp, rng) ->
      val tp' = kinfer(expected, tp)
      TpParens(tp', rng)
    TpAnn(tp, userKind) ->
      val rng = userType.range
      val kind = userKind.to-kind
      unify(rng, expected, kind)
      with check-annot(rng)
      val tp' = kinfer(kind, tp)
      TpAnn(tp', kind)

fun get-effect-lift(utp: kUserType<infKind>): inferKindEnvEffect (forall<k> (kUserType<k>, range) -> kUserType<k>)
  match utp
    TpQuan(_, _, tp) -> get-effect-lift(tp)
    TpParens(tp) -> get-effect-lift(tp)
    TpApp(tp) -> get-effect-lift(tp)
    TpCon(nm) ->
      match lookup-data-effect(nm)
        DataEffect(isnamed, islinear) ->
          fn(u, r) TpApp(TpCon(make-tp-handled(isnamed, islinear), null), [u], null)
        DataNoEffect -> fn(tp, _) tp
    _ ->
      trace("get-effect-lift: ")
      fn(tp, _) tp

fun param/kinfer(expected: infKind, (nm, tp): (name, userType))
  (nm, kinfer(expected, tp))

// Add indirection constructor to a lazy datatype
fun add-lazy-indirect(dt)
  match dt
    DataType(newtp, targs, cons, range, vis, sort, ddef, dataEff, doc) | cons.any(user-con-is-lazy) || ddef.datadef/is-lazy ->
      val (lazyCons, strictCons) = cons.partition(user-con-is-lazy)
      val rng = newtp.name-range.hide
      val indirectName = "indirect".new-hidden-name
      fun make-tp-app(t: kUserType<k>, targs': list<kUserType<k>>): kUserType<k>
        if targs'.is-nil then t else TpApp(t, targs', rng)
      val indirectPar = ValueBinder(indirectName, make-tp-app(TpCon(newtp.name, rng), targs.map(fn(targ) TpVar(targ.name, targ.name-range))), Nothing, rng, rng)
      val indirectCon = UserCon(newtp.name.to-lazy-indirect-con-name, [], [(Private, indirectPar)], Nothing, Just((fipNoAlloc, Var(indirectName, False, rng))), 
                        rng, rng, Public, "// automatically generated lazy indirection constructor")
      
      // order with lazy last (so we can check quickly at runtime)
      val new-cons = strictCons ++ [indirectCon] ++ lazyCons
      val validDdef =
        match ddef
          DataDefAuto -> True
          DataDefNormal -> True
          DataDefLazy -> True
          _ -> False
      if !validDdef then
        add-error(rng, "Cannot add lazy constructors to a".text |+| ddef.show.text |+| "type".text)
      
      // get fip annotation of the data definition
      fun user-con-fip(c)
        match c.userCon/mblazy
          Just((f, _)) -> f
          _ -> noFip
      val defaultFip = lazyCons.map(user-con-fip).foldr(fipBot, max)
      val fipT = match ddef
        DataDefLazy(NoFip(False)) -> defaultFip
        DataDefLazy(fipT) ->
          if !fipT.subsumes(defaultFip) then // annotated
            add-error(rng, "The datatype".text |+| fipT.show.text |+| "annotation cannot be more restrictive than the fip annotations of the lazy constructors".text)
            defaultFip
          else fipT
        _ -> defaultFip
      DataType(newtp, targs, new-cons, range, vis, sort, DataDefLazy(fipT), dataEff, doc)
    td -> td


fun user-con-is-lazy(ucon)
  match ucon.userCon/mblazy
    Just -> True
    Nothing -> is-lazy-indirect-con-name(ucon.name)


fun check-quant(rng, f)
  with override val uctx = Check("Can only quantify over types", rng)
  f()

fun check-pred(rng, f)
  with override val uctx = Check("The left-hand side of a \"=>\" can only contain predicates", rng)
  f()

fun check-arg(rng, f)
  with override val uctx = Check("The parameters of a function type must be types", rng)
  f()

fun check-eff(rng, f)
  with override val uctx = Check("The effect of a function type must be an effect type", rng)
  f()

fun check-res(rng, f)
  with override val uctx = Check("The result of a function type must be a type", rng)
  f()

fun check-annot(rng, f)
  with override val uctx = Check("The inferred kind doesn't match the annotated kind", rng)
  f()

fun check-app(rng, f)
  with override val uctx = Check("The type cannot be applied to those arguments", rng)
  f()

fun check-extend-tail(rng, f)
  with override val uctx = Check("The extension of an effect must be an effect type", rng)
  f()

fun check-extend-label(rng, f)
  with override val uctx = Check("The elements of an effect must be effect constants", rng)
  f()

fun kind/arity(kind: kind)
  match kind
    KApp(KApp(kcon, k1), k2) | kcon == kindArrow -> Cons(k1, arity(k2))
    _ -> []

// Resolve kinds: from InfKind to Kind, and UserType to Type
fun resolve-typedef(isRec: bool, recNames: list<name>, td: syntax/syntax/typeDef<kUserType<infKind>, userType, infKind>)
  match td
    Synonym(syn, params, tp, rng, vis, doc) ->
      val syn' = syn.resolve-typebinder-def(doc)
      val params' = params.map(_.resolve-typebinder(""))
      val typeVars = params'.map(_.fresh-typevar(Bound))
      val tvarMap = LinearMap([]) + params'.map(name).zip(typeVars)
      val tp' = resolve-type(tvarMap, True, tp)
      // eta-expand type synonyms
      val kind = syn'.tb/kind
      val karity = kind.arity
      val etaKinds = karity.drop(typeVars.length)
      val (etaTp, etaParams) = 
        if etaKinds.is-nil then
          (tp', typeVars)
        else
          val etaVars = etaKinds.map(TypeVar(unique-id("eta"), _, Bound))
          (TApp(tp', etaVars.map(TVar)), typeVars ++ etaVars)
      add-range-info(rng, RIDecl("alias", syn'.name, syn.name.mangle-type-name, Just(tp')))
      (Synonym(SynInfo(syn'.name, syn'.tb/kind, etaParams, etaTp, etaTp.max-synonym-rank + 1, rng, vis, doc)), [])
    DataType(newtp, params, constrs, rng, vis, sort, ddef, dataEff, doc) ->
      val newtp' = 
        if ddef.is-extend then
          val (qname, ikind, _) = find-infkind(newtp.name, newtp.range)
          val kind = ikind.resolve-kind
          TypeBinder(qname, kind, newtp.name-range, newtp.range)
        else
          newtp.resolve-typebinder-def(doc)
      val params' = params.map(_.resolve-typebinder(""))
      val typeResult = TCon(TypeCon(newtp'.name, newtp'.tb/kind))
      val typeVars =
        val (kargs, _kres) = extract-kind-fun(newtp'.tb/kind)
        if params.is-nil && !kargs.is-nil then
          kargs.map(fn(karg) TypeVar(unique-id("k"), karg, Bound)) // invent parameters if they are not given (and it has an arrow kind)
        else
          params'.map(_.fresh-typevar(Bound))
      val tvarMap = LinearMap([]) + params'.map(name).zip(typeVars)
      val qname = newtp'.name
      val fname = qname.unqualify
      val name = fname
      val nameDoc = name.pretty.color(colors.colorType)
      val consinfos = constrs.map-indexed fn(i, c) 
        resolve-constructor(qname, sort, !ddef.is-open && constrs.length == 1, typeResult, typeVars, tvarMap, c, i + 1) // constructor tags start at 1
      val (lazyExprss, conInfos0) = consinfos.unzip
      // check recursion
      if sort.is-retractive then
        ()
      else
        fun from-ops-name(nm: name)
          if nm.is-operations-name then [nm.from-operations-name] else []
        val effNames = recNames.map(from-ops-name).concat
        if conInfos0.any(occurs-negative-con(recNames ++ effNames, _)) then
          add-error(rng, "Type".text |+| nameDoc |+| "is declared as being".text |-| "(co)inductive but it occurs recursively in a negative position.".text |-|
            " hint: declare it as a divergent (or retractive) type using 'div type' (or 'effect rec)' to allow negative occurences".text)
        else ()
      // create datadef and coninfos with correct ValueRepr and ordered fields
      fun emit-error(d)
        add-error(rng, "Type".text |+| nameDoc |+| d)
      fun emit-warning(d)
        add-warning(rng, "Type".text |+| nameDoc |+| d)
      val resultHasKindStar = typeResult.kind.has-kind-star-result
      val maxMembers = conInfos0.map(_.conInfo/params.length).maximum
      val conCount = conInfos0.length
      val willNeedStructTag = ddef.is-value && conCount > 1 && maxMembers >= 1
      val extraFields = 
        if ddef.is-open then 1 // open datatype tag
        elif willNeedStructTag then 1 // explicit struct tag
        else 0
      val (ddef1, conInfos1) = create-data-def(emit-error, emit-warning, lookup-datainfo, platform, qname, resultHasKindStar, isRec, sort, extraFields, ddef, conInfos0)
      val dataInfo = DataInfo(sort, qname, newtp'.tb/kind, typeVars, conInfos1, rng, ddef1, dataEff, isRec, vis, doc)
      val declaration = (if dataInfo.di/is-lazy then "lazy " else "")
                        ++ (if !sort.is-inductive then "" elif ddef1.is-value then "value " else "reference ")
                        ++ sort.show

      // TODO: Assertion
      add-range-info(rng, RIDecl(declaration, qname, qname.mangle-type-name, Nothing))
      (Data(dataInfo), lazyExprss.concat)

fun occurs-negative-con(names: list<name>, ci: conInfo)
  val (_, rho) = ci.typeScheme.split-type-scheme
  match rho.split-fun-type
    Just((pars, _, res)) -> pars.map(snd).any(_.occurs-negative(names)) || res.occurs-negative(names)
    _ -> False

fun occurs-negative(tp: ktype, names: list<name>)
  tp.occurs(names, False)

fun occurs(tp: ktype, names: list<name>, isNeg: bool)
  match tp
    TForAll(_, tp) -> tp.occurs(names, isNeg)
    TFun(args, eff, res) -> args.map(snd).any(_.occurs(names, !isNeg)) || eff.occurs(names, !isNeg) || res.occurs(names, isNeg)
    TCon(tcon) -> if names.any(_ == tcon.name) then isNeg else False
    TVar -> False
    TApp(tp, args) -> Cons(tp, args).any(_.occurs(names, isNeg))
    TSyn(_, _, t) -> t.occurs(names, isNeg)

fun typebinder/show(TypeBinder(name, kind, _, _): typeBinder<kind>)
  name.show ++ ":" ++ kind.show

fun resolve-typebinder-def(TypeBinder(name, infkind, rngName, rng): typeBinder<infKind>, doc)
  val infkind' = infkind.resolve-kind
  val qname = name.qualify-def
  add-range-info(rngName, RIId(qname, NITypeCon(infkind', doc), [], True))
  TypeBinder(qname, infkind', rngName, rng)

fun resolve-typebinder(TypeBinder(name, infkind, rngName, rng): typeBinder<infKind>, doc)
  val infkind' = infkind.resolve-kind
  add-range-info(rngName, RIId(name, NITypeCon(infkind', doc), [], True))
  TypeBinder(name, infkind', rngName, rng)

fun resolve-kind(infkind: infKind)
  val skind = subst(infkind)
  fun resolve(k: infKind)
    match skind
      KIVar(_) -> kindStar // default unconstrained parameter to kind star
      KICon(k') -> k'
      KIApp(k1, k2) -> KApp(k1.resolve, k2.resolve)
  skind.resolve

val nameTVMapEmpty = LinearMap([])

fun resolve-constructor(typeName: name, typeSort: dataKind, isSingleton: bool, typeResult: ktype, typeParams: list<typeVar>,
  idmap: name-map<typeVar>, UserCon(cname, exists0, params, mbResult, mblazy, rngName, rng, vis, doc): userCon<kUserType<infKind>, userType, infKind>, tag)
  val qname = cname.qualify-def
  val exists' = exists0.map(_.resolve-typebinder(""))
  val existsVars = exists'.map(fresh-typevar(_, Bound))
  val idmap' = (nameTVMapEmpty + exists'.map(name).zip(existsVars)) // assume left biased union 
  val params' = params.map(resolve-con-param(idmap', _))
  val result = match mbResult
    Nothing -> TApp(typeResult, typeParams.map(TVar))
    Just(tp) -> resolve-type(idmap', False, tp)
  val mbLazy' = match mblazy
    Nothing -> Nothing
    Just((fip, e)) -> Just((fip, kinfer(e)))
  val lazyExpr = match mbLazy'
    Nothing -> []
    Just((_, e)) -> [(qname, e)]
  val mbLazyFip = mbLazy'.map(fn((fip, _)) fip)
  val scheme = quantify-type(typeParams ++ existsVars, if params'.is-nil then result else TFun(params'.map(fn((_, p)) (p.name, p.binderType)), typeTotal, result))
  add-range-info(rng, RIDecl("con", qname, qname.mangle-con-name, Just(scheme)))
  add-range-info(rngName, RIId(qname, NICon(scheme, doc), [], True))
  val fields = params'.map(snd).map-indexed(fn(i, b) (if b.name.is-nil then (i + 1).new-field-name else b.name, b.binderType))
  (lazyExpr, 
   ConInfo(qname, typeName, typeParams, existsVars, fields, scheme, typeSort, rngName, 
    params'.map(fn((_, b)) b.name-range), params'.map(fst), isSingleton, [], zero, // Initialized later at the datadef
    mbLazyFip, tag, vis, doc))

fun resolve-con-param(idmap: name-map<typeVar>, (vis, ValueBinder(name, tp, mbExpr, nameRng, rng)): (visibility, valueBinder<kUserType<infKind>, maybe<syntax/syntax/expr<userType>>>))
  val tp' = resolve-type(idmap, False, tp)
  val expr = match mbExpr
    Nothing -> Nothing
    Just -> Just(fail("kind/kinfer/resolve-con-param: optional parameter expression in constructor"))
  // add-range-info(nameRng, RIId(name, NIValue("val", tp', "", True), [], True))
  (vis, ValueBinder(name, tp', expr, nameRng, rng))

// resolve-type takes: a map from locally quantified type name variables to types,
// a boolean that is 'True' if partially applied type synonyms are allowed (i.e. when
// these are arguments to type synonyms themselves), a user type with inference kinds,
// and it returns a fully resolved type
fun resolve-type(idmap: name-map<typeVar>, partialSyn: bool, userType: kUserType<infKind>)
  fun resolve-param((nm, tp): (name, kUserType<infKind>))
    (nm, resolve-type(idmap, False, tp))
  fun collect-args(args: list<kUserType<k>>, tp: kUserType<k>): (kUserType<k>, list<kUserType<k>>)
    match tp
      TpApp(tp', args') -> collect-args(args' ++ args, tp')
      TpParens(tp') -> collect-args(args, tp')
      TpAnn(tp') -> collect-args(args, tp')
      _ -> (tp, args)
  match userType
    TpQuan(QForall, tname, tp) ->
      val tname' = tname.resolve-typebinder("")
      val tvar = fresh-typevar(tname', Bound)
      val tp' = resolve-type(idmap.set(tname.name, tvar), False, tp)
      quantify-type([tvar], tp')
    TpQuan(QSome, tname, tp) ->
      val tname' = tname.resolve-typebinder("")
      val tvar = fresh-typevar(tname', Meta)
      val tp' = resolve-type(idmap.set(tname.name, tvar), False, tp)
      tp'
    TpQuan(QExists) ->
      fail("kind/kinfer resolve-type: existentials are not supported yet")
    TpFun(args, eff, tp) ->
      val args' = args.map(resolve-param)
      val eff' = resolve-type(idmap, False, eff)
      val tp' = resolve-type(idmap, False, tp)
      TFun(args', eff', tp')
    TpApp(tp, args, rng) ->
      resolve-app(idmap, partialSyn, args.collect-args(tp), rng)
    TpVar(_, rng) ->
      resolve-app(idmap, partialSyn, (userType, []), rng)
    TpCon(_, rng) ->
      resolve-app(idmap, partialSyn, (userType, []), rng)
    TpParens(tp) ->
      resolve-type(idmap, partialSyn, tp)
    TpAnn(tp) ->
      resolve-type(idmap, partialSyn, tp)

fun resolve-app(idmap: name-map<typeVar>, partialSyn: bool, (tp, args): (kUserType<infKind>, list<kUserType<infKind>>), rng: range)
  match (tp, args)
    (TpVar(name, r), _) ->
      val (tp', kind) = match idmap.lookup(name)
        Nothing ->
          add-error(rng, "Type variable".text |+| name.pretty.color(colors.colorType) |+| "is undefined".text |-|
            " hint: bind the variable using".text |+| ("forall<".text |.| name.pretty |.| ">".text).color(colors.colorType))
          (TVar(TypeVar(name.show.unique-id, kindStar, Bound)), kindStar)
        Just(tvar) -> (TVar(tvar), tvar.kind)
      if !name.is-implicit-typevar-name then
        add-range-info(r, RIId(name, NITypeVar(kind), [], False))
      val args' = args.map(resolve-type(idmap, False, _))
      TApp(tp', args')
    (TpCon(name), [fixed, ext]) | name == nameEffectAppend ->
      val fixed' = resolve-type(idmap, False, fixed)
      val ext' = resolve-type(idmap, False, ext)
      val (_, tl) = fixed'.extract-ordered-effect
      if !tl.is-effect-empty then
        add-error(rng, "Effects can only have one extension point (use a `|` instead of a comma in the effect type ?)".text)
      (fixed'.shallow-effect-extend(ext'))
    (TpCon(nm, r), _) ->
      val (qname, ikind, doc) = find-infkind(nm, rng)
      val k = ikind.resolve-kind
      add-range-info(r, RIId(qname, NITypeCon(k, doc), [], False))
      val mbSyn = get-syns().lookup(nm)
      match mbSyn
        Just(syn as SynInfo(name, kind, params, tp', rank)) ->
          // check over/under application
          if !partialSyn && args.length < params.length then
            add-error(rng, "Type alias".text |+| name.pretty.color(colors.colorType) |+| "is not fully applied".text |-|
              " hint: add more type arguments".text)
          elif args.length > params.length then
            add-error(rng, "Type alias".text |+| name.pretty.color(colors.colorType) |+| "is over-applied".text |-|
              " hint: remove some type arguments".text)
          else ()
          val args' = args.map(resolve-type(idmap, False, _)) // partially applied synonyms are allowed in synonym applications
          val tsyn = TSyn(TypeSyn(name, kind, rank, Just(syn)), args', params.zip(args').sub |-> tp')
          tsyn
          // NOTE: on partially applied type synonyms, we geet a funky body type with free parameters but this
          // is only inside synonyms arguments so we are ok
        Nothing ->
          TApp(TCon(TypeCon(nm, k)), args.map(resolve-type(idmap, False, _)))
    _ -> fail("kind/kinfer resolve-app: this case should never occur after kind checking")

fun make-effect-append(fixed, ext)
  TpApp(TpCon(nameEffectAppend, null), [fixed, ext], null)

fun make-effect-extend(label, ext)
  TpApp(TpCon(nameEffectExtend, null), [label, ext], null)

val make-effect-empty =
  TpCon(nameEffectEmpty, null)