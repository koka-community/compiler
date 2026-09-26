module compiler/kind/synthesize

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
import compiler/common/unique
import compiler/syntax/syntax
import compiler/syntax/promote
import compiler/syntax/range-map
import compiler/core/core
import compiler/kind/import-map
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
import std/data/rb-set
import std/data/sort
import std/data/rb-map
// Synthesized definitions for data types: copy/accessors/testers/tags and lazy machinery.
// Split out of kind/infer.kk (upstream this all lives in Kind/Infer.hs) to speed up type checking.
// Ported as of 2026-01-29; approx upstream baseline commit 486ef0d of Kind/Infer.hs (backfilled 2026-07-23; synced 2026-07-23)

alias lazyExpr = (name, syntax/syntax/expr<ktype>)

// resolve a promoted user type to a ktype; provided by kind/infer.kk
// (avoids a circular dependency on the kind-inference of type expressions)
pub effect lazy-resolve
  fun lazy-resolve-type(tp: user-type, rng: range): ktype

pub fun syn-typedef-groups(tdgs: list<core/core/typedef-group>, lazyExprs: list<lazyExpr>)
  tdgs.flatmap(_.syn-typedef-group(lazyExprs))

fun syn-typedef-group(tdg: core/core/typedef-group, lazyExprs: list<lazyExpr>): _ syntax/syntax/def-groups<ktype>
  tdg.flatmap(_.syn-typedef(lazyExprs))

fun syn-typedef(td: core/core/typedef, lazyExprs: list<lazyExpr>): _ list<syntax/syntax/def-group<ktype>>
  match td
    core/core/Synonym -> []
    Data(di) | di.name.is-hidden-name -> []
    Data(di) ->
      with with-data(di)
      val accessors = if !(di.is-open || di.di/is-lazy) then syn-accessors() else []
      val copycon = if di.constrs.length == 1 && !(di.is-open || di.di/is-lazy) && !di.constrs.head.unjust.name.is-hidden-name && di.kind.has-kind-star-result then
                      [with-con(di.constrs.head.unjust, syn-copycon)]
                    else []
      val testers = if (di.constrs.length > 1 || di.is-open) && !di.di/is-lazy then
                      di.constrs.flatmap(with-con(_, syn-tester))
                    else []
      val contag = if di.is-open then di.constrs.map(with-con(_, syn-constr-tag)) else []
      val synLazy = if di.di/is-lazy then // upstream synTypeDef: tag ++ evalLocked ++ eval ++ whnf ++ force ++ step
                      [syn-lazy-tag()] ++ syn-lazy-eval-locked(lazyExprs) ++
                        [syn-lazy-eval(), syn-lazy-whnf(), syn-lazy-force(), syn-lazy-step()]
                    else [] 
      // Accessors ++ copycon ++ testers ++ contag ++ synLazy
      accessors ++ copycon ++ testers ++ contag ++ synLazy

effect current-data-info
  val data-info : data-info
  val data-def-name: name
  val lazy-constructors: list<con-info>
  val whnf-constructors: list<con-info>
  fun lazy-name(str: string): name
  fun alloc-size-scan(conInfo: con-info): (int, int)
effect current-con-info
  val con-info : con-info
  val con-range: range
  val con-name: name
fun with-data(di: data-info, action: () -> _ a): _ a
  val (lazy-cons, whnf-cons) = di.constrs.partition(coninfo/is-lazy)
  val p = get-platform()
  with handler 
    val data-info = di 
    val data-def-name = di.name
    fun lazy-name(n) di.lazy-name(n)
    fun alloc-size-scan(ci)
      alloc-size-scan(di.con-repr(ci), p)
    val lazy-constructors = lazy-cons
    val whnf-constructors = whnf-cons
  action()
fun with-con(ci: con-info, action: () -> _ a): _ a
  with handler 
    val con-info = ci 
    val con-range = ci.range.hide
    val con-name = ci.name
  action()

fun syn-copycon()
  val cr = con-range
  val defName = copy-name-of(data-def-name).unqualify
  val argName = "@this".new-name
  val fullTp = 
    val (vars, rho) = con-info.typeScheme.split-type-scheme
    match rho.split-fun-type
      Just((args, eff, res)) -> TForAll(vars, TFun([(argName, res)] ++ args.map(fn((nm, t)) (nm, if !has-accessor(nm, t) then t else t.make-optional)), eff, res))
      Nothing -> TForAll(vars, TFun([(argName, rho)], typeTotal, rho))
  fun vvar(n) Var(n, False, cr)
  fun app(x, xs)
    match xs 
      Nil -> x 
      _ -> App(x, xs.map((Nothing, _)), cr)
  val params0 = con-info.params.map(fn((fldname, t)) ValueBinder(fldname, Nothing, if !has-accessor(fldname, t) then Nothing else Just(app(vvar(type-qualified-name-of(data-def-name, fldname)), [vvar(argName)])), cr, cr))
  val body = app(vvar(con-name), con-info.params.map(fn((nm, _)) vvar(nm)))
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, cr, cr)] ++ params0, body, True, cr)
  DefNonRec(Def(ValueBinder(defName, (), Ann(expr, fullTp, cr), cr, cr), cr, data-info.vis, def-fun([]), InlineAuto, ""))

fun ci/has-accessor(ci: con-info, nm: name, tp: ktype)
  val tvs = tp.free-type-vars
  !(nm.is-field-name || nm == nil) && ci.existentials.all(!tvs.member(_))

fun con-info/has-accessor(nm: name, tp: ktype)
  val tvs = tp.free-type-vars
  !(nm.is-field-name || nm == nil) && con-info.existentials.all(!tvs.member(_))

fun is-alphanum(c: char)
  c.is-alpha || c.is-digit

fun syn-accessors()
  val di = data-info
  val paramss = di.constrs.map(fn(ci) ci.params.zipwith(ci.paramVis.zip(ci.paramRanges)) fn((nm, tp), (pvis, rng))
    (nm, (tp, rng, pvis, ci))
  )
  fun occurs-on-all-constrs((nm, (tp, _, _, _)))
    nm != nil && paramss.all(_.any(fn((n, (t, _, _, _))) n == nm && t.eq-type(tp)))
  val fields = paramss.concat.filter(fn((nm, (tp, _, _, cinfo))) cinfo.has-accessor(nm, tp)).nub-by(_.fst == _.fst).filter(occurs-on-all-constrs)
  fun syn-accessor((nm, (tp, xrng, visibility, _)))
    val rng = xrng.hide
    val defName = type-qualified-name-of(di.name, nm).unqualify
    val arg = 
      val dataName = di.name.unqualify
      if dataName.show.list.all(is-alphanum) then dataName else "@this".new-name
    val fld = "x".new-hidden-name
    val dataTp = type-app(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
    fun make-branch(ci: con-info)
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
    val doc = "// Automatically generated. Retrieves the `" ++ nm.show ++ "` constructor field of the `:" ++ di.name.local ++ "` type.\n"
    val defaultBranch = if isPartial then [Branch(PatWild(rng), [Guard(guardTrue, App(Var(namePatternMatchError, False, rng), messages.map((Nothing, _)), rng))])] else []
    val caseExpr = Case(Var(arg, False, rng), branches.map(snd) ++ defaultBranch, False, rng)
    val expr = Ann(Lam([ValueBinder(arg, Nothing, Nothing, rng, rng)], caseExpr, True, rng), fullTp, xrng)
    DefNonRec(Def(ValueBinder(defName, (), expr, xrng, xrng), rng, visibility, def-fun-ex([Borrow], noFip), InlineAlways, doc))
  fields.map(syn-accessor)

fun syn-tester()
  val ci = con-info
  if ci.name.is-hidden-name || ci.coninfo/is-lazy then []
  else
    val def-name = "is-".prepend-raw(ci.name.unqualify.to-var-name)
    val arg = data-def-name.unqualify
    val rc = ci.range.hide
    val patterns = ci.params.map(fn(_) (Nothing, PatWild(rc)))
    val branch1 = Branch(PatCon(ci.name, patterns, rc, rc), [Guard(guardTrue, Var(nameTrue, False, rc))])
    val branch2 = Branch(PatWild(rc), [Guard(guardTrue, Var(nameFalse, False, rc))])
    val caseExpr = Case(Var(arg, False, rc), [branch1, branch2], ci.coninfo/is-lazy, rc)
    val expr = Lam([ValueBinder(arg, Nothing, Nothing, rc, rc)], caseExpr, True, rc)
    val doc = "// Automatically generated. Tests for the `" ++ ci.name.name/local ++ "` constructor of the `:" ++ data-def-name.name/local ++ "` type.\n"
    [DefNonRec(Def(ValueBinder(def-name, (), expr, rc, rc), rc, ci.vis, def-fun-ex([Borrow], Fip(AllocAtMost(0))), InlineAlways, doc))]

fun syn-constr-tag()
  val ci = con-info
  val nm = ci.name.unqualify.to-open-tag-name
  val rc = ci.range.hide
  val expr = Literal(LitString(ci.name.show, rc))
  // Tags must be public, since they may extend a type outside of the current module
  DefNonRec(Def(ValueBinder(nm, (), expr, rc, rc), rc, Public, DefVal, InlineNever, ""))

// Lazy types and constructors 
/* 
add a lazy tag
```koka
lazy type stream<a>
  SNil
  SCons(head: a, tail: stream<a>)
  lazy SAppRev(pre: stream<a>, post:list<a>) -> 
    match pre 
      SNil -> sreverse(post)
      SCons(x,xx) -> SCons(x, SAppRev(xx,post))
  
val stream/lazy-tag = 3
```
*/

fun syn-lazy-tag()
  val di = data-info
  val xrng = di.range
  val rng = xrng.hide
  val defName = lazy-name("tag")
  val lazyTag = 
    match di.constrs.find(_.name.is-lazy-indirect-con-name)
      Nothing -> failure/fail("kind/infer/syn-lazy-tag: no indirection constructor found: " ++ di.name.show)
      Just(ind) -> ind.tag
  val expr = App(Var(nameInternalInt32, False, rng), [(Nothing, Literal(syntax/syntax/LitInt(lazyTag, rng)))], rng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefVal, InlineAlways, "// Automatically generated tag value of lazy indirection"))

/*
force is a one step unfolding of whnf and is inlined at call sites.
inline fun stream/lazy-force(s: stream<a>): div stream<a>
  if lazy/datatype-is-whnf(s,stream/lazy-tag)
    then s 
    else stream/lazy-whnf(s)
*/
fun syn-lazy-force()
  val di = data-info
  val xrng = di.range
  val rng = xrng.hide
  val defName = lazy-name("force")
  val dataTp = type-app(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  val fullTp = TForAll(di.params, TFun([(nil, dataTp)], typeDivergent, dataTp))
  val nameIsWhnf = 
    if di.constrs.all(fn(ci: con-info) ci.params.length > 0)
    then nameLazyPtrIsWhnf else nameLazyIsWhnf
  
  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)
  val tst = App(Var(nameIsWhnf, False, rng), [(Nothing, arg), (Nothing, Var(lazy-name("tag"), False, rng))], rng)
  val whnf = App(Var(lazy-name("whnf"), False, rng), [(Nothing, arg)], rng)
  val body = Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, arg)]), 
                        Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, whnf)])], False, rng)
  val expr = Ann(Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], body, True, xrng), fullTp, rng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineAlways, ""))

// recursive force:
// noinline fun stream/lazy-whnf(s: stream<a>): div stream<a>
//   val x = stream/lazy-eval(s,True)
//   if lazy/datatype-is-whnf(x, stream/lazy-tag) then x else stream/lazy-whnf(x)

fun syn-lazy-whnf()
  val di = data-info
  val xrng = di.range
  val rng = xrng.hide
  val defName = lazy-name("whnf")
  val dataTp = type-app(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  val nameIsWhnf = 
    if di.constrs.all(fn(ci: con-info) ci.params.length > 0)
    then nameLazyPtrIsWhnf else nameLazyIsWhnf

  val valName = "val".new-hidden-name
  val vl = Var(valName, False, rng)

  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)

  val nameEval = lazy-name("eval")
  val evalExpr = App(Var(nameEval, False, rng), [(Nothing, arg), (Nothing, Var(nameTrue, False, rng))], rng)
  val valDef = Def(ValueBinder(valName, (), evalExpr, rng, rng), rng, Private, DefVal, InlineNever, "")
  val tst = App(Var(nameIsWhnf, False, rng), [(Nothing, vl), (Nothing, Var(lazy-name("tag"), False, rng))], rng)
  val whnf = App(Var(lazy-name("whnf"), False, rng), [(Nothing, vl)], rng)
  val body = Bind(valDef, Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, vl)]), 
                                     Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, whnf)])], False, rng), rng)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], body, True, xrng)
  DefRec([Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineNever, "")])


// Add lazy evaluation step:
// ```
// inline fun stream/lazy-step( @lazy : stream<a> ) : _ stream<a>
//   if lazy/datatype-is-whnf(@lazy,stream/lazy-tag)
//       then s
//       else stream/lazy-eval(@lazy,False)
// ```
fun syn-lazy-step()
  val di = data-info
  val xrng = di.range
  val rng = xrng.hide
  val defName = lazy-name("step")
  val dataTp = type-app(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  // val fullTp = TForAll(di.params, TFun([(nil, dataTp)], typePure, dataTp))
  val nameIsWhnf = 
    if di.constrs.all(fn(ci: con-info) ci.params.length > 0)
    then nameLazyPtrIsWhnf else nameLazyIsWhnf
  val argName = "lazy".new-hidden-name
  val arg = Var(argName, False, rng)
  val tst = App(Var(nameIsWhnf, False, rng), [(Nothing, arg), (Nothing, Var(lazy-name("tag"), False, rng))], rng)
  val eval = App(Var(lazy-name("eval"), False, rng), [(Nothing, arg), (Nothing, Var(nameFalse, False, rng))], rng)
  val body = Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, arg)]),
                        Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, eval)])], 
                        False, rng)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rng, rng)], body, True, xrng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineNever, ""))

/*
noinline fun stream/lazy-eval(s : stream<a>, recurse : bool ) : _ stream<a>
  if lazy/datatype-ptr-is-unique || !lazy/atomic-enter(s,stream/lazy-tag) then
    stream/lazy-eval-locked(s,recurse)
  else
    val v = stream/lazy-eval-locked(s,recurse)
    lazy/atomic-leave(s)
    v
*/
fun syn-lazy-eval()
  val di = data-info
  val xrng = di.range
  val rng = xrng.hide
  val defName = lazy-name("eval")
  val dataTp = type-app(TCon(TypeCon(di.name, di.kind)), di.params.map(TVar))
  val fullTp = TForAll(di.params, TFun([(nil, typeBool), (nil, dataTp)], typePure, dataTp))
  val recName = "recurse".new-hidden-name
  val argName = "lazy".new-hidden-name
  val recurse = Var(recName, False, rng)
  val arg = Var(argName, False, rng)
  val tst = App(Var(nameOr, False, rng), [(Nothing, App(Var(nameDataTypePtrIsUnique, False, rng), [(Nothing, arg)], rng)),
                                          (Nothing, App(Var("std/core/types".new-qualified("not"), False, rng), 
                                                        [(Nothing, App(Var(nameLazyEnter, False, rng), 
                                                                       [(Nothing, arg),(Nothing,Var(lazy-name("tag"), False, rng))], rng))], rng))], rng)
  val eval = App(Var(lazy-name("eval-locked"), False, rng), [(Nothing, arg), (Nothing, recurse)], rng)
  val atomic = 
    val v = "v".new-name 
    val vdef = Def(ValueBinder(v, (), eval, rng, rng), rng, Private, DefVal, InlineNever, "")
    val bdef = Def(ValueBinder(nil, (), App(Var(nameLazyLeave, False, rng), [(Nothing, arg)], rng), rng, rng), rng, Private, DefVal, InlineNever, "")
    Bind(vdef, Bind(bdef, Var(v, False, rng), rng), rng)
  val body = Case(tst, [Branch(PatCon(nameTrue, [], rng, rng), [Guard(guardTrue, eval)]), 
                        Branch(PatCon(nameFalse, [], rng, rng), [Guard(guardTrue, atomic)])], False, rng)
  val expr = Lam([ValueBinder(argName, Nothing, Nothing, rng, rng), ValueBinder(recName, Just(typeBool), Nothing, rng, rng)], body, True, xrng)
  DefNonRec(Def(ValueBinder(defName, (), expr, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineNever, ""))

/*
Add lazy evaluation:
```koka
noinline fbip fun stream/lazy-eval-locked( s : stream<a>,recurse : bool ) : _ stream<a>
  lazy-whnf-target(s)
  match s
    SAppRev(pre, post) -> stream/lazy-SAppRev( s, recurse, pre, post )
    SIndirect(ind)     -> ind
    _                  -> s
```
*/
fun syn-lazy-eval-locked(les : list<lazyExpr>): _ list<compiler/syntax/syntax/def-group<ktype>>
  val di = data-info
  val xrng = di.range 
  val rng = xrng.hide
  val def-name = lazy-name("eval-locked")
  val rec-name = "recurse".new-hidden-name
  val arg-name = "lazy".new-hidden-name
  val rec = Var(rec-name, False, rng)
  val arg = Var(arg-name, False, rng)
  fun rotate(xs)
    match xs 
      Nil -> Nil
      Cons(x, xs) -> xs ++ [x]
  val lazy-cons = di.constrs.filter(coninfo/is-lazy).rotate // indirect match comes last
  fun branch-expr(ci: con-info, par-names: list<name>)
    match les.lookup(ci.name)
      Just(lazyExpr) -> with-con(ci, {lazy-con-def-call(di, ci, par-names, rec, arg, lazyExpr)}) 
      Nothing -> failure/fail("kind/infer/syn-lazy-eval-locked/branch-expr: cannot find expression for lazy constructor " ++ ci.name.show)
  fun branch(ci: con-info)
    if ci.name.is-lazy-indirect-con-name then 
      val [(par, _)] = ci.params
      val compress = App(Var(nameLazyIndirectCompress, False, rng), [(Nothing, Var(par, False, rng)), (Nothing, Var(lazy-name("tag"), False, rng))], rng)
      ([],Branch(PatCon(ci.name, [(Nothing, PatVar(ValueBinder(par, Nothing, PatWild(rng), rng, rng)))], rng, rng), [Guard(guardTrue, compress)]))
    else 
      val par-names = ci.params.map-indexed(fn(i: int, (par, _)) if par.is-wildcard then par.un-wildcard.postpend-raw((i + 1).int/show) else par)
      val (def, body) = ci.branch-expr(par-names)
      fun make-pat(p, r)
        if p.is-wildcard then PatWild(r)
        else PatVar(ValueBinder(p, Nothing, PatWild(r), r, r))
      ([def], Branch(PatCon(ci.name, par-names.map(fn(par) (Nothing, make-pat(par, rng))), rng, rng), [Guard(guardTrue, body)]))
  val (defss, branches) = lazy-cons.map(branch).unzip
  val body = Case(arg, branches ++ [Branch(PatWild(rng), [Guard(guardTrue, arg)])], True, rng)
  val lam = Lam([ValueBinder(arg-name, Nothing, Nothing, rng, rng), ValueBinder(rec-name, Just(typeBool), Nothing, rng, rng)], body, True, xrng)
  val def = Def(ValueBinder(def-name, (), lam, rng, rng), rng, di.vis, DefFun([], di.lazy-fip), InlineNever, "")
  defss.concat.map(DefNonRec) ++ [DefNonRec(def)]

fun lookup-con(constrs: list<con-info>, cname: name)
  val modName = data-info.name.qualifier
  constrs.find fn(ci: con-info)
    ci.name == (if cname.is-qualified then cname else qualify(modName, cname))

fun is-whnf-con(cname: name)
  lookup-con(whnf-constructors, cname).is-just

fun is-whnf-con-pat(p)
  match p
    PatParens(pat) -> is-whnf-con-pat(pat)
    PatAnn(pat) -> is-whnf-con-pat(pat)
    syntax/syntax/PatVar(v) -> is-whnf-con-pat(v.expr)
    syntax/syntax/PatCon(cname) -> is-whnf-con(cname)
    _ -> False

fun is-whnf-con-branch(b)
  match b
    syntax/syntax/Branch(p) -> is-whnf-con-pat(p)

// Lazy constructor
//  ```
// SAppRev( pre, post )
//     -> match pre
//          SNil        -> sreverse(post)
//          SCons(x,xx) -> SCons(x,SAppRev(xx,post))
// ```
// ~>
// ```
// fun stream/lazy-SAppRev(  @lazy : stream<a>, recurse : bool, pre : stream<a>, post : stream<a> ) : stream<a>
//   lazy/memoize-target(@lazy)
//   match pre
//     SNil        -> lazy/memoize(@lazy,sreverse(post))
//                 or: if recurse then lazy-SAppRev(s,recurse,...) else lazy/memoize(@lazy,SAppRev(...))
//     SCons(x,xx) -> lazy/memoize(@lazy,SCons(x,SAppRev(xx,post)))
// ```


fun lazy-con-def-call(di: data-info, ci: con-info, par-names: list<name>, recurse-arg: compiler/syntax/syntax/expr<ktype>, memo-target: compiler/syntax/syntax/expr<ktype>, top-expr: compiler/syntax/syntax/expr<ktype>): _ (compiler/syntax/syntax/def<ktype>, compiler/syntax/syntax/expr<ktype>)
  val rng = ci.range 
  val nameLazyCon = lazy-name(ci.name.unqualify.show)// lazy-SAppRev
  val modName = di.name.qualifier
  fun memoize-con(cname, c, nargs, range)
    match whnf-constructors.lookup-con(cname)
      Just(whnfCon) -> // strict constructor result
        memoize-check-can-fit(rng, whnfCon)
        make-app(c, nargs, range).simple/memoize
      Nothing -> // lazy constructor
        match lazy-constructors.lookup-con(cname)
          Nothing -> // unknown constructor
            memoize-unknown(make-app(c, nargs, range))
          Just(cinfo) -> // known lazy constructor 
            val (target-size, target-scan) = alloc-size-scan(ci)
            val (result-size, result-scan) = alloc-size-scan(cinfo)
            if target-size >= result-size && target-scan >= result-scan then 
              // recursively call a lazy constructor function directly
              val rec-call = 
                val con-fun-name = lazy-name(cinfo.name.unqualify.show)
                App(Var(con-fun-name, False, range), [(Nothing, Var(nameLazyMemo, False, range)), (Nothing, Var(nameRecurse, False, range))] ++ nargs, range)
              val step-call = make-app(c, nargs, range).simple/memoize
              Case(Var(nameRecurse, False, range), [Branch(PatCon(nameTrue, [], range, range), [Guard(guardTrue, rec-call)]), 
                                                    Branch(PatCon(nameFalse, [], range, range), [Guard(guardTrue, step-call)])], False, range)
            else // memoize and return; whnf does the recursion
              memoize-warning(range, fn(_) "in-place as the result constructor does not have the same size as the lazy target (".text |.| target-size.pretty |+| "vs".text |+| result-size.pretty |+| "bytes) -- using an indirection instead".text)
              make-app(c, nargs, range).simple/memoize

  // lazy-SAppRev(@recurse,@lazy,pre,post)
  val call-expr = App(Var(nameLazyCon, False, rng), [(Nothing, memo-target), (Nothing, recurse-arg)] ++ par-names.map((Nothing, Var(_, False, rng))), rng)
  val branch-expr = top-expr.expr/memoize
  val user-tp-con = TpCon(di.name, rng)
  val user-tp-var-names = di.params.map(("_" ++ _.show).new-name)
  val user-data-tp = if user-tp-var-names.is-nil then user-tp-con else TpApp(user-tp-con, user-tp-var-names.map(TpVar(_, rng)), rng)
  val user-con-tps = ci.params.map-indexed fn(i, (par, _)) 
    (par, TpVar(("_" ++ (i + 1).show).new-name, rng))
  val user-full-tp = TpFun([(nil, user-data-tp), (nil, TpCon(nameTpBool, rng))] ++ user-con-tps, TpVar("_eff".new-name, rng), user-data-tp, rng)
  val full-tp = lazy-resolve-type(user-full-tp, rng)
  val (target-size, target-scan) = alloc-size-scan(ci)
  val target = Def(ValueBinder(nil, (), App(Var(nameLazyMemoizeTarget, False, rng), 
                  [(Nothing, Var(nameLazyMemo, False, rng)),
                   (Nothing, Literal(LitInt(target-size, rng))),
                   (Nothing, Literal(LitInt(target-scan, rng)))], rng), rng, rng), rng, Private, DefVal, InlineNever, "")
  val lam = Lam([ValueBinder(nameLazyMemo, Nothing, Nothing, rng, rng), ValueBinder(nameRecurse, Just(typeBool), Nothing, rng, rng)] ++ 
                 par-names.map(ValueBinder(_, Nothing, Nothing, rng, rng)), Bind(target, branch-expr, rng), True, rng)
  // fun lazy-SAppRev(@memo,recurse,pre,post)
  //   lazy/memoize-target(@memo)
  //   <memoize topExpr>
  val def = Def(ValueBinder(nameLazyCon, (), Ann(lam, full-tp, rng), rng, rng), rng, Private, DefFun([], ci.lazy-fip), InlineAuto, "")
  (def, call-expr)

fun expr/memoize(e)
  match e
    Lam(binds, expr, tl, rng) -> Lam(binds, expr.expr/memoize, tl, rng)
    Let(defs, expr, rng) -> Let(defs, expr.expr/memoize, rng)
    Bind(def, expr, rng) -> Bind(def, expr.expr/memoize, rng)
    Ann(expr, tp, rng) -> Ann(expr.expr/memoize, tp, rng)
    Case(expr, brs, lazy-match, rng) -> 
      // specialize force insertion here so the dependency is known
      // for all other matches, this is done during type inference
      val brs' = brs.map(branch/memoize)
      val force-name = lazy-name("force")
      val expr-force = if !lazy-match && brs.any(is-whnf-con-branch) then 
          val r = expr.range.hide 
          App(Var(force-name, False, r), [(Nothing, expr)], r)
        else expr
      Case(expr-force, brs', lazy-match, rng)
    Parens(expr, name, pre, range) -> Parens(expr.expr/memoize, name, pre, range)
    App(c as Var(cname), nargs, range) -> cname.memoize-con(c, nargs, range)
    Var(cname, _, range) -> cname.memoize-con(e, [], range)
    _ -> memoize-unknown(e)
fun branch/memoize(compiler/syntax/syntax/Branch(pat, guards))
  compiler/syntax/syntax/Branch(pat, guards.map(guard/memoize))
fun guard/memoize(compiler/syntax/syntax/Guard(test, body))
  compiler/syntax/syntax/Guard(test, body.expr/memoize)
fun memoize-warning(rng, fdoc)
  fun show-con-name(n)
    n.unqualify.pretty.color(colors.colorCons)
  // upstream: `text "..." <+> showConName (conInfoName conInfo) <+> fdoc showConName`
  // -- the lazy constructor's NAME is printed between the prefix and the
  // detail (fdoc receives the show function for naming OTHER constructors)
  add-warning(rng, "Cannot update the lazy constructor".text |+| con-info.con-info/name.show-con-name |+| fdoc(show-con-name))
fun memoize-unknown(expr: compiler/syntax/syntax/expr<ktype>)
  val rng = expr.range.hide
  memoize-warning(rng, fn(_) "in-place as the result constructor is not statically known -- using an indirection instead".text)
  expr.simple/memoize 
fun memoize-con(cname : name, con-expr: compiler/syntax/syntax/expr<ktype>, nargs: list<(maybe<(name,range)>,compiler/syntax/syntax/expr<ktype>)>, range: range)
  match whnf-constructors.lookup-con(cname)
    // strict constructor result
    Just(whnf-con) -> 
      memoize-check-can-fit(range, whnf-con)
      make-app(con-expr, nargs, range).simple/memoize
    // lazy constructor
    Nothing -> 
      match lazy-constructors.lookup-con(cname)
        // Unknown constructors
        Nothing -> make-app(con-expr, nargs, range).memoize-unknown
        // Known lazy constructor
        Just(cinfo) -> 
          val (target-size, target-scan) = alloc-size-scan(con-info)
          val (result-size, result-scan) = alloc-size-scan(cinfo)
          if target-size >= result-size && target-scan >= result-scan then 
            val rec-call = // Recursively call a lazy constructor function directly
              val con-fun-name = lazy-name(cinfo.name.unqualify.show)
              App(Var(con-fun-name, False, range), 
                   [(Nothing, Var(nameLazyMemo, False, range)), 
                    (Nothing, Var(nameRecurse, False, range))] ++ nargs, range)
            val step-call = // step function; return the lazy constructor
              make-app(con-expr, nargs, range).simple/memoize
            val if-expr = Case(Var(nameRecurse, False, range), 
                [Branch(PatCon(nameTrue, [], range, range), [Guard(guardTrue, rec-call)]),
                 Branch(PatCon(nameFalse, [], range, range), [Guard(guardTrue, step-call)])], False, range)
            if-expr
          else // memoize and return; whnf does the recursion
            memoize-warning(range, fn(_) "in-place as the result constructor does not have the same size as the lazy target (".text |.| target-size.pretty |+| "vs".text |+| result-size.pretty |+| "bytes) -- using an indirection instead".text)
            make-app(con-expr, nargs, range).simple/memoize

val nameRecurse = "recurse".new-hidden-name
val nameLazyMemo = "lazy".new-hidden-name

fun memoize-check-can-fit(range, result-con)
  val (target-size, _) = alloc-size-scan(con-info)
  val (result-size, _) = alloc-size-scan(result-con)
  if target-size < result-size then 
    memoize-warning(range, 
      fn(_) "in-place as the result constructor is larger (".text 
        |.| target-size.pretty |+| "vs".text |+| result-size.pretty 
        |+| "bytes) -- using an indirection instead".text)
  
fun simple/memoize(expr: compiler/syntax/syntax/expr<ktype>)
  val rng = expr.range.hide 
  App(Var(nameLazyMemoize, False, rng), [(Nothing, Var(nameLazyMemo, False, rng)), (Nothing, expr)], rng)

fun make-app(c, nargs, range)
  match nargs
    Nil -> c
    Cons(_, _) -> App(c, nargs, range)

fun lazy-add-update(evalName: name, arg, topExpr)
  update/add(topExpr, arg)

fun add-guard(g, arg)
  match g
    syntax/syntax/Guard(test, expr) -> Guard(test, add(expr, arg))

fun add-branch(b, arg)
  match b
    syntax/syntax/Branch(patt, guards) -> Branch(patt, guards.map(add-guard(_, arg)))

fun update/add(e: syntax/syntax/expr<t>, arg: syntax/syntax/expr<t>): _ syntax/syntax/expr<t>
  match e
    syntax/syntax/Lam(binds, expr, tl, rng) -> syntax/syntax/Lam(binds, add(expr, arg), tl, rng)
    Let(defs, expr, rng) -> Let(defs, add(expr, arg), rng)
    Bind(def, expr, rng) -> Bind(def, add(expr, arg), rng)
    Ann(expr, tp, rng) -> Ann(add(expr, arg), tp, rng)
    Case(expr, brs, lzy, rng) ->
      val brs' = brs.map(add-branch(_, arg))
      val forceName = lazy-name("force")
      val r = expr.range.hide
      val exprForce = if !lzy && brs.any(is-whnf-con-branch) then
                        App(Var(forceName, False, r), [(Nothing, expr)], r)
                      else
                        expr
      Case(exprForce, brs', lzy, rng)
    Parens(expr, name, pre, rng) -> Parens(add(expr, arg), name, pre, rng)
    App(syntax/syntax/Var(cname), _, _) -> lazy-update-con(cname, e, arg)
    syntax/syntax/Var(cname) -> lazy-update-con(cname, e, arg)
    _ -> unknown-update(e, arg)

fun update-warning(rng: range, fdoc: (name -> doc) -> doc)
  val cs = colors
  fun show-con-name(nm: name)
    nm.unqualify.pretty.color(cs.colorCons)
  add-warning(rng, "Cannot update the lazy constructor".text |+| con-info.name.show-con-name |+| fdoc(show-con-name))

fun lazy-update-con(cname: name, expr, arg)
  match whnf-constructors.lookup-con(cname)
    Nothing -> match lazy-constructors.lookup-con(cname)
      Nothing -> unknown-update(expr, arg)
      Just(ci') -> recursive-update(ci', expr, arg)
    Just(whnf) ->
      warn-update(expr.range, whnf)
      lazy-update(expr, arg)

fun unknown-update(expr, arg)
  val rng = expr.expr/range.hide
  update-warning(rng, fn(_) "in-place as the result constructor is not statically known -- using an indirection instead".text)
  lazy-update(expr, arg)

fun recursive-update(ci': con-info, expr, arg)
  val r0 = expr.expr/range.hide
  // No need to warn anymore as we don't force recursively here
  warn-update(expr.range, ci')
  lazy-update(expr, arg)

fun warn-update(rng: range, resultCon)
  val di = data-info
  val ci = con-info
  val lazySize = alloc-size(con-repr(di, ci), get-platform())
  val whnfSize = alloc-size(con-repr(di, resultCon), get-platform())
  if lazySize < whnfSize then
    // upstream `warnUpdate` always names the constructor actually being
    // updated (from the ambient `ConEnv`/`con-info` installed by the
    // caller), never the replacement `resultCon` -- re-handling `con-info`
    // to `resultCon` here made `update-warning`'s diagnostic (which reads
    // the ambient `con-info.name`) name the wrong constructor.
    update-warning(rng, fn(_) "in-place as the result constructor is larger(".text |.| lazySize.pretty |+| "vs".text |+| whnfSize.pretty |+| "bytes".text)

fun lazy-update(expr, arg)
  val rng = expr.expr/range.hide
  App(Var(nameLazyMemoize, False, rng), [(Nothing, arg), (Nothing, expr)], rng)

fun lazy-fip(di: data-info)
  match di.def
    DataDefLazy(fip) -> fip
    _ -> failure/fail("kind/infer/lazy-fip: not a lazy data type? " ++ di.name.show)

// Types for constructors
pub fun constructor-gamma(dis: list<data-info>, is-value: (data-info) -> bool): _ gamma
  fun gamma(cis: list<(con-info, con-repr)>)
    cis.map(fn((ci: con-info, crepr)) (ci.name, InfoCon(ci.vis, ci.typeScheme, crepr, ci, ci.range, ci.doc))).gamma/new
  dis.flatmap(fn(di) di.constrs.zip(data-repr(di, is-value).snd)).gamma

pub fun constructor-check-duplicates(cis: list<con-info>)
  fun same-name(ci1: con-info, ci2: con-info)
    ci1.name == ci2.name
  fun duplicate(cis': list<con-info>)
    match cis'
      Cons(ci1, Cons(ci2)) -> 
        // upstream: `show (conInfoRange ci1)` -- Show Range is the start pos only
        kind-add-error(ci2.range, "Constructor".text |+| ci2.name.pretty.color(colors.colorSource) 
          |+| "is already defined at".text |+| ci1.range.start.pos/show.text)
      _ -> ()
  cis.group-by(same-name).foreach(duplicate)

