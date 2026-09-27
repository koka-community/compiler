// Updated as of 7/23/26: Commit 9bc234e
// Responsibilities of the kind checker:
// - Kindcheck all types in the program
// - Translate user types to internal types
// - Collect lists of data types, synonyms and constructors
// - Expand all synonyms (i.e., replace @id(int)@ by @id(int) == int@)
// - Translate type definition groups and externals to Core.

// Updated to 486ef0d on 11/18/25
module compiler/kind/infer

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
import compiler/kind/synthesize
import std/data/rb-map

// Kindcheck a program and calculate types
// Also group recursive type and expressing bindings in order
pub fun infer-kinds(
      isValue: (data-info) -> pure bool, // is this a value type
      target: target-platform, // target platform
      imports: import-map, // import aliases
      kgamma0: kGamma, // initial kind kgamma
      syns0: synonyms, // initial list of synonyms
      data0: newtypes) // initial list of data types
  // original program
  val Program(_, modName, nmrng, tdefs, defs, importdefs, externals, _, doc) = current-program
  // order and group recursive let-bindings
  with run-kind-infer(target, modName, imports, kgamma0, syns0, data0)
  val tdgroups0 = tdefs.group-bindings
  val (tdgroups, kgamma1, syns1, data1, lazyExprs) = kinfer(tdgroups0)
  // phase boundary: upstream never forces a failed phase's (garbage) results
  // in later phases (laziness); stop here when the typedef phase errored
  kind-flush-errors()
  // keep the extended kind environment in scope for the value definitions and
  // externals (upstream threads this through the KInfer state)
  with override val inf-kind-env = inf-kind-env(kGamma = kgamma1, synonyms = syns1, newtypesExtended = data1)
  val externals1 = kinfer(externals)
  val defs1 = kinfer(defs)
  with fun lazy-resolve-type(tp: user-type, rng: range)
    with val uctx = Infer(rng)
    tp.promote-type.inf-resolve-type
  val synDefs = tdgroups.syn-typedef-groups(lazyExprs)
  inf-imports(modName, nmrng, importdefs)

  val (_, dataInfos) = tdgroups.extract-infos.unzip-either
  val conInfos = dataInfos.flatmap(constrs)
  val cons1 = conInfos.constructors-from-list
  val gamma1 = dataInfos.constructor-gamma(data/is-value)
  conInfos.constructor-check-duplicates
  // Now order and group definitions including newly synthesized definitions for type definitions
  val dgroups = (synDefs ++ defs1).group-bindings
  (dgroups, kgamma1, (syns1, data1, cons1, gamma1), Core(modName, [], [], tdgroups, [], externals1, doc))
  
fun extract-infos(groups: list<core/core/typedef-group>): list<either<syn-info, data-info>>
  fun extract-info(td: core/core/typedef): either<syn-info, data-info>
    match td
      core/core/Synonym(si) -> Left(si)
      Data(di) -> Right(di)
  fun extract-group-infos(g: core/core/typedef-group): list<either<syn-info, data-info>>
    g.map(extract-info)
  groups.flatmap(extract-group-infos)


fun inf-imports(modName: name, modRange: range, imports: list<syntax/syntax/kimport>)
  add-range-info(modRange, RIId(modName, NIModule, [], True))
  imports.foreach(inf-import)

fun inf-import(imp: syntax/syntax/kimport)
  val syntax/syntax/Kimport(aliasn, qname, aliasRng, nameRange) = imp
  add-range-info(nameRange, RIId(qname, NIModule, [], True))
  add-range-info(aliasRng, RIId(aliasn, NIModule, [], True))

// Infer kinds for type definition groups
fun inf-resolve-type(tp: user-type)
  val infTp = kinfer(infKindStar, tp)
  resolve-type(nameTVMapEmpty, False, infTp)

fun inf-resolve-hx(tp: user-type)
  val infTp = kinfer(infKindHandled, tp)
  resolve-type(nameTVMapEmpty, False, infTp)

fun inf-resolvex(tp: user-type, rng: range)
  val ikind = fresh-kind()
  val infTp = kinfer(ikind, tp)
  val skind = subst(ikind)
  // also allow effect label constructors without giving type parameters
  val (kargs, kres) = skind.inf-extract-kind-fun
  if kargs.length > 2 || kargs.is-cons && kres.is-infkind-label then
    // either user defined, or a primitive like `:local`
    val vars = list(1, kargs.length - (if kres.is-infkind-label then 0 else 2)).map(("_" ++ _.show).new-name)
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

fun tdgs/kinfer(tdgs: list<syntax/syntax/typedef-group<user-type,user-kind>>)
  fun get-ranges(tdg)
    match tdg
      TypeDefRec(tdefs) -> tdefs.map(range)
      TypeDefNonRec(tdef) -> [tdef.range]
  match tdgs
    Nil -> (Nil, inf-kind-env.kGamma, get-syns(), inf-kind-env.allnewtypes, [])
    Cons(tdgroup, tdgroups) ->
      val (ctdgroup, lazyExprs) = kinfer(tdgroup)
      with extend-kgamma(tdgroup.get-ranges, ctdgroup)
      val (ctdgroups, kgamma1, syns1, data1, lazyExprss) = tdgs/kinfer(tdgroups)
      (Cons(ctdgroup, ctdgroups), kgamma1, syns1, data1, lazyExprs ++ lazyExprss)

fun tdg/kinfer(td: syntax/syntax/typedef-group<user-type,user-kind>)
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

fun tdl/kinfer(isRec: bool, tdefs0: list<syntax/syntax/typedef<user-type, user-type, user-kind>>)
  val tdefs = tdefs0.map(add-lazy-indirect)
  val xinfgamma = tdefs.map(bind-typedef) // set up recursion
  val infgamma = xinfgamma.filter(snd).map(fst)
  with with-data-effects(rb-map/empty() + infgamma.zip(tdefs).flatmap(get-data-effect)) // make effect types visible for lifting to handled
  val ctdefs' =   
    with extend-infgamma(infgamma) // extend inference gamma, also checks for duplicates
    val names = infgamma.map(name)
    val tdefs1 = xinfgamma.map(fst).zip(tdefs).map(fn((a, b)) kinfer(a, b))
    // Resolve SYNONYMS in this group before anything else.
    //
    // `resolve-typedef` is what registers a synonym (via `add-synonym`), and
    // `resolve-app` needs that registration to build a `TSyn` -- without it a
    // reference to the alias silently becomes an opaque `TCon` with no
    // expansion, which later fails to unify against a structured effect row
    // (reported, confusingly, as "effects do not match ... cannot be subsumed").
    //
    // The dependency is one-directional and so this order is always safe: data
    // types are NOMINAL, so a synonym body referring to a group data type only
    // needs its `TCon`, whereas a data type field referring to a group synonym
    // needs the synonym's expansion. Relying on the scc's member order to get
    // this right is fragile -- any change in grouping or
    // sort order silently reintroduces the bug. Mutually recursive synonyms are
    // rejected separately by `check-recursion`.
    // pass 1: resolve the group's SYNONYMS only; pass 2: everything else.
    // Order within the list is preserved for the emitted core typedefs.
    val pass1 = tdefs1.map fn(td)
      match td
        Synonym(_, _, _, _, _, _) -> Just(resolve-typedef(isRec, names, td))
        _ -> Nothing
    tdefs1.zip(pass1).map fn((td, mb))
      match mb
        Just(r) -> r
        Nothing -> resolve-typedef(isRec, names, td)
  check-recursion(tdefs) // check for recursive type synonym definitions rather late so we spot duplicate definitions first
  val (ctdefs, lazyExprss) = ctdefs'.unzip
  (ctdefs, lazyExprss.concat)

fun check-recursion(tdefs: list<syntax/syntax/typedef<user-type, user-type, user-kind>>)
  if tdefs.length <= 1 || tdefs.any(is-dataType) then
    ()
  else
    kind-add-error(if tdefs.length > 0 then tdefs.head.unjust.range.combine(tdefs.last.unjust.range) else null, 
              "Type synonyms cannot be recursive".text)

// Setup type environment for recursive definitions
fun bind-typedef(tdef: syntax/syntax/typedef<user-type, user-type, user-kind>)
  val TypeBinder(name, kind, rngName, rng) = bind-typebinder(tdef.binder)
  val isExtend = 
    match tdef
      DataType(ddef=ddef) -> ddef.is-extend
      _ -> False
  val qname = if isExtend then name else name.qualify-def
  (TypeBinder(qname, kind, rngName, rng), !isExtend)

fun bind-typebinder(TypeBinder(name, user-kind, rngName, rng): type-binder<user-kind>)
  val kind = to-kind(user-kind)
  TypeBinder(name, kind, rngName, rng)

fun userkind/to-kind(user-kind: user-kind)
  match user-kind
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
      (core/core/External(cname, tp', pinfos, calls.format-call(tp', target-platform), vis, fipT, nameRng, doc), Cons(qname, names))
    syntax/syntax/ExternalImport(imps, rng) -> (core/core/ExternalImport(imps, rng), names)

fun format-call(external-call: external-call, tp: ktype, tpl: target-platform): string
  match external-call
    ExternalInline(inl) -> inl
    ExternalCall(fname) ->
      val (foralls, rho) = tp.split-type-scheme
      val argumentCount = match rho.split-fun-type
        Just((args, _, _)) -> args.length
        _ -> 0
      val arguments = "(" ++ list(1, argumentCount).map("#" ++ _.show).join(",") ++ ")"
      // upstream: `intersperse "," (["#"++show i | i <- [1..n]] ++ ctx)` -- the
      // context goes into the argument LIST before the commas are inserted.
      // Joining first and concatenating after drops the separator, emitting
      // `kk_vector_at_borrow(v,i_0kk_context())` for any `c "kk_..."` extern
      // that takes arguments.
      val ctxArg = if fname.starts-with("kk_").is-just then ["kk_context()"] else []
      val argumentsC = "(" ++ (list(1, argumentCount).map("#" ++ _.show) ++ ctxArg).join(",") ++ ")"
      val typeArguments = if foralls.is-nil then "" else "<" ++ list(1, foralls.length).map("##" ++ _.show).join(",") ++ ">"
      match tpl.tpl-target
        CS -> fname ++ typeArguments ++ arguments
        JS -> fname ++ arguments
        C -> fname ++ argumentsC
        DefaultTarget -> fname ++ arguments
        Unsupported -> fname ++ arguments

fun dgs/kinfer(dgs: list<syntax/syntax/def-group<user-type>>)
  dgs.map(kinfer)

fun dg/kinfer(dg: syntax/syntax/def-group<user-type>)
  match dg
    syntax/syntax/DefRec(defs) -> DefRec(defs.map(kinfer))
    syntax/syntax/DefNonRec(def) -> DefNonRec(kinfer(def))

fun def/kinfer(syntax/syntax/Def(binder, rng, vis, isVal, inl, doc): syntax/syntax/def<user-type>)
  Def(binder.kinfer, rng, vis, isVal, inl, doc)

fun valuebinder/kinfer(ValueBinder(nm, u, x, nmRng, rng): value-binder<(), syntax/syntax/expr<user-type>>)
  ValueBinder(nm, u, x.kinfer, nmRng, rng)

fun lam-valuebinder/kinfer(ValueBinder(lamnm, mbTp, mbExpr, nmRng, rng): value-binder<maybe<user-type>, maybe<syntax/syntax/expr<user-type>>>)
  val mbTp' = mbTp.map fn(t)
    with override val uctx = Check("Function parameters must be values", rng)
    t.inf-resolve-type()
  val isImplicit = lamnm.is-implicit-param-name
  val mbExpr' = mbExpr.map fn(e)
    match e
      Parens(Var(iname, _, nrng), nm, _, prng) | isImplicit ->
        // when the parameter name IS a type, qualify it (`.?order` unpacks an
        // `order`); otherwise pass the plain name through -- the type checker
        // unpacks via the parameter's type annotation instead (`.?key : child`)
        val qname = lookup-infkind-name(iname).default(iname)
        Parens(Var(qname, False, nrng), nm, "implicit", prng)
      expr -> expr.kinfer
  ValueBinder(lamnm, mbTp', mbExpr', nmRng, rng)

fun pat-valuebinder/kinfer(ValueBinder(nm, mbTp, pat, nmRng, rng): value-binder<maybe<user-type>, syntax/syntax/pattern<user-type>>)
  val mbTp' = mbTp.map fn(t)
    with override val uctx = Check("Matched expressions must be values", rng)
    t.inf-resolve-type()
  ValueBinder(nm, mbTp', pat.kinfer, nmRng, rng)

fun handler-valuebinder/kinfer(ValueBinder(nm, mbTp, u, nmRng, rng): value-binder<maybe<user-type>, ()>)
  val mbTp' = mbTp.map fn(t)
    with override val uctx = Check("Handler parameters must be values", rng)
    inf-resolve-type(t)
  ValueBinder(nm, mbTp', u, nmRng, rng)

fun expr/kinfer(ex: syntax/syntax/expr<user-type>)
  match ex
    syntax/syntax/Lam(binds, expr, tl, rng) -> syntax/syntax/Lam(binds.map(kinfer), expr.kinfer, tl, rng)
    syntax/syntax/Let(defs, expr, rng) -> syntax/syntax/Let(defs.kinfer, expr.kinfer, rng)
    syntax/syntax/Bind(def, expr, rng) -> syntax/syntax/Bind(def.kinfer, expr.kinfer, rng)
    syntax/syntax/App(f, nargs, rng) -> syntax/syntax/App(f.kinfer, nargs.map(fn((nm, arg)) (nm, arg.kinfer)), rng)
    syntax/syntax/Var(nm, isOp, rng) -> syntax/syntax/Var(nm, isOp, rng) // resolve qualified term identifiers during type inference
    Literal(l) -> Literal(l)
    Ann(expr, tp, rng) -> 
      val tp' = 
        with override val uctx = Check("Expressions must be values", rng) 
        tp.inf-resolve-type()
      Ann(expr.kinfer, tp', rng)
    syntax/syntax/Case(expr, brs, lzy, rng) -> syntax/syntax/Case(expr.kinfer, brs.map(kinfer), lzy, rng)
    syntax/syntax/Parens(expr, nm, pre, rng) -> syntax/syntax/Parens(expr.kinfer, nm, pre, rng)
    Handler(hsort, scoped, over, allowMask, meff, pars, reinit, ret, fin, ops, hrng, rng) ->
      val meff' = meff.map fn(eff)
        with override val uctx = Check("Handler effects must be effect constants (of kind X)", hrng)
        eff.inf-resolvex(rng)
      Handler(hsort, scoped, over, allowMask, meff', pars.map(kinfer), reinit.map(kinfer), ret.map(kinfer), fin.map(kinfer), ops.map(kinfer), hrng, rng)
    Inject(tp, expr, b, rng) ->
      val tp' =
        with override val uctx = Check("Can only inject effect constants (of kind X)", tp.range)
        tp.inf-resolvex(rng)
      Inject(tp', expr.kinfer, b, rng)

fun pat/kinfer(p: syntax/syntax/pattern<user-type>)
  match p
    syntax/syntax/PatWild(rng) -> syntax/syntax/PatWild(rng)
    syntax/syntax/PatLit(l) -> syntax/syntax/PatLit(l)
    syntax/syntax/PatVar(binder) -> syntax/syntax/PatVar(binder.kinfer)
    syntax/syntax/PatAnn(pat, tp, rng) ->
      val tp' = 
        with override val uctx = Check("Patterns must be values", rng)
        tp.inf-resolve-type()
      syntax/syntax/PatAnn(pat.kinfer, tp', rng)
    syntax/syntax/PatCon(name, args, r1, r2) -> syntax/syntax/PatCon(name, args.map(fn((mbNm, p')) (mbNm, p'.kinfer)), r1, r2)
    syntax/syntax/PatParens(pat, rng) -> syntax/syntax/PatParens(pat.kinfer, rng)

fun handlerbranch/kinfer(HandlerBranch(name, pars, expr, opSort, nmRng, rng): handler-branch<user-type>)
  HandlerBranch(name, pars.map(kinfer), expr.kinfer, opSort, nmRng, rng)

fun branch/kinfer(syntax/syntax/Branch(pat, guards): syntax/syntax/branch<user-type>)
  syntax/syntax/Branch(pat.kinfer, guards.map(kinfer))

fun guard/kinfer(syntax/syntax/Guard(test, body): syntax/syntax/guard<user-type>)
  syntax/syntax/Guard(test.kinfer, body.kinfer)

// Infer the kinds for a type definition
fun typedef/kinfer(tb: type-binder<inf-kind>, td: syntax/syntax/typedef<user-type, user-type, user-kind>)
  match td
    syntax/syntax/Synonym(_, args, tp, rng, vis, doc) ->
      val infgamma = args.map(bind-typebinder)
      val k = fresh-kind()
      val tp' = 
        with extend-infgamma(infgamma)
        with override val uctx = Infer(rng)
        kinfer(k, tp)
      val tbinder = unify-binder(tb, rng, infgamma, k)
      syntax/syntax/Synonym(tbinder, infgamma, tp', rng, vis, doc)
    DataType(newTp, args, constrs, rng, vis, sort, ddef, dataEff, doc) ->
      val infgamma = args.map(bind-typebinder)
      val constrs' = 
        with extend-infgamma(infgamma)
        constrs.map(kinfer)
      val resKind = if ddef.is-open then infKindStar else fresh-kind()
      val tbinder' = unify-binder(tb, rng, infgamma, resKind)
      if !ddef.is-extend then ()
      else
        val (_, kd, _) = find-infkind(newTp.name, newTp.range)
        with val uctx = Check("extended type must have the same kind as the open type", newTp.range)
        unify(newTp.range, tbinder'.tb/kind, kd)
      DataType(tbinder', infgamma, constrs', rng, vis, sort, ddef, dataEff, doc)

fun unify-binder(tb: type-binder<inf-kind>, rng: range, infgamma: list<type-binder<inf-kind>>, resKind: inf-kind)
  val kind = inf-kind-funN(infgamma.map(tb/kind), resKind)
  with val uctx = Infer(rng)
  unify(rng, tb.tb/kind, kind)
  tb

fun tb/kind(TypeBinder(_, k, _, _): type-binder<k>): k
  k

fun constr/kinfer(UserCon(name, exists0, params, mbresult, mblazy, rngName, rng, vis, doc): user-con<user-type,user-type,user-kind>)
  val infgamma = exists0.map(bind-typebinder)
  val params' = 
    with extend-infgamma(infgamma)
    params.map(kinfer)
  val result' = mbresult.map fn(t)
    with override val uctx = Check("Constructor results must be values", rng)
    kinfer(infKindStar, t)
  UserCon(name, infgamma, params', result', mblazy, rngName, rng, vis, doc)

fun con-valuebinder/kinfer((vis,ValueBinder(name, tp, mbExpr, nameRng, rng)): (visibility, value-binder<user-type, maybe<syntax/syntax/expr<user-type>>>))
  with override val uctx = Check("Constructor parameters must be values", rng)
  (vis, ValueBinder(name, kinfer(infKindStar, tp), mbExpr, nameRng, rng))

fun usertp/kinfer(expected: inf-kind, user-type: user-type)
  match user-type
    TpQuan(quant, tname, tp, r) ->
      val ikind = match quant
        QSome -> expected
        _ -> 
          unify(r, expected, infKindStar)
          expected
      val tname' = tname.bind-typebinder
      val tp' = 
        with extend-infgamma([tname'])
        with check-quant(r)
        kinfer(ikind, tp)
      TpQuan(quant, tname', tp', r)
    TpFun(args, eff, tp, r) ->
      unify(r, expected, infKindStar)
      val args' = 
        with check-arg(r)
        args.map(kinfer(infKindStar, _))
      // somewhat involved since we auto-wrap labels L into effects E here
      val ekind = fresh-kind()
      val etp = 
        with check-eff(r)
        kinfer(ekind, eff)
      val skind = subst(ekind)
      val eff' = match skind
        KICon(k) | k == kindLabel -> make-effect-extend(etp, make-effect-empty)
        KICon(k) | k.is-kind-handled ->
          make-effect-extend(get-effect-lift(etp)(etp, r), make-effect-empty) 
        _ ->
          with check-eff(r)
          unify(r, KICon(kindEffect), skind)
          etp
      val tp' = 
        with check-res(r)
        kinfer(infKindStar, tp)
      TpFun(args', eff', tp', r)
    TpApp(tp as TpCon(nm), [lab, tl], r) | nm == nameEffectExtend ->
      val tp' = 
        with check-app(r)
        kinfer(inf-kind-funN([KICon(kindLabel), KICon(kindEffect)], expected), tp)
      val tl' = 
        with check-extend-tail(r)
        kinfer(KICon(kindEffect), tl)
      // somewhat involved since we allow fixed effects to be used as labels
      // the append nodes are just used temporarily (see resolve-app in this file)
      val lkind = fresh-kind()
      val ltp = 
        with override val uctx = Infer(r)
        kinfer(lkind, lab)
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
      val tp' = 
        with check-app(rng)
        kinfer(inf-kind-funN(kinds, expected), tp)
      val args' = 
        with override val uctx = Infer(rng)
        kinds.zipwith(args, kinfer)
      TpApp(tp', args', rng)
    TpVar(nm, rng) ->
      val (qname, kind, _) = find-infkind(nm, rng)
      unify(rng, expected, kind)
      TpVar(qname, rng)
    TpCon(nm, rng) ->
      val (qname, kind, _) = find-infkind(nm, rng)
      unify(rng, expected, kind)
      TpCon(qname, rng)
    TpParens(tp, rng) -> TpParens(kinfer(expected, tp), rng)
    TpAnn(tp, user-kind) ->
      val kind = user-kind.to-kind
      val rng = user-type.range
      unify(rng, expected, kind)
      val tp' = 
        with check-annot(rng)
        kinfer(kind, tp)
      TpAnn(tp', kind) 

fun get-effect-lift(utp: kuser-type<inf-kind>): inf-kind-env (forall<k> (kuser-type<k>, range) -> kuser-type<k>)
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

fun param/kinfer(expected: inf-kind, (nm, tp): (name, user-type))
  (nm, kinfer(expected, tp))

// Add indirection constructor to a lazy datatype
fun add-lazy-indirect(dt)
  match dt
    DataType(newtp, targs, cons, range, vis, sort, ddef, dataEff, doc) | cons.any(user-con-is-lazy) || ddef.datadef/is-lazy ->
      val (lazyCons, strictCons) = cons.partition(user-con-is-lazy)
      val rng = newtp.name-range.hide
      val indirectName = "indirect".new-hidden-name
      fun make-tp-app(t: kuser-type<k>, targs': list<kuser-type<k>>): kuser-type<k>
        if targs'.is-nil then t else TpApp(t, targs', rng)
      val indirectPar = ValueBinder(indirectName, 
        make-tp-app(TpCon(newtp.name, rng), 
          targs.map(fn(targ) TpVar(targ.name, targ.name-range))), 
          Nothing, rng, rng)
      val indirectCon = UserCon(newtp.name.to-lazy-indirect-con-name, [], 
           [(Private, indirectPar)], Nothing, 
           Just((fipNoAlloc, Var(indirectName, False, rng))), 
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
        kind-add-error(rng, "Cannot add lazy constructors to a".text |+| ddef.show.text |+| "type".text)
      
      // get fip annotation of the data definition
      fun user-con-fip(c)
        match c.user-con/mblazy
          Just((f, _)) -> f
          _ -> noFip
      val defaultFip = lazyCons.map(user-con-fip).foldr(fipBot, max)
      val fipT = match ddef
        DataDefLazy(NoFip(False)) -> defaultFip
        DataDefLazy(fipT) ->
          if !fipT.subsumes(defaultFip) then // annotated
            kind-add-error(rng, "The datatype".text |+| fipT.show.text |+| "annotation cannot be more restrictive than the fip annotations of the lazy constructors".text)
            defaultFip
          else fipT
        _ -> defaultFip
      DataType(newtp, targs, new-cons, range, vis, sort, DataDefLazy(fipT), dataEff, doc)
    td -> td


fun user-con-is-lazy(ucon)
  match ucon.user-con/mblazy
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
fun resolve-typedef(isRec: bool, recNames: list<name>, td: syntax/syntax/typedef<kuser-type<inf-kind>, user-type, inf-kind>)
  match td
    Synonym(syn, params, tp, rng, vis, doc) ->
      val syn' = syn.resolve-typebinder-def(doc)
      val params' = params.map(_.resolve-typebinder(""))
      val type-vars = params'.map(_.fresh-typevar(Bound))
      val tvarMap = rb-map/empty() + params'.map(name).zip(type-vars)
      val tp' = resolve-type(tvarMap, True, tp)
      // eta-expand type synonyms
      val kind = syn'.tb/kind
      val karity = kind.arity
      val etaKinds = karity.drop(type-vars.length)
      val (etaTp, etaParams) = 
        if etaKinds.is-nil then
          (tp', type-vars)
        else
          val etaVars = etaKinds.map(TypeVar(unique-id("eta"), _, Bound))
          (type-app(tp', etaVars.map(TVar)), type-vars ++ etaVars)
      add-range-info(rng, RIDecl("alias", syn'.name, syn'.name.mangle-type-name, Just(tp')))
      val syn-info = SynInfo(syn'.name, syn'.tb/kind, etaParams, etaTp, etaTp.max-synonym-rank + 1, rng, vis, doc)
      add-synonym(syn-info)
      (Synonym(syn-info), [])
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
      val type-vars =
        val (kargs, _kres) = extract-kind-fun(newtp'.tb/kind)
        if params.is-nil && !kargs.is-nil then
          kargs.map(TypeVar(unique-id("k"), _, Bound)) // invent parameters if they are not given (and it has an arrow kind)
        else
          params'.map(_.fresh-typevar(Bound))
      val tvarMap = rb-map/empty() + params'.map(name).zip(type-vars)
      val qname = newtp'.name
      val fname = qname.unqualify
      val name = fname
      val nameDoc = name.pretty.color(colors.colorType)
      val consinfos = constrs.map-indexed fn(i, c) 
        resolve-constructor(qname, sort, !ddef.is-open && constrs.length == 1, typeResult, type-vars, tvarMap, c, i + 1) // constructor tags start at 1
      val (lazyExprss, conInfos0) = consinfos.unzip
      // check recursion
      if sort.is-retractive then
        ()
      else
        fun from-ops-name(nm: name)
          if nm.is-operations-name then [nm.from-operations-name] else []
        val effNames = recNames.map(from-ops-name).concat
        if conInfos0.any(occurs-negative-con(recNames ++ effNames, _)) then
          kind-add-error(rng, "Type".text |+| nameDoc |+| "is declared as being".text |-| "(co)inductive but it occurs recursively in a negative position.".text |-|
            " hint: declare it as a divergent (or retractive) type using 'div type' (or 'div effect') to allow negative occurrences".text)
        else ()
      // create datadef and coninfos with correct ValueRepr and ordered fields
      fun emit-error(d)
        kind-add-error(rng, "Type".text |+| nameDoc |+| d)
      fun emit-warning(d)
        add-warning(rng, "Type".text |+| nameDoc |+| d)
      val resultHasKindStar = typeResult.kind.has-kind-star-result
      val maxMembers = conInfos0.map(_.con-info/params.length).maximum
      val conCount = conInfos0.length
      val willNeedStructTag = ddef.is-value && conCount > 1 && maxMembers >= 1
      val extraFields = 
        if ddef.is-open then 1 // open datatype tag
        elif willNeedStructTag then 1 // explicit struct tag
        else 0
      val (ddef1, conInfos1) = create-data-def(emit-error, emit-warning, lookup-datainfo, get-platform(), qname, resultHasKindStar, isRec, sort, extraFields, ddef, conInfos0)
      val dataInfo = DataInfo(sort, qname, newtp'.tb/kind, type-vars, conInfos1, rng, ddef1, dataEff, isRec, vis, doc)
      val declaration = (if dataInfo.di/is-lazy then "lazy " else "")
                        ++ (if !sort.is-inductive then "" elif ddef1.is-value then "value " else "reference ")
                        ++ sort.show

      // TODO: Assertion
      add-range-info(rng, RIDecl(declaration, qname, qname.mangle-type-name, Nothing))
      (Data(dataInfo), lazyExprss.concat)

fun occurs-negative-con(names: list<name>, ci: con-info)
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

fun typebinder/show(TypeBinder(name, kind, _, _): type-binder<kind>)
  name.show ++ ":" ++ kind.show

fun resolve-typebinder-def(TypeBinder(name, infkind, rngName, rng): type-binder<inf-kind>, doc)
  val infkind' = infkind.resolve-kind
  val qname = name.qualify-def
  add-range-info(rngName, RIId(qname, NITypeCon(infkind', doc), [], True))
  TypeBinder(qname, infkind', rngName, rng)

fun resolve-typebinder(TypeBinder(name, infkind, rngName, rng): type-binder<inf-kind>, doc)
  val infkind' = infkind.resolve-kind
  add-range-info(rngName, RIId(name, NITypeCon(infkind', doc), [], True))
  TypeBinder(name, infkind', rngName, rng)

fun resolve-kind(infkind: inf-kind)
  val skind = subst(infkind)
  fun resolve(k: inf-kind)
    match k
      KIVar(_) -> kindStar // default unconstrained parameter to kind star
      KICon(k') -> k'
      KIApp(k1, k2) -> KApp(k1.resolve, k2.resolve)
  skind.resolve

val nameTVMapEmpty: name-map<type-var> = rb-map/empty()

fun resolve-constructor(typeName: name, typeSort: data-kind, isSingleton: bool, typeResult: ktype, typeParams: list<type-var>,
  idmap: name-map<type-var>, UserCon(cname, exists0, params, mbResult, mblazy, rngName, rng, vis, doc): user-con<kuser-type<inf-kind>, user-type, inf-kind>, tag)
  val qname = cname.qualify-def
  val exists' = exists0.map(_.resolve-typebinder(""))
  val existsVars = exists'.map(fresh-typevar(_, Bound))
  // the datatype parameters stay in scope; existentials shadow them
  val idmap' = exists'.map(name).zip(existsVars).foldl(idmap, fn(m, (k, v)) rb-map/set(m, k, v))
  val params' = params.map(resolve-con-param(idmap', _))
  val result = match mbResult
    Nothing -> type-app(typeResult, typeParams.map(TVar))
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

fun resolve-con-param(idmap: name-map<type-var>, (vis, ValueBinder(name, tp, mbExpr, nameRng, rng)): (visibility, value-binder<kuser-type<inf-kind>, maybe<syntax/syntax/expr<user-type>>>))
  val tp' = resolve-type(idmap, False, tp)
  val expr = match mbExpr
    Nothing -> Nothing
    Just -> Just(failure/fail("kind/kinfer/resolve-con-param: optional parameter expression in constructor"))
  // add-range-info(nameRng, RIId(name, NIValue("val", tp', "", True), [], True))
  (vis, ValueBinder(name, tp', expr, nameRng, rng))

// resolve-type takes: a map from locally quantified type name variables to types,
// a boolean that is 'True' if partially applied type synonyms are allowed (i.e. when
// these are arguments to type synonyms themselves), a user type with inference kinds,
// and it returns a fully resolved type
fun resolve-type(idmap: name-map<type-var>, partialSyn: bool, user-type: kuser-type<inf-kind>)
  fun resolve-param((nm, tp): (name, kuser-type<inf-kind>))
    (nm, resolve-type(idmap, False, tp))
  fun collect-args(args: list<kuser-type<k>>, tp: kuser-type<k>): (kuser-type<k>, list<kuser-type<k>>)
    match tp
      TpApp(tp', args') -> collect-args(args' ++ args, tp')
      TpParens(tp') -> collect-args(args, tp')
      TpAnn(tp') -> collect-args(args, tp')
      _ -> (tp, args)
  match user-type
    TpQuan(QForall, tname, tp) ->
      val tname' = tname.resolve-typebinder("")
      val tvar = fresh-typevar(tname', Bound)
      val tp' = resolve-type(rb-map/set(idmap, tname.name, tvar), False, tp)
      quantify-type([tvar], tp')
    TpQuan(QSome, tname, tp) ->
      val tname' = tname.resolve-typebinder("")
      val tvar = fresh-typevar(tname', Meta)
      val tp' = resolve-type(idmap.set(tname.name, tvar), False, tp)
      tp'
    TpQuan(QExists) ->
      failure/fail("kind/kinfer resolve-type: existentials are not supported yet")
    TpFun(args, eff, tp) ->
      val args' = args.map(resolve-param)
      val eff' = resolve-type(idmap, False, eff)
      val tp' = resolve-type(idmap, False, tp)
      TFun(args', eff', tp')
    TpApp(tp, args, rng) ->
      resolve-app(idmap, partialSyn, args.collect-args(tp), rng)
    TpVar(_, rng) ->
      resolve-app(idmap, partialSyn, (user-type, []), rng)
    TpCon(_, rng) ->
      resolve-app(idmap, partialSyn, (user-type, []), rng)
    TpParens(tp) ->
      resolve-type(idmap, partialSyn, tp)
    TpAnn(tp) ->
      resolve-type(idmap, partialSyn, tp)

fun resolve-app(idmap: name-map<type-var>, partialSyn: bool, (tp, args): (kuser-type<inf-kind>, list<kuser-type<inf-kind>>), rng: range)
  match (tp, args)
    (TpVar(name, r), _) ->
      val (tp', kind) = match idmap.lookup(name)
        Nothing ->
          kind-add-error(rng, "Type variable".text |+| name.pretty.color(colors.colorType) |+| "is undefined".text |-|
            " hint: bind the variable using".text |+| ("forall<".text |.| name.pretty |.| ">".text).color(colors.colorType))
          (TVar(TypeVar(name.show.unique-id, kindStar, Bound)), kindStar)
        Just(tvar) -> (TVar(tvar), tvar.kind)
      if !name.is-implicit-typevar-name then
        add-range-info(r, RIId(name, NITypeVar(kind), [], False))
      val args' = args.map(resolve-type(idmap, False, _))
      type-app(tp', args')
    (TpCon(name), [fixed, ext]) | name == nameEffectAppend ->
      val fixed' = resolve-type(idmap, False, fixed)
      val ext' = resolve-type(idmap, False, ext)
      val (_, tl) = fixed'.extract-ordered-effect
      if !tl.is-effect-empty then
        kind-add-error(rng, "Effects can only have one extension point (use a `|` instead of a comma in the effect type ?)".text)
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
            kind-add-error(rng, "Type alias".text |+| name.pretty.color(colors.colorType) |+| "has too few arguments".text)
          elif args.length > params.length then
            kind-add-error(rng, "Type alias".text |+| name.pretty.color(colors.colorType) |+| "has too many arguments".text)
          else ()
          // upstream: `resolveType idmap True` -- partially applied synonyms
          // ARE allowed in synonym arguments
          val args' = args.map(resolve-type(idmap, True, _))
          val tsyn = TSyn(TypeSyn(name, kind, rank, Just(syn)), args', params.zip(args').sub |-> tp')
          tsyn
          // NOTE: on partially applied type synonyms, we get a funky body type with free parameters but this
          // is only inside synonyms arguments so we are ok
        Nothing ->
          type-app(TCon(TypeCon(nm, k)), args.map(resolve-type(idmap, False, _)))
    _ -> failure/fail("kind/kinfer resolve-app: this case should never occur after kind checking")

fun make-effect-append(fixed, ext)
  TpApp(TpCon(nameEffectAppend, null), [fixed, ext], null)

fun make-effect-extend(label, ext)
  TpApp(TpCon(nameEffectExtend, null), [label, ext], null)

val make-effect-empty =
  TpCon(nameEffectEmpty, null)
