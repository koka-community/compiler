module compiler/type/infer

import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/failure
import compiler/common/unique
import compiler/common/message
import compiler/platform/config
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/import-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/assumption
import compiler/type/infgamma
import compiler/type/unify
import compiler/type/pretty
import compiler/type/operations
import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/syntax/range-map
import compiler/core/core
import compiler/core/corevar
import compiler/core/analysis-match
import compiler/lib/pprint
import std/data/linear-map
import std/data/linear-set
import std/data/sort
import std/core/undiv
import std/core/unsafe
import compiler/lib/core
import compiler/type/infer-effect

fun checkFun(rng: range) 
  Check("function type does not match the argument types", rng)
fun checkMatch(rng: range) 
  Check("branch has not the same type as previous branches", rng)
fun checkAnn(rng: range) 
  Check("type cannot be instantiated to match the annotation", rng)
fun checkRec(rng: range) 
  Check("recursive invocations do not match the assumed type; add a type annotation?", rng)
fun checkGuardTotal(rng: range) 
  Check("guard expressions must be total", rng)
fun checkGuardBool(rng: range) 
  Check("guard expressions must be of a boolean type", rng)
fun checkConMatch(rng: range) 
  Check("constructor must have the same the type as the matched term", rng)
fun checkLitMatch(rng: range) 
  Check("literal pattern does not match the type of the matched term", rng)
fun checkConTotal(rng: range) 
  Check("constructor in a pattern must have a total effect type", rng)
fun checkLit(rng: range)      
  Check("literal does not match the expected type", rng)
fun checkOptional(rng: range) 
  Check("default value does not match the parameter type", rng)
fun checkOptionalTotal(rng: range) 
  Check("default value expression must be total", rng)
fun checkInject(rng: range) 
  Check("inject expects a parameter-less function argument", rng)
val checkEffect = Infer
fun checkEffectSubsume(rng: range) 
  Check("effect cannot be subsumed", rng)
fun checkReturnResult(rng: range) 
  Check("function returns values of different types", rng)
fun checkReturn(rng: range)        
  Check("return type does not match an earlier return type", rng)
fun checkOp(rng: range)         
  Check("operator type does not match the parameter types", rng)
fun checkMakeHandler(rng: range) 
  Check("handler types do not match the handler maker; please report this as a bug!", rng)
fun checkMakeHandlerBranch(rng: range) 
  Check("handle branch types do not match the handler branch maker; please report this as a bug!", rng)
fun checkEffectTp(rng: range)   
  Check("operator type does not match the effect type", rng)
fun checkLocalScope(rng: range) 
  Check("a reference to a local variable escapes it's scope", rng)

fun expr/infer(mb, expect, expr)
  throw("Unimplemented")
//////////////////////////////////////////
// Infer Types
//////////////////////////////////////////


//////////////////////////////////////////
// Definition Groups
//////////////////////////////////////////


//////////////////////////////////////////
// Definition
//////////////////////////////////////////

fun unskolemize(tp: ktype): _ ktype
  val svs = tp.fsv.list
  val uvs = svs.map(fn(tv) fresh-tvar(tv.kind, Meta))
  val sub' = svs.zip(uvs).sub
  val tpu = sub' |-> tp
  tpu






fun checkValue(rng: range) Check("Values cannot have an effect", rng)
fun checkPolyValue(rng: range) Check("Polymorphic values cannot have an effect", rng)
fun unused-warning(rng: range)
  inf-warning(rng, "expression has no effect and is unused".text |-|
                   " hint: did you forget an operator? or used \"fun\" instead of \"fn\"?".text)

//////////////////////////////////////////
// Expression
//////////////////////////////////////////
type expect
  Generalized(b: bool)
  Instantiated

fun expect/(==)(e1: expect, e2: expect): bool
  match (e1, e2)
    (Generalized(b1), Generalized(b2)) -> b1 == b2
    (Instantiated, Instantiated) -> True
    _ -> False
fun expect/show(e: expect): string
  match e
    Generalized(b) -> "Generalized(" ++ b.show ++ ")"
    Instantiated -> "Instantiated"

pub fun remove-local-effect(ftp: ktype)
  match ftp.split-fun-scheme
    Just((foralls, args, eff, resTp)) -> 
      val (ls, tl) = eff.extract-ordered-effect
      quantify-type(foralls, TFun(args, ls.filter(_.label-name != nameTpLocal).foldr(tl, effect-extend), resTp))
    _ -> failure/fail("type/infer/remove-local-effect: unexpected type: " ++ ftp.show)


//////////////////////////////////////////
// Infer Effect Handlers
//////////////////////////////////////////

fun infer-handler(propagated: maybe<(ktype, range)>, expect: expect, handlerSort: handler-sort, 
                  handlerScoped: handler-scope, allowMask: bool, mbeff: maybe<keffect>, 
                  localPars: list<value-binder<maybe<ktype>, ()>>, 
                  initially: maybe<(syntax/syntax/expr<ktype>)>, ret: maybe<(syntax/syntax/expr<ktype>)>, 
                  finally: maybe<(syntax/syntax/expr<ktype>)>, branches: list<handler-branch<ktype>>, hrng: range, rng: range): _ (ktype, keffect, core/core/expr)
  // Regular handler
  match localPars
    Cons -> 
      context-error(hrng, rng, "text \"Type.Infer.inferHandler: TODO: not supporting local parameters\"".text, [])
      failure/fail("abort")
    Nil -> 
      // get the handled effect
      val heff = infer-handled-effect(hrng, handlerSort, mbeff, branches)

      throw("Unimplemented")

// inferHandler :: Maybe (Type,Range) -> Expect -> HandlerSort -> HandlerScope -> Bool
//                       -> Maybe Effect
//                       -> [ValueBinder (Maybe Type) ()] -> Maybe (Expr Type) -> Maybe (Expr Type) -> Maybe (Expr Type)
//                       -> [HandlerBranch Type] -> Range -> Range -> Inf (Type,Effect,Core.Expr)
// -- Regular handler
// inferHandler propagated expect handlerSort handlerScoped allowMask
//              mbEffect (_:localPars) initially ret finally branches hrng rng
//   = do contextError hrng rng (text "Type.Infer.inferHandler: TODO: not supporting local parameters") []
//        failure "abort"
// inferHandler propagated expect handlerSort handlerScoped allowMask
//              mbEffect [] initially ret finally branches hrng rng
//   = do -- get the handled effect
//        heff <- inferHandledEffect hrng handlerSort mbEffect branches
//        let isInstance = isHandlerInstance handlerSort
//            effectName = effectNameFromLabel heff
//            handlerConName = toHandlerConName effectName
//        -- check operations
//        checkCoverage rng heff handlerConName branches

//        -- infer the result type to improve inference
//        res  <- case (propagated,ret) of
//                 (Nothing,Just expr) -> do (tp,_,_) <- inferExpr propagated Instantiated expr
//                                           case splitFunScheme tp of
//                                             Just (_,_,_,retTp) -> return retTp
//                                             _ -> Op.freshStar
//                 (Just (retTp,_),_) -> return retTp
//                 _ -> Op.freshStar
//        eff  <- Op.freshEffect
//        resumeArgs <- mapM (\_ -> Op.freshStar) branches  -- TODO: get operation result types to improve inference

//        -- construct the handler
//        let -- create expressions for each clause
//            opName b1 b2 = compare (show (unqualify (hbranchName b1))) (show (unqualify (hbranchName b2)))
//            clause (HandlerBranch opName pars body opSort nameRng patRng, resumeArg)
//             = withScope $
//               do (clauseName, cparams, prefix) <- case opSort of
//                           OpVal        -> return (nameClause "tail" (length pars), pars, "val")
//                           OpFun        -> return (nameClause "tail" (length pars), pars, "fun")
//                           OpExcept     -> return (nameClause "never" (length pars), pars, "final ctl")
//                           -- don't optimize ctl to exc since exc runs the finalizers before the clause (unlike ctl)
//                           -- OpControl    | not (hasFreeVar body (newName "resume"))
//                           --             -> (nameClause "never" (length pars), pars)  -- except
//                           OpControl    -> do let resumeTp = TFun [(nameNil,resumeArg)] eff res
//                                                  resumeDoc shorten = if shorten then text "resume" else empty
//                                              addRangeInfo nameRng (RM.Implicits resumeDoc)
//                                              return (nameClause "control" (length pars),
//                                                      pars ++ [ValueBinder (newName "resume") (Just resumeTp) () (rangeHide nameRng) nameRng],
//                                                      "ctl")
//                           OpControlRaw -> do let eff0 = effectExtend heff eff
//                                                  resumeContextTp = typeResumeContext resumeArg eff eff0 res
//                                                  resumeDoc shorten = if shorten then text "rcontext" else empty
//                                              addRangeInfo nameRng (RM.Implicits resumeDoc)
//                                              return (nameClause "control-raw" (length pars),
//                                                      pars ++ [ValueBinder (newName "rcontext") (Just resumeContextTp) () (rangeHide hrng) patRng],
//                                                      "raw ctl")
//                           OpControlErr -> failure "Type.Infer.inferHandler: using a bare operation is deprecated.\n  hint: start with 'val', 'fun', 'brk', or 'ctl' instead."
//                           -- _            -> failure $ "Type.Infer.inferHandler: unexpected resume kind: " ++ show rkind

//                  let qopname = if isQualified opName then opName else qualify (qualifier effectName) opName
//                  (_,gtp,_) <- resolveFunName qopname (CtxFunArgs False (length pars + (if isInstance then 1 else 0)) [] Nothing) patRng nameRng -- todo: resolve more specific with known types?
//                  (tp,_,_)  <- instantiateEx nameRng gtp
//                  let parTps = case splitFunType tp of
//                                 Just (tpars,_,_) -> (if (isInstance) then tail else id) $ -- drop the first parameter of an op for an instance (as it is the instance name)
//                                                     map (Just . snd) tpars ++ repeat Nothing  -- TODO: propagate result type as well?
//                                 _ -> failure $ "Type.Infer.inferHandler: bad operation type: " ++ show opName ++ ": " ++ show (pretty gtp)
//                      cparamsx = map (\(b,mbtp) -> case b of
//                                                     ValueBinder name Nothing _ nameRng rng -> ValueBinder name mbtp Nothing nameRng rng
//                                                     ValueBinder name annTp _ nameRng rng   -> ValueBinder name annTp Nothing nameRng rng)
//                                 $ zip (cparams :: [ValueBinder (Maybe Type) ()]) (parTps)
//                      frng = combineRanged nameRng body
//                      cname = case opSort of
//                                OpVal -> fromValueOperationsName opName
//                                _     -> opName
//                      capp  = App (Var clauseName False (rangeHide hrng))
//                                  [(Nothing,Parens (Lam cparamsx body False (getRange body)) cname prefix nameRng)] frng
//                  -- addRangeInfo nameRng (RM.Id cname (RM.NIValue "fun" gtp "" False) [] False)
//                  return (Nothing, capp)

//        clauses <- mapM clause (zip (sortBy opName branches) resumeArgs)

//        let grng = rangeNull
//        let handlerCon = let hcon = Var handlerConName False hrng
//                         in App hcon ([(Nothing,Lit (LitInt handlerCfc grng))] ++ clauses) rng
//            handlerCfc = -- (\i -> App (Var nameInternalInt32 False grng) [(Nothing,Lit (LitInt i grng))] grng) $
//                         if (null branches) then 1 --linear
//                                            else foldr1 cfcLub (map hbranchCfc branches)
//                       where
//                         cfcLub x y   = if ((x==0&&y==1)||(x==1&&y==0)) then 2 else max x y
//                         hbranchCfc b = case hbranchSort b of -- todo: more refined analysis
//                                         OpVal    -> 1
//                                         OpFun    -> 1
//                                         OpExcept -> 0
//                                         _        -> 3 --multi/wild
//            -- create handler expression
//            actionName = newHiddenName "action"
//            handleName = toHandleName effectName
//            handleRet  = case ret of -- todo: optimize return by using maybe<a->b> value in case no clause was given?
//                           Nothing -> let argName = (newHiddenName "res")
//                                      in Lam [ValueBinder argName Nothing Nothing rng rng] (Var argName False rng) False hrng -- don't pass `id` as it needs to be opened
//                           Just expr -> expr
//            handleExpr action = App (Var handleName False rng)
//                                 [{-(Nothing,handlerCfc),-}(Nothing,handlerCon),(Nothing,handleRet),(Nothing,action)] hrng



//        -- extract the action type for the case where it is higher-ranked (for scoped effects)
//        -- this way we can annotate the action parameter with a higher-rank type if needed
//        -- so it is propagated automatically.
//        penv <- getPrettyEnv
//        (_,handleTp,_)  <- resolveFunName handleName CtxNone rng rng
//        (handleRho,_,_) <- instantiateEx rng handleTp
//        actionTp <- case splitFunType handleRho of
//                         Just ([_,_,actionTp],_,_)
//                           -> subst (snd actionTp)
//                         _ -> failure ("Type.Infer: unexpected handler type: " ++ show (ppType penv handleRho))
//        let handlerExpr = Parens (Lam [ValueBinder actionName (Just actionTp) Nothing rng rng]
//                                      (handleExpr (Var actionName False rng)) False hrng) (newName "handler") "expr" rng

//        -- and check the handle expression
//        hres@(xhtp,_,_) <- inferExpr propagated expect handlerExpr
//        htp <- subst xhtp

//        -- extract handler effect
//        let (actionTp1,heffect) = case splitFunScheme(htp) of
//                         Just (_,[arg],heff,hresTp) -> (snd arg,heff)
//                         _ -> failure $ "Type.Infer.inferHandler: unexpected handler type: " ++ show (ppType penv htp)

//        if (not (labelIsLinear heff))
//         then return ()
//         else checkLinearity effectName heffect branches hrng rng

//        -- insert a mask<local> over the action?
//        if True -- (not (containsLocalEffect heffect) || not allowMask)
//          then return hres
//          else do
//                  hp <- Op.freshTVar kindHeap Meta
//                  let actionTp2  = removeLocalEffect penv actionTp1
//                      handlerExprMask
//                         = if isInstance
//                            then let instName   = newHiddenName "hname"
//                                 in Lam [ValueBinder actionName (Just actionTp2) Nothing rng rng]
//                                     (handleExpr (Lam [ValueBinder instName Nothing Nothing rng rng]
//                                                    (Inject (TApp typeLocal [hp])
//                                                       (Lam [] (App (Var actionName False rng) [(Nothing,Var instName False rng)] rng) False rng)
//                                                       False hrng) False hrng)) False hrng
//                            else Lam [ValueBinder actionName (Just actionTp2) Nothing rng rng]
//                                   (handleExpr (Lam [] (Inject (TApp typeLocal [hp]) (Var actionName False rng) False hrng) False hrng)) False hrng
//                  inferExpr propagated expect handlerExprMask  -- and re-infer :-)



fun check-linearity(effectName: name, heffect: ktype, branches: list<handler-branch<ktype>>, hrng: range, rng: range)
  fun check-linear-clauses()
    fun check(hbranch)
      if hbranch.branchSort <= OpFun then ()
      else context-error(rng, hbranch.branchPatRange, 
        "operation".text |+| hbranch.branchName.pp-name |+| 
        "needs to be linear but is handled in a non-linear way (as '".text |.| hbranch.branchSort.show.text |.| "')".text, 
        [("hint".text, "use a 'val' or 'fun' operation clause instead".text)])
    branches.map(check)
  fun check-linear-effect()
    val (effs, tl) = heffect.extract-effect-extend
    match effs.drop-while(_.label-is-linear)
      Cons(e) -> 
        context-error(rng, hrng, 
          "handler for".text |+| pp-name(effectName) |+| 
          "needs to be linear but uses a non-linear effect:".text |+| e.pp-type, 
          [("hint".text, "ensure only linear effects are used in a handler".text)])
      [] -> ()
  check-linear-clauses()
  check-linear-effect()

// Infer the handled effect from looking at the operation clauses
fun infer-handled-effect(rng: range, handlerSort: handler-sort, mbeff: maybe<keffect>, ops: list<handler-branch<ktype>>): _ keffect
  match mbeff
    Just(eff) -> eff
    Nothing -> 
      match ops
        Cons(HandlerBranch(name, pars, expr, opSort, nameRng, rng), _) ->
          // TODO: handle errors if we find a non-operator
          val isInst = handlerSort.is-handlerInstance
          val (qname, tp, info) = resolve-fun-name(name, CtxFunArgs(isInst, pars.length + (if isInst then 1 else 0), [], Nothing), rng, nameRng)
          val (_, rho, _) = instantiate-ex(tp, nameRng)
          match rho.split-fun-type
            Just((Cons((op-name, rtp)), _, _)) | isInst && op-name == new-hidden-name("hname") ->
              match rtp
                TApp(TCon(ev), [teff]) | ev.type-con/name == nameTpEv ->
                  val dataInfo = find-data-info(teff.get-type-name)
                  wrap-handled-from-data-effect(dataInfo.dEffect, teff)
                _ -> inf-error(rng, "Type.Infer.inferHandledEffect: illegal named effect type in operation?".text)
            Just((_, eff, _)) | handlerSort.is-handlerInstance -> 
              match eff.extract-effect-extend
                (ls, _) ->
                  match ls.filter(_.is-handled-effect)
                    Cons(l, _) -> l // TODO: can we assume the effect comes first?
                    Nil -> inf-error(rng, "Type.Infer.inferHandledEffect: not an effect operation:".text |+| qname.pp-name |.| ".".text)
                _ -> inf-error(rng, "Type.Infer.inferHandledEffect: cannot resolve effect operation:".text |+| qname.pp-name |.| ".".text |-| " hint: maybe wrong number of parameters?".text)
            _ -> inf-error(rng, "Type.Infer.inferHandledEffect: unable to determine the handled effect.".text |-| " hint: use a `handler<eff>` declaration?".text)

// Check coverage is not needed for type inference but gives nicer error messages
fun check-coverage(rng: range, eff: ktype, handler-con-name: name, branches: list<handler-branch<ktype>>)
  val mod-name = handler-con-name.qualifier
  fun field-to-op-name(fname: name)
    val (pre, post) = fname.nameLocalQual.list.span(_ != '-')
    val (op-sort, op-name) = 
      match (read-op-sort(pre.string), pre.take(1), post) 
        (Just(op-sort), ['@'], Cons(_, op-name)) -> (op-sort, op-name.string)
        _ -> failure/fail("Type.Infer.checkCoverage: illegal operation field name: " ++ fname.show ++ " in " ++ handler-con-name.show)
    (mod-name.qualify(new-qualified(fname.nameModule, op-name)), op-sort)
  fun branch-to-op-name(hbranch: handler-branch<ktype>)
    val nm = 
      if is-value-operation-name(hbranch.branchName) then // .val-<op>
        from-value-operation-name(hbranch.branchName) 
      else hbranch.branchName
    (mod-name.qualify(nm.unqualify), hbranch.branchSort)
  fun check-coverage-of(all-op-names: list<name>, op-names: list<(name, operation-sort)>, branch-names: list<(name, operation-sort)>)
    match op-names 
      [] ->
        if branch-names.is-empty then () 
          // should not occur if branches typechecked previously
        else match branch-names.filter(fn((bname, _)) !all-op-names.contains(bname))
          Cons((bname, _), _) -> term-error(rng, "operator".text |+| bname.pp-name |+| "is not part of the handled effect".text, eff, [])
          Nil -> inf-error(rng, "some operators are handled multiple times for effect".text |+| eff.pretty)
      Cons((op-name, op-sort),op-names') ->
        val (matches, branch-names') = branch-names.partition(fn((bname, _)) bname == op-name)
        match matches
          [(bname, bsort)] -> 
            if bsort != op-sort && op-sort == OpVal then 
              inf-error(rng, "cannot handle a 'val' operation".text |+| op-name.pp-name |+| "with".text |+| squotes(bsort.show.text))
            elif bsort > op-sort then 
              inf-warning(rng, "operation".text |+| op-name.pp-name |+| "is declared as '".text |+| op-sort.show.text |+| "' but handled here using '".text |+| bsort.show.text |+| "'".text)
            else ()
          [] -> inf-error(rng, "operator".text |+| op-name.pp-name |+| "is not handled".text)
          _ -> inf-error(rng, "operator".text |+| op-name.pp-name |+| "is handled multiple times".text)
  val (_, _, _, con-info) = resolve-con-name(handler-con-name, Nothing, rng)
  val op-names = con-info.params.drop(1).map(fn((fname, _)) field-to-op-name(fname)) // Drop (cfc) parameter
  val branch-names = branches.map(_.branch-to-op-name)
  check-coverage-of(op-names.map(fst), op-names, branch-names)

// resolve the effect tag core expression for handled effects.
fun effect-name-core(eff: keffect, rng: range): _ (maybe<core/core/expr>, name)
  match eff.expand-syn
    // handled effects (from an `effect` declaration)
    TApp(TCon(tc), [hx])
      | tc.name == nameTpHandled || tc.name == nameTpHandled1 || tc.name == nameTpNHandled || tc.name == nameTpNHandled1 ->
        val eff-name = hx.effect-name-from-label
        val (tag-qname, _, tag-info) = resolve-name(eff-name.to-effect-tag-name, Nothing, rng)
        (Just(tag-info.core-expr(tag-qname)), eff-name)
    // builtin effect
    _ ->
      (Nothing, eff.effect-name-from-label)

///////////////////////////////////////////////////////////
// Infer Applications and Resolve Overloaded Identifiers
//////////////////////////////////////////////////////////
fun infer-app-fun-first(prop, fexpr, fresolved, fixed0, named0, implicits0: list<((name, range), syntax/syntax/expr<ktype>, bool -> _ doc)>, rng, origFun: syntax/syntax/expr<_>, expect)
  with maybe-instantiate-or-generalize(rng, origFun.range, expect)
  // infer type of function
  val fprop = match (prop, fexpr)
    (Nothing, syntax/syntax/Var(name)) | !name.is-constructor-name ->
      val (_, ptp, info) = resolve-name(name, prop, rng)
      match (ptp, info.allow-implicit-mask)
        (TVar(), True) -> 
          // we propagate a function type (for example to mask<local> for function parameters)
          val teff = operations/fresh-effect()
          val tres = fresh-star() 
          val tpars = list(1, fixed0.list/length + named0.list/length + implicits0.list/length).map(fn(_) fresh-star())
          val ftp = TFun(tpars.map((nil, _)), teff, tres)
          Just((ftp, rng))
        _ -> prop
    _ -> prop
  val (ftp, eff1, fcore) = 
    with no-allow-return
    infer(fprop, Instantiated, fexpr)
  // we allow passing implicit parameters as a fixed argument: here we name those explicitly based on the type
  // todo: for now disallow implicit parameters as fixed ones as it can lead to long inference times?
  val allow-implicits-as-fixed = True
  val (fixed, named1) =  
    match ftp.split-fun-type
      Just((pars, _, _)) | allow-implicits-as-fixed -> 
        val (tfixed, toptionals, timplicits) = split-optional-implicit(pars)
        val (fixed1, fixed-implicit-args) = fixed0.split(tfixed.length + toptionals.length)
        if fixed-implicit-args.is-empty || fixed-implicit-args.length > timplicits.length then // too many arguments? see `test/static/wrong/rec1`
          (fixed0, named0)
        else 
          val fixed-implicits = timplicits.zipwith(fixed-implicit-args, fn((name, _), expr: syntax/syntax/expr<_>) ((name, expr.range), expr))
          (fixed1, fixed-implicits ++ named0)
      _ -> (fixed0, named0)
  // only add resolved implicits that were not already named
  val already-given = named1.map(_.fst.fst)
  val rimplicits = implicits0.filter(fn(((name,_), _, _)) !already-given.contains(name))
  val named' = named1 ++ rimplicits.map(fn(((name, _), expr, _)) ((name, range/null), expr)) // so no range info is emitted when checking 
  rimplicits.foreach fn((_, _, doc)) 
    add-range-info(fexpr.range, RIImplicits(doc))
  
  // match the type with a function type, wrap optional arguments, and order named arguments
  val FunMatchTypeArgs(iargs, pars0, fun-eff0, fun-tp0, core-app) = match-fun-type-args(rng, fexpr, ftp, fresolved, fixed, named')
  
  // match propagated type with the function result type
  // note: we may disable this in the future?
  val (pars, fun-eff, fun-tp) = 
    match prop
      Just((pres, prng)) -> 
        val _ = 
          with val ctxt = checkAnn(prng)
          infer-subsume(rng, fun-tp0, pres)
        (pars0.subst, fun-eff0.subst, fun-tp0.subst)
      Nothing -> (pars0, fun-eff0, fun-tp0)
  
  // infer the argument expressions and subsume the type
  val sftp = ftp.subst
  val unused = fresh-name("unused")
  val sd = infer-effect/scope-depth
  val (eff-args, core-args) = 
    with extend-inf-gamma([(unused, InfoVal(Public, unused, sftp, sd, rng, False, False, ""))]) // don't generalize over free propagated types
    val free = free-in-gamma() 
    val par-args = pars.map(snd).zip(iargs.map(snd))
    match origFun
      Var(name, _, _) | name == nameRunLocal -> 
        with with-local-scope
        with val ctxt = checkLocalScope(rng)
        infer-argsN(rng, par-args)
      _ -> infer-argsN(rng, par-args)
  
  // ensure arguments are evaluated in the declaration order
  val core = 
    match short-circuit(fcore, core-args)
      Just(c) -> c
      Nothing -> 
        // ensure named arguments are evaluated in the correct order
        if iargs.map(fst).monotonic || core-args.all(is-total) then 
          core-app(fcore, core-args)
        else 
          // let bind in evaluation order
          val vars = iargs.map(fn(_) unique-name("arg"))
          val vargs = zip(vars, core-args.zipwith(iargs, fn(carg, (i, _)) (i, carg)))
          val eargs: list<(name,(int,core/core/expr))> = vargs.sort(fn((_: name, (i: int, _)), (_: name, (j: int, _))) i < j)
          val defs = eargs.map fn((v, (_, arg)))
            DefNonRec(Def(v, arg.type-of, arg, Private, DefVal, InlineAuto, null, ""))
          val cargs = vargs.map fn((v, (_, arg)))
            Var(TName(v, arg.type-of), InfoNone)
          if fcore.is-total then 
            make-let(defs, core-app(fcore, cargs))
          else
            val fname = "fct".unique-name
            val fdef = DefNonRec(Def(fname, ftp, fcore, Private, DefFun([]) /* all own, TODO: maintain borrow annotations? */, InlineAuto, null, ""))
            val fvar = Var(TName(fname, ftp), InfoNone)
            Let(Cons(fdef, defs), core-app(fvar, cargs))
  
  // take top effect
  // todo: sub effecting should add core terms
  val top-eff = 
    with val ctxt = checkEffect(rng)
    infer-unifies(Cons((origFun.range, eff1), zip(iargs.map(_.snd.range), eff-args)))
  val _ = 
    with val ctxt = checkEffectSubsume(rng)
    infer-unify(rng, fun-eff, top-eff)
  
  // instantiate or generalize result type
  (fun-tp.subst, top-eff.subst, core)

// inferAppFirst <guessed fixed arg types> <priority order fixed args> <fixed args> <named args>
fun infer-app-args-first(fresolved, funExpr, args, fixed, named0, rng, expect, prop)
  match args
    Nil -> // we inferred all fixed arguments
      // this always fails since we have not been able to resolve the function name
      infer-app-fun-first(Nothing, funExpr, fresolved, fixed, named0, [], rng, funExpr, expect)
    Cons((idx,fix: syntax/syntax/expr<_>), fixs) -> 
      // try to improve our guess
      val (tp-arg, eff-arg, core-arg) = 
        with no-allow-return 
        infer(Nothing, Instantiated, fix)
      val fresolved' = fresolved ++ [(idx, (fix.range, tp-arg, eff-arg, core-arg))]
      val amb = 
        match funExpr.root-expr
          Var(name, _, name-range) ->
            val sctx = fixed-context(prop, fresolved', fixed.length, named0.map(_.fst.fst))
            match lookup-app-name(fixs.is-empty /* allow disambiguate */, name, sctx, rng, name-range)
              Right((itp, fexpr, implicits: list<((name,range), syntax/syntax/expr<ktype>, bool -> pretty-eff doc)>)) -> Just(((itp,rng), fexpr, implicits))
              Left() -> Nothing
          _ -> Nothing
      match amb
        Just((prop-tp, fexpr, implicits)) -> infer-app-fun-first(Just(prop-tp), fexpr, fresolved', fixed, named0, implicits, rng, funExpr, expect) 
        Nothing -> infer-app-args-first(fresolved', funExpr, fixs, fixed, named0, rng, expect, prop)
  
fun infer-app(prop: maybe<(ktype, range)>, expect: expect, funExpr: syntax/syntax/expr<ktype>, nargs: list<(maybe<(name,range)>, syntax/syntax/expr<ktype>)>, rng: range): _ (ktype, keffect, core/core/expr)
  // we cannot resolve an overloaded function name: infer types of arguments without propagation first.
  // The code handles inferring arguments in any order by keeping track of the index, but at the moment
  // we always infer from left to right until we can resolve the function type and then propagate argument types. 
  fun infer-app-from-args(fixed, named0)
    match fixed
      Nil -> 
        // there are no fixed arguments, use fun first anyways (and error..)
        infer-app-fun-first(Nothing, funExpr, [], [], named0, [], rng, funExpr, expect)
      _ -> infer-app-args-first([], funExpr, fixed.indexed, fixed, named0, rng, expect, prop)

  val (fixed, named-args) = nargs.split-named-args
  val amb = 
    match funExpr.root-expr
      Var(name, _, name-range) ->
        val sctx = fixed-count-context(prop, fixed.length, named-args.map(_.fst.fst))
        match lookup-app-name(False, name, sctx, rng, name-range)
          Right((tp, fexpr, implicits)) -> Just((Just((tp, rng)), fexpr, implicits)) // known type, propagate the function type into the parameters
          Left(_) -> Nothing // many matches, start with argument inference and try to resolve the function type
          // Note: lookup-app-name never unifies type variables so we should not emit errors on `Left()`
          // for example in `fn(f) f()` the `f` has a type `_a` and will not match `sctx`
      _ -> Just((Nothing, funExpr, [])) // Function expression first
  match amb
    Just((prop-tp, fexpr, implicits)) -> infer-app-fun-first(prop-tp, fexpr, [], fixed, named-args, implicits, rng, funExpr, expect)
    _ -> infer-app-from-args(fixed, named-args)

//////////////////////////////////////////
// Infer Lambda
//////////////////////////////////////////

fun infer-lam(top: bool, prop: maybe<(ktype, range)>, expect: expect, bindersl: list<value-binder<maybe<ktype>, maybe<syntax/syntax/expr<ktype>>>>, body0: syntax/syntax/expr<ktype>, rng: range)
  with is-named <- is-named-lam
  with with-scope
  with disallow-hole
  fun inf-body()
    val (bindersX, unpack-implicitss) = bindersl.map(infer-implicit-param).unzip
    val body = unpack-implicitss.foldr(body0, fn(f, x) f(x))
    val FunMatchResult(prop-args, prop-eff, prop-body, skolems, expect-body) = match-fun(bindersX.length, prop)
    val binders0 = bindersX.zipwith(prop-args) fn(binder, mb-prop)
      match binder.binderType
        Nothing -> ValueBinder(binder.name, mb-prop.map(snd), binder.expr, binder.name-range, binder.range)
        Just(_) -> ValueBinder(binder.name, binder.binderType, binder.expr, binder.name-range, binder.range)
    val binders1 = binders0.map(instantiate-binder)
    val eff = 
      match prop-eff
        Nothing -> operations/fresh-effect() 
        Just((eff, _)) -> eff
    val ldepth = infer-effect/local-depth
    val (infgamma, sub, defs) = infer-optionals(ldepth == 0, eff, [], binders1)
    fun coref(c) make-let(defs.map(DefNonRec), sub |-> c)
    val return-tp = 
      match prop-body
        Nothing -> fresh-star()
        Just((tp, _)) -> tp
    // nice names for eta-expanded expressions for in the IDE 
    val eta-expanded = !binders0.is-empty && binders0.all(_.name.hidden/starts-with("eta"))
    fun create-eta(name: name, n: int) 
      match "xyz".list.drop(n)
        Cons(c, rest) -> c.char
        Nil -> pretty(n+1)
    fun nice-eta(act)
      if eta-expanded then
        with with-nice-names(create-eta, binders0.map(name))
        add-range-info(rng.start, RIInlayHint(False /* append before */, "fn".text |.| parens(docs.map("_".text |.| _).intersperse(comma).hcat) |.| " ".text))
        act()
      else act()
    val (tp, eff1, core) = 
      with trace-indent
      with with-scope
      with extend-inf-gamma(infgamma)
      with extend-inf-gamma([(nameReturn, create-name-infoX(Public, nameReturn, ldepth, DefVal, body.range, return-tp, ""))])
      with nice-eta
      if is-named then infer-isolated(rng, body.rng, body, infer-expr(prop-body, expect-body, body))
      else infer(prop-body, expect-body, body)
    val _ = 
      with val ctxt = checkReturnResult(rng)
      infer-unify(body.range, return-tp, tp)
    val _ = 
      with val ctxt = Infer(rng)
      infer-unify(body.range, eff, eff1)
    val top-eff = 
      match prop-eff
        Nothing -> eff.subst
        Just((top-eff, r)) -> 
          val _ = 
            with val ctxt = checkEffectSubsume(rng)
            infer-unify(r, eff, top-eff)
          top-eff.subst
    val opt-pars = binders1.map(fn(b) (b.name, b.tp.subst))
    val body-core1 = add-lambdas(opt-pars, top-eff, Lam([], top-eff, coref(core)))
    val body-core2 = body-core1.subst
    val pars = opt-pars
    val sftp0 = TFun(pars, top-eff, tp).subst
    // check skolem escape (should this be after generalize?)
    if !top then 
      checkSkolemEscape(rng, sftp0, Nothing, skolems, tvsEmpty) // TODO: not having this check improves error messages but is it really safe?
    
    // substitute back skolems to meta variables
    val (sktvars, sksubs) = fresh-sub(Meta, skolems)
    val sftp1 = sksubs |-> sftp0
    val body-core3 = sksubs |-> body-core2
    subst-implicit-constraints(sksubs)

    // check for polymorphic parameters
    val unannot-binders = binders0.zip(binders1).filter(fn((b0, b1)) b0.is-nothing).map fn((b0, b1))
      (b.name, b.tp.subst)
    val poly-binders = unannot-binders.filter(fn((_, tp)) !tp.is-tau)
    if !poly-binders.is-empty then 
      val b = poly-binders[0].unjust
      type-error(rng, b.range, "unnannotated parameters cannot be polymorphic ".text, b.tp, [("hint".text, "annotate the parameter with a polymorphic type".text)])

    // add range info for each parameter
    if !eta-expanded then
      opt-pars.zipwith(par-types) fn(b, tp)
        val annotated =
          match (prop, b.tp)
            (Just((_, rng)), Just()) | rng.is-hidden -> True // actual annotation
            _ -> False
        add-range-info(b.name-range, RIId(b.name, NIValue("val", tp, "", annotated)), [], True)
    (sftp1, type-total, body-core3)
  val (ftp, _, fcore) = maybe-generalize(rng, body0.range, expect, inf-body)
  val eff = operations/fresh-effect()
  (ftp, eff, fcore)

//////////////////////////////////////////
// Infer Variables
//////////////////////////////////////////

fun infer-var(prop: maybe<(ktype, range)>, expect, name, rng, is-rhs)
  if name.is-constructor-name then 
    // constructor
    val (qname1, tp1, con-repr, con-info) = resolve-con-name(name, prop.map(tuple2/fst), rng)
    val info1 = InfoCon(Public, tp1, con-repr, con-info, rng, con-info.doc)
    val (qname, tp, info) = 
      val def-name: name = current-def-name()
      val creator-name: name = qname1.new-creator-name
      if def-name != creator-name.unqualify && def-name != nameCopy then 
        // a bit hacky, but ensure we don't call the creator function inside itself or the copy function
        match lookup-fun-name(creator-name, prop, rng)
          Just((qname', tp', info')) -> (qname', tp', info')
          Nothing -> (qname1, tp1, info1)
      else (qname1, tp1, info1)
    val core-var = info.core-expr(qname)
    add-range-info(rng, RIId(info1.canonical-name(qname1), NICon(tp, info1.doc), [], False))
    val (itp, coref) = maybe-instantiate(rng, expect, tp)
    (itp, fresh-effect(), coref(core-var))
  else 
    // variable
    // we cannot directly "resolveName" with a propagated type
    // as sometimes the types do not match and need to coerce due to local variables or references on the right-hand-side
    val vinfo =
      match prop
        Just(p) | is-rhs -> resolve-rhs-name(name, p, rng)
        _ -> resolve-name(name, prop, rng)
    infer-var-name(prop, expect, name, rng, is-rhs, vinfo)

fun infer-var-name(prop: maybe<(ktype, range)>, expect, name: name, rng: range, is-rhs: bool, (qname: name, tp: ktype, info: assumption/name-info))
  if tp.is-type-local-var && is-rhs then 
    val irng = rng.range/extend(-1)
    val (tp1, eff1, core1) = expr/infer(prop, expect, Parens(App(Var(nameLocalGet, False, irng), [(Nothing, App(Var(nameByref, False, irng), [(Nothing, Var(name, False, irng))], irng))], irng), name, "var", rng))
    add-range-info(rng, RIId(qname, NIValue(info.sort, tp1, info.doc, False), [], False))
    (tp1, eff1, core1)
  else 
    match info
      InfoVal(isVar=isVar) | isVar && is-rhs -> // is it a right hand side variable?
        val (tp1, eff1, core1) = expr/infer(prop, expect, App(Var(nameDeref, False, rng), [(Nothing, App(Var(nameByref, False, rng), [(Nothing, Var(name, False, rng))], rng))], rng))
        add-range-info(rng, RIId(qname, NIValue(info.sort, tp1, info.doc, False), [], False))
        (tp1, eff1, core1)
      InfoVal() | tp.is-value-operation ->
        add-range-info(rng, RIId(qname, NIValue(info.sort, tp, info.doc, False), [], False))
        expr/infer(prop, expect, App(Var(qname.to-value-operation-name, False, null), [], null))
      _ -> 
        val eff = fresh-effect()
        match compilation-constants.lookup(_ == qname)
          Just((tp', fcore)) -> (tp', eff, fcore(module-name(), rng))
          Nothing -> 
            val core-var = info.core-expr(qname)
            val fixed-effect = match tp.split-fun-scheme
              Just((_, _, eff', _)) -> eff'.is-effect-fixed
              _ -> False
            val (itp, coref) = maybe-instantiate(rng, expect, tp)
            val sitp = itp.subst
            val (rm-name, rm-doc) =
              if qname.hidden/starts-with("eta") then 
                match qname.lookup-nice-name
                  Nothing -> ()
                  Just(nice) -> add-range-info(rng.end-of-range, RIInlayHint(True, nice))
                (new-name("_"), "eta-expanded parameter")
              else (info.canonical-name(qname), info.doc)
            add-range-info(rng, RIId(rm-name, NIValue(info.sort, sitp, rm-doc, False), [], False))
            val depth = infer-effect/scope-depth
            fun inject-local(n)
              val hp = fresh-tvar(kindHeap, Meta)
              val local-tp = TApp(typeLocal, [hp])
              val mask-expr = eta-expand(n, rng, fn(apply) Inject(local-tp, Lam([], apply(Var(qname, False, rng)), False, rng), False, rng))
              val (tp', eff', core) = 
                with with-no-local-scope
                expr/infer(Nothing /* do not propagate as the effect is different */, Instantiated, mask-expr)
              (tp', eff', core)
            match (itp.expand-syn, prop)
              (TFun(pars), _) | !fixed-effect && info.allow-implicit-mask && !qname.is-hidden-name && depth > 0 ->
                inject-local(pars.length)
              (_, Just((TFun(pars, _, _), _))) | !fixed-effect && info.allow-implicit-mask && !qname.is-hidden-name && depth > 0 -> 
                inject-local(pars.length)
              _ -> (sitp, eff, coref(core-var))

val compilation-constants = 
  [
   // for now, use the module name to not leak info of a dev system
   (nameCoreFileFile, (typeString, fn(mod, rng) ELit(LitString(mod.show-plain ++ ".kk")))), 
   (nameCoreFileLine, (typeString, fn(mod, rng) ELit(LitString(rng.start.line.show)))),
   (nameCoreFileModule, (typeString, fn(mod, rng) ELit(LitString(mod.show-plain))))
  ]

//////////////////////////////////////////
// infer match, branches and patterns
//////////////////////////////////////////

type pattern-kind
  PatternOutermost(is-lazy: bool)
  PatternNested

fun infer-case(prop: maybe<(ktype, range)>, expect: expect, expr: syntax/syntax/expr<ktype>, 
              branches: list<syntax/syntax/branch<ktype>>, is-lazy-match: bool, rng: range): _ (ktype, keffect, core/core/expr)
  with maybe-instantiate-or-generalize(rng, branches.range, expect)
  val (ctp, ceff, ccore0) =
    with no-allow-return
    with disallow-hole
    infer(Nothing, Instantiated, expr)
  // infer branches
  val matched-names = expr.extract-matched-names
  val pat-kind = PatternOutermost(is-lazy-match)
  val bress = 
    with disallow-hole
    with with-scope
    match (prop, branches)
      (Nothing, Cons(b, bs)) -> // propagate the type of the first branch
        val (tpeffs, br) = infer-branch(pat-kind, prop, ctp, expr.range, matched-names, b)
        val tp = 
          match tpeffs
            Cons((tp, _), _) -> tp
            _ -> failure/fail("type/infer/infer-case: branch without guard")
        val bress = bs.map(infer-branch(pat-kind, Just((tp, b.range)), ctp, expr.range, matched-names, _))
        Cons((tpeffs, br), bress)
      _ -> branches.map(infer-branch(pat-kind, prop, ctp, expr.range, matched-names, _))
  val (tpeffss, bcores) = bress.unzip
  val (tps, effs) = unzip(tpeffss.concat)
  // ensure branches match 
  val rngs = branches.map(_.branchGuard.range)
  val brngs = branches.map(range)
  fun recur(tpsx: list<(ktype, (range, range))>)
    match tpsx
      Cons((tp, _)) -> tp.subst
      Cons((tp1, r), Cons((tp2, (ctx2, rng2)), tps')) ->
        val _ =
          with val ctxt = checkMatch(ctx2)
          infer-unify(rng2, tp1, tp2)
        recur(Cons((tp1,r), tps'))
  val res-tp = recur(zip(tps, zip(brngs, rngs)))
  val res-eff = fresh-effect()
  val _ = 
    with val ctxt = checkEffectSubsume(rng)
    Cons(expr.range, rngs).zipwith(Cons(ceff,effs)) fn(r, eff) 
      infer-unify(r, eff, res-eff)
  // check scrutinee type
  val stp = ctp.subst
  if stp.type-is-case-legal then ()
  else type-error(rng, expr.range, "can only match on literals or data types".text, stp, [])
  // get data info and analyze branches
  val data-info = stp.get-type-name.find-data-info
  val def-name = current-def-name()
  val sbcores = bcores.subst 
  // TODO: Analysis match 
  val (is-total, cbranches) = branches/analyze(def-name, rng, sbcores, [stp], [data-info], is-lazy-match)
  val cbranches' = 
    if is-total then cbranches
    else 
      val mod-name = module-name()
      val lit-pos = Literal(syntax/syntax/LitString(mod-name.show ++ rng.show, rng))
      val lit-def = Literal(syntax/syntax/LitString(def-name.show, rng))
      val exn-branch = Branch(PatWild(rng), [Guard(guardTrue, App(Var(namePatternMatchError, False, rng), [(Nothing, lit-pos), (Nothing, lit-def)], rng))])
      val cexn-branch = infer-branch(pat-kind, Just((res-tp, rng)), ctp, expr.range, matched-names, exn-branch)
      match cexn-branch 
        (Cons((_, eff)), cbranch) -> // already propagated
          with val ctxt = checkEffectSubsume(rng)
          infer-unify(rng, eff, res-eff)
          cbranches ++ [cbranch]
        _ -> failure/fail("type/infer/infer-case: should never, happen, cexn-branch always contains a guard")
  // add lazy force
  // todo: warning if lazy match on regular datatype?
  val ccore1 = 
    if !is-lazy-match && data-info.di/is-lazy then 
      val forceName = data-info.lazy-name("force")
      val (force, force-tp, force-info) = resolve-fun-name(forceName, CtxFunArgs(False, 1, [], Nothing), rng, expr.range)
      val cforce = force-info.core-expr(force)
      match ccore0
        core/core/App(Var(fname), [_]) | force == fname.get-name -> ccore0 // don't duplicate as force(force(expr)) -- this can happen in kind/infer where force is explicitly inserted sometimes
        _ -> 
          val (ftp, _, coref) = infer-effect/instantiate(force-tp, rng) 
          match ftp.split-fun-type
            Just((_, eff, rtp)) -> 
              val _ = 
                with val ctxt = Infer(rng)
                infer-unify(expr.range, ctp, rtp)
              val _ = 
                with val ctxt = checkEffectSubsume(rng)
                infer-unify(expr.range, eff, res-eff)
              App(coref(cforce), [ccore0])
    else ccore0
  val core = get-subst() |-> Case([ccore1], cbranches')
  val sres-eff = res-eff.subst
  (res-tp, sres-eff, core)  

fun infer-branch(pat-kind, prop, match-type, match-range, matched-names, branch)
  match branch
    syntax/syntax/Branch(pattern, guards) -> 
      infer-pattern(pat-kind, match-type, branch.range, pattern, fn(pcore, gcores: list<core/core/guard>) {
          if pattern.range != range/null then  
            // check for unused pattern bindings 
            val defined = pcore.pat/bound-vars
            val free = gcores.free-vars.list.map(get-name).linear-set
            match defined.filter(fn(tn) !free.member(tn.get-name)).list
              [] -> ()
              names -> 
                inf-warning(pattern.range, "pattern variables ".text |+| tupled(names.map(_.get-name.pp-name)) |+| "are unused (or a wrongly spelled constructor?)".text |-| 
                  " hint: prepend an underscore to make it a wildcard pattern".text)
          core/core/Branch([pcore], gcores)
        }, 
        fn(inf-gamma) {
            extend-inf-gamma-ex(False, matched-names, inf-gamma, {guards.map(infer-guard(prop, branch.range, _)).unzip})
        })

fun infer-guard(prop: maybe<(ktype,range)>, branch-range: range, Guard(test, expr): syntax/syntax/guard<ktype>)
  val (gtp, geff, gcore) = 
    with no-allow-return 
    infer(Just((typeBool, test.range)), Instantiated, test)
  val _ = 
    with val ctxt = checkGuardTotal(branch-range)
    infer-unify(test.range, typeTotal, geff)
  val _ = 
    with val ctxt = checkGuardBool(branch-range)
    infer-unify(test.range, typeBool, gtp)
  // check branch expression
  val (btp, beff, bcore) = infer(prop, Instantiated, expr)
  ((btp, beff), get-subst() |-> core/core/Guard(gcore, bcore))

fun infer-pattern-nested(pat-kind: pattern-kind, match-type: ktype, branch-range: range, pattern: syntax/syntax/pattern<ktype>): _ (core/core/pattern, list<(name, assumption/name-info)>)
  val (_, res) = infer-pattern(pat-kind, match-type, branch-range, pattern, fn(pcore, inf-gamma) (pcore, inf-gamma)) fn(inf-gamma)
    val smatch-type = match-type.subst
    ([(smatch-type, typeTotal)], inf-gamma)
  res

fun use-skolemized-con(con-info: con-info, gcon-tp: ktype, range, name-range: range, cont)
  if con-info.existentials.is-empty then 
    val (conRho, _, _) = gcon-tp.infer-effect/instantiate(name-range)
    val (res, _) = cont(conRho, [])
    res
  else 
    val con-res-tp = fresh-star()
    val con-exists-tp = TForAll(con-info.existentials, if con-info.params.is-empty then con-res-tp else TFun(con-info.params, typeTotal, con-res-tp))
    with-skolemized(range, con-exists-tp, Nothing) fn(conXRho0, xvars)
      val conXRho = operations/instantiate(TForAll(con-info.foralls, conXRho0), name-range)
      val (iconRho, _, _) = gcon-tp.infer-effect/instantiate(name-range)
      val _ =
        with val ctxt = checkOp(range)
        infer-unify(name-range, conXRho, iconRho)
      cont(iconRho.subst, xvars)

fun infer-pattern(pat-kind: pattern-kind, match-type: ktype, branch-range: range, 
    pat: syntax/syntax/pattern<ktype>, 
    with-pattern: (core/core/pattern, a) -> _ b, 
    infer-part: (list<(name,assumption/name-info)> -> _ (list<(ktype, keffect)>, a)), 
    ?(|->): (sub, a) -> _ a): _ (list<(ktype, keffect)>, b)
  match pat 
    PatCon(name, patterns0, name-range, range) -> 
      val (qname, gcon-tp, repr, con-info) = resolve-con-pattern-name(name, match-type, patterns0.length, range)
      add-range-info(name-range, RIId(qname, NiCon(gcon-tp, con-info.doc), [], False))
      use-skolemized-con(con-info, gcon-tp, branch-range, range) fn(con-rho, xvars)
        val (con-par-tps, con-eff-tp, con-res-tp) = con-rho.split-con-tp
        val _ =
          with val ctxt = checkConTotal(range)
          infer-unify(name-range, con-eff-tp, typeTotal)
        val _ = 
          with val ctxt = checkConMatch(range)
          infer-unify(name-range, con-res-tp, match-type)
        // check valid lazy constructors
        val data-info = find-data-info(con-res-tp.get-type-name)
        if data-info.di/is-lazy then 
          match pat-kind
            PatternOutermost(is-lazy-match) -> 
              if con-info.coninfo/is-lazy && !is-lazy-match then 
                inf-error(name-range, qname.pp-name |.| ": lazy constructors are not allowed in a (non lazy) match".text)
            PatternNested -> 
              inf-error(name-range, qname.pp-name |.| ": constructors of a lazy type cannot be matched in a nested pattern (but must always be matched as an outermost pattern)".text)
        val patterns = match-patterns(range, name-range, con-rho, con-par-tps, patterns0)
        val (cpatterns, inf-gammas) = con-par-tps.map(snd).zipwith(patterns, fn(par-tp, p) infer-pattern-nested(PatternNested, par-tp.subst, branch-range, p)).unzip
        val inf-gamma = inf-gammas.concat
        val (btpeffs: list<(ktype, keffect)>, core-guards0) = infer-part(inf-gamma) // infer-guards
        val (pcore, core-guards) = 
          if xvars.is-empty then (PatCon(TName(qname, con-rho), cpatterns, repr, con-par-tps.map(snd), [], con-res-tp, con-info, False), core-guards0)
          else 
            val (bind-exists, sub-exists: sub) = fresh-sub(Bound, xvars)
            val pcore = PatCon(TName(qname, con-rho), sub-exists |-> cpatterns, repr, sub-exists |-> con-par-tps.map(snd), bind-exists, con-res-tp, con-info, False)
            (pcore, sub-exists |-> core-guards0)
        ((btpeffs, with-pattern(pcore, core-guards)), btpeffs.free-type-vars)
    PatVar(binder) -> 
      add-range-info(binder.name-range, RIId(binder.name, NIValue("val", match-type, "", binder.is-annotated), [], True))
      match binder.binderType
        Just(tp) -> 
          with val ctxt = checkAnn(binder.range)
          infer-unify(binder.name-range, match-type, tp)
        Nothing -> ()
      val (cpat, infgamma0) = infer-pattern-nested(pat-kind, match-type, branch-range, binder.expr)
      val infgamma = [(binder.name, create-name-infoX(Public, binder.name, infer-effect/scope-depth, DefVal, binder.name-range, match-type, ""))] ++ infgamma0
      val (btpeffs, x) = infer-part(infgamma)
      (btpeffs, with-pattern(PatVar(TName(binder.name, match-type), cpat), x))
    PatWild() ->
      val (btpeffs, x) = infer-part([])
      (btpeffs, with-pattern(PatWild, x))
    PatAnn(pat, tp, rng) -> 
      infer-pattern(pat-kind, tp, rng, pat, with-pattern) fn(infgamma)
        val _ = 
          with val ctxt = checkAnn(rng)
          infer-unify(pat.pattern/range, match-type, tp) // TODO: improve error message
        infer-part(infgamma)
    PatParens(pat) -> infer-pattern(pat-kind, match-type, branch-range, pat, with-pattern, infer-part)
    PatLit(lit) -> 
      val (pat', tp) = match lit 
        LitInt(i, _) -> (PatLit(LitInt(i)), typeInt)
        LitChar(c, _) -> (PatLit(LitChar(c)), typeChar)
        LitFloat(f, _) -> (PatLit(LitFloat(f)), typeFloat)
        LitString(s, _) -> (PatLit(LitString(s)), typeString)
      val _  = 
        with val ctxt = checkLitMatch(lit.range)
        infer-unify(branch-range, tp, match-type)
      val (btpeffs,x) = infer-part([])
      (btpeffs, with-pattern(pat', x))

fun infer-binders(inf-gamma, binders: list<value-binder<_, _>>)
  match binders
    [] -> inf-gamma
    Cons(par, pars) -> 
      val info = (par.name, create-name-infoX(Public, par.name, infer-effect/scope-depth, DefVal, par.range, par.binderType, ""))
      infer-binders(inf-gamma ++ [info], pars)

// infer implicit parameter declaration:
// check if the expression is a single identifier and possibly generate unpacking of fields
fun infer-implicit-param(par: value-binder<t1, maybe<syntax/syntax/expr<t2>>>): _ (value-binder<t1, maybe<syntax/syntax/expr<t2>>>, syntax/syntax/expr<ktype> -> syntax/syntax/expr<ktype>)
  if par.name.is-implicit-param-name then 
    val unpack = 
      match par.expr
        Just(Parens(Var(qname, _, rng))) -> // encoded in the parser as a default expression
          infer-implicit-unpack(par.range.hide, rng.hide, par.name, qname)
        Nothing -> id
        Just(expr) -> 
          context-error(par.range, expr.range, "the value of an implicit parameter must be a single identifier".text, [])
          id
    // leave the binder name locally qualified as `@implicit/name` -- binderName = pname,
    (ValueBinder(par.name, par.binderType, Nothing, par.name-range, par.range), unpack)
  else (par, id)
     
    
fun infer-implicit-unpack(rng: range, nrng: range, pname: name, qname: name): _ (syntax/syntax/expr<ktype> -> syntax/syntax/expr<ktype>)
  match newtypes-lookup-any(qname)
    Just(DataInfo(sort=Inductive, constrs=[conInfo], def=ddef)) | !ddef.is-open -> 
      // struct unpack the fields
      val pats = conInfo.params.map(fst).filter(!_.is-nil).map(fn(fname) PatVar(ValueBinder(pname.qualify-unpacked(fname), Nothing, PatWild(nrng), nrng, rng)))
      val pat = PatCon(conInfo.name, pats.map(fn(p) (Nothing, p)), nrng, null) // no warnings for unused pattern variables by using a null range
      fun unpack(body)
        Case(Var(pname, False, nrng), [Branch(pat, [Guard(guardTrue, body)])], False, rng)
      fun extract-struct-type(tp)
        match tp.expand-syn
          TApp(TCon(tcon), _) -> [tcon.name]
          TCon(tcon) -> [tcon.name]
          _ -> []
      val bases = conInfo.params.filter(fn((fname, _)) fname.name/starts-with("base")).flatmap(fn((fname, ftp)) ftp.extract-struct-type.map((fname, _)))
      fun compose(l, e) 
        match l
          Nil -> e
          Cons(f, fs) -> f(compose(fs, e))
      val unpackBases = bases.map fn((fname, fqname))
        infer-implicit-unpack(rng, nrng, pname.qualify-unpacked(fname), fqname)
      fn(e) compose(Cons(unpack, unpackBases), e)
    _ -> id

// Infer automatic unwrapping for parameters with default values, and adjust their type from optional<a> to a
// Takes an accumulated InfGamma (initially empty), a list of parameters (as value binders) and returns
// the new InfGamma and a substitution from optional parameter names to the local unique names (of type a)
// and a list of core (non-recursive) bindings (where the substitution has already been applied)
fun infer-optionals(allow-implicit-mask: bool, eff : keffect, inf-gamma: list<(name, assumption/name-info)>, params: list<value-binder<ktype, maybe<syntax/syntax/expr<ktype>>>>): _ (list<(name, assumption/name-info)>, list<(tName, core/core/expr)>, list<core/core/def>)
  match params 
    [] -> (inf-gamma, [], [])
    Cons(par: value-binder<ktype, maybe<syntax/syntax/expr<ktype>>>, pars) -> 
      match par.expr
        Nothing -> infer-optionals(allow-implicit-mask, eff, inf-gamma ++ [(par.name, create-name-infoEX(Public, par.name, infer-effect/scope-depth, DefVal, allow-implicit-mask, par.range, par.binderType, ""))], pars)
        Just(def-expr) -> // default value 
          val def-range = def-expr.range
          val full-range = par.range.combine(def-range)
          val opt-tp = par.binderType
          // infer parameter type from optional
          val tvar = fresh-star()
          val _ = 
            with val ctxt = Infer(full-range)
            infer-unify(par.range, opt-tp, tvar.make-optional)
          val partp = tvar.subst
          // infer expression
          val (expr-tp, expr-eff: ktype, core-expr) = 
            extend-inf-gamma(inf-gamma) 
              infer(Just((partp, par.range)), if partp.is-rho then Instantiated else Generalized(False), def-expr)
          val _ = 
            with val ctxt = checkOptional(full-range)
            infer-unify(def-range, partp, expr-tp)
          
          // check optional expressions; avoid unifying with `eff` type if possible
          match expr-eff.subst
            TVar(_) -> 
              with val ctxt = checkOptionalTotal(full-range)
              infer-unify(def-range, eff, expr-eff)
            _ -> if expr-eff.is-type-total then () else 
              with val ctxt = Infer(full-range)
              infer-unify(def-range, eff, expr-eff)
          
          val tp = partp.subst
          val infgamma' = inf-gamma ++ [(par.name, create-name-infoEX(Public, par.name, infer-effect/scope-depth, DefVal, allow-implicit-mask, par.range, tp, ""))]

          // build up core to get the optional value
          val local = par.name.unique-name-from
          val temp = par.name.unique-name-from
          val di = find-data-info(nameTpOptional)
          val (core-name-opt, core-tp-opt, core-repr-opt, con-info-opt) = resolve-con-name(nameOptional, Nothing, full-range)
          val (core-name-opt-none, core-tp-opt-none, core-repr-opt-none, con-info-opt-none) = resolve-con-name(nameOptionalNone, Nothing, full-range)
          val temp-name = TName(temp, tp)
          val par-name = TName(par.name, opt-tp)
          val core-par = Var(par-name, InfoNone) 
          val core-res-tp = TApp(TCon(TypeCon(di.name, di.kind)), [tp])
          val init = core/core/Case([core-par], 
               [Branch([
                  PatCon(TName(core-name-opt, core-tp-opt), [PatVar(temp-name, PatWild)], core-repr-opt, [tp], [], core-res-tp, con-info-opt, False
                    )], [core/core/Guard(exprTrue, Var(temp-name, InfoNone))]),
                Branch([
                  PatCon(TName(core-name-opt-none, core-tp-opt-none), [], core-repr-opt-none, [], [], core-res-tp, con-info-opt-none, True // Skip test
                    )], [core/core/Guard(exprTrue, core-expr)])
              ])
          val def = Def(local, partp, init, Private, DefVal, InlineNever, par.name-range, "")
          val sub = [(TName(par.name, tp), Var(TName(local, partp), InfoNone))]
          // infer the rest
          val (infgamma2, sub2, defs2) = infer-optionals(allow-implicit-mask, eff, infgamma', pars)
          (infgamma2, sub ++ sub2, Cons(def, sub |-> defs2))


//////////////////////////////////////////
// infer arguments
//////////////////////////////////////////

// infer the types of argument expressions, some of which may have already been inferred (`:FixedArg`).
fun infer-argsN(rng: range, par-args: list<(ktype, arg-expr)>): _ (list<keffect>, list<core/core/expr>)
  fun infer-arg-expr(tp: ktype, arg-expr: _, hidden: bool) // TODO: Add context for better error messages for implicit parameters?
    with (if hidden then no-range-info else fn(f) f())
    with allow-return 
    val eta-arg = eta-expand-var-arg(tp, arg-expr)
    throw("")
    infer(Just((tp, arg-expr.range)), if tp.is-rho then Instantiated else Generalized(False), eta-arg)
  fun infer-arg(acc, args)
    match args 
      [] -> acc.reverse
      Cons((tpar: ktype, arg: arg-expr), args) ->
        val tpar0 = tpar.subst
        fun subsume-arg((targ, teff: ktype, core))
          val tpar1 = tpar0.subst
          val (_, coref) = infer-subsume(arg.range, tpar1, targ)
          (teff.subst, coref(core))
        val (eff, core) = match arg
          ArgExpr(arg-expr, hidden) -> subsume-arg(infer-arg-expr(tpar0, arg-expr, hidden))
          ArgCore((_, ctp, ceff, carg)) -> 
            val res = if tpar0.is-rho then (ctp, ceff, carg)
                      else generalize(rng, rng, False, {(ctp, ceff, carg)}) // TODO: is this ok?
            subsume-arg(res)
          ArgImplicit(name, r, _) ->
            val (arg-expr, term-info) = resolve-implicit-name(name, tpar0, r, r.end-of-range)
            // for any errors in `rng` we can show a nice representation as `termInfo` since
            // the `argExpr` is generated by implicit name resolving
            with hidden-term-doc(rng, term-info)
            subsume-arg(infer-arg-expr(tpar0, arg-expr, True))
        infer-arg(Cons((eff, core), acc), args)
  with trace-indent
  infer-arg([], par-args).unzip
 


// Possibly eta-expand an (variable) argument to resolve any optional and implicit parameters
fun eta-expand-var-arg(tp: ktype, arg-expr: syntax/syntax/expr<ktype>): _ syntax/syntax/expr<ktype>
  fun is-named-arg(arg)
    match arg
      (Just(_), _) -> True
      _ -> False
  match (arg-expr, tp.split-fun-type) // not for polymorphic types (e.g. `type/hr1.kk`)
    (Var(name, _, vrng), Just((par-tps, _, res-tp))) | !par-tps.has-optional-or-implicits -> 
      // variable argument with an expected function type without optional parameters
      eta-expand-expr(name, vrng, 0, par-tps, res-tp, fn(extra-args, rng) App(arg-expr, extra-args, rng), arg-expr)
    (App(v as Var(name, _, vrng), args, _), Just((par-tps, _, res-tp))) | !par-tps.has-optional-or-implicits && args.all(is-named-arg) ->
      eta-expand-expr(name, vrng, args.length, par-tps, res-tp, fn(extra-args, rng) App(v, extra-args ++ args, rng), arg-expr)
    _ -> arg-expr

fun eta-expand-expr(name: name, nm-range: range, arg-count: int, par-tps: list<(name, ktype)>, res-tp: ktype, make-app: (list<(maybe<(name, range)>, syntax/syntax/expr<ktype>)>, range) -> syntax/syntax/expr<ktype>, arg-expr: syntax/syntax/expr<ktype>): _ syntax/syntax/expr<ktype>
  val matches = lookup-name-ctx(is-info-val-fun-ext, name, CtxFunArgs(True /* Not partial */, par-tps.length, [], Just(res-tp)), nm-range)
  match matches
    [(_, info)] -> 
      match info.scheme.split-fun-scheme
        Just((_, vpar-tps, _, _)) | arg-count < vpar-tps.length && vpar-tps.has-optional-or-implicits 
          && par-tps.map(snd).all(is-mono-type) -> // cannot abstract over polymorphic parameters
            // the variable has a type with optional parameters, eta-expand it to match the expected type without optional parameters
            val rng = arg-expr.range
            val named-fixed = par-tps.map-indexed(fn(i, _) make-hidden-name("arg", ("x" ++ i.show).new-name))
            val args-fixed = par-tps.map(fst).zipwith(named-fixed) fn(orig-name, new-name)
              val named-param = 
                    if !orig-name.is-nil && vpar-tps.any(fn((n, _)) n == orig-name) then Just((orig-name, rng))
                    else Nothing
              (named-param, Var(new-name, False, rng))
            val body = make-app(args-fixed, rng) // App arg-expr args-fixed rng
            Lam(named-fixed.map(fn(nm) ValueBinder(nm, Nothing, Nothing, rng, rng)), body, False, rng)
        _ -> arg-expr
    _ -> arg-expr

fun split-named-args(nargs: list<(maybe<(name, range)>, a)>): _ (list<a>, list<((name, range), a)>)
  val nfixed = nargs.filter(fn((nm, _)) nm.is-nothing)
  val nnamed = nargs.filter(fn((nm, _)) nm.is-just)
  val fixed = nfixed.map(snd)
  val named-args = nnamed.map(fn((Just((name, r)), arg)) ((name, r), arg))
  // check that named arguments all come after the positional ones
  fun check-duplicates(seen: list<name>, named-argsx)
    match named-argsx
      Cons(((name, r), _), rest) -> 
        if seen.contains(name) then  
          inf-error(r, "named argument".text |+| name.pp-name |+| "is given more than once".text) // TODO: Should this consider implicits differently?
          check-duplicates(seen, rest)
        else 
          check-duplicates(Cons(name, seen), rest)
      Nil -> ()
  check-duplicates([], named-args)
  (fixed, named-args)

fun match-patterns(ctx-range: range, nm-range: range, con-tp: ktype, con-par-types: list<(name, ktype)>, patterns0: list<(maybe<(name,range)>, syntax/syntax/pattern<ktype>)>): _ list<syntax/syntax/pattern<ktype>>
  fun match-fixed(pars, pats)
    (pars.list/drop(pats.list/length), pats)
  fun remove(nm: name, acc, l)
    match l
      [] -> Nothing
      Cons(par as (i, (par-name, _)), pars) -> 
        if par-name == nm then Just((i, acc.reverse ++ pars))
        else remove(nm, Cons(par, acc), pars)
  fun match-named(pars, pats)
    match (pars, pats)
      ([], []) -> []
      ([], Cons) -> []
      (pars, Cons(((name, rng), pat), named-pats)) -> 
        match remove(name, [], pars)
          Nothing ->
            type-error(ctx-range, rng, "there is no constructor field with name".text |+| name.pretty, con-tp, [])
            match-named(pars, named-pats)
          Just((i, pars1)) ->
            Cons((i, pat), match-named(pars1, named-pats))
      (pars, []) -> pars.map(fn((i, _)) (i, PatWild(ctx-range)))
  val patterns1 = 
      if con-par-types.length < patterns0.length then 
        type-error(ctx-range, nm-range, "constructor has too many arguments".text, con-tp, [])
        patterns0.take(con-par-types.length)
      else patterns0
  val (fixed, named-args) = split-named-args(patterns1)
  val (pars1, pats1) = match-fixed(con-par-types.indexed, fixed)
  val ipats = match-named(pars1, named-args)
  (pats1 ++ ipats.sort(fn((i: int, _), (j: int, _)) i < j).map(snd))

// Match given fixed arguments and named arguments with a function type.
// some fixed arguments may already have been inferred (`fresolved`).
// also returns a list of implicit arguments that need to be resolved.
// returns:
// - iargs: a list of indexed argument terms, either user expressions, already resolved (from `fresolved`), or implicit names
//          the indices indicate the required evaluation order (due to named arguments).
// - pars: list of the full function parameters (name,type)
// - effect of the function
// - the result type of the function
// - a core transformer that modifies the application appropriately (for constructor copy)
type arg-expr
  ArgExpr(e: syntax/syntax/expr<ktype>, hide-range-info: bool)
  ArgCore(arg: fixed-arg)
  ArgImplicit(name: name, app-range: range, name-range: range)

fun arg-expr/range(a: arg-expr): range
  match a
    ArgExpr(e, _) -> e.range
    ArgCore((rng, _, _, _)) -> rng
    ArgImplicit(_, app-rng, _) -> app-rng

fun pp-arg-expr(ae: arg-expr): _ doc
  match ae
    ArgExpr(e, _) -> "ArgExpr".text |+| e.pretty 
    ArgCore((_, tp, _, _)) -> "ArgCore".text |+| tp.pp-type
    ArgImplicit(n, _, _) -> "ArgImplicit".text |+| n.pp-name

// Try to match the propagated type with a function type,
// returning the propagated argument, effect, and result type, and the expected instantiation of the result
type fun-match-result
  FunMatchResult(
    mb-args: list<maybe<(name, ktype)>>,
    mb-eff: maybe<(ktype, range)>,
    mb-body: maybe<(ktype, range)>,
    mb-skolems: list<type-var>,
    expect: expect
  )
type fun-match-type-args
  FunMatchTypeArgs(
    mb-args: list<(int, arg-expr)>,
    mb-named: list<(name, ktype)>,
    eff: keffect,
    res: ktype,
    fcore: (core/core/expr, list<core/core/expr>) -> core/core/expr
  )

fun wrap-delay(e: syntax/syntax/expr<ktype>): _ syntax/syntax/expr<ktype>
  fun is-delayed(expr: syntax/syntax/expr<ktype>): _ bool
    match expr
      Lam([]) -> True
      Var(n) -> 
        match lookup-name-ctx(is-info-val-fun-ext, n, CtxFunArgs(False, 0, [], Nothing), expr.range)
          [(_, info)] -> info.scheme.is-delayed-type
          _ -> False
      _ -> False
  if is-delayed(e) then e
  else Lam([], e, False, e.range)

fun extract(name: name, acc: list<(int, (name, ktype))>, args: list<(int, (name, ktype))>): maybe<(int, ktype, list<(int, (name, ktype))>)>
  match args
    [] -> Nothing
    Cons(par as (i, (n, tp)), rest) -> 
      if n == name || name == n.split-implicit-param-name.fst then Just((i, tp, acc.reverse ++ rest))
      else extract(name, Cons(par, acc), rest)

fun match-fun-type-args(ctx-range: range, f: syntax/syntax/expr<ktype>, tp: ktype, fresolved: list<(int, fixed-arg)>, fixed: list<syntax/syntax/expr<ktype>>, named-args: list<((name, range), syntax/syntax/expr<ktype>)>): _ fun-match-type-args
  val rng = f.range
  val fixed-length = fixed.length
  val named-length = named-args.length
  fun report-non-callable()
    fun shadow-hint((nm: name, name-info: assumption/name-info))
      [("hint".text, nm.pp-name |+| "at position".text |+| name-info.range.show.text |+| "might be shadowing another function".text)]
    val hints = 
      match f
        Var(name) ->
          match lookup-local-name(is-infoVal, name)
            Right((nm, nm-info)) -> shadow-hint((nm, nm-info))
            Left(results) -> results.flatmap(shadow-hint) //  Multiple locals with the same name?
        _ -> []
    type-error(ctx-range, rng, "only functions or types with a copy constructor can be applied".text, tp, hints)
    FunMatchTypeArgs((fixed ++ named-args.map(snd)).map-indexed(fn(i, x) (i, ArgExpr(x, True))), [], typeTotal, typeUnit, core/core/App)
  fun arg-wrap-tp(argtp: ktype, arg)
    if argtp.is-optional then arg.wrap-optional
    elif argtp.is-delay then arg.wrap-delay
    else arg
  fun match-fixed(pars, fixedx)
    match (pars, fixedx)
      (pars, []) -> (pars, [])
      (Cons((_, tp'), pars'), Cons((i: int, arg), fixed')) -> 
        match fresolved.lookup(_ == i)
          Just((crng, ctp, ceff, carg)) -> 
            val (newtp, newarg) = 
                  if tp'.is-optional then (ctp.make-optional, ctp.wrap-optional(carg))
                  else (ctp, carg)
            val (prest, rest) = match-fixed(pars', fixed')
            (prest, Cons((i, ArgCore((crng, newtp, ceff, newarg))), rest))
          Nothing -> 
            val (prest, rest) = match-fixed(pars', fixed')
            (prest, Cons((i, ArgExpr(arg-wrap-tp(tp', arg), False)), rest))
      _ -> 
        type-error(ctx-range, rng, "function is applied to too many arguments".text, tp, [])
        ([], [])
  // in the result, the first int is position of the parameter `j`, the second int `i` is the original position of
  // the argument (so we can evaluate in argument order)
  fun match-named(pars, named-argsx: list<(int, ((name, range), syntax/syntax/expr<ktype>))>)
    match (pars, named-argsx)
      ([], []) -> []
      ([], Cons()) -> 
        type-error(ctx-range, rng, "function is applied to too many arguments".text, tp, [])
        []
      (_, Cons((i, ((name, r), arg)), named-rest)) -> 
        match extract(name, [], pars)
          Just((j, tp', pars-rest)) -> 
            Cons((j, (i, ArgExpr(arg-wrap-tp(tp', arg), r.range/is-null))), 
              match-named(pars-rest, named-rest))
          Nothing -> 
            type-error(ctx-range, rng, "there is no parameter with name".text |+| name.pp-name, tp, [])
            match-named(pars, named-rest)
      (_, []) -> 
        if pars.all(_.snd.is-optional-or-implicit) then 
          val (optionals, implicits) = pars.span(_.snd.snd.is-optional)
          val ops = zip(list(fixed-length + named-length, pars.length), optionals) // TODO Fix the list()
            .map fn((i, (j, (_, _)))) (j, (i, ArgExpr(optionalNone, True)))
          val imps = zip(list(fixed-length + named-length + ops.length, pars.length), implicits)
            .map fn((i, (j, (n, _)))) (j, (i, ArgImplicit(n, rng, rng)))
          ops ++ imps
        else 
          val hints = match f.root-expr
            Var(name, _, _) | name == "resume".new-name ->
              [("hint".text, "cannot use \"resume\" inside a val/fun/except clause".text)]
            _ -> []
          type-error(ctx-range, rng, "function does not have enough arguments".text, tp, hints)
          [] 
  fun match-parameters(pars)
    val (pars1, args1) = match-fixed(pars, fixed.indexed) 
    val indexed-pars = list(fixed-length, fixed-length + pars1.length)
    val iargs2 = match-named(zip(indexed-pars, pars1), zip(indexed-pars, named-args))
    args1 ++ iargs2.sort(fn((i1, _), (i2, _)) cmp(i1, i2).is-lt).map(snd)
  match tp
    TFun(pars, eff, res) -> 
      val iargs = match-parameters(pars)
      FunMatchTypeArgs(iargs, pars, eff, res, core/core/App)
    TSyn(_, _, t) -> match-fun-type-args(ctx-range, f, t, fresolved, fixed, named-args)
    TVar(tv) -> 
      if !named-args.is-empty then // TODO: take fresolved into account
        inf-error(rng, "cannot use named arguments on an inferred function".text |-| 
                        " hint: annotate the parameters".text)
      val targs = fixed.map(fn(_) (nil, fresh-star())) ++ named-args.map(fn((n, _)) (n.fst, fresh-star()))
      val teff = fresh-effect()
      val tres = fresh-star()
      add-sub(sub/single(tv, TFun(targs, teff, tres)))
      FunMatchTypeArgs((fixed ++ named-args.map(snd)).map-indexed(fn(i, x) (i, ArgExpr(x, False))), targs, teff, tres, core/core/App)
    _ -> 
      // apply the copy constructor if we can find it
      val matches = lookup-name-ctx(is-info-val-fun-ext, nameCopy, CtxFunTypes(True, [tp], [], Nothing), rng)
      match matches 
        [(qname, info)] ->
          val (_, contp, coreInst) = info.scheme.instantiate-ex(rng)
          val FunMatchTypeArgs(iargs, pars, eff, res, _) = match-fun-type-args(ctx-range, f, contp, fresolved, Cons(f, fixed), named-args)
          FunMatchTypeArgs(iargs, pars, eff, res, fn(c, cargs) core/core/App(coreInst(info.core-expr(qname)), cargs))
        _ -> report-non-callable()

fun match-fun(nargs: int, mb-type: maybe<(ktype, range)>): _ fun-match-result
  match mb-type
    Nothing -> FunMatchResult(Nothing.replicate(nargs), Nothing, Nothing, [], Instantiated)
    Just((tp, rng)) -> 
      val (skolems, rho, _) = tp.skolemize-ex(rng)
      match rho.split-fun-type
        Nothing -> FunMatchResult(Nothing.replicate(nargs), Nothing, Nothing, skolems, Instantiated)
        Just((args, eff, res)) -> 
          val m = args.length 
          // can happen: see test/type/wrong/hm4 and hm4a
          FunMatchResult((args.map(Just) ++ Nothing.replicate(nargs - m)).take(nargs), 
                          Just((eff, rng)), Just((res, rng)), skolems, 
                          if res.is-rho then Instantiated else Generalized(False))




//////////////////////////////////////////
// Helpers
//////////////////////////////////////////
fun instantiate-binder(b: value-binder<maybe<ktype>, e>): _ value-binder<ktype, e>
  match b
    ValueBinder(name, Just(tp), e, nrng, rng) -> ValueBinder(name, tp, e, nrng, rng)
    ValueBinder(name, Nothing, e, nrng, rng) -> ValueBinder(name, fresh-star(), e, nrng, rng)

// Maybe generalize. The effect is the current effect context and should not be generalized over.
fun maybe-generalize(ctx-range: range, rng: range, expect: expect, f: () -> _ (ktype, keffect, core/core/expr)): _ (scheme, keffect, core/core/expr)
  match expect
    Instantiated -> f()
    Generalized(close) -> generalize(ctx-range, rng, close, f) 

fun maybe-instantiate(rng: range, expect: expect, tp: scheme): _ (rho, core/core/expr -> core/core/expr)
  match expect
    Generalized() -> (tp, id)
    Instantiated -> 
      val (rho, _, coref) = tp.infer-effect/instantiate(rng)
      (rho, coref)

fun maybe-instantiate-or-generalize(ctx-range: range, rng: range, expect: expect, f: () -> _ (ktype, keffect, core/core/expr)): _ (ktype, keffect, core/core/expr)
  match expect
    Generalized(close) -> generalize(ctx-range, rng, close, f)
    Instantiated -> 
      val (tp, eff, core) = f()
      val (itp, _, icore) = tp.infer-effect/instantiate(rng)
      (itp, eff, icore(core))

fun core-vector(cs: list<core/core/expr>, tp: ktype): _ core/core/expr
  val (vecName, _, vecInfo) = resolve-fun-name(nameVector, CtxFunArgs(False, 0, ["xs".new-name], Nothing), null, null) // TODO: lookup vector less fragile?
  val vecx = TypeApp(vecInfo.core-expr(vecName), [tp])
  core/core/App(vecx, [cs.core-list(tp)])

fun core-list(cs: list<core/core/expr>, tp: ktype): _ core/core/expr 
  val (consName, consTp, consRepr, _) = resolve-con-name(nameCons, Nothing, null)
  val (nilName, nilTp, nilRepr, _) = resolve-con-name(nameListNil, Nothing, null)
  val consx = TypeApp(core/core/Con(TName(consName, consTp), consRepr), [tp])
  val nil = TypeApp(core/core/Con(TName(nilName, nilTp), nilRepr), [tp])
  cs.foldr(nil) fn(c, acc)
    core/core/App(consx, [c, acc])