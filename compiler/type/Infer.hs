{--------------------------------------------------------------------------
  Infer Types
--------------------------------------------------------------------------}
inferTypes :: Env -> Maybe RM.RangeMap -> Synonyms -> Newtypes -> Constructors -> ImportMap -> Gamma -> Name -> Bool -> DefGroups Type
                -> Core.CorePhase b (Gamma, Core.DefGroups, Maybe RM.RangeMap )
inferTypes prettyEnv mbRangeMap syns newTypes cons imports gamma0 context allowInfiniteChains defs
  = do uniq0 <- unique
       ((gamma1, coreDefs),uniq1,mbRm) <- Core.liftError $
                                          runInfer prettyEnv mbRangeMap syns newTypes imports gamma0 context allowInfiniteChains
                                            (uniq0 + 10 {- to not clash with at least 10 bound type variables -})
                                            (inferDefGroups True (arrange defs))
       setUnique uniq1
       return (gamma1,coreDefs,mbRm)
  where
    arrange defs
      = if (context /= nameSystemCore)
         then defs
         else -- pull in front certain key definitions that are used in functions generated from constructors (like accessors)
              let (first,rest) = partition isKeyDef defs
              in first ++ rest

    isKeyDef (DefNonRec def)  = defName def `elem` (map unqualify keyDefNames)
    isKeyDef _                = False

    keyDefNames = [{-namePatternMatchError,-}nameRef,nameRefSet,nameDeref]

{--------------------------------------------------------------------------
  Definition groups
--------------------------------------------------------------------------}
inferDefGroups :: Bool -> DefGroups Type -> Inf (Gamma,Core.DefGroups)
inferDefGroups topLevel (defGroup : defGroups)
  = inferDefGroupX topLevel defGroup (inferDefGroups topLevel defGroups)
inferDefGroups topLevel []
  = do gamma <- getGamma
       return (gamma,[])


inferDefGroupX :: HasCallStack => Bool -> DefGroup Type -> Inf (Gamma,Core.DefGroups) -> Inf (Gamma,Core.DefGroups)
inferDefGroupX topLevel defGroup cont
  = do (cgroups0,(g,cgroups1)) <- inferDefGroup topLevel defGroup cont
       zapSubst
       return (g,seqqList cgroups0 ++ cgroups1)

traceCoreDefs :: [Core.Def] -> Inf ()
traceCoreDefs cdefs
  = traceDoc $ \penv -> vcat (map (\cdef -> prettyDef penv{coreShowDef=True} cdef) cdefs)

traceCoreDefGroups :: [Core.DefGroup] -> Inf ()
traceCoreDefGroups cdefgs
  = traceDoc $ \penv -> vcat (map (\cdefg -> prettyDefGroup penv{coreShowDef=True} cdefg) cdefgs)



inferDefGroup :: Bool -> DefGroup Type -> Inf a -> Inf ([Core.DefGroup], a)
inferDefGroup topLevel (DefNonRec def) cont
  = (if topLevel && nameStartsWith (unqualify (defName def)) "wrong" && nameStem (defName def) /= "wrong"
       then ignoreErrors (do{ x <- cont; return ([],x) })
       else id) $
    do core <- inferDef topLevel (Generalized True) def
       mod  <- getModuleName

       (x,core1) <- let cgroup = [Core.DefNonRec core]
                    in if topLevel
                           then let core0 = core{ Core.defName = qualify mod (Core.defName core) }
                                in extendGammaCore False {- already canonical? -} [Core.DefNonRec core0] $
                                    do coreDef <- fixCanonicalName False core0
                                       x <- cont
                                       return (x,coreDef)
                           else do x <- extendInfGammaCore topLevel [Core.DefNonRec core] cont
                                   return (x,core)
       addRangeInfoCoreDef topLevel mod def core1
       let cgroup1 = Core.DefNonRec core1
       return ([cgroup1],x)
inferDefGroup topLevel (DefRec defs0) cont
  = do sd <- getScopeDepth
       (gamma,infgamma,defs) <- createGammas sd [] [] defs0 []
       (coreDefsX,assumed) <- extendGamma False gamma $ extendInfGammaEx topLevel [] infgamma $
                                 do assumed <- mapM (\def -> lookupInfName (getName def)) defs
                                    coreDefs0 <- mapM (\def -> inferDef topLevel Instantiated def) defs
                                    coreDefs1 <- mapM (fixCanonicalName True) coreDefs0
                                    return (coreDefs1,assumed)
       -- re-analyze the mutual recursive groups
       scoreDefsX <- subst coreDefsX
       let coreGroups0 = regroup scoreDefsX
       when topLevel (mapM_ checkRecVal coreGroups0)
       -- now analyze divergence
       (coreGroups1,divTNames)
            <- fmap unzip $
               mapM (\cgroup -> case cgroup of
                                   Core.DefRec cdefs | analyzeDivergence cdefs -> do cdefs' <- addDivergentEffect cdefs
                                                                                     return (Core.DefRec cdefs',map Core.defTName cdefs')
                                   _ -> return (cgroup,[])) $
               coreGroups0
       -- build a mapping from core name to original definition and assumed type
       -- hack: we map from the name range since there may be overloaded names, and the types are not fully determined yet..
       let coreMap = M.fromList (map (\(def,tp) -> (binderName (defBinder def), (def,tp))) (zip defs assumed))
       -- check assumed types agains inferred types
       coreGroups2 <- mapMDefs (\cdef -> inferRecDef2 topLevel cdef ((Core.defTName cdef) `elem` concat divTNames) (M.find (unqualify $ Core.defName cdef) coreMap)) coreGroups1
       -- add range info (for documentation)
       mod <- getModuleName
       mapMDefs_ (\cdef -> addRangeInfoCoreDef topLevel mod (fst (M.find (unqualify $ Core.defName cdef) coreMap)) cdef) coreGroups2
       -- TODO: fix local info in the core; test/algeff/nim.kk with no types for bobTurn and aliceTurn triggers this
       let sub = map (\cdef -> let tname    = Core.defTName cdef
                                   nameInfo = -- trace ("fix local info: " ++ show (Core.defName cdef)) $
                                              createNameInfoX Public (Core.defName cdef) sd (Core.defSort cdef) (Core.defNameRange cdef) (Core.defType cdef) (Core.defDoc cdef)
                                   varInfo  = coreVarInfoFromNameInfo nameInfo
                                   var      = Core.Var tname varInfo
                               in (tname, var)) (Core.flattenDefGroups coreGroups2)
           coreGroups3 = (CoreVar.|~>) sub coreGroups2
       -- extend gamma
       x <- (if topLevel then extendGammaCore True {- already canonical -} else extendInfGammaCore False {-toplevel -}) coreGroups3 cont
       return (seqqList coreGroups3,x)
  where
    -- we use a bit of trickery here:
    -- * things on toplevel with full types get added to the gamma since only the gamma can distinguish
    --   multiple recursive definitions with the same overloaded name
    --   this can only be done on toplevel, or otherwise we may do the scoping wrong with
    --   respect to infgamma
    -- * anything else gets added to infgamma -- this means that in a toplevel recursive
    --   group, some defs end up in infgamma and others in gamma: but at the toplevel that
    --   is ok while infering the types of the recursive group. Eventually, all inferred
    --   types will end up in gamma.
    createGammas :: Int -> [(Name,NameInfo)] -> [(Name,NameInfo)] -> [Def Type] -> [Def Type] -> Inf ([(Name,NameInfo)],[(Name,NameInfo)],[Def Type])
    createGammas scopeDepth gamma infgamma [] acc
      = return (seqqList (reverse gamma), seqqList (reverse infgamma), reverse acc)
    createGammas scopeDepth gamma infgamma (def@(Def binder@(ValueBinder name () expr nameRng vrng) rng vis sort inl doc) : defs) acc
      = case (lookup name infgamma) of
          (Just _)
            -> do env <- getPrettyEnv
                  if topLevel
                   then infError nameRng (text "recursive functions with the same overloaded name must all have a full type signature" <+> parens (ppName env name) <->
                                          text " hint: give a type annotation for each function (including the effect type).")
                   else infError nameRng (text "recursive functions with the same overloaded name cannot be defined as local definitions" <+> parens (ppName env name) <->
                                          text " hint: use different names for each function.")

          Nothing
            -> case expr of
                  Ann _ tp _  | topLevel && tvsIsEmpty (ftv tp)
                    -> do qname <- qualifyName name
                          let nameInfo = createNameInfoX Public qname scopeDepth sort nameRng tp doc -- (not topLevel || isValue) nameRng tp  -- NOTE: Val is fixed later in "FixLocalInfo"
                          -- traceDoc $ \penv -> text "recursive group: assume:" <+> ppParam penv (name,tp)
                          createGammas scopeDepth ((qname,nameInfo):gamma) (seqqList infgamma) defs (def:acc)
                  _ -> case lookup name gamma of
                         Just _
                          -> do env <- getPrettyEnv
                                infError nameRng (text "recursive functions with the same overloaded name must have a full type signature" <+> parens (ppName env name))
                         Nothing
                          -> do qname <- if (topLevel) then qualifyName name else return name
                                case expr of
                                  Ann _ tp _
                                    -> do let info = createNameInfoX Public qname scopeDepth sort nameRng tp doc  -- may be off due to incomplete type: get fixed later in inferRecDef2
                                          createGammas scopeDepth gamma (seqqList ((qname,info):infgamma)) defs (def:acc)
                                  _ -> do info <- case expr of
                                                    Lam pars _ _ _
                                                      -> do tpars <- mapM (\b -> do t <- case binderType b of
                                                                                            Just tp -> return tp
                                                                                            _       -> Op.freshStar
                                                                                    return (binderName b,t)
                                                                          ) pars
                                                            teff  <- Op.freshEffect
                                                            tres  <- Op.freshStar
                                                            let tp = TFun tpars teff tres
                                                            return (createNameInfoX Public qname scopeDepth DefVal nameRng tp doc)
                                                    _ -> do tp <- Op.freshStar
                                                            return (createNameInfoX Public qname scopeDepth DefVal nameRng tp doc)  -- must assume Val for now: get fixed later in inferRecDef2
                                          let def' = def{ defBinder = (defBinder def){ binderExpr = Ann expr (infoType info) (getRange expr) } }
                                          createGammas scopeDepth gamma (seqqList ((qname,info):infgamma)) defs (def':acc)

checkRecVal :: Core.DefGroup -> Inf ()
checkRecVal (Core.DefNonRec def) = return ()
checkRecVal (Core.DefRec defs)
  = mapM_ checkDef defs
  where
    checkDef def
      = if (not (Core.defIsVal def)) then return () else
         do infError (Core.defNameRange def) (text ("value definition is recursive.\n  recursive group: " ++ show (map Core.defName defs)))

fixCanonicalName :: Bool -> Core.Def -> Inf Core.Def
fixCanonicalName isRec def
  = do -- first look in the inf gamma for recursive definitions (since they may not resolve unambiguously)
       mbAssumedType <- if isRec then lookupInfName (Core.defName def) else return Nothing
       case mbAssumedType of
         Just (qname,_)
           -> return (def{ Core.defName = qname })
         _ -> -- failure ("Type.Infer.fixCanonicalName: cannot find in infGamma: " ++ show (Core.defName def))
              -- otherwise, we resolve normally
              do (_,_,info) <- resolveName (Core.defName def) (Just (Core.defType def, Core.defNameRange def)) (Core.defNameRange def) -- should never fail
                 let cname = infoCanonicalName (Core.defName def) info
                 return (def{ Core.defName = cname })




mapMDefs :: Monad m => (Core.Def -> m Core.Def) -> Core.DefGroups -> m Core.DefGroups
mapMDefs f cgroups
  = mapM (\cgroup -> case cgroup of
                       Core.DefRec cdefs   -> do cdefs' <- mapM f cdefs
                                                 return (Core.DefRec (seqqList cdefs'))
                       Core.DefNonRec cdef -> do cdef' <- f cdef
                                                 return (Core.DefNonRec cdef')) (seqqList cgroups)

mapMDefs_ :: Monad m => (Core.Def -> m ()) -> Core.DefGroups -> m ()
mapMDefs_ f cgroups
  = mapM_ (\cgroup -> case cgroup of
                        Core.DefRec cdefs   -> mapM_ f cdefs
                        Core.DefNonRec cdef -> f cdef) cgroups


addRangeInfoCoreDef topLevel mod def coreDef
  = let qname = if (topLevel && not (isQualified (Core.defName coreDef)))
                 then qualify mod (Core.defName coreDef)
                 else Core.defName coreDef
        sort = (if defIsVal def then "val" else "fun")
    in do addRangeInfo (Core.defNameRange coreDef) (RM.Id qname (RM.NIValue sort (Core.defType coreDef) (defDoc def) (True)) [] True)
          addRangeInfo (defRange def) (RM.Decl sort qname (RM.mangle qname (Core.defType coreDef)) (Just (Core.defType coreDef)))


-- | Add divergent effect to the type of the core definitions
-- Should really fully instantiate and eta-expand to insert evidence
-- but for now, we just fix up the types as necessary without evidence insertion
addDivergentEffect :: [Core.Def] -> Inf [Core.Def]
addDivergentEffect coreDefs0
  = mapM addDiv coreDefs0
  where
    addDiv def
      = do let rng = Core.defNameRange def
           (tp0,_,coref) <- instantiateNoEx rng (Core.defType def) -- no effect extension or otherwise div can be added even if the user specified total for example.
           case splitFunType tp0 of
             Nothing
              -> -- failure ( "Type.Infer.addDivergentEffect: unexpected non-function type:\n " ++ show coreDefs0) -- ?? should never happen?
                 -- can happen if a value contains a data structure containing recursive functions that refer to the value
                 return def
             Just (targs,teff,tres)
              -> do tv <- Op.freshEffect
                    let newEff = effectExtend typeDivergent tv
                    inferUnify (checkEffectSubsume rng) rng newEff teff
                    snewEff <- subst newEff
                    let tp1 = TFun targs snewEff tres
                    (resTp,_,resCore) <- generalize rng rng True $
                                         return (TFun targs snewEff tres, typeTotal, coref (Core.defExpr def))
                    inferSubsume (checkEffectSubsume rng) rng (Core.defType def) resTp
                    -- fix up the core since the recursive tname still refers to the old type without the 'div' effect
                    return (def{ Core.defType = resTp, Core.defExpr = resCore })



{--------------------------------------------------------------------------
  Definition
--------------------------------------------------------------------------}


-- TODO: for multiple recursive definitions, the "typeapp" substitution fails; we should
-- collect all substitions and apply them all definitions afterwards; similarly for the
-- VarInfo's that are now done separately
inferRecDef2 :: Bool -> Core.Def -> Bool -> (Def Type,Maybe (Name,Type)) -> Inf (Core.Def)
inferRecDef2 topLevel coreDef divergent (def,mbAssumed)
   = do let rng = defRange def
            nameRng = binderNameRange (defBinder def)
        (resTp0,assumedTp,coref0)
                        <- case mbAssumed of
                            Nothing
                              -> return (Core.defType coreDef, Core.defType coreDef, id)
                            Just (qname,assumed)
                              -> do assumedTp     <- subst assumed
                                    (resTp,coref) <- inferSubsume (checkRec rng) nameRng assumedTp (Core.defType coreDef)
                                    sassumedTp    <- subst assumedTp  -- needed for `type/wrong/scheduler2`
                                    sresTp <- subst resTp
                                    return (sresTp,sassumedTp,coref)
        resTpX <- if topLevel then unskolemize resTp0 else return resTp0
        (resTp1,_,resCore1) <- generalize rng nameRng True $
                                return (resTpX, typeTotal, (coref0 (Core.defExpr coreDef))) -- typeTotal is ok since only functions are recursive (?)
        sassumedTp <- subst assumedTp
        sd <- getScopeDepth
        let name = Core.defName coreDef
            csort = if (topLevel || CoreVar.isTopLevel coreDef) then Core.defSort coreDef else DefVal
            info = coreVarInfoFromNameInfo (createNameInfoX Public name sd csort (defRange def) resTp1 (defDoc def))
        penv <- getPrettyEnv
        (resTp2,coreExpr)
              <- case (resCore1) of
                  Core.TypeLam tvars expr | isRho sassumedTp  -- we assumed a monomorphic type, but generalized eventually
                    -> -- fix it up by adding the polymorphic type application
                       do assumedTpX <- normalize True sassumedTp -- resTp0
                          -- resTpX <- subst resTp0 >>= normalize
                          simexpr <- return expr -- liftUnique $ uniqueSimplify penv False False 1 {-runs-} 0 expr
                          coreX <- subst simexpr
                          (mvars,msub) <- Op.freshSub Bound tvars
                          let resCoreX = (CoreVar.|~>) [(Core.TName ({- unqualify -} name) assumedTpX,
                                                        Core.TypeApp (Core.Var (Core.TName ({- unqualify -} name) (resTp1)) info)
                                                                      (map TVar mvars))] -- TODO: check: was `tvars` TODO: wrong for unannotated polymorphic recursion: see codegen/wrong/rec2
                                          (msub |-> coreX)

                              resCoreY = Core.addTypeLambdas mvars resCoreX
                              -- TODO: check: this was:
                              -- bsub  = subNew (zip mvars (map TVar tvars))
                          return (resTp1,resCoreY)
                        
                  _ | divergent  -- we added a divergent effect, fix up the occurrences of the assumed type
                    -> -- trace "  divergent" $
                       do assumedTpX <- normalize True assumedTp >>= subst -- resTp0
                          simResCore1 <- return resCore1
                          coreX <- subst simResCore1
                          let resCoreX = (CoreVar.|~>) [(Core.TName ({- unqualify -} name) assumedTpX, Core.Var (Core.TName ({- unqualify -} name) resTp1) info)] coreX
                          return (resTp1, resCoreX)
                  _  -- ensure we insert the right info  (test: static/div2-ack)
                    -> do assumedTpX <- normalize True assumedTp >>= subst
                          simResCore1 <- return resCore1 
                          coreX <- subst simResCore1
                          let resCoreX = (CoreVar.|~>) [(Core.TName ({- unqualify -} name) assumedTpX, Core.Var (Core.TName ({- unqualify -} name) resTp1) info)] coreX
                          return (resTp1, resCoreX)
                  

        coreDef2    <- subst (Core.Def (Core.defName coreDef) resTp2 coreExpr (Core.defVis coreDef) csort (Core.defInline coreDef) (Core.defNameRange coreDef) (Core.defDoc coreDef))
        return (coreDef2)



inferDef :: Bool -> Expect -> Def Type -> Inf Core.Def
inferDef topLevel expect (Def (ValueBinder name mbTp expr nameRng vrng) rng vis sort inl doc)
 =do penv <- getPrettyEnv
     if (verbose penv >= 4)
      then Lib.Trace.trace ("infer: " ++ show sort ++ " " ++ show name) $ return ()
      else return ()
     withDefName name $ withScope $ disallowHole $ scopeImplicitConstraints $
      (if (not (isDefFun sort) || nameIsNil name) then id else allowReturn True) $
        do (resTp,eff,resCore)   <- maybeGeneralize rng nameRng expect $
                                    traceIndent $
                                    do (resTp,eff,resCore) <- inferExpr Nothing expect expr
                                       inferUnify (checkValue rng) nameRng typeTotal eff
                                       seff <- subst eff
                                       sresTp <- subst resTp
                                       srecCore <- subst resCore
                                       return (sresTp,seff,srecCore)

                                       -- may not have been generalized due to annotation
           when (verbose penv >= 4) $
            Lib.Trace.trace (show (text (" inferred: " ++ show sort) <+> pretty name <.> text ":" <+> niceType penv{showIds=True} resTp)) $ return ()

           when (isDefFun sort) $
             case splitFunScheme resTp of
               Just (_,_,effTp,resultTp)
                 -> let tp = makeValueOperation effTp resultTp -- pretty prints nicely as `-> eff res`
                    in addRangeInfo (endOfRange vrng {-')'-}) (RM.Id (newName "result") (RM.NIValue "expr" tp "" False) [] True)
               _ -> return ()

           subst (Core.Def name resTp resCore vis sort inl nameRng doc)  -- must 'subst' since the total unification can cause substitution. (see test/type/hr1a)

inferBindDef :: Def Type -> Inf (Type,Effect,Core.Def)
inferBindDef def@(Def (ValueBinder name () expr nameRng vrng) rng vis sort inl doc)
  = withDefName name $ withScope $ disallowHole $ 
    do  (tp,eff,coreExpr) <- traceIndent $ inferExpr Nothing Instantiated expr
        stp <- subst tp
        seff <- subst eff
        -- check for polymorphic values with an effect
        when (not (isRho stp)) $
          inferUnify (checkPolyValue rng) nameRng typeTotal seff
                            --  Just annTp -> inferExpr (Just (annTp,rng)) Instantiated (Ann expr annTp rng)
        coreDef <- if (sort /= DefVar)
                    then return (Core.Def name stp coreExpr vis sort inl nameRng doc)
                    else do hp <- Op.freshTVar kindHeap Meta
                            (qrefName,_,info) <- resolveName nameRef Nothing rng
                            let refTp  = typeApp typeRef [hp,stp]
                                refVar = coreExprFromNameInfo qrefName info
                                refExpr = Core.App (Core.TypeApp refVar [hp,stp]) [coreExpr] -- TODO: fragile: depends on order of quantifiers of the ref function!
                            -- traceDoc $ \penv -> text "reference" <+> pretty name <.> colon <+> ppType penv stp
                            return (Core.Def name refTp refExpr vis sort inl nameRng doc)

        if (not (isWildcard name))
        then let sort = (if defIsVal def then "val" else "fun")
              in addRangeInfo nameRng (RM.Id name (RM.NIValue sort (Core.defType coreDef) doc (isAnnot expr)) [] True)
        else if (isTypeUnit (Core.typeOf coreDef))
          then return ()
          else do let (ls,tl) = extractEffectExtend seff
                  case (ls,tl) of
                    ([],tl) | isTypeTotal tl -> unusedWarning rng
                    ([],TVar tv)
                      -> do occ <- occursInContext tv (ftv stp)
                            if (not occ) then unusedWarning rng else return ()
                            -- return ()
                    _ -> return ()
        return (stp,seff,coreDef)


{--------------------------------------------------------------------------
  Expression
--------------------------------------------------------------------------}

inferIsolated :: Range -> Range -> Expr a -> Inf (Type,Effect,Core.Expr) -> Inf (Type,Effect,Core.Expr)
inferIsolated contextRange range body inf
  = do (tp,eff,core) <- inf
       res@(itp,ieff,coref) <- improve contextRange range True eff tp
       case hasVarDecl body of
         Nothing   -> return (itp,ieff,coref core)
         Just vrng -> do sieff <- subst ieff
                         let (ls,tl) = extractOrderedEffect sieff
                         case filter (\l -> labelName l == nameTpLocal) ls of
                           (_:_) -> typeError contextRange vrng
                                      (text "reference to a local variable escapes its lexical scope") sieff []
                           _ -> return ()
                         return (itp,sieff,coref core)
   where
     hasVarDecl expr
       = case expr of
           Parens x _ _ _ -> hasVarDecl x
           Let _ x _  -> hasVarDecl x
           Bind _ x _ -> hasVarDecl x
           Ann x _ _  -> hasVarDecl x
           Inject _ x _ _ -> hasVarDecl x
           App (Var name _ rng) _ _ | name == nameLocalNew -> Just rng
           _ -> Nothing

-- | @inferExpr propagated expect expr@ takes a potential propagated type, whether the result is expected to be generalized or instantiated,
-- and the expression. It returns its type, effect, and core expression. Note that the resulting type is not necessarily checked that it matches
-- the propagated type: the propagated type is just a hint (used for example to resolve overloaded names).
inferExpr :: HasCallStack => Maybe (Type,Range) -> Expect -> Expr Type -> Inf (Type,Effect,Core.Expr)
inferExpr propagated expect (Lam binders body toplevel rng)
  = inferLam toplevel propagated expect binders body rng

inferExpr propagated expect (Let defgroup body rng)
  = do (cgroups,(tp,eff,core)) <- inferDefGroup False defgroup (inferExpr propagated expect body)
       return (tp,eff,Core.Let cgroups core)

inferExpr propagated expect (Bind def body rng)
  = do (tp1,eff1,coreDef) <- inferBindDef def
       mod  <- getModuleName
       let cgroup = Core.DefNonRec coreDef
       (tp,eff2,coreBody) <- traceIndent $ extendInfGammaCore False [cgroup] $ inferExpr propagated expect body
       inferUnify (checkEffect rng) (getRange rng) eff1 eff2
       topEff <- subst eff2
       stp1 <- subst tp1
       return (tp,topEff,Core.Let [cgroup] coreBody)

-- | Return expressions
inferExpr propagated expect (App (Var name _ nameRng) [(_,expr)] rng)  | name == nameReturn
  = do allowed <- isReturnAllowed
       if (False && not allowed)
        then infError rng (text "illegal expression context for a return statement")
        else  do mbTp <- lookupInfName nameReturn -- (unqualify nameReturn)
                 case mbTp of
                   Nothing
                    -> do infError rng (text "illegal context for a return statement")
                          inferExpr propagated expect expr
                   Just (_,retTp)
                    -> do (tp,eff,core) <- inferExpr (Just (retTp,nameRng)) expect expr
                          inferUnify (checkReturn rng) (getRange expr) retTp tp
                          resTp <- Op.freshStar
                          let typeReturn = typeFun [(nameNil,tp)] typeTotal resTp
                          addRangeInfo nameRng (RM.Id (newName "return") (RM.NIValue "expr" tp "" False) [] False)
                          return (resTp, eff, Core.App (Core.Var (Core.TName nameReturn typeReturn)
                                                (Core.InfoExternal [(Default,"return #1")])) [core])
-- | Assign expression
inferExpr propagated expect (App assign@(Var name _ arng) [lhs@(_,lval),rhs@(_,rexpr)] rng) | name == nameAssign
  = case lval of
      App fun args lrng  -- array[i] := e
          -> do xargs <- case args of
                          ((mbName,arg@(Var target _ vrng)) : rest)  -- var_vec[i] := e   TODO: perhaps unsafe for general use?
                            -> do (_,gtp,_) <- resolveName target Nothing vrng
                                  (tp,_,_) <- instantiate vrng gtp
                                  -- traceDoc $ \penv -> text "setting:" <+> pretty target <+> text ":" <+> ppType penv tp
                                  if (isTypeLocalVar tp)
                                   then return ((mbName,App (Var nameByref False vrng) [(Nothing, arg)] lrng) : rest)
                                   else return args
                          _ -> return args
                inferExpr propagated expect (App fun (xargs ++ [(Nothing,rexpr)]) rng)
      Var target _ lrng
        -> do (_,gtp,_) <- resolveName target Nothing lrng
              (tp,_,_) <- instantiateEx lrng gtp
              nameSet <- if (isTypeLocalVar tp)
                           then return nameLocalSet
                           else do r <- freshRefType
                                   inferUnify (checkAssign rng) lrng r tp
                                   return nameRefSet
              inferExpr propagated expect
                        (App (Var nameSet False arng) [(Nothing,App (Var nameByref False (before lrng)) [lhs] lrng), rhs] rng)

      _ -> errorAssignable
  where
    errorAssignable
      = do contextError rng (getRange lval) (text "not an assignable expression") [(text "because",text "an assignable expression must be an application, index expression, or variable")]
           return (typeUnit,typeTotal,Core.Con (Core.TName (nameTuple 0) typeUnit) (Core.ConEnum nameTpUnit Core.DataEnum valueReprZero 0))

    checkAssign
      = Check "an assignable identifier must have a reference type"

    freshRefType
      = do hvar <- Op.freshTVar kindHeap Meta
           xvar <- Op.freshStar
           return (typeApp typeRef [hvar,xvar])

-- | applied handlers are treated specially by allowing automatic masking of local effects
inferExpr propagated expect (App (h@Handler{hndlrAllowMask=Nothing}) [action] rng)
  = do lvars <- getLocalVars
       let allow = not (usesLocals (S.fromList (map fst lvars)) (snd action))
       inferExpr propagated expect (App h{hndlrAllowMask=Just allow} [action] rng)

-- | Byref expressions
inferExpr propagated expect (App (Var byref _ _) [(_,Var name _ rng)] _)  | byref == nameByref
  = inferVar propagated expect name rng False

-- | Hole expressions
inferExpr propagated expect (App fun@(Var hname _ nameRng) [] rng)  | hname == nameCCtxHoleCreate
  = do ok <- useHole
       when (not ok) $
         contextError rng rng (text "ill-formed constructor context")
            [(text "because",text "there can be only one hole, and it must occur under a constructor context 'ctx'")]
       (tp,eff,core) <- inferApp propagated expect fun [] rng
       addRangeInfo nameRng (RM.Id (newName "hole") (RM.NIValue "expr" tp "" False) [] False)
       return (tp,eff,core)

-- | Context expressions
inferExpr propagated expect (App (Var ctxname _ nameRng) [(_,expr)] rng)  | ctxname == nameCCtxCreate
  = do tpv <- Op.freshStar
       holetp <- Op.freshStar
       let ctxTp = TApp typeCCtxx [tpv,holetp]
       prop <- case propagated of
                 Nothing -> return Nothing
                 Just (ctp,crng) -> do inferUnify (checkMatch crng) nameRng ctp ctxTp
                                       stp <- subst tpv
                                       return (Just (stp,rng))
       ((tp,eff,core),hole) <- allowHole $ inferExpr prop Instantiated expr
       inferUnify (Infer rng) nameRng tp tpv
       when (not hole) $
          do penv <- getPrettyEnv
             contextError rng rng (text "ill-formed constructor context") [(text "because",text "the context has no hole"),(text "hint",text "perhaps you used an underscore instead of the" <+> dquotes (keyword penv "hole") <+> text "keyword?")]
       newtypes <- getNewtypes
       score <- subst core
       (ccore,errs) <- withUnique (analyzeCCtx rng newtypes score)
       mapM_ (\(rng,err) -> infError rng err) errs
       let ctp = Core.typeOf ccore
       addRangeInfo nameRng (RM.Id (newName "ctx") (RM.NIValue "expr" ctp "" False) [] False)
       return (Core.typeOf ccore,eff,ccore)

-- | Application nodes. Inference is complicated here since we need to disambiguate overloaded identifiers.
inferExpr propagated expect (App fun nargs rng)
  = inferApp propagated expect fun nargs rng

inferExpr propagated expect (Ann expr annTp0 rng)
  = do -- match with propagated type first
       annTp <- case propagated of
                  Just (propAnn,propRng) -> do inferUnify (checkAnn propRng) rng propAnn annTp0
                                               subst annTp0
                  Nothing -> return annTp0
       
       (tp,eff,core) <- inferExpr (Just (annTp,rangeHide rng)) (if isRho annTp then Instantiated else Generalized False) expr
       sannTp <- subst annTp
       stp    <- subst tp
       seff   <- subst eff
       (resTp0,coref) <- -- withGammaType rng sannTp $
                         inferSubsume (checkAnn rng) (getRange expr) sannTp stp
       let resCore1 = coref core
           resTp1   = resTp0
       resTp  <- subst resTp1
       resEff <- subst eff
       resCore <- subst resCore1
       return (resTp,resEff,resCore)


inferExpr propagated expect (Handler handlerSort scoped HandlerNoOverride mbAllowMask mbEff pars reinit ret final branches hrng rng)
  = let allowMask = case mbAllowMask of
                      Just True -> True
                      _         -> False
    in inferHandler propagated expect handlerSort scoped allowMask mbEff pars reinit ret final branches hrng rng
inferExpr propagated expect (Handler handlerSort scoped HandlerOverride mbAllowMask mbEff pars reinit ret final branches hrng rng)
  = do heff <- inferHandledEffect hrng handlerSort mbEff branches
       let h = (Handler handlerSort scoped HandlerNoOverride mbAllowMask mbEff pars reinit ret final branches hrng rng)
           actionName = newHiddenName "override-action"
           actionVar  = Var actionName False rng
           actionBind = ValueBinder actionName Nothing Nothing rng rng
           mask   = if (isHandlerInstance handlerSort)
                      then let instName = newHiddenName "override-inst"
                               instBind = ValueBinder instName Nothing Nothing rng rng
                               instVar  = Var instName False rng
                               instLam  = Lam [] (App actionVar [(Nothing,instVar)] rng) False rng
                           in Lam [instBind] (Inject heff instLam True rng) False rng  -- mask behind
                      else Lam [] (Inject heff actionVar True rng) False rng  -- mask behind
           lam    = Lam [actionBind] (App h [(Nothing,mask)] rng) False rng
       inferExpr propagated expect lam

inferExpr propagated expect (Case expr branches isLazyMatch rng)
  = inferCase propagated expect expr branches isLazyMatch rng

inferExpr propagated expect (Var name isOp rng)
  = inferVar propagated expect name rng True

inferExpr propagated expect (Lit lit)
  = do let (tp,core,rng,docs) =
              case lit of
                LitInt i r  -> (typeInt,Core.Lit (Core.LitInt i),r,
                                   ["dec  = " ++ show i] ++
                                    if i < toInteger (minBound :: Int) || i > toInteger (maxBound :: Int)
                                      then []
                                      else let x0 = (fromInteger i) :: Int
                                               x  = if x0 >= 0 then x0
                                                      else if x0 >= -0x80 then 0x100 + x0
                                                      else if x0 >= -0x8000 then 0x10000 + x0
                                                      else if x0 >= -0x80000000 then 0x100000000 + x0
                                                      else fromInteger (0x10000000000000000 + i)
                                           in if (x < 0) then []
                                                else if (x <= 0x7F || (i < 0 && x <= 0xFF))
                                                  then ["hex8 = 0x" ++ showHex 2 x,"bit8 = 0b" ++ showBinary 8 x]
                                                  else if (x <= 0x7FFF || (i < 0 && x <= 0xFFFF))
                                                    then ["hex16= 0x" ++ showHex 4 x,"bit16= 0b" ++ showBinary 16 x]
                                                    else if (x <= 0x7FFFFFFF || (i < 0 && x <= 0xFFFFFFFF))
                                                      then ["hex32= 0x" ++ showHex 8 x, "bit32= 0b" ++ showBinary 32 x]
                                                      else ["hex64= 0x" ++ showHex 16 x, "bit64= 0b" ++ showBinary 64 x]
                                )
                LitChar c r  -> (typeChar,Core.Lit (Core.LitChar c),r,
                                     let i = fromEnum c
                                     in ["unicode= " ++
                                          if (i < 0 || i > 0xFFFFF)
                                            then show i ++ " (out of range)"
                                            else if i <= 0xFFFF
                                                   then "u" ++ showHex 4 i
                                                   else "U" ++ showHex 6 i]
                                 )
                LitFloat f r  -> (typeFloat,Core.Lit (Core.LitFloat f),r,
                                     ["hex64= " ++ showHexFloat f])
                LitString s r  -> (typeString,Core.Lit (Core.LitString s),r,
                                     ["count= " ++ show (length s)])
       addRangeInfo rng (RM.Id (newName "literal") (RM.NIValue "expr" tp "" False) (map text docs) False)
       eff <- Op.freshEffect
       return (tp,eff,core)


inferExpr propagated expect (Parens expr name pre rng)
  = do (tp,eff,core) <- inferExpr propagated expect expr
       if (name /= nameNil)
         then do addRangeInfo rng (RM.Id name (RM.NIValue (if null pre then "expr" else pre) tp "" False) [] False)
         else return ()
       return (tp,eff,core)

inferExpr propagated expect (Inject label expr behind rng)
  = do eff0 <- Op.freshEffect
       let eff = if (not behind) then eff0 else (effectExtend label eff0)

       let tfun r = typeFun [] eff r
           prop = case propagated of
                    Nothing  -> Nothing
                    Just (ptp,prng) -> case splitTypeScheme ptp of
                                        (foralls,rho)
                                          -> Just (quantifyType foralls $ tfun rho, prng)

       (mbHandled,effName) <- effectNameCore label rng
       (exprTp,exprEff,exprCore) <- (if effName == nameTpLocal then withNoLocalScope else id) $
                                    inferExpr prop Instantiated expr

       res <- Op.freshStar
       let fullRng = combineRanges [rng,getRange expr]
       inferUnify (checkInject fullRng) (getRange expr) (tfun res) exprTp
       inferUnify (checkInject fullRng) (getRange expr) eff exprEff
       resTp <- subst res

       effTo <- subst $ effectExtend label eff

       sexprTp <- subst exprTp
       let coreLevel  = if behind then Core.exprTrue else Core.exprFalse -- Core.Lit (Core.LitInt (if behind then 1 else 0))
       core <- case mbHandled of
                 -- general handled effects use "@inject-effect"
                 Just coreHTag
                   -> do (maskQName,maskTp,maskInfo) <- resolveFunName nameMaskAt (CtxFunArgs False 3 [] Nothing) rng rng
                         (evvIndexQName,evvIndexTp,evvIndexInfo) <- resolveFunName nameEvvIndex (CtxFunArgs False 1 [] Nothing) rng rng
                         let coreMask = coreExprFromNameInfo maskQName maskInfo
                             coreIndex= Core.App (Core.TypeApp (coreExprFromNameInfo evvIndexQName evvIndexInfo) [effTo])
                                                 [coreHTag]
                             core     = Core.App (Core.TypeApp coreMask [resTp,eff,effTo]) [coreIndex,coreLevel,exprCore]
                         return core
                 Nothing
                   -> do (maskQName,maskTp,maskInfo) <- resolveFunName nameMaskBuiltin (CtxFunArgs False 1 [] Nothing) rng rng
                         let coreMask = coreExprFromNameInfo maskQName maskInfo
                             core     = Core.App (Core.TypeApp coreMask [resTp,eff,effTo]) [exprCore]
                         return core
       return (resTp,effTo,core)


inferCheckedExpr expectTp expr
  = do (_,_,core) <- inferExpr Nothing Instantiated (Ann expr expectTp (getRange expr))
       return core

inferUnifyTypes contextF [] = matchFailure "Type.Infer.inferinferUnifyTypes"
inferUnifyTypes contextF [(tp,_)]  = subst tp
inferUnifyTypes contextF ((tp1,r):(tp2,(ctx2,rng2)):tps)
  = do inferUnify (contextF ctx2) rng2 tp1 tp2
       inferUnifyTypes contextF ((tp1,r):tps)


{--------------------------------------------------------------------------
  infer effect handlers
--------------------------------------------------------------------------}

inferHandler :: Maybe (Type,Range) -> Expect -> HandlerSort -> HandlerScope -> Bool
                      -> Maybe Effect
                      -> [ValueBinder (Maybe Type) ()] -> Maybe (Expr Type) -> Maybe (Expr Type) -> Maybe (Expr Type)
                      -> [HandlerBranch Type] -> Range -> Range -> Inf (Type,Effect,Core.Expr)

-- Regular handler
inferHandler propagated expect handlerSort handlerScoped allowMask
             mbEffect (_:localPars) initially ret finally branches hrng rng
  = do contextError hrng rng (text "Type.Infer.inferHandler: TODO: not supporting local parameters") []
       failure "abort"
inferHandler propagated expect handlerSort handlerScoped allowMask
             mbEffect [] initially ret finally branches hrng rng
  = do -- get the handled effect
       heff <- inferHandledEffect hrng handlerSort mbEffect branches
       let isInstance = isHandlerInstance handlerSort
           effectName = effectNameFromLabel heff
           handlerConName = toHandlerConName effectName
       -- check operations
       checkCoverage rng heff handlerConName branches

       -- infer the result type to improve inference
       res  <- case (propagated,ret) of
                (Nothing,Just expr) -> do (tp,_,_) <- inferExpr propagated Instantiated expr
                                          case splitFunScheme tp of
                                            Just (_,_,_,retTp) -> return retTp
                                            _ -> Op.freshStar
                (Just (retTp,_),_) -> return retTp
                _ -> Op.freshStar
       eff  <- Op.freshEffect
       resumeArgs <- mapM (\_ -> Op.freshStar) branches  -- TODO: get operation result types to improve inference

       -- construct the handler
       let -- create expressions for each clause
           opName b1 b2 = compare (show (unqualify (hbranchName b1))) (show (unqualify (hbranchName b2)))
           clause (HandlerBranch opName pars body opSort nameRng patRng, resumeArg)
            = withScope $
              do (clauseName, cparams, prefix) <- case opSort of
                          OpVal        -> return (nameClause "tail" (length pars), pars, "val")
                          OpFun        -> return (nameClause "tail" (length pars), pars, "fun")
                          OpExcept     -> return (nameClause "never" (length pars), pars, "final ctl")
                          -- don't optimize ctl to exc since exc runs the finalizers before the clause (unlike ctl)
                          -- OpControl    | not (hasFreeVar body (newName "resume"))
                          --             -> (nameClause "never" (length pars), pars)  -- except
                          OpControl    -> do let resumeTp = TFun [(nameNil,resumeArg)] eff res
                                                 resumeDoc shorten = if shorten then text "resume" else empty
                                             addRangeInfo nameRng (RM.Implicits resumeDoc)
                                             return (nameClause "control" (length pars),
                                                     pars ++ [ValueBinder (newName "resume") (Just resumeTp) () (rangeHide nameRng) nameRng],
                                                     "ctl")
                          OpControlRaw -> do let eff0 = effectExtend heff eff
                                                 resumeContextTp = typeResumeContext resumeArg eff eff0 res
                                                 resumeDoc shorten = if shorten then text "rcontext" else empty
                                             addRangeInfo nameRng (RM.Implicits resumeDoc)
                                             return (nameClause "control-raw" (length pars),
                                                     pars ++ [ValueBinder (newName "rcontext") (Just resumeContextTp) () (rangeHide hrng) patRng],
                                                     "raw ctl")
                          OpControlErr -> failure "Type.Infer.inferHandler: using a bare operation is deprecated.\n  hint: start with 'val', 'fun', 'brk', or 'ctl' instead."
                          -- _            -> failure $ "Type.Infer.inferHandler: unexpected resume kind: " ++ show rkind

                 let qopname = if isQualified opName then opName else qualify (qualifier effectName) opName
                 (_,gtp,_) <- resolveFunName qopname (CtxFunArgs False (length pars + (if isInstance then 1 else 0)) [] Nothing) patRng nameRng -- todo: resolve more specific with known types?
                 (tp,_,_)  <- instantiateEx nameRng gtp
                 let parTps = case splitFunType tp of
                                Just (tpars,_,_) -> (if (isInstance) then tail else id) $ -- drop the first parameter of an op for an instance (as it is the instance name)
                                                    map (Just . snd) tpars ++ repeat Nothing  -- TODO: propagate result type as well?
                                _ -> failure $ "Type.Infer.inferHandler: bad operation type: " ++ show opName ++ ": " ++ show (pretty gtp)
                     cparamsx = map (\(b,mbtp) -> case b of
                                                    ValueBinder name Nothing _ nameRng rng -> ValueBinder name mbtp Nothing nameRng rng
                                                    ValueBinder name annTp _ nameRng rng   -> ValueBinder name annTp Nothing nameRng rng)
                                $ zip (cparams :: [ValueBinder (Maybe Type) ()]) (parTps)
                     frng = combineRanged nameRng body
                     cname = case opSort of
                               OpVal -> fromValueOperationsName opName
                               _     -> opName
                     capp  = App (Var clauseName False (rangeHide hrng))
                                 [(Nothing,Parens (Lam cparamsx body False (getRange body)) cname prefix nameRng)] frng
                 -- addRangeInfo nameRng (RM.Id cname (RM.NIValue "fun" gtp "" False) [] False)
                 return (Nothing, capp)

       clauses <- mapM clause (zip (sortBy opName branches) resumeArgs)

       let grng = rangeNull
       let handlerCon = let hcon = Var handlerConName False hrng
                        in App hcon ([(Nothing,Lit (LitInt handlerCfc grng))] ++ clauses) rng
           handlerCfc = -- (\i -> App (Var nameInternalInt32 False grng) [(Nothing,Lit (LitInt i grng))] grng) $
                        if (null branches) then 1 --linear
                                           else foldr1 cfcLub (map hbranchCfc branches)
                      where
                        cfcLub x y   = if ((x==0&&y==1)||(x==1&&y==0)) then 2 else max x y
                        hbranchCfc b = case hbranchSort b of -- todo: more refined analysis
                                        OpVal    -> 1
                                        OpFun    -> 1
                                        OpExcept -> 0
                                        _        -> 3 --multi/wild
           -- create handler expression
           actionName = newHiddenName "action"
           handleName = toHandleName effectName
           handleRet  = case ret of -- todo: optimize return by using maybe<a->b> value in case no clause was given?
                          Nothing -> let argName = (newHiddenName "res")
                                     in Lam [ValueBinder argName Nothing Nothing rng rng] (Var argName False rng) False hrng -- don't pass `id` as it needs to be opened
                          Just expr -> expr
           handleExpr action = App (Var handleName False rng)
                                [{-(Nothing,handlerCfc),-}(Nothing,handlerCon),(Nothing,handleRet),(Nothing,action)] hrng



       -- extract the action type for the case where it is higher-ranked (for scoped effects)
       -- this way we can annotate the action parameter with a higher-rank type if needed
       -- so it is propagated automatically.
       penv <- getPrettyEnv
       (_,handleTp,_)  <- resolveFunName handleName CtxNone rng rng
       (handleRho,_,_) <- instantiateEx rng handleTp
       actionTp <- case splitFunType handleRho of
                        Just ([_,_,actionTp],_,_)
                          -> subst (snd actionTp)
                        _ -> failure ("Type.Infer: unexpected handler type: " ++ show (ppType penv handleRho))
       let handlerExpr = Parens (Lam [ValueBinder actionName (Just actionTp) Nothing rng rng]
                                     (handleExpr (Var actionName False rng)) False hrng) (newName "handler") "expr" rng

       -- and check the handle expression
       hres@(xhtp,_,_) <- inferExpr propagated expect handlerExpr
       htp <- subst xhtp

       -- extract handler effect
       let (actionTp1,heffect) = case splitFunScheme(htp) of
                        Just (_,[arg],heff,hresTp) -> (snd arg,heff)
                        _ -> failure $ "Type.Infer.inferHandler: unexpected handler type: " ++ show (ppType penv htp)

       if (not (labelIsLinear heff))
        then return ()
        else checkLinearity effectName heffect branches hrng rng

       -- insert a mask<local> over the action?
       if True -- (not (containsLocalEffect heffect) || not allowMask)
         then return hres
         else do
                 hp <- Op.freshTVar kindHeap Meta
                 let actionTp2  = removeLocalEffect penv actionTp1
                     handlerExprMask
                        = if isInstance
                           then let instName   = newHiddenName "hname"
                                in Lam [ValueBinder actionName (Just actionTp2) Nothing rng rng]
                                    (handleExpr (Lam [ValueBinder instName Nothing Nothing rng rng]
                                                   (Inject (TApp typeLocal [hp])
                                                      (Lam [] (App (Var actionName False rng) [(Nothing,Var instName False rng)] rng) False rng)
                                                      False hrng) False hrng)) False hrng
                           else Lam [ValueBinder actionName (Just actionTp2) Nothing rng rng]
                                  (handleExpr (Lam [] (Inject (TApp typeLocal [hp]) (Var actionName False rng) False hrng) False hrng)) False hrng
                 inferExpr propagated expect handlerExprMask  -- and re-infer :-)

checkLinearity effectName heffect branches hrng rng
  = do checkLinearClauses
       checkLinearEffect
  where
    checkLinearClauses
      = mapM_ check branches
      where
        check hbranch
          = if (hbranchSort hbranch <= OpFun) then return ()
             else do penv <- getPrettyEnv
                     contextError rng (hbranchPatRange hbranch)
                        (text "operation" <+> ppName penv (hbranchName hbranch) <+>
                         text ("needs to be linear but is handled in a non-linear way (as '" ++ show (hbranchSort hbranch) ++ "')"))
                        [(text "hint",text "use a 'val' or 'fun' operation clause instead")]

    checkLinearEffect
      = do let (effs,tl) = extractEffectExtend heffect
           --traceDoc $ \env -> text "operation" <+> text (show opName) <+> text ": " <+> niceType env effBranch -- hsep (map (\tp -> niceType env tp) effs)
           case (dropWhile labelIsLinear effs) of
             (e:_) -> do penv <- getPrettyEnv
                         contextError rng hrng
                            (text "handler for" <+> (ppName penv effectName) <+>
                             text "needs to be linear but uses a non-linear effect:" <+> ppType penv e)
                            [(text "hint",text "ensure only linear effects are used in a handler")]
             [] -> return ()



-- Infer the handled effect from looking at the operation clauses
inferHandledEffect :: Range -> HandlerSort -> Maybe Effect -> [HandlerBranch Type] -> Inf (Effect)
inferHandledEffect rng handlerSort mbeff ops
  = case mbeff of
      Just eff -> return (eff)
      Nothing  -> case ops of
        (HandlerBranch name pars expr opSort nameRng rng: _)
          -> -- todo: handle errors if we find a non-operator
             do let isInstance = isHandlerInstance handlerSort
                env <- getPrettyEnv
                (qname,tp,info) <- resolveFunName name (CtxFunArgs False (length pars + (if isInstance then 1 else 0)) [] Nothing) rng nameRng
                (rho,_,_) <- instantiateEx nameRng tp
                case splitFunType rho of
                  Just((opname,rtp):_,_,_) | isHandlerInstance handlerSort && opname == newHiddenName "hname"
                                -> case rtp of
                                        TApp (TCon ev) [teff]  | typeConName ev == nameTpEv
                                           -> do dataInfo <- findDataInfo (getTypeName teff)
                                                 let effLabel = wrapHandledFromDataEffect (dataInfoEffect dataInfo) teff
                                                 return effLabel
                                        _  -> failure "Type.Infer.inferHandledEffect: illegal named effect type in operation?"
                  Just(_,eff,_) | not (isHandlerInstance handlerSort)
                                -> case extractEffectExtend eff of
                                    (ls,_) ->
                                      case filter isHandledEffect ls of
                                        (l:_) -> return (l)  -- TODO: can we assume the effect comes first?
                                        _ -> -- failure $ "Type.Infer.inferHandledEffect: cannot find handled effect in " ++ show eff
                                             infError rng (text "not an effect operation:" <+> ppName env qname <.> text ".")
                  _ -> infError rng (text "cannot resolve effect operation:" <+> ppName env qname <.> text "." <--> text " hint: maybe wrong number of parameters?")
        _ -> infError rng (text "unable to determine the handled effect." <--> text " hint: use a `handler<eff>` declaration?")


-- Check coverage is not needed for type inference but gives nicer error messages
checkCoverage :: Range -> Effect -> Name -> [HandlerBranch Type] -> Inf ()
checkCoverage rng effect handlerConName branches
  = do (_,gconTp,conRepr,conInfo) <- resolveConName handlerConName Nothing rng
       let opNames = map (fieldToOpName . fst) (drop 1 {-cfc-} (conInfoParams conInfo))
           branchNames = map branchToOpName branches
       checkCoverageOf rng (map fst opNames) opNames branchNames
       return ()
  where
    modName = qualifier handlerConName

    fieldToOpName fname
      = let (pre,post)      = span (/='-') (nameLocal fname)
            (opSort,opName) = case (readOperationSort (drop 1 pre),post) of
                                (Just opSort, _:opName) | take 1 pre == "@" -> (opSort,opName)
                                _ -> failure $ "Type.Infer.checkCoverage: illegal operation field name: " ++ show fname ++ " in " ++ show handlerConName
        in (qualify modName (newQualified (nameModule fname) opName), opSort)

    branchToOpName hbranch
      = (qualify modName $ unqualify $
         if (isValueOperationName (hbranchName hbranch))     -- .val-<op>
          then fromValueOperationsName (hbranchName hbranch) else hbranchName hbranch,
         hbranchSort hbranch)

    checkCoverageOf :: Range -> [Name] -> [(Name,OperationSort)] -> [(Name,OperationSort)] -> Inf ()
    checkCoverageOf rng allOpNames opNames branchNames
      = do env <- getPrettyEnv
           case opNames of
            [] -> if null branchNames
                   then return ()
                   -- should not occur if branches typechecked previously
                   else case (filter (\(bname,bsort) -> not (bname `elem` allOpNames)) branchNames) of
                          ((bname,bsort):_) -> termError rng (text "operator" <+> ppOpName env bname <+>
                                                     text "is not part of the handled effect") effect
                                                      [] -- hints
                          _        -> infError rng (text "some operators are handled multiple times for effect " <+> ppType env effect)
            ((opName,opSort):opNames')
              -> do let (matches,branchNames') = partition (\(bname,_) -> bname==opName) branchNames
                    case matches of
                      [(bname,bsort)]
                          -> if (opSort==OpVal && bsort /= opSort)
                              then infError rng (text "cannot handle a 'val' operation" <+> ppOpName env opName <+> text "with" <+> squotes (text (show bsort)))
                             else if (bsort > opSort)
                              then infWarning rng (text "operation" <+> ppOpName env opName <+> text "is declared as '" <.> text (show opSort) <.> text "' but handled here using '" <.> text (show bsort) <.> text "'")
                              else return ()
                      []  -> infError rng (text "operator" <+> ppOpName env opName <+> text "is not handled")
                      _   -> infError rng (text "operator" <+> ppOpName env opName <+> text "is handled multiple times")
                    checkCoverageOf rng allOpNames opNames' branchNames'
      where
        ppOpName env cname
          = ppName env cname

{--------------------------------------------------------------------------
  infer applications and resolve overloaded identifiers
--------------------------------------------------------------------------}

inferApp :: Maybe (Type,Range) -> Expect -> Expr Type -> [(Maybe (Name,Range),Expr Type)] -> Range -> Inf (Type,Effect,Core.Expr)
inferApp propagated expect fun nargs rng
  = do (fixed,named) <- splitNamedArgs nargs
       amb <- case rootExpr fun of
                (Var name _ nameRange)
                  -> do let sctx = fixedCountContext propagated (length fixed) (map (fst . fst) named)
                        matches <- lookupAppName False name sctx rng nameRange
                        -- traceDefDoc $ \env -> text "matched for: " <+> ppName env name <+> text " = " <+> pretty (length matches)
                        case matches of
                          Right (tp,funExpr,implicits)
                              -> return (Just (Just (tp,rng), funExpr, implicits)) -- known type, propagate the function type into the parameters
                          _   -> return Nothing -- many matches, -- start with argument inference and try to resolve the function type
                                 -- note: lookupAppName never unifies type variables so we should not emit errors on `Left []`.
                                 -- for example, in `fn(f) f()` the `f` has a type `_a` and will not match `sctx`.
                _ -> return (Just (Nothing,fun,[])) -- function expression first
       case amb of
         Just (prop,funExpr,implicits)
                  -> inferAppFunFirst prop funExpr [] fixed named implicits
         Nothing  -> inferAppFromArgs fixed named

  where
    -- infer the function type first, and propagate it to the arguments
    -- can take an `fresolved` list of fixed arguments that have been inferred already (in the case
    -- where a overloaded function name could only be resolved after inferring some arguments)
    inferAppFunFirst :: Maybe (Type,Range) -> Expr Type -> [(Int,FixedArg)] ->
                          [Expr Type] -> [((Name,Range),Expr Type)] -> [((Name,Range), Expr Type, (Bool -> Doc))] ->
                            Inf (Type,Effect,Core.Expr)
    inferAppFunFirst prop funExpr fresolved fixed0 named0 implicits0
      = maybeInstantiateOrGeneralize rng (getRange fun) expect $
        do
           -- infer type of function
           fprop <- case (prop,funExpr) of
                      (Nothing,Var name _ _) | not (isConstructorName name)
                        -> do (_,ptp,info) <- resolveName name prop rng
                              case (ptp,infoAllowImplictMask info) of
                                (TVar{},True) -> do teff <- Op.freshEffect  -- we propagate a function type (for example to mask<local> for function parameters)
                                                    tres <- Op.freshStar
                                                    tpars <- mapM (\_ -> Op.freshStar) [1..(length fixed0 + length named0 + length implicits0)]
                                                    let ftp = TFun [(nameNil,tpar) | tpar <- tpars] teff tres
                                                    return (Just (ftp, rng))
                                _ -> return prop
                      _ -> return prop
           (ftp,eff1,fcore) <- allowReturn False $ inferExpr fprop Instantiated funExpr

           -- we allow passing implicit parameters as a fixed argument: here we name those explicitly based on the type
           -- todo: for now disallow implicit parameters as fixed ones as it can lead to long inference times?
           let allowImplicitsAsFixed = True
           (fixed,named1) <- case splitFunType ftp of
                              Just (pars,_,_) | allowImplicitsAsFixed
                                  -> let (tfixed,toptionals,timplicits) = Op.splitOptionalImplicit pars
                                         (fixed1,fixedImplicitArgs) = splitAt (length tfixed + length toptionals) fixed0
                                     in if null fixedImplicitArgs || length fixedImplicitArgs > length timplicits -- too many arguments?; see `test/static/wrong/rec1`
                                          then return (fixed0,named0)
                                          else do let fixedImplicits = zipWith (\(name,tp) expr -> ((name,getRange expr),expr))
                                                                        timplicits fixedImplicitArgs
                                                  return (fixed1, fixedImplicits ++ named0)
                              _  -> return (fixed0,named0)
           -- only add resolved implicits that were not already named
           let alreadyGiven = [name | ((name,_),_) <- named1]
               rimplicits   = [imp | imp@((name,_),_,_) <- implicits0, not (name `elem` alreadyGiven)]
               named        = named1 ++ [((name,rangeNull) {-so no range info is emmitted when checking -}
                                          , expr) | ((name,_),expr,_) <- rimplicits]

           mapM_ (\((name,_),_,fdoc) -> addRangeInfo (getRange funExpr) (RM.Implicits fdoc)) rimplicits

           -- match the type with a function type, wrap optional arguments, and order named arguments.
           -- traceDefDoc $ \env -> text "infer-fun-first, tp:" <+> ppType env ftp
           (iargs,pars0,funEff0,funTp0,coreApp) <- matchFunTypeArgs rng funExpr ftp fresolved fixed named

           -- match propagated type with the function result type
           -- note: we may disable this in the future?
           (pars,funEff,funTp) <- case propagated of
              Just (propRes,propRng) -> do inferSubsume (checkAnn propRng) rng funTp0 propRes
                                           pars1   <- subst pars0
                                           funEff1 <- subst funEff0
                                           funTp1  <- subst funTp0
                                           return (pars1,funEff1,funTp1)
              _ -> return (pars0,funEff0,funTp0)

           -- infer the argument expressions and subsume the type
           sftp <- subst ftp
           unused <- Core.freshName "unused"
           sd <- getScopeDepth
           (effArgs,coreArgs) <- -- withGammaType rng (TFun pars funEff funTp) $ -- ensure the free 'some' types are free in gamma
                                 (extendInfGamma [(unused,InfoVal Public unused sftp sd rng False False "")]) $ -- don't generalize over free propagated types
                                 do free <- freeInGamma
                                    -- traceDefDoc $ \penv -> text "propagate:" <+> ppType penv sftp <.> comma <+> ppTvs penv free
                                    let parArgs = zip (map snd pars) (map snd iargs)
                                    res <- case (fun) of
                                            (Var name _ _) | name == nameRunLocal
                                              -> withLocalScope $
                                                 inferArgsN (checkLocalScope rng) rng parArgs
                                            _ -> inferArgsN (Infer rng) rng parArgs
                                    free1 <- freeInGamma
                                    sftp1 <- subst sftp
                                    -- traceDefDoc $ \penv -> text "done propagate:" <+> ppType penv sftp1 <.> comma <+> ppTvs penv free1
                                    return res

           -- ensure arguments are evaluated in the declaration order
           core <- case shortCircuit fcore coreArgs of
                    Just cexpr -> return cexpr
                    Nothing ->
                      -- ensure named arguments are evaluated in the correct order
                      if (monotonic (map fst iargs) || all Core.isTotal coreArgs)
                        then return (coreApp fcore coreArgs)
                        else do -- let bind in evaluation order
                                vars <- mapM (\_ -> uniqueName "arg") iargs
                                let vargs = zip vars [(i,carg) | (carg,(i,_)) <- zip coreArgs iargs]
                                    eargs = sortBy (\(_,(i,_)) (_,(j,_)) -> compare i j) vargs
                                    defs  = [Core.DefNonRec (Core.Def var (Core.typeOf arg) arg Core.Private DefVal InlineAuto rangeNull "") | (var,(_,arg)) <- eargs]
                                    cargs = [Core.Var (Core.TName var (Core.typeOf arg)) Core.InfoNone | (var,(_,arg)) <- vargs]
                                if (Core.isTotal fcore)
                                then return (Core.makeLet defs (coreApp fcore cargs))
                                else do fname <- uniqueName "fct"
                                        let fdef = Core.DefNonRec (Core.Def fname ftp fcore Core.Private (defFun [] {-all own, TODO: maintain borrow annotations?-}) InlineAuto rangeNull "")
                                            fvar = Core.Var (Core.TName fname ftp) Core.InfoNone
                                        return (Core.Let (fdef:defs) (coreApp fvar cargs))
           -- take top effect
           -- todo: sub effecting should add core terms
           topEff <- inferUnifies (checkEffect rng) ((getRange fun, eff1) : zip (map (getRangeArg . snd) iargs) effArgs)
           inferUnify (checkEffectSubsume rng) (getRange fun) funEff topEff

           -- instantiate or generalize result type
           funTp1 <- subst funTp
           stopEff <- subst topEff
           return (funTp1,stopEff,core)


    -- we cannot resolve an overloaded function name: infer types of arguments without propagation first.
    -- The code handles inferring arguments in any order by keeping track of the index, but at the moment
    -- we always infer from left to right until we can resolve the function type and then propagate argument types.
    inferAppFromArgs :: [Expr Type] -> [((Name,Range),Expr Type)] -> Inf (Type,Effect,Core.Expr)
    inferAppFromArgs [] named       -- there are no fixed arguments, use fun first anyways (and error..)
      = inferAppFunFirst Nothing fun [] [] named []
    inferAppFromArgs fixed named
      = do inferAppArgsFirst [] ((zip [0..] fixed)) fixed named

    -- inferAppFirst <guessed fixed arg types> <priority order fixed args> <fixed args> <named args>
    inferAppArgsFirst :: [(Int,FixedArg)] -> [(Int,Expr Type)] -> [Expr Type] -> [((Name,Range),Expr Type)] -> Inf (Type,Effect,Core.Expr)
    inferAppArgsFirst fresolved [] fixed named     -- we inferred all fixed arguments
      = -- this always fails since we have not been able to resolve the function name
        inferAppFunFirst Nothing fun fresolved fixed named []

    inferAppArgsFirst fresolved ((idx,fix):fixs) fixed named  -- try to improve our guess
      = do (tpArg,effArg,coreArg)  <- allowReturn False $ inferExpr Nothing Instantiated fix
           let fresolved' = fresolved ++ [(idx,(getRange fix,tpArg,effArg,coreArg))]
           amb <- case rootExpr fun of
                    (Var name _ nameRange)
                      -> do sctx    <- fixedContext propagated fresolved' (length fixed) (map (fst . fst) named)
                            matches <- lookupAppName (null fixs {- allow disambiguate -}) name sctx rng nameRange
                            case matches of
                              Right (itp,funExpr,implicits)
                                 -> return (Just ((itp,rng),funExpr,implicits))
                              _  -> return Nothing
                    _ -> return Nothing

           case amb of
             Just (prop,funExpr,implicits)
                      -> inferAppFunFirst (Just prop) funExpr (seqqList fresolved') fixed named implicits
             Nothing  -> inferAppArgsFirst (seqqList fresolved') fixs fixed named


getRangeArg :: ArgExpr -> Range
getRangeArg (ArgExpr expr _)      = getRange expr
getRangeArg (ArgCore (rng,_,_,_)) = rng
getRangeArg (ArgImplicit _ rng _) = rng


{--------------------------------------------------------------------------
  infer lambda
--------------------------------------------------------------------------}

inferLam ::  HasCallStack => Bool -> Maybe (Type,Range) -> Expect -> [ValueBinder (Maybe Type) (Maybe (Expr Type))] -> Expr Type -> Range -> Inf (Type,Effect,Core.Expr)
inferLam topLevel propagated expect bindersL body0 rng
  = isNamedLam $ \isNamed ->
    withScope $
    disallowHole $
    do (ftp,_,fcore) <- maybeGeneralize rng (getRange body0) expect $ infBody isNamed
       eff <- Op.freshEffect
       return (ftp,eff,fcore)
  where
    infBody isNamed =
     do (bindersX,unpackImplicitss) <- unzip <$> mapM inferImplicitParam bindersL
        let body = foldr (\f x -> f x) body0 unpackImplicitss

        (propArgs,propEff,propBody,skolems,expectBody) <- matchFun (length bindersX) propagated
        let binders0 = [case binderType binder of
                          Nothing -> binder{ binderType = fmap snd mbProp }
                          Just _  -> binder
                        | (binder,mbProp) <- zip bindersX propArgs]
        binders1 <- mapM instantiateBinder binders0
        eff <- case propEff of
                  Nothing  -> Op.freshEffect  -- TODO: use propEff?
                  Just (eff,_) -> return eff
        localDepth <- localScopeDepth
        scopeDepth <- getScopeDepth
        (infgamma,sub,defs) <- inferOptionals scopeDepth (localDepth == 0) eff [] binders1
        let coref c = Core.makeLet (map Core.DefNonRec defs) ((CoreVar.|~>) sub c)

        returnTp <- case propBody of
                      Nothing     -> Op.freshStar
                      Just (tp,_) -> return tp

        -- nice names for eta-expanded expressions for in the IDE
        let etaExpanded      = (not (null binders0) && all (\b -> hiddenNameStartsWith (binderName b) "eta") binders0)
            createEta name n = case drop n "xyz" of
                                 c:_ -> char c
                                 _   -> pretty (n+1)
            niceEta inf      = if etaExpanded
                                 then withNiceNames createEta (map binderName binders0) $ \docs ->
                                        do addRangeInfo (startOfRange rng) $ RM.InlayHint False {-=append before-} $
                                             (text "fn" <.> parens (hcat (intersperse comma [text "_" <.> doc | doc <- docs])) <.> text " ")
                                           inf
                                else inf

        (tp,eff1,core) <- traceIndent $ withScope $
                          extendInfGamma infgamma  $
                          extendInfGamma [(nameReturn,createNameInfoX Public nameReturn localDepth DefVal (getRange body) returnTp "")] $
                          niceEta $
                          (if (isNamed) then inferIsolated rng (getRange body) body else id) $
                            -- inferIsolated rng (getRange body) body $
                            inferExpr propBody expectBody body

        inferUnify (checkReturnResult rng) (getRange body) returnTp tp
        inferUnify (Infer rng) (getRange body) eff eff1
        topEff <- case propEff of
                    Nothing -> subst eff
                    Just (topEff,r) -> do inferUnify (checkEffectSubsume rng) r eff topEff
                                          subst topEff
        parTypes2 <- subst (map binderType binders1)
        let optPars   = zip (map binderName binders1) parTypes2 -- (map binderName binders1) parTypes2
            bodyCore1 = Core.addLambdas optPars topEff (Core.Lam [] topEff (coref core))
        bodyCore2 <- subst bodyCore1
        let pars = optPars

        sftp0 <- subst (typeFun pars topEff tp)
        -- check skolem escape (should this be after generalize?)
        when (not topLevel) $
          checkSkolemEscape rng sftp0 Nothing skolems tvsEmpty  -- TODO: not having this check improves error messages but is it really safe?

        -- substitute back skolems to meta variables
        (sktvars,subSkolems) <- Op.freshSub Meta skolems
        let sftp1 = subSkolems |-> sftp0
            bodyCore3 = subSkolems |-> bodyCore2
        substImplicitConstraints subSkolems

        -- check for polymorphic parameters
        unannotBinders <- mapM (\b -> do tp <- subst (binderType b); return b{ binderType = tp })
                            [b1  | (b0,b1) <- zip binders0 binders1, isNothing (binderType b0)]

        let polyBinders = filter (not . isTau . binderType) unannotBinders
        if (null polyBinders)
        then return ()
        else let b = head polyBinders
              in typeError rng (binderNameRange b) (text "unannotated parameters cannot be polymorphic") (binderType b) [(text "hint",text "annotate the parameter with a polymorphic type")]

        -- add range info for each parameter
        when (not etaExpanded) $
          mapM_ (\(binder,tp) -> addRangeInfo (binderNameRange binder) (RM.Id (binderName binder)
                                  (RM.NIValue "val" tp "" (case (propagated,binderType binder) of
                                                              (Just (_,rng), Just _) | rangeIsHidden rng -> True -- there was an actual annotation
                                                              _   -> False
                                                          )) [] True))
                (zip binders0 parTypes2)


        return (sftp1, typeTotal, bodyCore3)

{--------------------------------------------------------------------------
  infer variables
--------------------------------------------------------------------------}

inferVar :: HasCallStack => Maybe (Type,Range) -> Expect -> Name -> Range -> Bool -> Inf (Type,Effect,Core.Expr)

-- constructor
inferVar propagated expect name rng isRhs  | isConstructorName name
  = do (qname1,tp1,conRepr,conInfo) <- resolveConName name (fmap fst propagated) rng
       let info1 = InfoCon Public tp1 conRepr conInfo rng (conInfoDoc conInfo)
       (qname,tp,info) <- do defName <- currentDefName
                             let creatorName = newCreatorName qname1
                             if (defName /= unqualify creatorName && defName /= nameCopy) -- a bit hacky, but ensure we don't call the creator function inside itself or the copy function
                               then do mbRes <- lookupFunName creatorName propagated rng
                                       case mbRes of
                                          Just (qname',tp',info') -> return (qname',tp',info')
                                          Nothing  -> return (qname1,tp1,info1)
                               else return (qname1,tp1,info1)
       let coreVar = coreExprFromNameInfo qname info
       addRangeInfo rng (RM.Id (infoCanonicalName qname1 info1) (RM.NICon tp (infoDocString info1)) [] False)
       (itp,coref) <- maybeInstantiate rng expect tp
       eff <- Op.freshEffect
       return (itp,eff,coref coreVar)

-- variable
inferVar propagated expect name rng isRhs
  = -- we cannot directly "resolveName" with a propagated type
    -- as sometimes the types do not match and need to coerce due to local variables or references on the right-hand-side
    do vinfo <- case propagated of
                  Just prop | isRhs -> do -- traceDefDoc $ \penv -> text "inferVar" <+> ppParam penv (name,fst prop)
                                          resolveRhsName name prop rng
                  _                 -> resolveName name propagated rng
       inferVarName propagated expect name rng isRhs vinfo

inferVarName propagated expect name rng isRhs (qname,tp,info)
  = do if (isTypeLocalVar tp && isRhs)
        then do let irng = extendRange rng (-1)
                (tp1,eff1,core1) <- inferExpr propagated expect (Parens (App (Var nameLocalGet False irng)
                                                                             [(Nothing,App (Var nameByref False irng)
                                                                                           [(Nothing,Var name False irng)] irng)] irng)
                                                                        name "var" rng)
                addRangeInfo rng (RM.Id qname (RM.NIValue (infoSort info) tp1  (infoDocString info) False) [] False)
                return (tp1,eff1,core1)
        else case (info) of
         InfoVal{}  | infoIsVar info && isRhs  -- is it a right-hand side variable?
           -> do (tp1,eff1,core1) <- inferExpr propagated expect (App (Var nameDeref False rng) [(Nothing,App (Var nameByref False rng) [(Nothing,Var name False rng)] rng)] rng)
                 addRangeInfo rng (RM.Id qname (RM.NIValue (infoSort info) tp1 (infoDocString info) False) [] False)
                 return (tp1,eff1,core1)
         InfoVal{} | isValueOperation tp
           -> do addRangeInfo rng (RM.Id qname (RM.NIValue (infoSort info) tp (infoDocString info) False) [] False)
                 inferExpr propagated expect (App (Var (toValueOperationName qname) False rangeNull) [] rangeNull)
         _ -> do --  inferVarX propagated expect name rng qname1 tp1 info1
                 eff <- Op.freshEffect
                 case lookup qname compilationConstants of
                  Just (tp,fcore)
                    -> do mod  <- getModuleName
                          return (tp,eff,fcore mod rng)
                  Nothing
                    -> do let coreVar = coreExprFromNameInfo qname info
                              fixedEffect = case splitFunScheme tp of
                                              Just (_, _, eff, _) -> isEffectFixed eff
                                              _ -> False
                          (itp,coref) <- maybeInstantiate rng expect tp
                          sitp <- subst itp
                          (rmName,rmDoc) <- if hiddenNameStartsWith qname "eta"
                                              then do mbNice <- lookupNiceName qname
                                                      case mbNice of
                                                        Nothing   -> return ()
                                                        Just nice -> addRangeInfo (endOfRange rng) (RM.InlayHint True nice)
                                                      return (newName "_", "eta-expanded parameter")
                                              else return (infoCanonicalName qname info, infoDocString info)
                          addRangeInfo rng (RM.Id rmName (RM.NIValue (infoSort info) sitp rmDoc False) [] False)
                          localDepth <- localScopeDepth
                          let injectLocal n =  do hp <- Op.freshTVar kindHeap Meta
                                                  let localTp = TApp typeLocal [hp]
                                                      maskExpr = etaExpand n rng
                                                                  (\apply -> Inject localTp (Lam [] (apply (Var qname False rng)) False rng) False rng)
                                                  (tp,eff,core) <- withNoLocalScope $ inferExpr Nothing {- do not progate as the effect is different -} Instantiated maskExpr
                                                  return (tp,eff,core)
                          case (expandSyn itp,propagated) of
                            (TFun pars _ _,_) | not fixedEffect && infoAllowImplictMask info && not (isHiddenName qname) && localDepth > 0
                              -> injectLocal (length pars)
                            (_,Just (openTp@(TFun pars openEff tres),_)) | not fixedEffect && infoAllowImplictMask info && not (isHiddenName qname) && localDepth > 0
                              -> injectLocal (length pars)
                            _ -> return (sitp,eff,coref coreVar)

  where
    bestTp (TVar _) (Just (propTp,_)) = propTp
    bestTp tp _                       = tp

compilationConstants :: [(Name,(Type,Name -> Range -> Core.Expr))]
compilationConstants
  = [(nameCoreFileFile,   (typeString, \mod rng ->
        -- Core.Lit (Core.LitString (sourceName (rangeSource rng))))),
        Core.Lit (Core.LitString (showPlain mod ++ ".kk")))),  -- for now, use the module name to not leak info of a dev system
     (nameCoreFileLine,   (typeString, \mod rng -> Core.Lit (Core.LitString (show (posLine $ rangeStart rng))))),
     (nameCoreFileModule, (typeString, \mod rng -> Core.Lit (Core.LitString (showPlain mod))))
   ]

{--------------------------------------------------------------------------
  infer match, branches and patterns
--------------------------------------------------------------------------}