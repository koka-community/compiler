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
  infer applications and resolve overloaded identifiers
--------------------------------------------------------------------------}