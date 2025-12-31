

improve :: Range -> Range -> Bool -> Effect -> Rho -> Inf (Rho,Effect,Core.Expr -> Core.Expr )
improve contextRange range close eff0 rho0
  = do seff  <- subst eff0
       srho  <- subst rho0
       free0 <- freeInGamma
       (eff1,coref) <- mapImplicitConstraints $ \ics ->
                       do let free = tvsUnion free0 (ftv srho)
                          (ics1,eff1,coref) <- isolate contextRange close free ics seff
                          return ((eff1,coref),ics1)
       (nrho) <- normalizeX close free0 srho  -- use free0 or otherwise function results are not closed, see `test/type/talpin-jouvelot1/#t1`
       return (nrho,eff1,coref)

-- | Automatically remove heap effects when safe to do so.
isolate :: Range -> Bool -> Tvs -> [ImplicitConstraint] -> Effect -> Inf ([ImplicitConstraint], Effect, Core.Expr -> Core.Expr)
isolate rng close free ics eff
  = do -- traceDefDoc $ \penv -> text "isolate:" <+> Pretty.ppType penv eff
                                -- <-> text "  free" <+> ppTvs penv free
                                -- <-> text "  ics:" <+> list (map (ppConstraint penv) ics)
       let (ls,tl) = extractOrderedEffect eff
       case filter (\l -> labelName l `elem` [nameTpLocal,nameTpRead,nameTpWrite]) ls of
          (lab@(TApp labcon [TVar h]) : _)
            -> -- has heap variable 'h' in its effect
               do (polyIcs,ics1) <- splitHDiv h ics
                  let isLocal = (labelName lab == nameTpLocal)
                  -- determineds <- mapM (\ic -> (icCanSolve ic) free ic) polyIcs
                  if not (tvsMember h free) -- || and determineds --  not (.. || tvsMember h (ftv ics1))
                    then do -- we can isolate, and discharge the polyIcs hdiv predicates
                            -- traceDefDoc $ \penv -> text "can isolate:" <+> Pretty.ppType penv eff <+> text ", poly ics" <+> list (map (ppConstraint penv) polyIcs)
                            tv <- freshEffect
                            if isLocal
                             then do -- trace ("isolate local") $ return ()
                                varScope <- getScopeDepth
                                if varScope == 0 then
                                     nofailUnify $ unify (effectExtend lab tv) eff
                                else return ()
                             else do mbSyn <- lookupSynonym nameTpST
                                     let (Just syn) = mbSyn
                                         [bvar] = synInfoParams syn
                                         st     = subNew [(bvar,TVar h)] |-> synInfoType syn
                                     -- traceDoc $ \penv -> text "isolate st: " <+> Pretty.ppType  penv{Pretty.showKinds=True,Pretty.showIds=True} st
                                     nofailUnify $ unify (effectExtend st tv) eff
                            coref  <- resolveImplicitConstraints free polyIcs

                            neweff <- subst tv
                            sics   <- subst ics1
                            -- trace ("isolate to:"  ++ show (pretty neweff)) $ return ()
                            -- return (sps, neweff, id) -- TODO: supply evidence (i.e. apply the run function)
                            -- and try again
                            (ics',eff',coref') <- isolate rng close free sics neweff
                            let coreRun cexpr = if (isLocal)
                                                 then cexpr
                                                 else cexpr  -- TODO: apply runST?
                            return (ics',eff',coreRun . coref' . coref)
                     else do -- traceDefDoc $ \penv -> text "cannot isolate:" <+> Pretty.ppType penv eff <+> text ", poly ics" <+> list (map (ppConstraint penv) polyIcs) <+> text ", free ics:" <+> list (map (ppConstraint penv) ics1)
                             coref <- tryResolveImplicitConstraints close free
                             return (ics,eff,coref)
          (lab@(TApp labcon [TCon global]) : _) -> do
            coref <- tryResolveImplicitConstraints close free
            return (ics,eff,coref)
          _ -> return (ics,eff,id)

  where
    -- | 'splitHDiv h ics' splits constraints 'ics'. Constraints of the form hdiv<h,tp,e> where tp does
    -- not contain h are returned as the first element, all others as the second. This includes
    -- constraints where hdiv<h,a,e> for example where a is polymorphic. Normally, we need to assume
    -- divergence conservatively in such case; however, when we isolate, we know it cannot be instatiated
    -- to contain a reference to h and it is safe to discharge them during isolation without implying
    -- divergence. See test\type\talpin-jouvelot1 for an example: fun rid(x) { val r = ref(x) in !r }
    splitHDiv :: TypeVar -> [ImplicitConstraint] -> Inf ([ImplicitConstraint],[ImplicitConstraint])
    splitHDiv heapTv []
      = return ([],[])
    splitHDiv heapTv (ic:ics)
      = do (ics1,ics2) <- splitHDiv heapTv ics
           let defaultRes = (ics1,ic:ics2)
           tp <- implicitConstraintType ic
           case expandSyn tp of
              TApp (TCon tcon) [tpHeap,tpVal,tpEff]  | typeConName tcon == nameTypeHeapDiv
                -> do shp <- subst tpHeap
                      case expandSyn shp of
                        hp@(TVar tv) | tv == heapTv
                          -> do {- stp <- subst tpVal
                                if (isNothing (find (\ht -> eqType hp ht) (heapTypes stp)))
                                  then do let icnodiv = ic{ icSolve = resolveHeapDivConstraint True {-always no div-} tpHeap tpVal tpEff }
                                          return (icnodiv:ics1,ics2) -- even if polymorphic, we are ok if we isolate
                                  else -- return defaultRes -}
                                       return (ic:ics1,ics2)
                        _ -> return defaultRes
              _ -> return defaultRes

{--------------------------------------------------------------------------
  Implicit Constraints
--------------------------------------------------------------------------}

implicitConstraints :: [(Name,Name -> Type -> Maybe (Tvs -> ImplicitConstraint -> Inf Bool, Tvs -> ImplicitConstraint -> Inf (Core.Expr, Type)))]
implicitConstraints
  = [(nameHeapDiv, checkHeapDivConstraint)]

resolveImplicitConstraints :: Tvs -> [ImplicitConstraint] -> Inf (Core.Expr -> Core.Expr)
resolveImplicitConstraints free []  = return id
resolveImplicitConstraints free ics
  = do defs <- mapM resolve ics
       let fcore core = case core of
                          -- Core.Lam pars eff body -> Core.Lam pars eff (Core.makeDefsLet defs body)
                          -- Core.TypeLam tpars (Core.Lam pars eff body) -> Core.TypeLam tpars (Core.Lam pars eff (Core.makeDefsLet defs body))
                          _ -> Core.makeDefsLet defs core

       return fcore
  where
    resolve ic
      = do (evidence,tp) <- (icSolve ic) free ic
           solvedImplicitConstraint (icEvidence ic) tp
           return $ Core.makeTDef (Core.TName (icEvidence ic) tp) evidence


tryResolveImplicitConstraints :: Bool -> Tvs -> Inf (Core.Expr -> Core.Expr)
tryResolveImplicitConstraints close free
  = mapImplicitConstraints $ \ics -> tryResolve ([],[]) ics
  where
    tryResolve :: ([Core.Def],[ImplicitConstraint]) -> [ImplicitConstraint] -> Inf (Core.Expr -> Core.Expr,[ImplicitConstraint])
    tryResolve (defs,acc) []
      = do let fcore core = case core of
                              Core.Lam pars eff body -> Core.Lam pars eff (Core.makeDefsLet defs body)
                              Core.TypeLam tpars (Core.Lam pars eff body) -> Core.TypeLam tpars (Core.Lam pars eff (Core.makeDefsLet defs body))
                              _ -> Core.makeDefsLet defs core
           return (fcore, reverse acc)
    tryResolve (defs,acc) (ic:ics)
      = do determined <- (icCanSolve ic) free ic
           let force = -- let ftvs = fuv ic
                            --    generalized = tvsFilter (\tv -> not (tvsMember tv free)) ftvs
                            --in not (tvsIsEmpty generalized) || -- are any free variables about to be generalized?
                            --   tvsIsEmpty ftvs             -- or are no free variables left?
                            let freeTv = tvsList (fuv ic)
                            in null freeTv || not (all (\tv -> tvsMember tv free) freeTv)
           if determined || force || close
             then do (ev,tp) <- (icSolve ic) free ic
                     solvedImplicitConstraint (icEvidence ic) tp
                     let def = Core.makeTDef (Core.TName (icEvidence ic) tp) ev
                     tryResolve (def:defs, acc) ics
             else tryResolve (defs, ic:acc) ics



{--------------------------------------------------------------------------
  heap divergence constraints
--------------------------------------------------------------------------}

checkHeapDivConstraint :: Name -> Type -> Maybe (Tvs -> ImplicitConstraint -> Inf Bool, Tvs -> ImplicitConstraint -> Inf (Core.Expr, Type))
checkHeapDivConstraint name tp
  = case expandSyn tp of
      TApp (TCon tcon) [tpHeap,tpVal,tpEff]  | typeConName tcon == nameTypeHeapDiv
        -> Just (canResolveHeapDivConstraint,resolveHeapDivConstraint)
      _ -> Nothing

canResolveHeapDivConstraint :: Tvs -> ImplicitConstraint -> Inf Bool
canResolveHeapDivConstraint free ic
  = do icTp <- implicitConstraintType ic
       case expandSyn icTp of -- expand here again (should never fail!) so we get skolem substitutions
         TApp (TCon tcon) [tpHeap,tpVal,tpEff]
            -> do
              let never = heapNeverContainedIn free tpHeap tpVal
              let always = heapAlwaysContainedIn free tpHeap tpVal
              -- trace ("Check resolve\n" ++ show tpHeap ++ "\n" ++ show tpVal ++ "\n" ++ show never ++ " " ++ show always) $ return ()
              return (never || always)

implicitConstraintType :: HasCallStack => ImplicitConstraint -> Inf Type
implicitConstraintType ic
  = do ig <- iconstraintsGamma <$> getSt
       case infgammaLookup (icEvidence ic) ig of
         Right (_,nameInfo)
           -> subst (infoType nameInfo)  -- unlike icType, this may have substituted skolems
         _ -> failure "Type.InferMonad.implicitConstraintType" $ "unknown constraint: " ++ show (icEvidence ic)


resolveHeapDivConstraint :: Tvs -> ImplicitConstraint -> Inf (Core.Expr, Type)
resolveHeapDivConstraint free ic
  = do sic <- subst ic
       tp  <- implicitConstraintType ic
       case expandSyn tp of -- expand here again (should never fail!) so we get skolem substitutions
         TApp (TCon tcon) [tpHeap,tpVal,tpEff]
           -> do  -- traceDefDoc $ \penv -> text "resolveHeapDivConstraint:" <+> ppConstraint penv sic
                  --                        <-> text "  free:" <+> ppTvs penv free
                  --                        <-> text "  tvsHp:" <+> ppTvs penv tvsHp <.> text ", tvsTp:" <+> ppTvs penv tvsTp
                  maydiv <- if (heapNeverContainedIn free tpHeap tpVal)
                                -- not (tvsIsEmpty (ftv stp)))) -- conservative guess...
                              then return False
                              else do -- add div effect to tpEff
                                      tv <- Op.freshEffect
                                      let divEff = effectExtend typeDivergent tv
                                      inferUnify (Infer (icContext ic)) (icRange ic) tpEff divEff
                                      return True
                  (cname,ctype,cinfo) <- resolveNameEx isInfoCon Nothing
                                            (if maydiv then nameEvHeapDiv else nameEvHeapNoDiv) CtxNone (icContext ic) (icRange ic)
                                          -- resolveName nameEvHeapDiv Nothing (icRange ic)
                  seff <- subst tpEff
                  stp  <- subst tp
                  -- traceDefDoc $ \penv -> text "resolve @hdiv:" <+> Pretty.ppName penv (icEvidence ic) <.> colon <+> Pretty.ppType penv stp <+> text "as" <+> text (if maydiv then "divergent" else "non-divergent")
                  --                         <-> text "  , free: " <+> ppTvs penv free
                  let ev = Core.TypeApp (coreExprFromNameInfo cname cinfo) [tpHeap,tpVal,seff]
                  return (ev,stp)



{--------------------------------------------------------------------------
  Inference monad
--------------------------------------------------------------------------}


runInfer :: Pretty.Env -> Maybe RangeMap -> Synonyms -> Newtypes -> ImportMap -> Gamma -> Name -> Bool -> Int -> Inf a -> Error b (a,Int,Maybe RangeMap)
runInfer env mbrm syns newTypes imports assumption context allowInfiniteChains unique (Inf f)
  = case f (Env env context [] False newTypes syns assumption infgammaEmpty imports False False Nothing 0 0 allowInfiniteChains NM.empty)
           (St unique subNull [] infgammaEmpty False mbrm) of
      Err (rng,doc) warnings
        -> addWarnings (map (toWarning ErrType) warnings) (errorMsg (errorMessageKind ErrType rng doc))
      Ok x st warnings
        -> addWarnings (map (toWarning ErrType) warnings) (ok (x, uniq st, (sub st) |-> mbRangeMap st))


zapSubst :: HasCallStack => Inf ()
zapSubst
  = do env <- getEnv
       assertion "not an empty infgamma" (infgammaIsEmpty (infgamma env)) $
        do st <- getSt
           when (not (infgammaIsEmpty (iconstraintsGamma st))) $
            traceDefDoc $ \penv -> text "iconstraintsGamma:" <-> indent 2 (ppInfGamma penv (iconstraintsGamma st))
           updateSt (\st -> assertion "no empty iconstraints" (null (iconstraints st)) $
                            assertion "no empty iconstraints gamma" (infgammaIsEmpty (iconstraintsGamma st)) $
                            st{ sub = subNull, iconstraints = [], mbRangeMap = (sub st) |-> mbRangeMap st } ) -- this can be optimized further by splitting the rangemap into a 'substited part' and a part that needs to be done..
           return ()

tryRun :: Inf a -> Inf (Maybe a)
tryRun (Inf i) = Inf (\env st -> case i env st of
                                   Ok x st1 w -> Ok (Just x) st1 w
                                   Err err w  -> Ok Nothing st [])

ignoreErrors :: Inf a -> Inf a -> Inf a
ignoreErrors (Inf defaultRes) (Inf f)
  = Inf (\env st0 -> case f env st0 of
                       Err err ws -> case defaultRes env st0 of
                                       Ok x st1 ws1 -> Ok x st1 ([err] ++ ws ++ ws1)
                                       Err err1 ws1 -> Err err1 ([err] ++ ws ++ ws1)
                       ok         -> ok)


withNoRangeInfo :: Inf a -> Inf a
withNoRangeInfo inf
  = do st0 <- updateSt (\st -> st{ mbRangeMap = Nothing })
       let rm0 = mbRangeMap st0
       x   <- inf
       updateSt ( \st -> st{ mbRangeMap = rm0 })
       return x

withNiceNames :: (Name -> Int -> Doc) -> [Name] -> ([Doc] -> Inf a) -> Inf a
withNiceNames create names finf
  = do env <- getEnv
       let n   = NM.size (niceNames env)
           nms = [(name, create name i) | (i,name) <- zip [n..] names]
           env'= env{ niceNames = NM.union (niceNames env) (NM.fromList nms) }
       withEnv (\_ -> env') $ finf (map snd nms)

lookupNiceName :: Name -> Inf (Maybe Doc)
lookupNiceName name
  = do env <- getEnv
       return (NM.lookup name (niceNames env))


{--------------------------------------------------------------------------
  Helpers
--------------------------------------------------------------------------}

extendGammaCore :: Bool -> [Core.DefGroup] -> Inf a -> Inf (a)
extendGammaCore isAlreadyCanonical [] inf
  = inf
extendGammaCore isAlreadyCanonical (coreGroup:coreDefss) inf
  = do d <- getScopeDepth
       extendGamma isAlreadyCanonical (nameInfos d coreGroup) (extendGammaCore isAlreadyCanonical coreDefss inf)
  where
    nameInfos d (Core.DefRec defs)    = map (\def -> coreDefInfoX def d) defs
    nameInfos d (Core.DefNonRec def)
      = [coreDefInfoX def d]  -- used to be coreDefInfo

-- Specialized for recursive defs where we sometimes get InfoVal even though we want InfoFun? is this correct for the csharp backend?
coreDefInfoX def@(Core.Def name tp expr vis sort inl nameRng doc) scopeDepth
  = (name {- nonCanonicalName name -}, createNameInfoX Public name scopeDepth sort nameRng tp doc)

-- extend gamma with qualified names
extendGamma :: Bool -> [(Name,NameInfo)] -> Inf a -> Inf (a)
extendGamma isAlreadyCanonical defs inf
  = do env <- getEnv
       (gamma') <- extend (prettyEnv env) (context env) defs (gamma env)
       withEnv (\env -> env{ gamma = gamma' }) inf
  where
    extend penv ctx [] (gamma)
      = return (gamma)
    extend penv ctx ((name,info):rest) (gamma)
      = do let matches = gammaLookup name gamma
               localMatches = [(qname,info) | (qname,info) <- matches, not (isInfoImport info),
                                              qualifier qname == ctx || qualifier qname == nameNil,
                                              unqualify name == unqualify qname,
                                              isSameNamespace qname name ]
           case localMatches of
             ((qname,qinfo):_) -> infError (infoRange info) (text "definition" <+> Pretty.ppName penv name <+>
                                                             text "is already defined in this module, at" <+> text (show (rangeStart (infoRange qinfo))) <->
                                                             text "hint: use a local qualifier?")
             [] -> return ()
           extend penv ctx rest (gammaExtend name info gamma)


    checkNoOverlap :: Name -> Name -> NameInfo -> (Name,NameInfo) -> Inf ()
    checkNoOverlap ctx name info (name2,info2)
      = do checkCasingOverlap (infoRange info) name name2 info
           free <- freeInGamma
           res  <- runUnify (overlaps (infoRange info) free (infoType info) (infoType info2))
           case fst res of
            Right _ ->
              do env <- getEnv
                 let [nice1,nice2] = Pretty.niceTypes (prettyEnv env) [infoType info,infoType info2]
                     (_,rho1)      = splitTypeScheme (infoType info)
                     (_,rho2)      = splitTypeScheme (infoType info2)
                     valueType     = not (isFun rho1 && isFun rho2)
                 if (isFun rho1 && isFun rho2)
                  then infError (infoRange info) (text "definition" <+> Pretty.ppName (prettyEnv env) name <+> text "overlaps with an earlier definition of the same name" <->
                                                  table ([(text "type",nice1)
                                                         ,(text "overlaps",nice2)
                                                         ,(text "because", text "definitions with the same name must differ on the argument types")])
                                                 )
                  else infError (infoRange info) (text "definition" <+> Pretty.ppName (prettyEnv env) name <+> text "is already defined in this module" <->
                                                  text "because: only functions can have overloaded names")
            Left _ -> return ()


extendInfGammaCore :: Bool -> [Core.DefGroup] -> Inf a -> Inf a
extendInfGammaCore topLevel [] inf
  = inf
extendInfGammaCore topLevel (coreDefs:coreDefss) inf
  = do d <- getScopeDepth
       extendInfGammaEx topLevel [] (extracts d coreDefs) (extendInfGammaCore topLevel coreDefss inf)
  where
    extracts d (Core.DefRec defs) = map (extract d) defs
    extracts d (Core.DefNonRec def) = [extract d def]
    extract d def
      = coreDefInfo def d -- (Core.defName def,(Core.defNameRange def, Core.defType def, Core.defSort def))

extendInfGamma :: [(Name,NameInfo)] -> Inf a -> Inf a
extendInfGamma tnames inf
  = extendInfGammaEx False [] tnames inf

extendInfGammaEx :: Bool -> [Name] -> [(Name,NameInfo)] -> Inf a -> Inf a
extendInfGammaEx topLevel ignores tnames inf
  = do env <- getEnv
       infgamma' <- extend (context env) (gamma env) [] [(unqualify name,info) | (name,info) <- tnames, not (isWildcard name)] (infgamma env)
       withEnv (\env -> env{ infgamma = infgamma' }) inf
  where
    extend :: Name -> Gamma -> [(Name,NameInfo)] -> [(Name,NameInfo)] -> InfGamma -> Inf InfGamma
    extend ctx gamma seen [] infgamma
      = return infgamma
    extend ctx gamma seen (x@(name,info):rest) infgamma
      = do let qname = infoCanonicalName name info
               range = infoRange info
               tp    = infoType info
           case (lookup name seen) of
            Just (info2)
              -> do checkCasingOverlap range name (infoCanonicalName name info2) info2
                    env <- getEnv
                    infError range (Pretty.ppName (prettyEnv env) name <+> text "is already defined at" <+> pretty (show (infoRange info2))
                                     <-> text " hint: if these are potentially recursive definitions, give a full type signature to disambiguate them.")
            Nothing
              -> do case (infgammaLookup name infgamma) of
                      Right (cname,info2) | cname /= nameReturn  -- TODO: adapt to multiple matches?
                        -> do checkCasingOverlap range name cname info2
                              env <- getEnv
                              if (not (isHiddenName name) && show name /= "resume" && show name /= "resume-shallow" && not (name `elem` ignores))
                               then infWarning range (Pretty.ppName (prettyEnv env) name <+> text "shadows an earlier local definition or parameter")
                               else return ()
                      _ -> return ()
           extend ctx gamma (x:seen) rest (infgammaExtend qname (info{ infoCName =  if topLevel then createCanonicalName ctx gamma qname else qname}) infgamma)

createCanonicalName ctx gamma qname
  = let matches = gammaLookup (unqualify qname) gamma
        localMatches = [(qname,info) | (qname,info) <- matches, not (isInfoImport info), qualifier qname == ctx || qualifier qname == nameNil ]
        cname = {- canonicalName (length localMatches) -} qname
    in cname

withGammaType :: Range -> Type -> Inf a -> Inf a
withGammaType range tp inf
  = do defName <- currentDefName
       name <- uniqueNameFrom defName
       d <- getScopeDepth
       extendInfGamma [(name,(InfoVal Public name tp d range False False ""))] inf

currentDefName :: Inf Name
currentDefName
  = do dnames <- currentDefNames
       case dnames of
         (dname:_) -> return dname
         _         -> return (newName "")

withDefName :: Name -> Inf a -> Inf a
withDefName name inf
  = withEnv (\env -> env{ currentDefs = name : currentDefs env, namedLam = not (nameIsNil name || isWildcard name) }) inf

isNamedLam :: (Bool -> Inf a) -> Inf a
isNamedLam action
    = do env <- getEnv
         withEnv (\env -> env{ namedLam = False }) (action (namedLam env))

lookupInfName :: Name -> Inf (Maybe (Name,Type))
lookupInfName name
  = do env <- getEnv
       case infgammaLookup (unqualify name) (infgamma env) of
         Right (name,info)  -> return (Just (name,infoType info))
         Left []            -> return Nothing
         Left infos -> do def <- currentDefName
                          failure ("InferMonad.lookupInfName: ambigous local? " ++ show def ++ ": " ++ show name ++ ":\n" ++ unlines (map show infos))


findDataInfo :: Name -> Inf DataInfo
findDataInfo typeName
  = do env <- getEnv
       case newtypesLookupAny typeName (types env) of
         Just info -> return info
         Nothing   -> failure ("Type.InferMonad.findDataInfo: unknown type: " ++ show typeName ++ "\n in: " ++ show (types env))

traceDefDoc :: (Pretty.Env -> Doc) -> Inf ()
traceDefDoc f
  = do dnames <- currentDefNames
       traceDoc (\penv -> hcat (intersperse (text ".") (map (Pretty.ppName penv) dnames)) <+> text ":" <+> f penv)
