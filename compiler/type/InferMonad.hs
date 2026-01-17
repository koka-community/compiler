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
