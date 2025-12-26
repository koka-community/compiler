
{--------------------------------------------------------------------------
  Generalization
--------------------------------------------------------------------------}
generalize :: HasCallStack => Range -> Range -> Bool -> Inf (Rho,Effect,Core.Expr) -> Inf (Scheme,Effect,Core.Expr)
generalize contextRange range close inf
  = (if close then id else scopeImplicitConstraints) $
    do res <- inf
       generalizeX contextRange range close res

generalizeX :: HasCallStack => Range -> Range -> Bool -> (Rho,Effect,Core.Expr) -> Inf (Scheme,Effect,Core.Expr )
generalizeX contextRange range close (tp@(TForall _ _),eff,core0)
  = do stp  <- subst tp
       seff <- subst eff
       if (tvsIsEmpty (fuv stp))
        then return (tp,seff,core0)
        else do (rho,tvars,icore) <- instantiateNoEx range stp  -- instantiate first
                generalizeX contextRange range close (rho,seff,icore core0)

generalizeX contextRange range close (rho0,eff0,bodycore0)
  = do -- traceDefDoc $ \penv -> text "generalizing:" <+> Pretty.ppType penv rho0 <+> text "|" <+> Pretty.ppType penv eff0
       -- check that the computation is total
       if (close)
         then inferUnify (Check "Generalized values cannot have an effect" contextRange) range typeTotal eff0
         else return ()

       -- solve implicit constraints
       seff0 <- subst eff0
       free0 <- freeInGamma
       let free1 = tvsUnion free0 (fuv seff0)

       iccore <- tryResolveImplicitConstraints close free1
       let bodycore1 = iccore bodycore0

       -- normalize type
       seff  <- subst eff0
       srho  <- subst rho0
       let free = tvsUnion free0 (fuv seff)
       nrho <- normalizeX close free srho

       -- generalized type variables
       let tvars = filter (\tv -> not (tvsMember tv free)) (ofuv nrho)

      --  ics <- getImplicitConstraints
      --  traceDefDoc $ \penv -> text "generalize:" <+> Pretty.ppType penv nrho <+> text "|" <+> Pretty.ppType penv seff
      --                         <-> text "  genvars:" <+> ppTvs penv (tvsNew tvars)
      --                         <-> text "  free:" <+> ppTvs penv free
      --                         <-> text "  remaining ics:" <+> ppConstraints penv ics

       if (null tvars)
        then do return (nrho,seff,bodycore1)
        else do -- create fresh type variables for the bounds
                -- important to avoid duplicate names (`test/algeff/exn3`)
                (bvars,bsub) <- freshSub Bound tvars
                let (TForall [] rho5) = bsub |-> (TForall [] nrho)
                    -- core
                    corePre = bsub |-> bodycore1
                    core1 = Core.addTypeLambdas bvars corePre
                    resTp = quantifyType bvars rho5

                -- traceDoc $ \penv -> text "corePre:" <+> prettyExpr penv{Pretty.coreShowTypes=True} corePre
                return (resTp,seff,core1)



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


----------------------------------------------------------------
-- Resolve names
----------------------------------------------------------------

-- | Lookup a name with a certain type and return the fully qualified name and its type
resolveName :: HasCallStack =>  Name -> Maybe (Type,Range) -> Range -> Inf (Name,Type,NameInfo)
resolveName name mbType range
  = case mbType of
      Just (tp,ctxRange) -> resolveNameEx infoFilter (Just infoFilterAmb) name (CtxType tp) ctxRange range
      Nothing            -> resolveNameEx infoFilter (Just infoFilterAmb) name CtxNone range range
  where
    infoFilter = isInfoValFunExt
    infoFilterAmb = not . isInfoImport

-- | Lookup a name with a certain type and return the fully qualified name and its type
-- because of local variables and references a typed lookup may fail as we need to
-- dereference first. So we do a typed lookup first and fall back to untyped lookup
resolveRhsName :: HasCallStack => Name -> (Type,Range) -> Range -> Inf (Name,Type,NameInfo)
resolveRhsName name (tp,ctxRange) range
  = do -- traceDefDoc $ \penv -> text "resolveRhsName:" <+> text (show name)
       candidates <- lookupNameCtx isInfoValFunExt name (CtxType tp) range
       case candidates of
         -- unambiguous and matched
         [(qname,info)]
              -> do checkCasing range name qname info
                    return (qname,infoType info,info)
         -- not found; this may be due to needing a coercion term
         []   -> resolveName name Nothing range    -- try again without type info
         -- still ambiguous (even with a type), call regular lookup to throw an error
         amb  -> resolveName name (Just (tp,ctxRange)) range


-- | Lookup a name with a number of arguments and return the fully qualified name and its type
resolveFunName :: Name -> NameContext -> Range -> Range -> Inf (Name,Type,NameInfo)
resolveFunName name ctx rangeContext range
  = resolveNameEx infoFilter (Just infoFilterAmb) name ctx rangeContext range
  where
    infoFilter = isInfoValFunExt
    infoFilterAmb = not . isInfoImport

resolveConName :: Name -> Maybe (Type) -> Range -> Inf (Name,Type,Core.ConRepr,ConInfo)
resolveConName name mbType range
  = do (qname,tp,info) <- resolveNameEx isInfoCon Nothing name (maybeToContext mbType) range  range
       return (qname,tp,infoRepr info,infoCon info)

resolveConPatternName :: Name -> Type -> Int -> Range -> Inf (Name,Type,Core.ConRepr,ConInfo)
resolveConPatternName name matchType patternCount range
  = do (qname,tp,info) <- resolveNameEx isInfoCon Nothing name ctx range  range
       return (qname,tp,infoRepr info,infoCon info)
  where
    ctx = CtxFunArgs True {-partial?-} patternCount [] (Just matchType)
          {- if patternCount > 0
            then CtxFunArgs True {-partial?-} patternCount [] (Just matchType)
            else CtxType matchType -}


resolveNameEx :: HasCallStack => (NameInfo -> Bool) -> Maybe (NameInfo -> Bool) -> Name -> NameContext -> Range -> Range -> Inf (Name,Type,NameInfo)
resolveNameEx infoFilter mbInfoFilterAmb name ctx rangeContext range
  = do matches <- lookupNameCtx infoFilter name ctx range
       case matches of
        []   -> do amb <- case ctx of
                            CtxNone -> return []
                            _       -> lookupNameCtx infoFilter name CtxNone range
                   env <- getEnv
                   let penv = prettyEnv env
                       ctxTerm rangeContext = [(text "context", docFromRange (Pretty.colors penv) rangeContext)
                                              ,(text "term", docFromRange (Pretty.colors penv) range)]
                   case (ctx,amb) of
                    (CtxType tp, [(qname,info)])
                      -> do let [nice1,nice2] = Pretty.niceTypes penv [tp,infoType info]
                            infError range (Pretty.ppName penv name <+> text "does not match the argument types" <->
                                               table (ctxTerm rangeContext ++
                                                      [(text "inferred type",nice2)
                                                      ,(text "expected type",nice1)]))
                    (CtxType tp, (_:rest))
                      -> infError range (text "identifier" <+> Pretty.ppName penv name <+> text "has no matching definition" <->
                                         table (ctxTerm rangeContext ++
                                                [(text "inferred type", Pretty.niceType penv tp)
                                                ,(text "candidates", ppCandidates env amb)] ++ ppImplicitsHint env amb))
                    (CtxFunArgs matchSome fixed named (Just resTp), (_:rest))
                      -> do let message = "with " ++ show (fixed + length named) ++ " argument(s) matches the result type"
                            infError range (text "no function" <+> Pretty.ppName penv name <+> text message <+>
                                            Pretty.niceType penv resTp <.> ppAmbiguous env "" amb)
                    (CtxFunArgs matchSome fixed named Nothing, (_:rest))
                      -> do let message = "takes " ++ show (fixed + length named) ++ " argument(s)" ++
                                          (if null named then "" else " with such parameter names")
                            infError range (text "no function" <+> Pretty.ppName penv name <+> text message <.> ppAmbiguous env "" amb)
                    (CtxFunTypes partial fixed named mbResTp, (_:rest))
                      -> do let docs = Pretty.niceTypes penv (fixed ++ map snd named)
                                fdocs = take (length fixed) docs
                                ndocs = [color (colorParameter (Pretty.colors penv)) (pretty n <+> text ":") <+> tpdoc |
                                           ((_,n),tpdoc) <- zip named (drop (length fixed) docs)]
                                pdocs = if partial then [text "..."] else []
                                argsDoc = color (colorType (Pretty.colors penv)) $
                                           parens (hsep (punctuate comma (fdocs ++ ndocs ++ pdocs))) <+>
                                           text "-> ..." -- todo: show nice mbResTp if present
                            infError range (text "no function" <+> Pretty.ppName penv name <+> text "is defined that matches the argument types" <->
                                         table (ctxTerm rangeContext ++
                                                [(text "inferred type", argsDoc)
                                                ,(text "candidates", ppCandidates env amb)] ++ ppImplicitsHint env amb
                                                ++
                                                (if (name == newName "+")
                                                  then [(text "hint", text "did you mean to use append (++)? (instead  of addition (+) )")]
                                                  else [])
                                               ))

                    _ -> do amb2 <- case mbInfoFilterAmb of
                                      Just infoFilterAmb -> lookupNameCtx infoFilterAmb name ctx range
                                      Nothing            -> return []
                            case amb2 of
                              (_:_)
                                -> infError range ((text "identifier" <+> Pretty.ppName penv name <+> text "cannot be found") <->
                                                   (text "perhaps you meant: " <.> ppOr penv (map fst amb2)))
                              _ | nameIsEtaHole name
                                -> do inCtx <- holeAllowed <$> getSt
                                      let header = text "eta-expansion of \"_\" is not allowed for top-level expressions"
                                          message = if inCtx
                                                      then header <-> text "hint: perhaps you meant to use the \"hole\" keyword to denote the hole in a constructor context?"
                                                      else header
                                      infError range message
                                      error "done"
                              _ -> do -- when (isImplicitConstraintEvidenceName name) $ error ("evidence " ++ show name ++ " cannot be found")
                                      infError range (text "identifier" <+> Pretty.ppName penv name <+> text "cannot be found")
                                      error "done"

        [(qname,info)]
           -> do -- when (not asPrefix) $  -- todo: check casing for asPrefix as well
                 checkCasing range name qname info
                 return (qname,infoType info,info)
        _  -> do env <- getEnv
                 (term,termInfo) <- getTermDoc "context" rangeContext
                 infError range (text "identifier" <+> Pretty.ppName (prettyEnv env) name <+> text "cannot be resolved." <->
                                 table ([(term, termInfo),
                                         (text "inferred type", ppNameContext (prettyEnv env) ctx),
                                         (text "candidates", ppCandidates env matches),
                                         (text "hint", text "give a type annotation or qualify the name?")] ++ ppImplicitsHint env matches))
  where
    hintTypeSig = "give a type annotation to the function parameters or qualify the name?"


----------------------------------------------------------------
-- Resolving of implicit expressions
----------------------------------------------------------------

-- lookup an application name `f(...)` where the name context usually contains (partially) inferred
-- argument types. We reuse the lookup for implicit arguments as it works the same
-- (except that for implicit arguments we allow value types to be resolved with unit functions (for conversions))
lookupAppName :: Bool -> Name -> NameContext -> Range -> Range ->
                   Inf (Either [Doc] (Type,Expr Type,[((Name,Range),Expr Type, (Bool -> Doc))]))
lookupAppName allowDisambiguate name ctx contextRange range
  = do roots <- if not (isConstructorName name)
                  then -- normal identifier
                       return [(isInfoValFunExt,name)]
                  else -- constructor application: we need to consider creator functions too (for default fields)
                       do let cname = newCreatorName name
                          defName <- currentDefName
                          -- traceDefDoc $ \penv -> text "lookupAppName, constructor name:" <+> Pretty.ppName penv name <+> text "in definition" <+> Pretty.ppName penv defName
                          if (defName == unqualify cname || defName == nameCopy) -- a bit hacky, but ensure we don't call the creator function inside itself or the copy function
                            then return [(isInfoCon,name)]
                            else return [(isInfoFun,cname),(isInfoCon,name)]

       -- try to find a unique solution
       res <- resolveImplicitArg allowDisambiguate
                                 (not allowDisambiguate) {- allow unitFunVal: at first, when allowDisambiguate is False, we like to see all possible instantations -}
                                 ctx range roots
       case res of
          Right iarg@(ImplicitArg qname _ rho iargs)
            -> do -- when (not (null iargs)) $ traceDefDoc $ \penv -> text "resolved app name with implicits:" <+> prettyImplicitArg penv iarg
                  -- traceDefDoc $ \penv -> text "lookupAppName:" <+> Pretty.ppName penv name <.> text " to:" <+> prettyImplicitArg penv iarg
                  penv <- getPrettyEnv
                  let implicits = [((pname,range),
                                     toImplicitArgExpr (endOfRange range) iarg,
                                     prettyImplicitAssign penv "" pname iarg) | (pname,iarg) <- iargs]
                  return (Right (rho, Var qname False range, implicits))
          Left docs
            -> if (allowDisambiguate && not (null docs))
                then do env <- getEnv
                        (term,termInfo) <- getTermDoc "context" contextRange
                        infError range (text "identifier" <+> Pretty.ppName (prettyEnv env) name <+> text "cannot be resolved" <->
                                        table [(term, termInfo),
                                               (text "inferred type", ppNameContext (prettyEnv env) ctx),
                                               (text "candidates", ppAmbDocs docs),
                                               (text "hint", text "qualify the name?")])
                        return (Left docs)
                else return (Left docs)


-- resolve an implicit argument name to an expression
resolveImplicitName :: Name -> Type -> Range -> Range -> Inf (Expr Type, Doc)
resolveImplicitName name tp contextRange range
  = do res <- resolveImplicitArg True {-disambiguate-} True {-allow unit fun val for conversions -}
                                 (implicitTypeContext tp) range [(isInfoValFunExt, name)]
       penv <- getPrettyEnv
       case res of
         Right iarg   -> do traceDefDoc $ \penv -> text "resolved implicit" <+> prettyImplicitAssign penv "?" name iarg False
                            return (toImplicitArgExpr range iarg, prettyImplicitArg penv iarg)
         Left docs    -> do (term,termInfo) <- getTermDoc "context" contextRange
                            infError range
                                (text "cannot resolve implicit parameter" <->
                                table [(term, termInfo),
                                        (text "parameter",  text "?" <.> ppNameType penv (name,tp)),
                                        (text "candidates", ppAmbDocs docs),
                                        (text "hint", text "add a (implicit) parameter to the function signature?")])
                            return (Var name False range, Lib.PPrint.empty)


ppAmbDocs :: [Doc] -> Doc
ppAmbDocs docs
  = if null docs
      then text "..."
      else let cutdocs = take 10 docs ++ (if length docs > 10 then [text "..."] else [])
           in align (vcat cutdocs)


-----------------------------------------------------------------------
-- Resolving implicit names
-----------------------------------------------------------------------

-- Resolve an implicit argument fully
resolveImplicitArg :: Bool -> Bool -> NameContext -> Range -> [(NameInfo -> Bool, Name)] -> Inf (Either [Doc] (ImplicitArg))
resolveImplicitArg allowDisambiguate allowUnitFunVal ctx range roots
  = do env <- getEnv
       sel <- resolveImplicitArgEx allowDisambiguate allowUnitFunVal (allowInfiniteChains env) [] ctx range roots
       case sel of
         Found iarg -> return (Right iarg)
         _          -> do penv <- getPrettyEnv
                          return $ Left (map (prettyImplicitArg penv) (allCandidates sel))

-- Resolve an implicit argument fully. This is recursively used with the `chain` of previously resolved implicit names
resolveImplicitArgEx :: Bool -> Bool -> Bool -> [TypedArg] -> NameContext -> Range -> [(NameInfo -> Bool, Name)] -> Inf ImplicitSelect
resolveImplicitArgEx allowDisambiguate allowUnitFunVal allowInfiniteChains chain ctx range roots
  = do candidates1 <- concatMapM (\(infoFilter,name) -> lookupImplicitArg allowUnitFunVal infoFilter name ctx range) roots
       let candidates2 = filter (not . existConCreator candidates1) candidates1
           sorted = sortCandidates candidates2
      --  when (length chain >= 4) $
      --     traceDefDoc $ \penv -> text "resolveImplicitArg: chain:" <+> list (map (prettyTypedArg penv) chain) <.> text ", continue with:" <->
      --                             indent 2 (vcat (map (prettyTypedArg penv) (map fst sorted)))
       resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range None sorted
  where
    -- always prefer a creator definition over a plain constructor if it exists
    existConCreator :: [TypedArg] -> TypedArg -> Bool
    existConCreator candidates (name,info,_)
      = isInfoCon info && any (\(iargName,_,_) -> iargName == cname) candidates
      where
        cname = newCreatorName name

    sortCandidates :: [TypedArg] -> [(TypedArg,[(Name,Type)] {- further implicits to resolve-} )]
    sortCandidates candidates
      = let -- find for each candidate which further implicits need to be resolved
            icandidates  = map (implicitsToResolve ctx) candidates
            -- now we can sort them according to their cost
            cost ((name,info,_),iargs)  = ( -(iargScopeDepth name info) -- inner scopes first
                                          , length iargs                -- least further implicits arguments first
                                          )
        in sortBy (\x y -> compare (cost x) (cost y)) icandidates


-- Resolve the best candidate for an implicit parameter
resolveUniquely :: Bool -> Bool -> [TypedArg] -> NameContext -> Range -> ImplicitSelect -> [(TypedArg,[(Name,Type)])] -> Inf ImplicitSelect
resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range current []
  = -- nothing further to explore
    do -- traceDefDoc $ \penv -> text "resolveUniquely: explored all solutions:" <+> prettySelect penv current
       return current

resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range current@(Amb ambs@(_:_:_)) candidates
  = -- once we are ambiguous with 2 or more (possible) solutions, we don't need to explore further options
    do -- traceDefDoc $ \penv -> text "resolveUniquely: ambigious:" <+> prettySelect penv current
       let extra = map (toImplicitArg [] . fst) candidates  -- include all remaining potential candidates in the error message?
       return (Amb (ambs ++ extra))

resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range (Found current) (((qname,info,_),_):_)
  | allowDisambiguate && iaScopeDepth current > iargScopeDepth qname info
  = -- if we can disambiguate, the inner scope is always preferred (assuming sorted candidates)
    do -- traceDefDoc $ \penv -> text "resolveUniquely: found innermost solution:" <+> prettyImplicitArg penv current
       return (Found current)

resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range current (next@((qname,info,rho),ipars) : candidates)
  | not allowInfiniteChains && not (isDecreasingChain chain ctx qname rho)
  = -- if this might lead to an infinite derivation
    do -- traceDefDoc $ \penv -> text "resolveUniquely: infinite derivation:" <->
       --                      indent 2 (vcat (map (prettyTypedArg penv) (reverse (fst next:chain))))
       let iarg = toImplicitArg [(pname, emptyImplicitArg) | (pname,_) <- ipars] (fst next)
           sel  = Infty iarg
       resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range (merge current sel) candidates

resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range current candidates
  | length chain > resolveMaxChainDepth
  = do traceDefDoc $ \penv -> text "resolve implicit, cut off long chain:" <->
                               indent 2 (vcat (map (prettyTypedArg penv) (reverse chain)))
       let sels = map (Infty . toImplicitArg [] . fst) candidates
       return $! foldr merge None sels

resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range current (next@((name,info,rho),ipars) : candidates)
  = do -- recursively resolve the required implicit parameters
       -- traceDefDoc $ \penv -> text "resolveUniquely: resolve next candidate:" <+> prettyTypedArg penv (fst next)
       --                          <-> indent 2 (text "current:" <+> prettySelect penv current)
       sel <- resolveImplicitParameters allowDisambiguate allowInfiniteChains chain range next
       resolveUniquely allowDisambiguate allowInfiniteChains chain ctx range (merge current sel) candidates


-- Resolve recursively any further required implicit parameters
resolveImplicitParameters :: Bool -> Bool -> [TypedArg] -> Range -> (TypedArg,[(Name,Type)]) -> Inf ImplicitSelect
resolveImplicitParameters allowDisambiguate allowInfiniteChains chain range (current@(name,info,rho),ipars)
  = resolve [] ipars
  where
    chainNew
      = current : chain

    resolve :: [(Name,ImplicitArg)] -> [(Name,Type)] -> Inf ImplicitSelect
    resolve acc []
      = return (Found (ImplicitArg name info rho (reverse acc)))
    resolve acc (par:pars)
      = do sel <- resolveImplicitParameter allowDisambiguate allowInfiniteChains chainNew range par
           case sel of
             Found iarg -> do -- keep resolving
                              resolve ((fst par,iarg):acc) pars
             _          -> do -- give up early if we cannot resolve a parameter
                              let makePars iarg   = reverse acc ++ [(fst par, iarg)] ++ [(pname, emptyImplicitArg) | (pname,_) <- pars]
                                  extendIarg iarg = ImplicitArg name info rho (makePars iarg)
                              return $ mapCandidates extendIarg sel

-- recursively resolve an implicit parameter
resolveImplicitParameter :: Bool -> Bool -> [TypedArg] -> Range -> (Name, Type) -> Inf ImplicitSelect
resolveImplicitParameter allowDisambiguate allowInfiniteChains chain range (pname,ptp)
  = -- recursively resolve an implicit parameter
    let (pnameName,pnameExpr) = splitImplicitParamName pname
        newctx = implicitTypeContext ptp
    in resolveImplicitArgEx allowDisambiguate True {- allow unit val -} allowInfiniteChains chain newctx
                            (endOfRange range) -- use end of range to deprioritize with hover info
                            [(isInfoValFunExt,pnameExpr)]

-- Have a previously tried to derive this parameter?
isDecreasingChain :: [TypedArg] -> NameContext -> Name -> Type -> Bool
isDecreasingChain chain ctx qname tp
  = case filter (\(pname,_,_) -> pname == qname) chain of  -- find only matching definition in the chain
      []                  -> True                      -- never visited before
      prevtps  ->
        if length prevtps < decreasingWithin then True -- Not enough to decide yet (we want to be able to grow a bit at the beginning)
        else
          let limited = take decreasingWithin prevtps -- the last *k* elements in the same partition.
          in weight tp < (maximum $ map (\(_, _, tp) -> weight tp) limited) -- we want the instantiated type to "smaller" than any previous one (i.e. at least smaller than the maximum)
  where
    -- Note: pname and qname are fully qualified resolved names with their instantiated types
    --   pname=qname : forall as. t           e.g. list/show : (xs : list<a>, ?show : a -> string ) : string
    --
    -- This means ptp and tp are instantiations of the same type scheme (and only differ in substitution):
    --   ptp = t[as:=ts1]  tp = t[as:=ts2]
    --
    -- We can now put a decreasing measure on those types to see if the instantiation is getting smaller
    -- which ensures termination (but also prevents some programs to be accepted even though finite derivations exist (see `test/overload/wrong/blowup6.kk`))
    -- Our current measure is the number of constructors in the types of the implicit parameters.
    -- (and an even more precise one would be the size of each instantiated type variable used in implicits in a particular lexical order)

    weight :: Type -> Int
    weight tp
      = case splitFunScheme tp of
          Just (_,pars,eff,res) -> let (_,_,implicits) = splitOptionalImplicit pars
                                   in weightParams implicits
          _                     -> 0

    weightParams :: [(Name,Type)] -> Int
    weightParams pars
      = sum (map (weightType . snd) pars)

    weightType :: Type -> Int
    weightType tp
      = case tp of
          TForall tvars t      -> weightType t
          TFun tpars teff tres -> weightParams tpars + weightType teff + weightType tres
          TApp t targs         -> weightType t + sum (map weightType targs)
          TSyn _ _ t           -> weightType t
          TCon _               -> 1
          TVar _               -> 0



-- Find for an typed argument if it needs further implicits to be solved
implicitsToResolve :: NameContext -> TypedArg -> (TypedArg,[(Name,Type)])
implicitsToResolve ctx targ@(name,info,rho)
  = let iargs = case splitFunType rho of
                  Just (ipars,ieff,iresTp)  | any Op.isOptionalOrImplicit ipars
                    -- recursively resolve further required implicit parameters
                    -> implicitsOf ipars
                  _ -> []
    in (targ,iargs)
  where
    implicitsOf :: [(Name,Type)] -> [(Name,Type)]
    implicitsOf ipars
      = -- only return implicits that were not already given explicitly by the user (in `named`)
        let (fixed,optional,implicits)  = splitOptionalImplicit ipars
            alreadyGiven     = case ctx of
                                  CtxFunTypes partial fixedArgs named mbResTp
                                    -> let namedAsFixed = map fst (take (length fixedArgs - length fixed - length optional) implicits)
                                       in namedAsFixed ++ map fst named
                                  CtxFunArgs partial n named mbResTp
                                    -> let namedAsFixed = map fst (take (n - length fixed - length optional) implicits)
                                       in namedAsFixed ++ named
                                  _ -> []
            toResolve        = filter (\(name,_) -> let (pname,_) = splitImplicitParamName name
                                                    in not (pname `elem` alreadyGiven)) implicits
        in -- trace ("implicitsToResolve: " ++ show (map (fst . splitImplicitParamName . fst) toResolve) ++ ", " ++ show alreadyGiven) $
           toResolve


-----------------------------------------------------------------------
-- Looking up application names and implicit names
-----------------------------------------------------------------------

lookupImplicitArg :: Bool -> (NameInfo -> Bool) -> Name -> NameContext -> Range -> Inf [TypedArg]
lookupImplicitArg allowUnitFunVal infoFilter name ctx range
  = do -- traceDefDoc $ \penv -> text "lookupImplicitArg:" <+> ppNameCtx penv (name,ctx) <+> text ", previous:" <+> list (map (ppNameCtx penv) previousCtxs)
       candidates0 <- lookupNames infoFilter name ctx range
       candidates  <- case ctx of
                        -- for implicits we also allow conversion unit functions for values
                        -- if `expect` is a type variable we may need to remove duplicate candidates here.
                        CtxType expect | allowUnitFunVal && not (isFun expect)
                           -> do candidates1 <- lookupNames infoFilter name (CtxFunTypes False [] [] (Just expect)) range
                                 return (nubBy (\(_,info1,_) (_,info2,_) -> infoCName info1 == infoCName info2)
                                               (candidates0 ++ candidates1))
                        _  -> return candidates0
       -- add implicit constraints
       iargs <- case ctx of
                  CtxType expect -> do mbiarg <- checkImplicitConstraint name expect range range
                                       case mbiarg of
                                         Just iarg -> return [iarg]
                                         _         -> return []
                  _ -> return []
       return (candidates ++ iargs)


----------------------------------------------------------------
-- Lookup names
----------------------------------------------------------------

lookupFunName :: HasCallStack => Name -> Maybe (Type,Range) -> Range -> Inf (Maybe (Name,Type,NameInfo))
lookupFunName name mbType range
  = do matches <- lookupNameCtx isInfoFun name (maybeRToContext mbType) range
       case matches of
        []   -> return Nothing
        [(name,info)]  -> return (Just (name,infoType info,info))
        _    -> do env <- getEnv
                   infError range (text "identifier" <+> Pretty.ppName (prettyEnv env) name <+> text "cannot be resolved"
                                     <.> ppAmbiguous env hintQualify matches)
  where
    hintQualify = "qualify the name to disambiguate it?"

lookupNameCtx :: HasCallStack => (NameInfo -> Bool) -> Name -> NameContext -> Range -> Inf [(Name,NameInfo)]
lookupNameCtx infoFilter name ctx range
  = do candidates0 <- lookupNames infoFilter name ctx range
       let candidates = [(name,info) | (name,info,_) <- candidates0]
       -- traceDefDoc $ \penv -> text " lookupNameCtx:" <+> ppNameCtx penv (name,ctx) <+> colon
       --                       <+> list [Pretty.ppParam penv (name,rho) | (name,info,rho) <- candidates]
       case candidates of
         []  -> return candidates
         [_] -> return candidates
         _   -> case (filterInnerScopes candidates) of
                  [candidate] -> return [candidate]
                  _           -> return candidates
  where
    filterInnerScopes :: [(Name,NameInfo)] -> [(Name,NameInfo)]
    filterInnerScopes = filterInnerScopesEx compareScopeDepth

    filterInnerScopesEx cmpScope []  = []
    filterInnerScopesEx cmpScope (x:xs)
      = filter x [] xs
      where
        filter x acc []     = x : filterInnerScopesEx cmpScope (reverse acc)
        filter x acc (y:ys)
          = case cmpScope x y of
              LT -> filter y [] ys        -- continue with y, drop x and acc
              GT -> filter x acc ys       -- drop y
              EQ -> filter x (y:acc) ys

    compareScopeDepth (name1,info1) (name2,info2)
      = let sd1 = infoScopeDepth info1
            sd2 = infoScopeDepth info2
        in compare sd1 sd2


----------------------------------------------------------------
-- Error Helpers
----------------------------------------------------------------

checkCasingOverlaps :: Range -> Name -> [(Name,NameInfo)] -> Inf ()
checkCasingOverlaps range name matches
  = -- this is called when various definitions (possibly from different modules) match with a name
    -- we could check here that all these definitions agree on the casing
    -- .. but I think it is better to only complain if the actual definition
    -- used has a different casing to reduce potential conflicts between modules
    return ()

{--------------------------------------------------------------------------
  Implicit Constraints
--------------------------------------------------------------------------}

implicitConstraints :: [(Name,Name -> Type -> Maybe (Tvs -> ImplicitConstraint -> Inf Bool, Tvs -> ImplicitConstraint -> Inf (Core.Expr, Type)))]
implicitConstraints
  = [(nameHeapDiv, checkHeapDivConstraint)]

checkImplicitConstraint :: Name -> Type -> Range -> Range -> Inf (Maybe TypedArg)
checkImplicitConstraint name tp rangeContext range
  = case lookup name implicitConstraints of
      Just check
        -> case check name tp of
             Just (canResolve,resolve)
                -> do iarg <- addImplicitConstraint name tp canResolve resolve rangeContext range
                      return (Just iarg)
             Nothing -> return Nothing
      Nothing -> return Nothing

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

withHiddenTermDoc :: Range -> Doc -> Inf a -> Inf a
withHiddenTermDoc range doc inf
  = withEnv (\env -> env{ hiddenTermDoc = Just (range,doc) }) inf

inHiddenTermDoc :: Inf Bool
inHiddenTermDoc
  = do env <- getEnv
       case hiddenTermDoc env of
         Just _ -> return True
         _      -> return False

useHole :: Inf Bool
useHole
  = holeAllowed <$> updateSt (\st -> st{ holeAllowed = False } )

disallowHole :: Inf a -> Inf a
disallowHole action
  = do st0 <- updateSt (\st -> st{ holeAllowed = False })
       let prev = holeAllowed st0
       x <- action
       updateSt (\st -> st{ holeAllowed = prev })
       return x

allowHole :: Inf a -> Inf (a,Bool {- was the hole used? -})
allowHole action
  = do prev <- holeAllowed <$> updateSt (\st -> st{ holeAllowed = True })
       x <- action
       allowed <- holeAllowed <$> updateSt (\st -> st{ holeAllowed = prev })
       return (x,not allowed)


mapImplicitConstraints :: ([ImplicitConstraint] -> Inf (a,[ImplicitConstraint])) -> Inf a
mapImplicitConstraints f
  = do ics0 <- iconstraints <$> updateSt (\st -> st{ iconstraints = [] })
       (x,ics1) <- f ics0
       updateSt (\st -> st{ iconstraints = ics1 ++ iconstraints st })
       return x

scopeImplicitConstraints :: Inf a -> Inf a
scopeImplicitConstraints inf
  = do ics0 <- iconstraints <$> updateSt (\st -> st{ iconstraints = [] })
       -- traceDefDoc $ \penv -> text "scope ics:" <+> ppConstraints penv ics0
       x    <- traceIndent $ inf
       ics1 <- getImplicitConstraints
       --traceDefDoc $ \penv -> text "end scope: new ics:" <+> ppConstraints penv ics1 <+> text "++" <+> ppConstraints penv ics0
       updateSt (\st -> st{ iconstraints = ics1 ++ ics0 })
       return x

-- apply skolem substitution to unresolved implicit constraints
substImplicitConstraints :: Sub -> Inf ()
substImplicitConstraints sksub
  = do updateSt (\st -> st{ iconstraintsGamma = (sksub |-> (sub st |-> iconstraintsGamma st)) })
       ig <- iconstraintsGamma <$> getSt
       -- traceDefDoc $ \penv -> text "subst ics:" <+> Pretty.ppSub penv sksub <-> indent 2 (ppInfGamma penv{Pretty.showIds=True} ig)
       return ()

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

qualifyName :: Name -> Inf Name
qualifyName name
  = do env <- getEnv
       return (qualify (context env) name)

getModuleName :: Inf Name
getModuleName
  = do env <- getEnv
       return (context env)

getLocalVars :: Inf [(Name,Type)]
getLocalVars
  = do env <- getEnv
       return (filter (isTypeLocalVar . snd) (infgammaList (infgamma env)))

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

traceIndent :: Inf a -> Inf a
traceIndent inf
  = withEnv (\env -> env{ prettyEnv = (prettyEnv env){ Pretty.indentation = Pretty.indentation (prettyEnv env) + 2 } }) inf

traceDefDoc :: (Pretty.Env -> Doc) -> Inf ()
traceDefDoc f
  = do dnames <- currentDefNames
       traceDoc (\penv -> hcat (intersperse (text ".") (map (Pretty.ppName penv) dnames)) <+> text ":" <+> f penv)

traceDoc :: (Pretty.Env -> Doc) -> Inf ()
traceDoc f
  = do penv <- getPrettyEnv
       trace (show (indent (Pretty.indentation penv) $ f penv)) $ return ()

ppNameType penv (name,tp)
  = Pretty.ppName penv name <+> colon <+> Pretty.ppType penv tp
