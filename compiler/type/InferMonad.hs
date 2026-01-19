
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
