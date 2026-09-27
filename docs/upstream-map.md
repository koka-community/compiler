# Port to reference-compiler name map

Where a definition in this repository came from in the Haskell reference
compiler (`koka-lang/koka`, `src/`). The mapping lives here rather than in
comments: a comment that names an upstream function says nothing about the
code it sits above, and goes stale the moment either side moves -- or the
moment this port stops tracking upstream at all. Code comments state what must
hold; this table says where to look when comparing the two implementations.

Generated from the comments that carried these references, so it is a
SNAPSHOT: nothing keeps it current, and a row is only a hint about where to
start reading.

| port module | definition | reference compiler |
| --- | --- | --- |
| `backend/c/box` | `argTps` | `Box.hs` |
| `backend/c/helpers` | `new-var-names` | `newVarNames 0 = return []` |
| `backend/c/helpers` | `x` | `cstring` |
| `backend/c/parc-reuse` | `rux-to-assign` | `ruToAssign (ParcReuse.hs keeps its own copy, distinct from ParcReuseSpec's)` |
| `backend/c/parc-reuse` | `available` | `Available = IntMap [ReuseInfo]` |
| `backend/c/parc-reuse` | `deconstructed` | `Deconstructed = NameMap (Maybe Pattern, Int {-byte size-}, Int {-scan fields-})` |
| `backend/c/parc-reuse` | `reused` | `Reused = Set TName` |
| `backend/c/parc` | `tnameset` | `TNames = S.Set TName` |
| `backend/js/from-core` | `reserved-words` | `all isDigit (tail s)` |
| `common/id` | `id-set` | `IdSet = IntSet` |
| `common/name-collections` | `name-set` | `NameSet = Data.Set Name` |
| `common/name-collections` | `qname` | `Just [(qname,x)]` |
| `common/name-collections` | `qname-map/union` | `M.insertWith (safeCombine "insert") key new old` |
| `common/nice` | `x` | `insertWith` |
| `common/parse` | `parse-sep-end-by` | `semis p = sepEndBy p semiColons1` |
| `common/parse` | `parse-import-alias` | `importAlias` |
| `common/unique` | `unique-name-from` | `uniqueNameFrom baseName = toHiddenUniqueName i "uniq" baseName` |
| `compile/build-context` | `session-revalidate` | `buildcRoots` |
| `compile/build-context` | `check` | `buildcLookupTypeOf (qualify mainModName (newName "@expr"))` |
| `compile/build-context` | `st'` | `phaseVerbose 3 "validate" (Build.hs:921)` |
| `compile/build-context` | `wall-before-waves` | `phaseVerbose 3 "build order" (Build.hs:609)` |
| `compile/build-context` | — | `buildcRoots` |
| `compile/build` | `allow-at` | `ShowKindSigs` |
| `compile/build` | `typed-module` | `PhaseTyped` |
| `compile/build` | `s` | `searchPathsCanonical` |
| `compile/build` | `updirs` | `moduleLex (Build.hs, dev-uv 2026-06-11 `dc11bd31a`)` |
| `compile/build` | `canonical-modname` | `coreImportsFromModules` |
| `compile/build` | `canonical-modname` | `moduleWaitForPubImports` |
| `compile/build` | `build-order` | `toBuildOrder` |
| `compile/build` | `defs-of` | `defsFromModules :: [Module] -> Defs` |
| `compile/build` | `lookup-default-handler` | `lookupDefaultHandler` |
| `compile/build` | `body0` | `addDefaultHandler` |
| `compile/build` | `tcMods` | `moduleTypeCheck` |
| `compile/build` | `fullDefs` | `moduleWaitForInlineImports` |
| `compile/build` | `rm` | `phase "check" (Build.hs:442)` |
| `compile/build` | `rm` | `phaseVerbose 3 "check done" (Build.hs:458)` |
| `compile/build` | `stop-typed` | `PhaseTyped` |
| `compile/build` | `stop-typed` | `buildcTypeCheck` |
| `compile/build` | `mainName` | `mainEntryName` |
| `compile/build` | `topt1` | `phaseVerbose 2 "optimize" (Build.hs:395)` |
| `compile/build` | `topt1` | `phaseVerbose 3 "optimize done" (Build.hs:407)` |
| `compile/build` | `ordered` | `codeGenLinkC` |
| `compile/build` | `docKGamma` | `CodeGen.hs:114` |
| `compile/build` | `needsWrapper` | `addShow` |
| `compile/cc` | `cc/flags-build` | `ccFlagsBuildFromFlags` |
| `compile/cc` | `gnu-warn` | `gnuWarn (Options.hs:1194)` |
| `compile/cc` | `strip-ext` | `notext` |
| `compile/cc` | `cc-gcc` | `ccGcc (Options.hs:1199)` |
| `compile/cc` | `cc-msvc` | `ccMsvc (Options.hs:1232)` |
| `compile/code-gen` | `pp-env-from-flags` | `prettyEnvFromFlags` |
| `compile/code-gen` | `code-gen` | `codeGen (minus linking)` |
| `compile/code-gen` | `pp-prec` | `phaseVerbose 2 "codegen" (Build.hs:313)` |
| `compile/code-gen` | `isCTarget` | `CodeGen.hs:97` |
| `compile/code-gen` | `ifaceDoc` | `ifaceDoc` |
| `compile/code-gen` | `bcoreDoc` | `CodeGen.hs:294 (inside the C backend)` |
| `compile/code-gen` | `exePath` | `codeGenLinkExe` |
| `compile/code-gen` | — | `codeGenLinkExe` |
| `compile/code-gen` | — | `phaseVerbose 3 "codegen done" (Build.hs:324)` |
| `compile/link` | `search-c-library` | `searchCLibrary` |
| `compile/link` | `conan-settings-from-flags` | `conanSettingsFromFlags` |
| `compile/link` | `vcpkg-find-root` | `vcpkgFindRoot` |
| `compile/link` | `csyslibs-of-core` | `csyslibsFromCore` |
| `compile/link` | `copy-c-library` | `copyCLibrary` |
| `compile/link` | `ccompile-args` | `ccompile` |
| `compile/link` | `c` | `libs` |
| `compile/link` | `c` | `syslibs` |
| `compile/link` | `kklib-build` | `kklibBuild (CodeGen.hs)` |
| `compile/module` | `definitions` | `Definitions` |
| `compile/module` | `defs-from-modules` | `defsFromModules` |
| `compile/optimize` | `core-optimize` | `coreOptimize :: Flags -> Newtypes -> Gamma -> Inlines -> Core -> Error () (Core,[InlineDef])` |
| `compile/optimize` | `checkCoreDefs` | `checkCoreDefs title = when (coreCheck flags) $ checkCore False False penv gamma` |
| `compile/options` | — | `flagsNull` |
| `compile/options` | `package` | `getKokaDirs` |
| `compile/options` | `mode` | `Mode (Options.hs:125)` |
| `compile/options` | `flags/tpl` | `targetPlatformFromFlags` |
| `compile/options` | `flags/build-type` | `buildType (Options.hs:1178)` |
| `compile/options` | `build-variant` | `buildVariant` |
| `compile/options` | `flags/show-type-sigs` | `showTypeSigs (Options.hs:140)` |
| `compile/options` | `unquote` | `unquote` |
| `compile/options` | `undelim-paths` | `undelimPaths (Common/File.hs)` |
| `compile/options` | `parse-size` | `parseSize` |
| `compile/options` | `read-html-bases` | `readHtmlBases` |
| `compile/options` | `fflag` | `fflag (Options.hs, `where` block)` |
| `compile/options` | `fnum` | `fnum` |
| `compile/options` | — | `--include` |
| `compile/options` | `koka-flags` | `optionsAll` |
| `compile/options` | `parse-options` | `parseOptions` |
| `compile/options` | `host-os-name` | `hostOsName` |
| `compile/options` | `cc-check-exist` | `ccCheckExist` |
| `compile/options` | `cc-from-path` | `ccFromPath (Options.hs:1261)` |
| `compile/options` | `get-koka-dirs` | `getKokaDirs` |
| `compile/options` | `environment` | `environment (Options.hs:733)` |
| `compile/options` | `process-initial-options` | `processInitialOptions (Options.hs:831)` |
| `compile/options` | `is-target-c` | `processOptions` |
| `compile/options` | `is-target-c` | `isTargetC` |
| `compile/options` | `triplet-os-name` | `tripletOsName` |
| `compile/options` | `process-extra-options` | `processDerivedOptions (Options.hs:791)` |
| `compile/options` | `process-extra-options` | `processExtraOptions` |
| `compile/type-check` | `importMap` | `importMapFromCoreImports` |
| `compile/type-check` | `import-map-from-core-imports` | `importMapFromCoreImports` |
| `core/binding-groups` | `deps` | `S.intersection (S.fromList defNames) . fv` |
| `core/check-fbip` | `alloc-tree` | `AllocTree` |
| `core/check-fbip` | `check-fbip` | `checkFBIP` |
| `core/check-fbip` | `d` | `M.maxViewWithKey (gammaNm out)` |
| `core/check-fbip` | `lookup-fip` | `borrowedLookupFip` |
| `core/check` | `check-core` | `checkCore` |
| `core/check` | `check-defgroups` | `checkDefGroups dgs body` |
| `core/check` | `core-name-info` | `coreNameInfo` |
| `core/check` | `tforall` | `tForall` |
| `core/core` | `con-repr-ctx-path` | `conReprCtxPath` |
| `core/core` | `tnames/empty` | `type TNames = S.Set TName` |
| `core/core` | `cmp` | `instance Ord TName` |
| `core/core` | `deps` | `type Deps = S.Set Name` |
| `core/corevar` | `tvs-sorted` | `tvsList` |
| `core/ctail` | `ctail-def-group` | `ctailDefGroup` |
| `core/ctail` | `ctail-is-value-type-name` | `isValueType` |
| `core/ctail` | `ctail-unique-tname` | `uniqueTName` |
| `core/ctail` | `ctail-fun-expr` | `getCTailFun` |
| `core/ctail` | `ctail-with-current-def` | `withCurrentDef` |
| `core/ctail` | `ctail-with-context` | `withContext` |
| `core/inline` | `inline-defs` | `inlineDefs penv inlineMax inlines` |
| `core/inline` | `local-simplify` | `uniqueSimplify penv False True 3 0` |
| `core/inline` | `inl-lookup` | `inlLookup` |
| `core/inline` | `inl-extend` | `inlExtend` |
| `core/inline` | `extract-inline-defs` | `Core.Inlines.extractInlineDefs` |
| `core/inline` | `extract-inline-def-rec` | `extractInlineDefRec` |
| `core/inlines` | `inlines-filter` | `inlinesFilter` |
| `core/monadic-lift` | `lift-def` | `liftDefGroup True (DefRec defs)` |
| `core/open-resolve` | `resolve` | `resOpen` |
| `core/parse` | `prov` | `pimportProvenance` |
| `core/parse` | `tp` | `prange` |
| `core/parse` | `lqname` | `envLookupVar` |
| `core/simplify` | `simp-settings` | `SEnv` |
| `core/simplify` | `simplify-defs` | `simplifyDefs` |
| `core/simplify` | `top-down-let` | `topDownLet` |
| `core/simplify` | `bind-exprs` | `bindExprs` |
| `core/simplify` | `kmatch` | `kmatch*` |
| `core/simplify` | `occur` | `Occur` |
| `core/simplify` | `occurs` | `M.NameMap Occur` |
| `core/specialize` | `specialize` | `specialize :: Inlines -> Env -> CorePhase b () (Pretty.Env dropped)` |
| `core/specialize` | `spec-lookup` | `speclookup` |
| `core/specialize` | `spec-one-def-group` | `specOneDefGroup = mapMDefGroup specOneDef` |
| `core/specialize` | `spec-one-expr` | `specOneExpr thisDefName = descend (PR #906)` |
| `core/specialize` | `new-args` | `newArgs gArgs args = zipWith fromMaybe args gArgs` |
| `core/specialize` | `sic` | `specInnerCalls` |
| `core/specialize` | `replace-call` | `replaceCall` |
| `core/specialize` | `has-spec-residual` | `hasSpecializableResidual (PR #899)` |
| `core/specialize` | `spec-simplify` | `uniqueSimplify defaultEnv False False 1 10` |
| `core/specialize` | `spec-comment` | `comment` |
| `core/specialize` | `extract-specialize-defs` | `extractSpecializeDefs :: Inlines -> DefGroups -> [InlineDef]` |
| `core/specialize` | `keep-fun-param` | `filterMaybe (isFun . tnameType)` |
| `core/specialize` | `spec-is-fun` | `isFun = isJust . splitFunScheme` |
| `core/specialize` | `used-in-this-def` | `usedInThisDef (defined but never used upstream; kept for fidelity)` |
| `core/specialize` | `multi-step-inlines` | `multiStepInlines` |
| `core/specialize` | `calls-specializable` | `Alt Maybe` |
| `core/specialize` | `spec-call-overlap` | `goCommon` |
| `core/specialize` | `spec-vars` | `vars` |
| `interpreter/command` | `edit-backspaces` | `edit` |
| `interpreter/command` | `expression` | `expression` |
| `interpreter/command` | `try-symbol` | `symbol` |
| `interpreter/command` | `try-special` | `special` |
| `interpreter/command` | `anything` | `anything` |
| `interpreter/command` | `command-line` | `commandLine` |
| `interpreter/interpret` | `get-command` | `getCommand` |
| `interpreter/interpret` | `target` | `Edit` |
| `interpreter/interpret` | `not-wired` | `showCommand` |
| `kind/import-map` | `imports-empty` | `importsEmpty` |
| `kind/import-map` | `extend` | `importsExtend` |
| `kind/infer-kind` | `inf-kgamma` | `M.Map Name InfKind` |
| `kind/infer-kind` | `get-nice` | `niceKindVars` |
| `kind/synthesize` | `current-data-info` | `synTypeDef` |
| `lib/isocline` | `with-readline` | `withReadLine` |
| `lib/log` | `phase-line` | `phaseShowIO` |
| `lib/scc` | `graph` | `Map.fromListWith (++)` |
| `lsp/code-action` | `tp-forall` | `tpForall` |
| `lsp/code-action` | `user-tp` | `userTp` |
| `lsp/code-action` | `append-str` | `appendStr` |
| `lsp/code-action` | `syn-general-unary` | `synGeneralUnary` |
| `lsp/code-action` | `any-function-fields` | `synShowString` |
| `lsp/code-action` | `syn-overloaded` | `synOverloaded` |
| `lsp/code-action` | `syn-map` | `synMap` |
| `lsp/code-action` | `syn-binary-op` | `synBinaryOp` |
| `lsp/code-action` | `tuple-branch` | `tupleBranch` |
| `lsp/code-action` | `syn-equality` | `synEquality` |
| `lsp/code-action` | `syn-ord` | `synOrd` |
| `lsp/code-action` | `syn-order2` | `synOrder2` |
| `lsp/code-action` | `find-type` | `findType` |
| `lsp/code-action` | `gen` | `Core.runCorePhase 0` |
| `lsp/completion` | `completion-info-at` | `getCompletionInfo` |
| `lsp/completion` | `type-unifies` | `typeUnifies` |
| `lsp/completion` | `matches` | `filterInfix` |
| `lsp/completion` | `synonym-completions` | `synonymCompletions` |
| `lsp/completion` | `fun-item` | `makeFunctionCompletionItem` |
| `lsp/definition` | `definition` | `Handler/Definition.hs` |
| `lsp/definition` | `def-ranges` | `findDefLinks` |
| `lsp/diagnostics` | `items` | `termError` |
| `lsp/hover` | `hover-text` | `formatRangeInfoHover` |
| `lsp/hover` | `hover-text` | `formatRangeInfoHover` |
| `lsp/inlay-hints` | `inlay-hints` | `Handler/InlayHints.hs` |
| `lsp/inlay-hints` | `hints-for` | `createInlayHints` |
| `lsp/inlay-hints` | `qualifier-hints` | `qualifierHint` |
| `lsp/inlay-hints` | `implicit-hints` | `implicitsHint` |
| `lsp/inlay-hints` | `final-call-range` | `finalCallRange` |
| `lsp/inlay-hints` | `has-annotation` | `hasAnnot` |
| `lsp/pretty` | `pp-comment` | `ppComment` |
| `lsp/pretty` | `as-koka-code` | `asKokaCode` |
| `lsp/signature-help` | `first-id` | `firstId` |
| `lsp/signature-help` | `to-signature` | `getSignatureInformation` |
| `lsp/state` | `doc` | `LanguageServer/Monad.hs` |
| `lsp/symbols` | `make-symbol-select` | `makeSymbolSelect` |
| `lsp/symbols` | `spans-line` | `rangeSpansLine` |
| `main/driver` | `cwd` | `Main/Run.hs` |
| `main/driver` | `opts` | `getOptions` |
| `main/driver` | `opts` | `processInitialOptions` |
| `main/driver` | — | `Main/Run.hs` |
| `syntax/builders` | `builders/make-kind-handled` | `makeKindHandled` |
| `syntax/builders` | `clauseId` | `opSortString` |
| `syntax/colorize` | `cspan` | `cspan` |
| `syntax/colorize` | `fmt-html` | `fmtHtml` |
| `syntax/colorize` | `link-from-mod-name` | `linkFromModName` |
| `syntax/colorize` | `popup` | `popup` |
| `syntax/colorize` | `fmt-literate` | `fmtLiterate` |
| `syntax/colorize` | `html/compress` | `compress` |
| `syntax/colorize` | `transform1` | `transform` |
| `syntax/colorize` | `ends-before` | `after` |
| `syntax/colorize` | `remove-comment` | `Syntax.Colorize.removeComment` |
| `syntax/colorize` | `align` | `align` |
| `syntax/colorize` | `end-with-dot` | `endWithDot` |
| `syntax/colorize` | `fmt-qualify` | `fmtLexs` |
| `syntax/colorize` | `fmt-comment` | `fmtComment` |
| `syntax/colorize` | `show-doc` | `showDoc` |
| `syntax/colorize` | `colorize` | `--html=2` |
| `syntax/colorize` | `colorize` | `colorizeLexemes` |
| `syntax/gen-doc` | `link-to-source` | `linkToSource` |
| `syntax/gen-doc` | `lit-env` | `highlightType` |
| `syntax/gen-doc` | `show-types` | `showTypes` |
| `syntax/gen-doc` | `show-param` | `showParam` |
| `syntax/gen-doc` | `show-decl-type` | `showDeclType` |
| `syntax/gen-doc` | `val` | `genDoc` |
| `type/assumption` | `gamma/single` | `gammaSingle` |
| `type/assumption` | `pp-gamma` | `fill maxwidth (prettyName cscheme name) <.> typeColon <+> nice` |
| `type/infer-effect` | `subst-nice` | `substNice` |
| `type/infer-effect` | `realias-type` | `realiasType` |
| `type/infer-effect` | `ignore-errors` | `ignoreErrors (residue InferMonad.hs)` |
| `type/infer-effect` | `solve-iconstraint` | `solvedImplicitConstraint` |
| `type/infer-effect` | `subst-iconstraints` | `substImplicitConstraints` |
| `type/infer-effect` | `set-iconstraints` | `substImplicitConstraints` |
| `type/infer-effect` | `scope-implicit-constraints` | `scopeImplicitConstraints` |
| `type/infer-effect` | `map-implicit-constraints` | `mapImplicitConstraints` |
| `type/infer-effect` | `try-resolve-loop` | `mapImplicitConstraints` |
| `type/infer-helpers` | `add-divergent-effect` | `addDivergentEffect` |
| `type/infer-helpers` | `infer-rec-def2` | `inferRecDef2` |
| `type/infer-helpers` | `hints` | `show (infoRange ...)` |
| `type/infer-helpers` | `arrange` | `inferDefGroups` |
| `type/infer-helpers` | — | `runInfer` |
| `type/infer` | `expr/infer` | `inferExpr` |
| `type/infer` | `infer-def` | `inferDef` |
| `type/infer` | `stem` | `isInWrongNameSpace (defName def)` |
| `type/infer` | `infer-handler` | `createGammas` |
| `type/infer` | `run-infer` | `inferDefGroupX` |
| `type/infer` | `run-infer` | `arrange` |
| `type/infer` | `zap-subst` | `zapSubst (residue InferMonad.hs)` |
| `type/infer` | `infer-types` | `runInfer` |
| `type/infer` | `infer-types` | `inferTypes` |
| `type/pretty` | `tv-scheme` | `M.Map TypeVar (Prec -> Doc)` |
| `type/type` | `flavour` | `instance Ord TypeVar` |
| `type/unify` | `pars-not-named` | `subsumeSubst` |
