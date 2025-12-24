# Migration Plan: InferMonad.hs → infer-effect.kk

## Overview
This document outlines a structured plan to migrate the remaining functions from Haskell's `InferMonad.hs` (1950 lines) to Koka's `infer-effect.kk`. The plan groups related functions by complexity and dependencies, starting with the easiest conversions.

---


## 📋 Migration Groups (Priority Order)

### GROUP 3: Name/Context Resolution Helpers (Medium Complexity)
**Effort: Medium | Dependencies: Gamma, NameInfo | Haskell→Koka Difficulty: Medium**

### GROUP 4: Error Reporting (Medium Complexity)
**Effort: Medium | Dependencies: Error/Range infrastructure | Haskell→Koka Difficulty: Medium**

Error and warning generation functions.

2. **Range-aware error messages**
   - `withNoRangeInfo`: Temporarily disable range map (lines 1663-1671)
   - `withNiceNames`: Create nice variable names (lines 1672-1679)
   - `lookupNiceName`: Lookup a nice name (lines 1680-1685)
   - `withHiddenTermDoc`: Hide term in error (lines 1690-1691)
   - `inHiddenTermDoc`: Check if hidden (lines 1694-1700)
   - `getTermDoc`: Get display term + source range (lines 1701-1708)

3. **Type/context-specific errors**
   - `typeError`: Report type mismatch (lines 504-510)
   - `typeError'`: Internal version with Env (lines 511-519)
   - `contextError`: Error in name context (lines 520-524)
   - `contextError'`: Internal version (lines 525-532)
   - `termError`: Error in term (lines 534-539)
   - `termError'`: Internal version (lines 540-551)
   - `unifyError`: Unification error (lines 437-503)
   - `unifyError'`: Full error handling with error mapping (lines 505-551)

**Dependencies**:
- Range/RangeInfo handling
- Core error reporting
- UnifyError types

**Estimated Lines**: ~300

---

### GROUP 5: Remaining Hole & Constraint Management
**Effort: Low-Medium | Dependencies: State management | Haskell→Koka Difficulty: Low**

Environment/state manipulation functions for holes and constraints. **Most with-* functions already done.**

1. **Hole management** (STILL TODO)
   - `useHole`: Consume hole allowance (lines 1709-1711)
   - `disallowHole`: Run action with holes disabled (lines 1713-1720)
   - `allowHole`: Run action with holes enabled, track usage (lines 1721-1728)

2. **Implicit constraint mapping**
   - `mapImplicitConstraints`: Transform constraint list + run action (lines 1729-1735)
   - `scopeImplicitConstraints`: Create scope boundary for constraints (lines 1736-1745)
   - `substImplicitConstraints`: Apply substitution to constraints (lines 1747-1753)

3. **Definition context** (STILL TODO)
   - `withDefName`: Set current definition name (lines 1886-1887)
   - `isNamedLam`: Check if in named lambda (lines 1890-1894)
   - `currentDefName`: Get current definition (lines 1879-1883)
   - `currentDefNames`: Get definition name stack (embedded in currentDefName)
   - `qualifyName`: Fully qualify a name (lines 1895-1899)
   - `getModuleName`: Get current module (lines 1900-1904)
   - `freeInGamma`: Get free vars in gamma (lines 1905-1911)
   - `getLocalVars`: Get local variable bindings (lines 1912-1916)
   - `lookupInfName`: Look up inference-time name (lines 1917-1926)
   - `findDataInfo`: Find data constructor info (lines 1927-1932)

4. **Tracing** (STILL TODO)
   - `traceIndent`: Increase indentation for traces (lines 1934-1935)
   - `traceDefDoc`: Trace with current definition context (lines 1938-1942)
   - `traceDoc`: General tracing (lines 1943-1948)

**Dependencies**:
- Effect system (state access)
- Substitution (Sub)
- Gamma/environment access

**Estimated Lines**: ~200

---

### GROUP 6: Unification & Constraint Resolution (High Complexity)
**Effort: High | Dependencies: Unify module, Type operations | Haskell→Koka Difficulty: High**

Complex inference operations that require careful handling.

1. **Type checking context**
   - `Context` type (Check | Infer) - lines 323-327
   - `inferUnify`: Unify expected vs actual type (lines 333-342)
   - `inferUnifies`: Unify multiple types (lines 343-352)
   - `inferSubsume`: Subsumption checking (lines 354-365)

2. **Skolemization**
   - `withSkolemized`: Apply type with fresh skolem variables (lines 377-396)
   - `checkSkolemEscape`: Detect skolem variable escape (lines 397-415)

3. **Unification helpers**
   - `doUnify`: Run unification, return Either (lines 417-426)
   - `occursInContext`: Check occurs in free vars (lines 428-435)

4. **Implicit constraint checking**
   - `checkImplicitConstraint`: Check constraint for a type (lines 1454-1464)
   - `resolveImplicitConstraints`: Resolve all constraints to core expressions (lines 1465-1480)
   - `tryResolveImplicitConstraints`: Try resolution without failing (lines 1482-1511)
   - `implicitConstraints`: List of constraint checkers (lines 1450-1451)
   - `checkHeapDivConstraint`: Special case for @hdiv (lines 1514-1520)

5. **Heap divergence constraints**
   - `canResolveHeapDivConstraint`: Check if @hdiv can be resolved (lines 1526-1535)
   - `implicitConstraintType`: Get type of constraint (lines 1537-1545)
   - `resolveHeapDivConstraint`: Actually resolve @hdiv constraint (lines 1546-1604)

**Dependencies**:
- Unify module (runUnify, unification errors)
- Type substitution and operations
- Core expression building
- Effect operations

**Estimated Lines**: ~400

**Complexity Notes**:
- Heavy interaction with type class system
- Core.Expr and Core.ConRepr construction
- Multiple error paths and pattern matching

---

### GROUP 7: Name Resolution (Very High Complexity)
**Effort: Very High | Dependencies: Gamma, NameContext, all others | Haskell→Koka Difficulty: Very High**

The most complex part - extensive name lookup and implicit argument resolution.

1. **Core name resolution**
   - `resolveName`: Generic name lookup with optional type (lines 555-566)
   - `resolveRhsName`: RHS name lookup with typed fallback (lines 567-581)
   - `resolveFunName`: Function name lookup with context (lines 583-589)
   - `resolveConName`: Constructor name lookup (lines 590-594)
   - `resolveConPatternName`: Pattern constructor lookup (lines 595-604)
   - `resolveNameEx`: Core implementation with filters (lines 606-696)

2. **Application and implicit name lookup**
   - `lookupAppName`: Look up with partial application context (lines 697-737)
   - `resolveImplicitName`: Resolve implicit argument names (lines 738-755)
   - `ppAmbDocs`: Format ambiguous candidates (lines 756-762)

3. **Implicit argument resolution**
   - `resolveImplicitArg`: Single-level resolution (lines 900-908)
   - `resolveImplicitArgEx`: Multi-level with chain tracking (lines 910-937)
   - `resolveUniquely`: Find best candidate among multiple (lines 939-980)
   - `resolveImplicitParameters`: Recursively resolve dependencies (lines 982-1001)
   - `resolveImplicitParameter`: Single parameter resolution (lines 1003-1011)
   - `isDecreasingChain`: Detect infinite chains (lines 1017-1060)
   - `implicitsToResolve`: Extract implicit parameter requirements (lines 1062-1072)

4. **Low-level lookup**
   - `lookupImplicitArg`: Find implicit arg candidates (lines 1093-1117)
   - `lookupFunName`: Find function by name (lines 1119-1130)
   - `lookupNameCtx`: Lookup with name context filter (lines 1131-1164)
   - `lookupNames`: Generic lookup returning Rho (lines 1166-1179)
   - `lookupLocalName`: Check local scope (lines 1181-1189)
   - `lookupGlobalName`: Check global scope (lines 1191-1208)
   - `filterMatchNameContext`: Filter matches by context (lines 1210-1214)
   - `filterMatchNameContextEx`: Filter with Rho instantiation (lines 1215-1270)

**Dependencies**:
- All previous groups
- Gamma lookup/extend operations
- Type instantiation
- Substitution
- Effect handling

**Estimated Lines**: ~700

**Complexity Notes**:
- Most interdependent functions in the file
- Pattern matching on multiple type constructors
- Context-sensitive filtering logic
- Recursive implicit argument resolution with cycle detection
- Error handling and ambiguity reporting

---

### GROUP 8: Type Instantiation & Generalization (Very High Complexity)
**Effort: Very High | Dependencies: Type system, Core | Haskell→Koka Difficulty: Very High**

Most complex algorithm - polymorphic type handling.

1. **Instantiation**
   - `instantiate`: Default instantiation (line 78-79)
   - `instantiateEx`: Instantiation with existential handling (lines 81-89)
   - `instantiateNoEx`: Instantiation without existential (lines 90-98)

2. **Generalization**
   - `generalize`: Generalize type with optional constraint scoping (lines 5-10)
   - `generalizeX`: Core generalization algorithm (lines 11-64)
   - Handles:
     - Type variables already forall-quantified
     - Implicit constraint resolution
     - Type normalization
     - Fresh bound variable creation
     - Core type lambda generation

3. **Effect improvement**
   - `improve`: Improve type by isolating effects (lines 66-76)

4. **Effect isolation**
   - `isolate`: Remove unnecessary heap effects (lines 100-184)
   - Complex pattern matching on effects
   - Constraint filtering

**Dependencies**:
- All type operations from GROUP 2
- Substitution and unification
- Core.addTypeLambdas, quantifyType
- implicit constraint resolution

**Estimated Lines**: ~200

**Complexity Notes**:
- Core algorithm of type inference
- Multiple passes (instantiate, normalize, generalize)
- Fresh variable generation
- Type lambda construction
- Constraint ordering and scoping

---

### GROUP 9: Monad Infrastructure (Foundational - May Partially Exist)
**Effort: High | Dependencies: Base Koka | Haskell→Koka Difficulty: High**

Infrastructure for the inference monad. **Some may already be in effect system.**

1. **Run infrastructure**
   - `runInfer`: Execute inference computation (lines 1610-1619)
   - Initialize Env and St
   - Handle results/errors

2. **Error handling**
   - `tryRun`: Catch errors and return Maybe (lines 1632-1635)
   - `ignoreErrors`: Error recovery with fallback (lines 1637-1643)

3. **State access**
   - `withEnv`: Temporarily modify environment
   - `updateSt`: Update state with function
   - `getSt`: Get current state
   - `getEnv`: Get current environment

4. **Monad combinators**
   - May already be abstracted via Koka's effect system

**Dependencies**:
- Base monad/effect infrastructure
- Error handling types

**Estimated Lines**: ~150

**Note**: Most of this may already be expressed through Koka's effect system.

---

### GROUP 10: Extension/Context Management (Medium Complexity)
**Effort: Medium | Dependencies: Gamma, InfGamma | Haskell→Koka Difficulty: Medium**

Managing gamma extensions during type checking.

1. **Gamma extension**
   - `extendGammaCore`: Extend gamma from core definitions (lines 1759-1772)
   - `extendGamma`: Extend gamma with name-info pairs (lines 1775-1818)
   - `coreDefInfoX`: Extract name-info from core def (line 1774)
   - Name overlap checking

2. **Inf-gamma extension**
   - `extendInfGammaCore`: Same for InfGamma (lines 1820-1830)
   - `extendInfGamma`: Simple extension (lines 1832-1834)
   - `extendInfGammaEx`: With ignores and topLevel (lines 1836-1850)
   - `createCanonicalName`: Canonical name resolution (lines 1852-1870)

3. **Type context**
   - `withGammaType`: Extend gamma with type info (lines 1872-1878)

**Dependencies**:
- Gamma operations
- InfGamma operations
- Name overlap detection

**Estimated Lines**: ~150

---

## 📊 Summary Table

| Group | Category | Est. Lines | Priority | Dependencies | Complexity |
|-------|----------|-----------|----------|------|------------|
| 1 | Utilities | 100 | 1 | Basic types | ⭐ Easy |
| 2 | Type Manipulation | 250 | 2 | Type ops | ⭐⭐ Low |
| 3 | Name/Context Helpers | 200 | 3 | Gamma | ⭐⭐ Low |
| 4 | Error Reporting | 300 | 3 | Range/Error | ⭐⭐ Low |
| 5 | Hole/Constraint Mgmt | 200 | 4 | State | ⭐⭐ Low |
| 6 | Unification | 400 | 5 | Unify | ⭐⭐⭐ High |
| 7 | Name Resolution | 700 | 6 | Gamma/All | ⭐⭐⭐⭐ Very High |
| 8 | Instantiation/Gen | 200 | 7 | All | ⭐⭐⭐⭐ Very High |
| 9 | Monad Infra | 150 | 8 | Base | ⭐⭐⭐ High |
| 10 | Extension/Context | 150 | 9 | Gamma | ⭐⭐ Medium |

**Total Estimated Lines**: ~2,600 (covers all of InferMonad.hs)

---

## 🗺️ Recommended Migration Sequence

1. **Phase 1** (Foundation - ~550 lines): Groups 1, 2, 3, 4
   - Establishes all utility and type manipulation infrastructure
   - No monad complexity

2. **Phase 2** (State Management - ~350 lines): Groups 5, 10
   - Integrates state access and gamma extension
   - Prepares for monad-heavy operations

3. **Phase 3** (Basic Inference - ~400 lines): Groups 6, 9
   - Unification and monad infrastructure
   - Foundation for complex algorithms

4. **Phase 4** (Advanced - ~900 lines): Groups 7, 8
   - Name resolution (interdependent functions)
   - Instantiation and generalization (algorithms)
   - Requires all previous groups complete

---

## 🔧 Key Conversion Challenges

### Pattern Matching
**Haskell**: Extensive pattern matching with guards
**Koka**: Use `match` expressions; guards become `if` in action block

### Type Classes
**Haskell**: `HasCallStack`, `Ranged`, various Eq/Show instances
**Koka**: Explicit parameter passing, struct fields, custom functions

### Record Update Syntax
**Haskell**: `st{ sub = subNull, ... }`
**Koka**: Use `st(sub = subNull, ...)` or new struct with update

### Monad Operations
**Haskell**: `do` notation, monadic bind
**Koka**: Effect system, direct bindings with `<-`

### Type Annotations
**Haskell**: Extensive type sigs on every function
**Koka**: Type inference; explicit on complex functions

### Higher-Order Functions
**Haskell**: First-class predicates, partial application
**Koka**: Closures and explicit lambda syntax

---

## 📝 Notes for Implementation

1. **Module Structure**: The `infer-effect.kk` file is growing large. Consider splitting after Phase 2:
   - Keep `infer-effect.kk` for effects and Group 1-5 functions
   - `infer-unification.kk` - Group 6 functions
   - `infer-resolution.kk` - Group 7 functions
   - `infer-inference.kk` - Group 8 functions
   - `infer-gamma.kk` - Group 10 functions
   - `infer-monad.kk` - Group 9 infrastructure

2. **Testing**: Plan for unit tests after each group to verify:
   - Type operations work correctly (Group 2)
   - Name lookup returns expected results (Group 7)
   - Constraint resolution behaves correctly (Group 6)

3. **Dependencies**: Verify these modules are available:
   - `compiler/type/unify.kk` - For unification operations
   - `compiler/type/assumption.kk` - For gamma operations
   - `compiler/type/infgamma.kk` - For InfGamma operations
   - `compiler/core/core.kk` - For Core.Expr, Core.DefGroup

4. **Existing Haskell Code**: Will need to maintain both implementations during transition or rewrite callers

