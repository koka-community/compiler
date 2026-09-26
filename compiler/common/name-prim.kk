//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------

module compiler/common/name-prim

import compiler/common/name
import compiler/common/syntax
import compiler/common/failure
import std/core/unsafe
// Updated as of 11/19/25: Commit #b6fdf12

//---------------------------------
// Special
//---------------------------------
pub val nameExpr        = "@expr".new-name
pub val nameType        = "@type".new-name

pub val nameInteractiveModule  = "interactive".new-module-name

pub val nameMain        = "@main".new-name
pub val nameCopy        = "@copy".new-name
pub val nameOpExpr      = "@opexpr".new-name

pub fun copy-name-of(typename: name): _ name
  type-qualified-name-of(typename, nameCopy)

//---------------------------------
// Primitive operations
//---------------------------------
pub val nameIf          = "if".new-name
val nameCase        = "case".new-name

//---------------------------------
// Core
//---------------------------------
pub val nameTpIO = "io".prelude-name
pub val nameTpNamed     = "nmd".prelude-name
pub val nameTpScope     = "scope".prelude-name
pub val nameTpPure      = "pure".prelude-name

val nameTpAsync     = "std/async".new-qualified("async")
val nameTpAsyncX    = "std/async".new-qualified("asyncx")
val nameTpBuilder   = "std/text/string".new-qualified("builder")
val nameTpArray     = "std/data/array".new-qualified("array")
val nameTpMDict     = nameDict.qualify("mdict".new-name)
val nameTpDict      = nameDict.qualify("dict".new-name)

pub val nameTpDelay          = "delay".prelude-name
val nameMainConsole      = "main-console".prelude-name

pub val nameSubStr1          = "substr1".core-string-name
pub val namesSameSize   = ["id","map","reverse","foldl","foldr","filter"].map(prelude-name)

//---------------------------------
// Lists
//---------------------------------
pub val nameListNil        = "Nil".core-types-name
pub val nameCons        = "Cons".core-types-name
pub val nameTpList      = "list".core-types-name

//---------------------------------
// std/core/debug
//---------------------------------
pub val nameAssert      = nameCoreDebug.qualify("assert".new-name)
pub val nameTrace   = nameCoreDebug.qualify("trace".new-name)
pub val nameLog     = nameCoreDebug.qualify("log".new-name)

pub val nameCoreFileFile = nameCoreDebug.qualify(new-locally-qualified("", "file", "kk-file"))
pub val nameCoreFileLine = nameCoreDebug.qualify(new-locally-qualified("", "file", "kk-line"))
pub val nameCoreFileModule = nameCoreDebug.qualify(new-locally-qualified("", "file", "kk-module"))

//---------------------------------
// std/core/lazy
//---------------------------------

pub val nameLazyMemoizeTarget = "memoize-target".core-lazy-name
val nameLazyMemoize = "whnf-memoize".core-lazy-name
pub val nameLazyEnter  = "atomic-enter".core-lazy-name
pub val nameLazyLeave  = "atomic-leave".core-lazy-name
pub val nameLazyIsWhnf = "datatype-is-whnf".core-lazy-name
pub val nameLazyPtrIsWhnf = "datatype-ptr-is-whnf".core-lazy-name
pub val nameDataTypePtrIsUnique = "datatype-ptr-is-unique".core-lazy-name
pub val nameDataTypePtrIsThreadShared = "datatype-ptr-is-thread-shared".core-lazy-name
pub val nameLazyIndirectCompress = "indirect-compress".core-lazy-name

//---------------------------------
// std/core/vector
//---------------------------------
pub val nameVector      = "unvlist".core-vector-name
pub val nameVectorFromList = new-locally-qualified("std/core/vector", "list", "vector")
pub val nameVectorUnsafeCreate = "@unsafe-vector".core-vector-name

//---------------------------------
// std/core/int
//---------------------------------
pub val nameByte        = "std/core/int".new-qualified("uint8")
pub val nameInt8        = "std/core/int".new-qualified("int8")
pub val nameInt16       = "std/core/int".new-qualified("int16")
pub val nameInt32       = "std/num/int32".new-qualified("int32")
pub val nameInt64       = "std/num/int64".new-qualified("int64")
pub val nameSSizeT      = "std/core/int".new-qualified("ssize_t")
pub val nameIntPtrT     = "std/core/int".new-qualified("intptr_t")

pub val nameIntAdd      = "int-add".core-int-name
pub val nameIntSub      = "int-sub".core-int-name

// these are used by evidence in std/core/hnd and can be compiler generated
pub val nameInternalInt32 = "@make-int32".core-types-name
pub val nameInternalSSizeT = "@make-ssize_t".core-types-name

// javascript backend
pub val nameIntConst = "@int-const".core-types-name


//---------------------------------
// std/core/exn
//---------------------------------

pub val nameTpException  = "exception".core-exn-name
pub val nameTpPartial   = "exn".core-exn-name
pub val namePatternMatchError = "error-pattern".core-exn-name

//---------------------------------
// Contexts: std/core/types
//---------------------------------

pub fun cfield-name(n: string): name
  n.core-types-name()

pub val nameTpCCtxx           = "cctx".cfield-name
pub val nameTpCCtx            = "ctx".cfield-name

pub val nameEtaHole           = "_".new-name

pub val nameCCtxCreate        = "@cctx-create".cfield-name
pub val nameCCtxHoleCreate    = "@cctx-hole-create".cfield-name
pub val nameCCtxExtend        = "@cctx-extend".cfield-name
pub val nameCCtxComposeExtend = "@cctx-compose-extend".cfield-name
pub val nameCCtxSetCtxPath    = "@cctx-setcp".cfield-name

pub val nameCCtxEmpty         = new-locally-qualified("std/core/types", "cctx", "empty")
pub val nameCCtxApply         = new-locally-qualified("std/core/types", "cctx", "++.")
pub val nameCCtxCompose       = new-locally-qualified("std/core/types", "cctx", "++")

pub val nameTpFieldAddr       = "@field-addr".cfield-name
pub val nameFieldAddrOf       = "@field-addr-of".cfield-name

//---------------------------------
// std/core/hnd
//---------------------------------

pub val nameTpMarker     = "marker".core-hnd-name
pub val nameTpHTag       = "htag".core-hnd-name
pub fun name-tp-clause(i:int): name
  ("clause" ++ i.show).core-hnd-name
pub val nameTpEv         = "ev".core-hnd-name
pub val nameTpEvv        = "evv".core-hnd-name
pub val nameTpEvIndex    = "ev-index".core-hnd-name
pub fun name-clause(sort, i: int): name
  ("clause-" ++ sort ++ i.show).core-hnd-name
pub val nameTpResumeContext = "resume-context".core-hnd-name

pub val nameHTag         = "@new-htag".core-hnd-name
pub fun name-perform(i: int)
  ("@perform" ++ i.show).core-hnd-name
pub val nameEvvAt        = "@evv-at".core-hnd-name
pub val nameEvvIndex     = "@evv-index".core-hnd-name
pub val nameEvvIndexMask = "@evv-index-mask".core-hnd-name
pub val nameMaskAt       = "@mask-at".core-hnd-name
pub val nameMaskBuiltin  = "@mask-builtin".core-hnd-name
pub fun name-open-at(i: int)
  ("@open-at" ++ i.show).core-hnd-name
pub fun name-open-none(i: int)
  ("@open-none" ++ i.show).core-hnd-name
pub fun name-open(i: int)
  ("@open" ++ i.show).core-hnd-name
pub val nameEvvIsAffine  = ("@evv-is-affine").core-hnd-name

pub val nameHandle       = "@hhandle".core-hnd-name
pub val nameNamedHandle  = "@named-handle".core-hnd-name

pub val nameYielding     = "yielding".core-hnd-name
pub val nameYieldExtend  = "yield-extend".core-hnd-name
pub val nameBind         = "yield-bind".core-hnd-name // prelude-name  "bind"
pub val nameBind2        = "yield-bind2".core-hnd-name
pub val nameEffectOpen   =  "@open".core-types-name // prelude-name "@open"

pub val nameInitially    = "initially".core-hnd-name
pub val nameFinally      = "finally".core-hnd-name
pub fun name-clause-tail-no-op(n: int): _ name
  core-hnd-name("clause-tail-noop" ++ show(n))

pub fun is-clause-tail-name(n: name): _ maybe<int>
  if n.nameModule != nameCoreHnd.nameModule then Nothing
  else
    val s = n.local
    if s.starts-with("clause-tail").bool then
      s.slice.drop(11).string.parse-int
    else
      Nothing

//---------------------------------
// std/core/types
//---------------------------------

pub val nameToAny       = "@toany".core-types-name
pub val nameValueOp     = "@Valueop".core-types-name
pub val nameTpValueOp   = "@valueop".core-types-name

pub val nameDecreasing  = nameCoreUndiv.qualify("pretend-decreasing".new-name)
pub val nameUnsafeTotal = nameCoreUnsafe.qualify("unsafe-total".new-name)

pub val nameIndex       = "index".new-hidden-name // used for []
pub val nameReturn      = "return".new-hidden-name
pub val nameAssign      = "@assign".new-hidden-name // used for :=

pub val nameRefSet      = "set".core-types-name
pub val nameLocalSet    = "local-set".core-types-name
pub val nameLocalGet    = "local-get".core-types-name
pub val nameDeref       = try({qualify-locally("ref".new-module-name, "!".core-types-name)}).default("error".new-name)
pub val nameByref       = "@byref".core-types-name

pub val nameTypeHeapDiv = "hdiv".core-types-name
pub val nameEvHeapDiv   = "@Hdiv".core-types-name
pub val nameEvHeapNoDiv = "@Hnodiv".core-types-name
pub val nameHeapDiv     = "hdiv".new-name

pub val namePredHeapDiv = "hdiv".core-types-name
pub val namePredEffDiv  = "ediv".core-types-name

pub val nameTpRef       = "ref".core-types-name
pub val nameTpLocalVar  = "local-var".core-types-name
pub val nameTpLocal     = "local".core-types-name
pub val nameRef         = "ref".core-types-name
pub val nameLocalNew    = "local-new".core-types-name
pub val nameLocalVar    = "local-var".core-hnd-name
pub val nameRunLocal    = "local-scope".core-types-name

pub val nameTpTotal     = nameEffectEmpty // "total"
pub val nameTpDiv       = "div".core-types-name
pub val nameTpAlloc     = "alloc".core-types-name
pub val nameTpRead      = "read".core-types-name
pub val nameTpWrite     = "write".core-types-name
pub val nameTpST        = "st".core-types-name

pub val nameEffectEmpty = "total".core-types-name
pub val nameEffectExtend= "effect-extend".core-types-name
pub val nameEffectAppend= "@effect-append".new-name  // only used during kind inference

pub val nameAnd         = "&&".core-types-name
pub val nameOr          = "||".core-types-name

pub fun make-tp-handled(namedh: bool, linear: bool): name
  core-types-name(if namedh then "nhandled" else "handled" ++ (if linear then "1" else ""))

pub val nameTpHandled   = make-tp-handled(False, False)
pub val nameTpHandled1  = make-tp-handled(False, True)
pub val nameTpNHandled  = make-tp-handled(True, False)
pub val nameTpNHandled1 = make-tp-handled(True, True)

pub val nameIdentity    = "id".core-types-name

pub val nameUnit        = "Unit".core-types-name
pub val nameTrue        = "True".core-types-name
pub val nameFalse       = "False".core-types-name

pub val nameJust        = "Just".core-types-name
pub val nameNothing     = "Nothing".core-types-name
pub val nameTpMaybe     = "maybe".core-types-name

val nameOptional    = "@Optional".core-types-name
val nameOptionalNone= "@None".core-types-name
pub val nameTpOptional  = "@optional".core-types-name

pub val nameTpVoid      = "void".core-types-name
pub val nameTpUnit      = "unit".core-types-name
pub val nameTpBool      = "bool".core-types-name
pub val nameTpInt       = "int".core-types-name

// val nameTpByte      = "uint8".core-types-name
pub val nameTpInt8      = "int8".core-types-name
pub val nameTpInt16     = "int16".core-types-name
pub val nameTpInt32     = "int32".core-types-name
pub val nameTpInt64     = "int64".core-types-name
pub val nameTpSSizeT    = "ssize_t".core-types-name
pub val nameTpIntPtrT   = "intptr_t".core-types-name

pub val nameTpFloat     = "float64".core-types-name
pub val nameTpFloat32   = "float32".core-types-name
pub val nameTpFloat16   = "float16".core-types-name

pub val nameTpChar      = "char".core-types-name
pub val nameTpString    = "string".core-types-name
pub val nameTpAny       = "any".core-types-name
pub val nameTpVector    = "vector".core-types-name

// These are internal only inserted by the boxing phase
pub val nameTpBox       = "@box".core-types-name
pub val nameBoxCon      = "@Box".core-types-name
pub val nameBox         = "@box".core-types-name
pub val nameUnbox       = "@unbox".core-types-name

pub val nameTpReuse     = "@reuse".core-types-name
pub val nameReuseNull   = "@no-reuse".core-types-name
pub val nameDropReuse   = "@drop-reuse".core-types-name
pub val nameFreeReuse   = "@free-reuse".core-types-name
pub val nameAllocAt     = "@alloc-at".core-types-name
pub val nameAssignReuse = "@assign-reuse".core-types-name
pub val nameReuse       = "@reuse".core-types-name
pub val nameReuseIsValid= "@reuse-is-valid".core-types-name
pub val nameConFieldsAssign = "@con-fields-assign".core-types-name
pub val nameConTagFieldsAssign = "@con-tag-fields-assign".core-types-name
pub val nameConTagScanFieldsAssign = "@con-tag-scan-fields-assign".core-types-name
pub val nameSetTag      = "@set-tag".core-types-name
pub val nameKeep        = "keep".core-types-name

pub val nameDup         = "@dup".core-types-name
pub val nameDrop        = "@drop".core-types-name
pub val nameFree        = "@free".core-types-name
pub val nameDecRef      = "@dec-ref".core-types-name
pub val nameIsUnique    = "@is-unique".core-types-name
pub val nameKeepMatch   = "@keep-match".core-types-name
pub val nameDropMatch   = "@drop-match".core-types-name
pub val nameReuseMatch  = "@reuse-match".core-types-name

pub val nameReuseDrop   = "@reuse-drop".core-types-name

pub val nameDropSpecial = "@drop-special".core-types-name

pub fun name-tuple(n: int): name
  if n <= 1 then nameUnit else ("Tuple" ++ n.show).core-types-name // core-types-name("(" ++ replicate(",", n - 1).join ++ ")")

pub fun name-tp-tuple(n: int): name
  if n <= 1 then nameTpUnit else ("tuple" ++ n.show).core-types-name // core-types-name("(" ++ replicate(",", n - 1).join ++ ")")

pub fun is-name-tuple(n: name): bool
  val s = n.local
  n == nameUnit ||   
    n.nameModule == nameCoreTypes.nameModule && s.starts-with("Tuple").bool && s.slice.drop(5).string.list.all(is-digit)

pub fun is-name-tp-tuple(n: name): bool
  val s = n.local
  n == nameTpUnit ||   
    n.nameModule == nameCoreTypes.nameModule && s.starts-with("tuple").bool && s.slice.drop(5).string.list.all(is-digit)


fun prelude-name(s: string): name
  nameSystemCore.qualify(s.new-name)

fun core-hnd-name(s: string): name
  nameCoreHnd.qualify(s.new-name)
fun core-types-name(s: string): name
  nameCoreTypes.qualify(s.new-name)

fun core-int-name(s: string): name
  new-qualified("std/core/int", s)
fun core-list-name(s: string): name
  new-qualified("std/core/list", s)
fun core-exn-name(s: string): name
  new-qualified("std/core/exn", s)
fun core-vector-name(s: string): name
  new-qualified("std/core/vector", s)
fun core-string-name(s: string): name
  new-qualified("std/core/string", s)
fun core-lazy-name(s: string): name
  new-qualified("std/core/lazy", s)

pub val nameSystemCore  = "std/core".new-module-name
pub val nameCoreHnd     = "std/core/hnd".new-module-name
pub val nameCoreUndiv   = "std/core/undiv".new-module-name
pub val nameCoreUnsafe  = "std/core/unsafe".new-module-name
pub val nameCoreTypes   = "std/core/types".new-module-name
val nameDict        = "std/data/dict".new-module-name
pub val nameCoreDebug   = "std/core/debug".new-module-name

pub fun is-system-core-name(n: name): bool
  val m = n.nameModule
  m == "std/core" || m.starts-with("std/core/").bool

pub fun shorten-system-core-name(n: name): name
  val m = n.nameModule
  if m == "std/core" || m == "std/core/types" || m == "std/core/exn" then n.unqualify
  elif m.starts-with("std/core/").bool then qualify(m.list.drop(9).string.new-module-name, n.unqualify)
  else n


pub fun is-primitive-name(n: name): bool
  n.qualifier.is-primitive-module

pub fun is-primitive-module(n: name): bool
  n == nameCoreHnd || n == nameCoreTypes

//---------------------------------
// Primitive Kind Constructors
//---------------------------------
pub val nameKindStar    = "V".new-name
pub val nameKindLabel   = "X".new-name
pub val nameKindFun = "->".new-name
pub val nameKindEffect  = "E".new-name
pub val nameKindHeap    = "H".new-name
pub val nameKindScope   = "S".new-name
pub val nameKindHandled = "HX".new-name
pub val nameKindHandled1 = "HX1".new-name
