//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
module compiler/common/syntax
// Updated as of 11/3/25: Commit 486ef0d

pub type jsTarget
  JsDefault
  JsNode
  JsWeb

pub fun jstarget/(==)(j1: jsTarget, j2: jsTarget): bool
  match (j1, j2)
    (JsDefault, JsDefault) -> True
    (JsNode, JsNode) -> True
    (JsWeb, JsWeb) -> True
    _ -> False

pub type cTarget
  CDefault
  LibC
  Wasm
  WasmJs
  WasmWeb

pub fun ctarget/(==)(c1: cTarget, c2: cTarget): bool
  match (c1, c2)
    (CDefault, CDefault) -> True
    (LibC, LibC) -> True
    (Wasm, Wasm) -> True
    (WasmJs, WasmJs) -> True
    (WasmWeb, WasmWeb) -> True
    _ -> False

pub value type target
  CS
  JS(t: jsTarget)
  C(t: cTarget)
  DefaultTarget

pub fun target/(==)(t1: target, t2: target): bool
  match (t1, t2)
    (CS, CS) -> True
    (JS(j1), JS(j2)) -> j1 == j2
    (C(c1), C(c2)) -> c1 == c2
    (DefaultTarget, DefaultTarget) -> True
    _ -> False

pub fun is-target-wasm(t: target): bool
  match t
    C(Wasm) -> True
    C(WasmJs) -> True
    C(WasmWeb) -> True
    _ -> False

pub fun target/show(t: target): string
  match t
    CS -> "cs"
    JS(JsWeb) -> "jsweb"
    JS(JsNode) -> "jsnode"
    JS -> "js"
    C(Wasm) -> "wasm"
    C(WasmJs) -> "wasmjs"
    C(WasmWeb) -> "wasmweb"
    C(LibC) -> "libc"
    C -> "c"
    DefaultTarget -> ""

pub struct platform
  ptrSize: int // sizeof(intptr_t)
  sizeSize: int // sizeof(size_t)
  fieldSize: int // sizeof(kk_field_t) usually intptr_t but may be smaller for compression
  headerSize: int // used for correct alignment calculation

pub val platform32 = Platform(4, 4, 4, 8)
pub val platform64 = Platform(8, 8, 8, 8)
pub val platform64c = Platform(8, 8, 4, 8) // Compressed fields
pub val platformJS = Platform(8, 4, 8, 0)
pub val platformCS = Platform(8, 4, 8, 0)

pub fun platform/(==)(p1: platform, p2: platform): bool
  p1.ptrSize == p2.ptrSize && p1.sizeSize == p2.sizeSize && p1.fieldSize == p2.fieldSize && p1.headerSize == p2.headerSize

pub fun has-compressed-fields(p: platform): bool
  p.ptrSize != p.fieldSize

pub fun platform/show(p: platform): string
  "Platform(sizeof(void*)=" ++ p.ptrSize.show ++ ", sizeof(size_t)=" ++ p.sizeSize.show ++ ", sizeof(kk_box_t)=" ++ p.fieldSize.show ++ ", sizeof(kk_header_t)=" ++ p.headerSize.show ++ ")"

pub fun aligned/sum(start: int, xs: list<int>): int
  xs.foldl(start, aligned/add)

fun aligned/add(x: int, y: int): int
  align-up(x, y) + y

fun align-up(x: int, y: int): int
  if y <= 0 then x
  else ((x + y - 1) / y) * y

pub type buildType
  DebugFull
  Debug
  RelWithDebInfo
  Release

pub fun build-type/show(b: buildType): string
  match b
    DebugFull -> "debugfull"
    Debug -> "debug"
    RelWithDebInfo -> "drelease"
    Release -> "release"

// Visibility
pub type visibility
  Public
  Private

pub fun visibility/(==)(v1: visibility, v2: visibility): bool
  match (v1, v2)
    (Public, Public) -> True
    (Private, Private) -> True
    _ -> False

pub fun visibility/show(v: visibility): string
  match v
    Public -> "Public"
    Private -> "Private"

pub type handlerSort
  HandlerNormal
  HandlerInstance

pub fun handler-sort/show(h: handlerSort): string
  match h
    HandlerNormal -> "normal"
    HandlerInstance -> "named"

pub type operationSort
  OpVal
  OpFun
  OpExcept
  OpControlRaw
  OpControl
  OpControlErr

pub fun op-sort/show(o: operationSort): string
  match o
    OpVal -> "val"
    OpFun -> "fun"
    OpExcept -> "final ctl"
    OpControl -> "ctl"
    OpControlRaw -> "rawctl"
    OpControlErr -> ""

pub fun op-sort/string(o: operationSort): string
  match o
    OpVal -> "val"
    OpFun -> "fun"
    OpExcept -> "brk"
    OpControl -> "ctl"
    OpControlRaw -> "rawctl"
    OpControlErr -> ""

pub fun read-op-sort(s: string): maybe<operationSort>
  match s
    "val" -> Just(OpVal)
    "fun" -> Just(OpFun)
    "brk" -> Just(OpExcept)
    "ctl" -> Just(OpControl)
    "rawctl" -> Just(OpControlRaw)
    // legacy
    "except" -> Just(OpExcept)
    "control" -> Just(OpControl)
    "rcontrol" -> Just(OpControlRaw)
    _ -> Nothing

pub value type dataEffect
  DataNoEffect
  DataEffect(is-named: bool, is-linear: bool)

pub fun dataeffect/show(k: dataEffect): string
  match k
    DataNoEffect -> "noeffect"
    DataEffect(n, l) -> sep-by-space([if n then "named" else "", if l then "linear" else ""])

// DataKind
pub type dataKind
  Inductive
  CoInductive
  Retractive

pub fun datakind/show(k: dataKind): string
  match k
    Inductive -> "type"
    CoInductive -> "co type"
    Retractive -> "div type"

pub type dataDef
  DataDefValue(repr: valueRepr) // value type
  DataDefNormal // reference type
  DataDefLazy(fipT: fipT) // Lazy reference type
  DataDefOpen(isExtend: bool)
  DataDefAuto(declaredAsStruct: bool) // value or reference type; determined by kind inference (in kind/repr.kk:create-data-def)

pub fun datadef/(==)(d1: dataDef, d2: dataDef): bool
  match (d1, d2)
    (DataDefValue(r1), DataDefValue(r2)) -> r1 == r2
    (DataDefNormal, DataDefNormal) -> True
    (DataDefLazy(f1), DataDefLazy(f2)) -> f1 == f2
    (DataDefOpen, DataDefOpen) -> True
    (DataDefAuto, DataDefAuto) -> True
    _ -> False

pub fun datadef/show(d: dataDef): string
  match d
    DataDefValue(r) -> "value" ++ r.show
    DataDefNormal -> "reference"
    DataDefLazy(f) -> sep-by-space(["lazy", f.show])
    DataDefOpen(isExtend) -> if isExtend then "extend" else "open"
    DataDefAuto(isStruct) -> "auto" ++ (if isStruct then " struct" else "")

pub fun datadef/is-extend(d: dataDef): bool
  match d
    DataDefOpen(isExtend) -> isExtend
    _ -> False
  
pub fun datadef/is-open(d: dataDef): bool
  d.is-dataDefOpen

pub fun datadef/is-value(d: dataDef): bool
  d.is-dataDefValue

pub fun datadef/is-normal(d: dataDef): bool
  d.is-dataDefNormal

pub fun datadef/is-lazy(d: dataDef): bool
  d.is-dataDefLazy

pub fun datadef/size(d: dataDef, p: platform): int
  match d
    DataDefValue(r) -> size(p, r)
    _ -> p.fieldSize

pub value struct valueRepr
  rawSize: int // size in bytes
  scan-count: int // count of scannable fields 
  alignment: int // minimal alignment

pub fun valuerepr/(==)(v1: valueRepr, v2: valueRepr): bool
  v1.rawSize == v2.rawSize && v1.scan-count == v2.scan-count && v1.alignment == v2.alignment

pub fun valuerepr/show(v: valueRepr): string
  "{" ++ v.rawSize.show ++ ", " ++ v.scan-count.show ++ ", " ++ v.alignment.show ++ "}"

pub fun scan-size(p: platform, v: valueRepr): (int, int)
  (p.size(v), v.scan-count)

pub fun valuerepr/size(p: platform, v: valueRepr): int
  v.rawSize + (v.scan-count * p.fieldSize)

pub fun is-mixed(v: valueRepr): bool
  v.rawSize > 0 && v.scan-count > 0

pub fun is-raw(v: valueRepr): bool
  v.rawSize > 0 && v.scan-count == 0

pub val valuerepr/zero = ValueRepr(0,0,0)

pub fun value-repr-raw(m: int)
  ValueRepr(m,0,m)

pub fun value-repr-scan(n: int)
  ValueRepr(0,n,0)

pub type defSort
  DefFun(param: list<paramInfo>, fipKind: fipT=NoFip(False))
  DefVal
  DefVar

pub type paramInfo
  Borrow
  Own

pub fun def-fun-ex(pinfos: list<paramInfo>, fipKind: fipT)
  if pinfos.all(_.is-own) then DefFun([], fipKind) else DefFun(pinfos, fipKind)

pub fun def-fun(pinfos: list<paramInfo>)
  def-fun-ex(pinfos, noFip)

pub fun defsort/show(s: defSort): string
  match s
    DefFun -> "fun"
    DefVal -> "val"
    DefVar -> "var"

pub fun show-full(s: defSort): string
  match s
    DefFun(_, f) -> [f.show, "fun"].sep-by-space
    DefVal -> "val"
    DefVar -> "var"

pub fun defsort/is-fun(s: defSort): bool
  match s
    DefFun(_) -> True
    _ -> False

pub fun param/(==)(p1: paramInfo, p2: paramInfo): bool
  match (p1, p2)
    (Borrow, Borrow) -> True
    (Own, Own) -> True
    _ -> False

pub fun param/show(p: paramInfo): string
  match p
    Borrow -> "Borrow"
    Own -> "Own"

pub type defInline
  InlineNever
  InlineAlways
  InlineAuto

pub fun definline/show(i: defInline): string
  match i
    InlineNever -> "noinline"
    InlineAlways -> "inline"
    InlineAuto -> "autoinline"

// Fixities

// Operator fixity
pub type fixity
  FixInfix(prec: int, assoc: assoc) // Precedence and associativity
  FixPrefix
  FixPostfix

// Operator associativity
pub type assoc
  AssocNone
  AssocRight
  AssocLeft

pub fun fixity/(==)(f1: fixity, f2: fixity): bool
  match (f1, f2)
    (FixInfix(p1, a1), FixInfix(p2, a2)) -> p1 == p2 && a1 == a2
    (FixPrefix, FixPrefix) -> True
    (FixPostfix, FixPostfix) -> True
    _ -> False

pub fun fixity/show(f: fixity): string
  match f
    FixInfix(p, a) -> "FixInfix(" ++ p.show ++ ", " ++ a.show ++ ")"
    FixPrefix -> "FixPrefix"
    FixPostfix -> "FixPostfix"

pub fun assoc/(==)(a1: assoc, a2: assoc): bool
  match (a1, a2)
    (AssocNone, AssocNone) -> True
    (AssocRight, AssocRight) -> True
    (AssocLeft, AssocLeft) -> True
    _ -> False

pub fun assoc/show(a: assoc): string
  match a
    AssocNone -> "AssocNone"
    AssocRight -> "AssocRight"
    AssocLeft -> "AssocLeft"

// Fip
pub type fipT
  Fip(alloc: fipAlloc)
  Fbip(alloc: fipAlloc, tail: bool)
  NoFip(tail: bool) // Ordering seems wrong as `NoFip False` should be top but now NoFip True is the top

pub fun fipt/show(f: fipT): string
  match f
    Fip(a) -> "fip(" ++ a.show ++ ")"
    Fbip(a, t) -> "fbip(" ++ a.show ++ ", " ++ t.show ++ ")"
    NoFip(t) -> "NoFip(" ++ t.show ++ ")"

pub fun fipt/(==)(f1: fipT, f2: fipT): bool
  match (f1, f2) 
    (Fip(a1), Fip(a2)) -> a1 == a2
    (Fbip(a1, t1), Fbip(a2, t2)) -> a1 == a2 && t1 == t2
    (NoFip(t1), NoFip(t2)) -> t1 == t2
    _ -> False

// Note that "fbip" and "fip(1)" are incomparable so this cannot have an `cmp` function
pub fun subsumes(f1: fipT, f2: fipT): bool
  match (f1, f2)
    (NoFip, Fip) -> True
    (NoFip(t1), f2) -> !t1 || f2.is-tail
    (Fbip(a1, t1), Fbip(a2, t2)) -> a1 >= a2 && (!t1 || t2)
    (Fbip(a1), Fip(a2)) -> a1 >= a2
    (Fip(a1), Fip(a2)) -> a1 >= a2
    _ -> False

pub value type fipAlloc
  AllocAtMost(i: int)
  AllocFinitely
  AllocUnlimited

pub fun fipa/cmp(f1: fipAlloc, f2: fipAlloc): order
  match (f1, f2)
    (AllocAtMost(n1), AllocAtMost(n2)) -> n1.cmp(n2)
    (_, AllocAtMost) -> Gt
    (AllocAtMost, AllocFinitely) -> Lt
    (AllocFinitely, AllocFinitely) -> Eq
    (AllocUnlimited, AllocFinitely) -> Gt
    (AllocUnlimited, AllocUnlimited) -> Eq
    (_, AllocUnlimited) -> Lt
    _ -> Lt

pub fun fipa/(==)(f1: fipAlloc, f2: fipAlloc): bool
  match (f1, f2)
    (AllocAtMost(n1), AllocAtMost(n2)) -> n1 == n2
    (AllocFinitely, AllocFinitely) -> True
    (AllocUnlimited, AllocUnlimited) -> True
    _ -> False

pub fun combine(f1: fipAlloc, f2: fipAlloc)
  match (f1, f2)
    (AllocAtMost(n), AllocAtMost(m)) -> AllocAtMost(n + m)
    _ -> AllocFinitely

pub val fipa/zero = AllocAtMost(0)

pub fun fipalloc/show(a: fipAlloc): string
  match a
    AllocAtMost(0) -> "AllocAtMost(0)"
    AllocAtMost(n) -> "AllocAtMost(" ++ n.show ++ ")"
    AllocFinitely -> "AllocFinitely"
    AllocUnlimited -> "AllocUnlimited"

pub val fipBot = Fip(AllocAtMost(0))
pub val fipTop = NoFip(False)
pub val fipNoAlloc = fipBot
pub val noFip = fipTop

pub fun is-top(f: fipT): bool
  match f
    NoFip(False) -> True
    _ -> False

pub fun fipt/is-tail(f: fipT): bool
  match f
    Fip(_) -> True
    Fbip(_, t) -> t
    NoFip(t) -> t

pub fun fipt/alloc(f: fipT): fipAlloc
  match f
    Fip(a) -> a
    Fbip(a) -> a
    NoFip() -> AllocUnlimited

pub fun show-fip(f: fipT)
  fun show-tail(b: bool): string
    if b then "tail" else ""
  fun show-n(n: fipAlloc): string
    match n
      AllocAtMost(0) -> ""
      AllocAtMost(n) -> "(" ++ n.show ++ ")"
      AllocFinitely -> "(n)"
      AllocUnlimited -> "" 
  match f
    Fip(n) -> "fip" ++ show-n(n)
    Fbip(n, t) -> [t.show-tail, "fbip" ++ show-n(n)].sep-by-space
    NoFip(t) -> t.show-tail

pub fun sep-by-space(xs: list<string>)
  xs.filter(_ != "").join(" ")

pub fun fipt/max(fip1: fipT, fip2: fipT)
  match (fip1, fip2)
    (NoFip(isTail1), NoFip(isTail2)) -> NoFip(isTail1 && isTail2)
    (NoFip(t1), _) -> NoFip(t1 && fip2.is-tail)
    (_, NoFip(t2)) -> NoFip(t2 && fip1.is-tail)
    (Fbip(a1, t1), Fbip(a2, t2)) -> Fbip(max(a1, a2), t1 && t2)
    (Fbip(a1, t1), Fip(a2)) -> Fbip(max(a1, a2), t1)
    (Fip(a1), Fbip(a2, t2)) -> Fbip(max(a1, a2), t2)
    (Fip(a1), Fip(a2)) -> Fip(max(a1, a2))

pub fun fipa/max(a1: fipAlloc, a2: fipAlloc)
  match (a1, a2)
    (AllocUnlimited, _) -> AllocUnlimited
    (_, AllocUnlimited) -> AllocUnlimited
    (AllocFinitely, _) -> AllocFinitely
    (_, AllocFinitely) -> AllocFinitely
    (AllocAtMost(n1), AllocAtMost(n2)) -> AllocAtMost(max(n1, n2))

pub fun member-doc(doc: string, header: string, members: list<string>): string
  val mdoc = "// " ++ header ++ ":\n// ```koka\n" ++ members.map("// " ++ _).join("\n") ++ "// ```\n"
  if doc == "" then mdoc else doc ++ "\n// * * *\n" ++ mdoc
