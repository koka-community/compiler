import compiler/common/syntax
import std/test

fun suite()
  group("jsTarget equality")
    test("same jsTarget values are equal")
      expect(True)
        JsDefault == JsDefault

    test("different jsTarget values are unequal")
      expect(True)
        !(JsDefault == JsNode)

    test("JsWeb equals itself")
      expect(True)
        JsWeb == JsWeb

  group("cTarget equality")
    test("same cTarget values are equal")
      expect(True)
        CDefault == CDefault

    test("LibC equals itself")
      expect(True)
        LibC == LibC

    test("different cTarget values are unequal")
      expect(True)
        !(Wasm == WasmJs)

  group("target equality")
    test("CS targets are equal")
      expect(True)
        CS == CS

    test("JS targets with same jsTarget are equal")
      expect(True)
        JS(JsWeb) == JS(JsWeb)

    test("JS targets with different jsTarget are unequal")
      expect(True)
        !(JS(JsNode) == JS(JsWeb))

    test("C targets with same cTarget are equal")
      expect(True)
        C(Wasm) == C(Wasm)

    test("DefaultTarget equals itself")
      expect(True)
        DefaultTarget == DefaultTarget

    test("different target variants are unequal")
      expect(True)
        !(CS == DefaultTarget)

  group("is-target-wasm")
    test("C(Wasm) is wasm target")
      expect(True)
        C(Wasm).is-target-wasm

    test("C(WasmJs) is wasm target")
      expect(True)
        C(WasmJs).is-target-wasm

    test("C(WasmWeb) is wasm target")
      expect(True)
        C(WasmWeb).is-target-wasm

    test("C(LibC) is not wasm target")
      expect(False)
        C(LibC).is-target-wasm

    test("CS is not wasm target")
      expect(False)
        CS.is-target-wasm

  group("target/show")
    test("CS shows as 'cs'")
      expect(True)
        CS.target/show == "cs"

    test("JS with JsNode shows as 'jsnode'")
      expect(True)
        JS(JsNode).target/show == "jsnode"

    test("JS with JsWeb shows as 'jsweb'")
      expect(True)
        JS(JsWeb).target/show == "jsweb"

    test("JS with JsDefault shows as 'js'")
      expect(True)
        JS(JsDefault).target/show == "js"

    test("C with Wasm shows as 'wasm'")
      expect(True)
        C(Wasm).target/show == "wasm"

    test("C with WasmJs shows as 'wasmjs'")
      expect(True)
        C(WasmJs).target/show == "wasmjs"

    test("C with LibC shows as 'libc'")
      expect(True)
        C(LibC).target/show == "libc"

    test("DefaultTarget shows as empty string")
      expect(True)
        DefaultTarget.target/show == ""

  group("platform equality")
    test("same platform values are equal")
      expect(True)
        platform32 == Platform(4, 4, 4, 8)

    test("platform64 equals itself")
      expect(True)
        platform64 == platform64

    test("different platform values are unequal")
      expect(True)
        !(platform32 == platform64)

  group("platform definitions")
    test("platform32 has 4-byte ptr")
      expect(True)
        platform32.ptrSize == 4

    test("platform64 has 8-byte ptr")
      expect(True)
        platform64.ptrSize == 8

    test("platform64c has 4-byte fieldSize")
      expect(True)
        platform64c.fieldSize == 4

    test("platformJS has 4-byte sizeSize")
      expect(True)
        platformJS.sizeSize == 4

  group("has-compressed-fields")
    test("platform32 has no compressed fields")
      expect(False)
        platform32.has-compressed-fields

    test("platform64 has no compressed fields")
      expect(False)
        platform64.has-compressed-fields

    test("platform64c has compressed fields")
      expect(True)
        platform64c.has-compressed-fields

  group("platform/show")
    test("platform32 shows correctly")
      expect(True)
        platform32.platform/show.contains("4")

    test("platform64 shows correctly")
      expect(True)
        platform64.platform/show.contains("8")

  group("visibility equality")
    test("Public equals Public")
      expect(True)
        Public == Public

    test("Private equals Private")
      expect(True)
        Private == Private

    test("Public and Private are unequal")
      expect(True)
        !(Public == Private)

  group("visibility/show")
    test("Public shows as 'Public'")
      expect(True)
        Public.visibility/show == "Public"

    test("Private shows as 'Private'")
      expect(True)
        Private.visibility/show == "Private"

  group("buildType display")
    test("DebugFull shows as 'debugfull'")
      expect(True)
        DebugFull.build-type/show == "debugfull"

    test("Debug shows as 'debug'")
      expect(True)
        Debug.build-type/show == "debug"

    test("Release shows as 'release'")
      expect(True)
        Release.build-type/show == "release"

  group("handlerSort display")
    test("HandlerNormal shows as 'normal'")
      expect(True)
        HandlerNormal.handler-sort/show == "normal"

    test("HandlerInstance shows as 'named'")
      expect(True)
        HandlerInstance.handler-sort/show == "named"

  group("operationSort display and parsing")
    test("OpVal shows as 'val'")
      expect(True)
        OpVal.op-sort/show == "val"

    test("OpFun shows as 'fun'")
      expect(True)
        OpFun.op-sort/show == "fun"

    test("OpControl shows as 'ctl'")
      expect(True)
        OpControl.op-sort/show == "ctl"

    test("OpExcept shows as 'final ctl'")
      expect(True)
        OpExcept.op-sort/show == "final ctl"

    test("read-op-sort parses 'val'")
      expect(True)
        match read-op-sort("val")
          Just(OpVal) -> True
          _ -> False

    test("read-op-sort parses 'ctl'")
      expect(True)
        match read-op-sort("ctl")
          Just(OpControl) -> True
          _ -> False

    test("read-op-sort parses 'brk' as OpExcept")
      expect(True)
        match read-op-sort("brk")
          Just(OpExcept) -> True
          _ -> False

    test("read-op-sort returns Nothing for invalid")
      expect(True)
        match read-op-sort("invalid")
          Nothing -> True
          _ -> False

  group("dataeffect display")
    test("DataNoEffect shows as 'noeffect'")
      expect(True)
        DataNoEffect.dataeffect/show == "noeffect"

    test("DataEffect with both flags shows both")
      val de = DataEffect(True, True)
      expect(True)
        de.dataeffect/show.contains("named") && de.dataeffect/show.contains("linear")

  group("dataKind display")
    test("Inductive shows as 'type'")
      expect(True)
        Inductive.datakind/show == "type"

    test("CoInductive shows as 'co type'")
      expect(True)
        CoInductive.datakind/show == "co type"

    test("Retractive shows as 'div type'")
      expect(True)
        Retractive.datakind/show == "div type"

  group("dataDef equality")
    test("DataDefNormal equals itself")
      expect(True)
        DataDefNormal == DataDefNormal

    test("DataDefValue with same repr are equal")
      val r = ValueRepr(10, 2, 4)
      expect(True)
        DataDefValue(r) == DataDefValue(r)

    test("DataDefLazy with same fipT are equal")
      expect(True)
        DataDefLazy(fipTop) == DataDefLazy(fipTop)

    test("different dataDef are unequal")
      expect(True)
        !(DataDefNormal == DataDefValue(valuerepr/zero))

  group("dataDef predicates")
    test("is-extend returns True for DataDefOpen(True)")
      expect(True)
        DataDefOpen(True).is-extend

    test("is-extend returns False for DataDefOpen(False)")
      expect(False)
        DataDefOpen(False).is-extend

    test("is-value returns True for DataDefValue")
      expect(True)
        DataDefValue(valuerepr/zero).is-value

    test("is-value returns False for DataDefNormal")
      expect(False)
        DataDefNormal.is-value

    test("is-normal returns True for DataDefNormal")
      expect(True)
        DataDefNormal.is-normal

    test("is-lazy returns True for DataDefLazy")
      expect(True)
        DataDefLazy(fipTop).datadef/is-lazy

  group("valueRepr equality")
    test("same valueRepr are equal")
      val v1 = ValueRepr(8, 2, 4)
      val v2 = ValueRepr(8, 2, 4)
      expect(True)
        v1 == v2

    test("different valueRepr are unequal")
      val v1 = ValueRepr(8, 2, 4)
      val v2 = ValueRepr(8, 2, 8)
      expect(True)
        !(v1 == v2)

  group("valueRepr helpers")
    test("valuerepr/zero has all zeros")
      expect(True)
        valuerepr/zero.rawSize == 0 && valuerepr/zero.scan-count == 0

    test("value-repr-raw creates raw repr")
      val v = value-repr-raw(16)
      expect(True)
        v.rawSize == 16 && v.scan-count == 0

    test("value-repr-scan creates scan repr")
      val v = value-repr-scan(3)
      expect(True)
        v.rawSize == 0 && v.scan-count == 3

    test("is-mixed detects mixed repr")
      expect(True)
        ValueRepr(8, 2, 4).is-mixed

    test("is-raw detects raw repr")
      expect(True)
        ValueRepr(16, 0, 16).is-raw

  group("paramInfo equality")
    test("Borrow equals Borrow")
      expect(True)
        Borrow == Borrow

    test("Own equals Own")
      expect(True)
        Own == Own

    test("Borrow and Own are unequal")
      expect(True)
        !(Borrow == Own)

  group("paramInfo display")
    test("Borrow shows as 'Borrow'")
      expect(True)
        Borrow.param/show == "Borrow"

    test("Own shows as 'Own'")
      expect(True)
        Own.param/show == "Own"

  group("defSort display and creation")
    test("DefFun shows as 'fun'")
      expect(True)
        DefFun([]).defsort/show == "fun"

    test("DefVal shows as 'val'")
      expect(True)
        DefVal.defsort/show == "val"

    test("DefVar shows as 'var'")
      expect(True)
        DefVar.defsort/show == "var"

    test("def-fun creates DefFun")
      expect(True)
        def-fun([]).is-fun

    test("def-fun with all-own parameters simplifies")
      expect(True)
        def-fun([Own, Own]).is-fun

  group("defInline display")
    test("InlineNever shows as 'noinline'")
      expect(True)
        InlineNever.definline/show == "noinline"

    test("InlineAlways shows as 'inline'")
      expect(True)
        InlineAlways.definline/show == "inline"

    test("InlineAuto shows as 'autoinline'")
      expect(True)
        InlineAuto.definline/show == "autoinline"

  group("fixity equality")
    test("same FixInfix are equal")
      expect(True)
        FixInfix(10, AssocLeft) == FixInfix(10, AssocLeft)

    test("FixPrefix equals itself")
      expect(True)
        FixPrefix == FixPrefix

    test("FixPostfix equals itself")
      expect(True)
        FixPostfix == FixPostfix

    test("different fixity are unequal")
      expect(True)
        !(FixInfix(10, AssocLeft) == FixInfix(10, AssocRight))

  group("assoc equality")
    test("AssocLeft equals itself")
      expect(True)
        AssocLeft == AssocLeft

    test("AssocRight equals itself")
      expect(True)
        AssocRight == AssocRight

    test("different assoc are unequal")
      expect(True)
        !(AssocLeft == AssocRight)

  group("assoc display")
    test("AssocLeft shows as 'AssocLeft'")
      expect(True)
        AssocLeft.assoc/show == "AssocLeft"

    test("AssocRight shows as 'AssocRight'")
      expect(True)
        AssocRight.assoc/show == "AssocRight"

  group("fipT equality")
    test("same Fip are equal")
      expect(True)
        Fip(AllocAtMost(10)) == Fip(AllocAtMost(10))

    test("NoFip with same tail flag are equal")
      expect(True)
        NoFip(True) == NoFip(True)

    test("different fipT are unequal")
      expect(True)
        !(Fip(AllocAtMost(10)) == NoFip(False))

    test("fipTop and fipBot are defined")
      expect(True)
        fipTop != fipBot

  group("fipAlloc comparison")
    test("AllocAtMost values compare by number")
      expect(True)
        fipa/cmp(AllocAtMost(5), AllocAtMost(10)) == Lt

    test("AllocAtMost equal to same number")
      expect(True)
        fipa/cmp(AllocAtMost(10), AllocAtMost(10)) == Eq

    test("AllocFinitely greater than AllocAtMost")
      expect(True)
        fipa/cmp(AllocFinitely, AllocAtMost(10)) == Gt

  group("fipAlloc helpers")
    test("fipa/zero is AllocAtMost(0)")
      expect(True)
        fipa/zero == AllocAtMost(0)

    test("combine AllocAtMost values sums them")
      expect(True)
        combine(AllocAtMost(3), AllocAtMost(4)) == AllocAtMost(7)

    test("combine with AllocFinitely returns AllocFinitely")
      expect(True)
        combine(AllocAtMost(5), AllocFinitely) == AllocFinitely

  group("fipT helpers")
    test("is-top detects fipTop")
      expect(True)
        fipTop.is-top

    test("is-top returns False for others")
      expect(False)
        Fip(AllocAtMost(0)).is-top

    test("fipt/is-tail for Fip is True")
      expect(True)
        Fip(AllocAtMost(0)).is-tail

    test("fipt/alloc gets allocation")
      expect(True)
        Fip(AllocAtMost(10)).alloc == AllocAtMost(10)

fun main()
  run-tests(suite)
