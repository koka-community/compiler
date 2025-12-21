import compiler/common/syntax
import std/test

fun suite()
  group("equality")
    test("jsTarget, cTarget, target equality")
      expect(True)
        JsDefault == JsDefault && !(JsDefault == JsNode) && JsWeb == JsWeb &&
        CDefault == CDefault && LibC == LibC && !(Wasm == WasmJs) &&
        CS == CS && JS(JsWeb) == JS(JsWeb) && !(JS(JsNode) == JS(JsWeb)) && 
        C(Wasm) == C(Wasm) && DefaultTarget == DefaultTarget && !(CS == DefaultTarget)

    test("platform equality")
      expect(True)
        platform32 == Platform(4, 4, 4, 8) && platform64 == platform64 && !(platform32 == platform64)

    test("visibility equality")
      expect(True)
        Public == Public && Private == Private && !(Public == Private)

    test("param-info equality")
      expect(True)
        Borrow == Borrow && Own == Own && !(Borrow == Own)

    test("fixity equality")
      expect(True)
        FixInfix(10, AssocLeft) == FixInfix(10, AssocLeft) && FixPrefix == FixPrefix && 
        FixPostfix == FixPostfix && !(FixInfix(10, AssocLeft) == FixInfix(10, AssocRight))

    test("assoc equality")
      expect(True)
        AssocLeft == AssocLeft && AssocRight == AssocRight && !(AssocLeft == AssocRight)

    test("fipT equality")
      expect(True)
        Fip(AllocAtMost(10)) == Fip(AllocAtMost(10)) && NoFip(True) == NoFip(True) && 
        !(Fip(AllocAtMost(10)) == NoFip(False)) && fipTop != fipBot

    test("dataDef equality")
      val r = ValueRepr(10, 2, 4)
      expect(True)
        DataDefNormal == DataDefNormal && DataDefValue(r) == DataDefValue(r) && 
        DataDefLazy(fipTop) == DataDefLazy(fipTop) && !(DataDefNormal == DataDefValue(valuerepr/zero))

    test("valueRepr equality")
      val v1 = ValueRepr(8, 2, 4)
      val v2 = ValueRepr(8, 2, 4)
      val v3 = ValueRepr(8, 2, 8)
      expect(True)
        v1 == v2 && !(v1 == v3)

  group("wasm target detection")
    test("wasm targets")
      expect(True)
        C(Wasm).is-target-wasm && C(WasmJs).is-target-wasm && C(WasmWeb).is-target-wasm && 
        !C(LibC).is-target-wasm && !CS.is-target-wasm

  group("target/show")
    test("basic targets show correctly")
      expect(True)
        CS.target/show == "cs" && JS(JsNode).target/show == "jsnode" && 
        JS(JsWeb).target/show == "jsweb" && JS(JsDefault).target/show == "js"

    test("C targets show correctly")
      expect(True)
        C(Wasm).target/show == "wasm" && C(WasmJs).target/show == "wasmjs" && 
        C(WasmWeb).target/show == "wasmweb" && C(LibC).target/show == "libc" && 
        DefaultTarget.target/show == ""

  group("platform definitions")
    test("platform sizes")
      expect(True)
        platform32.ptrSize == 4 && platform64.ptrSize == 8 && 
        platform64c.fieldSize == 4 && platformJS.sizeSize == 4

  group("has-compressed-fields")
    test("compression detection")
      expect(True)
        !platform32.has-compressed-fields && !platform64.has-compressed-fields && 
        platform64c.has-compressed-fields

  group("platform/show")
    test("platform display")
      expect(True)
        platform32.platform/show.contains("4") && platform64.platform/show.contains("8")

  group("visibility/show")
    test("visibility display")
      expect(True)
        Public.visibility/show == "Public" && Private.visibility/show == "Private"

  group("buildType display")
    test("build type display")
      expect(True)
        DebugFull.build-type/show == "debugfull" && Debug.build-type/show == "debug" && 
        Release.build-type/show == "release" && RelWithDebInfo.build-type/show == "drelease"

  group("handler-sort display")
    test("handler sort display")
      expect(True)
        HandlerNormal.handler-sort/show == "normal" && HandlerInstance.handler-sort/show == "named"

  group("operation-sort display and parsing")
    test("operation sort display")
      expect(True)
        OpVal.op-sort/show == "val" && OpFun.op-sort/show == "fun" && 
        OpControl.op-sort/show == "ctl" && OpExcept.op-sort/show == "final ctl"

    test("read-op-sort parsing")
      val r1 = match read-op-sort("val") { Just(OpVal) -> True; _ -> False }
      val r2 = match read-op-sort("ctl") { Just(OpControl) -> True; _ -> False }
      val r3 = match read-op-sort("brk") { Just(OpExcept) -> True; _ -> False }
      val r4 = match read-op-sort("invalid") { Nothing -> True; _ -> False }
      expect(True)
        r1 && r2 && r3 && r4

  group("dataeffect display")
    test("dataeffect display")
      val de = DataEffect(True, True)
      expect(True)
        DataNoEffect.dataeffect/show == "noeffect" && 
        de.dataeffect/show.contains("named") && de.dataeffect/show.contains("linear")

  group("dataKind display")
    test("data kind display")
      expect(True)
        Inductive.datakind/show == "type" && CoInductive.datakind/show == "co type" && 
        Retractive.datakind/show == "div type"

  group("dataDef predicates")
    test("dataDef predicates")
      expect(True)
        DataDefOpen(True).is-extend && !DataDefOpen(False).is-extend && 
        DataDefValue(valuerepr/zero).is-value && !DataDefNormal.is-value && 
        DataDefNormal.is-normal && DataDefLazy(fipTop).datadef/is-lazy

  group("valueRepr helpers")
    test("valueRepr creation")
      val vraw = value-repr-raw(16)
      val vscan = value-repr-scan(3)
      expect(True)
        valuerepr/zero.rawSize == 0 && valuerepr/zero.scan-count == 0 &&
        vraw.rawSize == 16 && vraw.scan-count == 0 &&
        vscan.rawSize == 0 && vscan.scan-count == 3

    test("valueRepr predicates")
      expect(True)
        ValueRepr(8, 2, 4).is-mixed && ValueRepr(16, 0, 16).is-raw

  group("param-info display")
    test("param-info display")
      expect(True)
        Borrow.param/show == "Borrow" && Own.param/show == "Own"

  group("def-sort display and creation")
    test("def-sort display")
      expect(True)
        DefFun([]).defsort/show == "fun" && DefVal.defsort/show == "val" && 
        DefVar.defsort/show == "var"

    test("def-fun creation")
      expect(True)
        def-fun([]).is-fun && def-fun([Own, Own]).is-fun

  group("defInline display")
    test("inline display")
      expect(True)
        InlineNever.definline/show == "noinline" && InlineAlways.definline/show == "inline" && 
        InlineAuto.definline/show == "autoinline"

  group("assoc display")
    test("assoc display")
      expect(True)
        AssocLeft.assoc/show == "AssocLeft" && AssocRight.assoc/show == "AssocRight" && 
        AssocNone.assoc/show == "AssocNone"

  group("fipAlloc comparison")
    test("fipAlloc comparison")
      expect(True)
        fipa/cmp(AllocAtMost(5), AllocAtMost(10)) == Lt && 
        fipa/cmp(AllocAtMost(10), AllocAtMost(10)) == Eq && 
        fipa/cmp(AllocFinitely, AllocAtMost(10)) == Gt

  group("fipAlloc helpers")
    test("fipAlloc operations")
      expect(True)
        fipa/zero == AllocAtMost(0) && 
        combine(AllocAtMost(3), AllocAtMost(4)) == AllocAtMost(7) && 
        combine(AllocAtMost(5), AllocFinitely) == AllocFinitely

  group("fipT helpers")
    test("fipT operations")
      expect(True)
        fipTop.is-top && !Fip(AllocAtMost(0)).is-top && 
        Fip(AllocAtMost(0)).is-tail && Fip(AllocAtMost(10)).alloc == AllocAtMost(10)

  group("alignment calculation")
    test("aligned/sum with various sizes")
      expect(True)
        aligned/sum(0, [4, 4]) == 8 && aligned/sum(0, [1]) == 1

  group("valueRepr size calculation")
    test("valuerepr/size with platform")
      val v = ValueRepr(8, 2, 4)
      expect(True)
        valuerepr/size(platform32, v) == 16 && valuerepr/size(platform64, v) == 24

  group("datadef/show")
    test("dataDef display")
      val vr = ValueRepr(10, 2, 4)
      expect(True)
        DataDefNormal.datadef/show == "reference" && 
        DataDefValue(vr).datadef/show.contains("value") &&
        DataDefOpen(True).datadef/show == "extend" && 
        DataDefOpen(False).datadef/show == "open"

  group("subsumes relation")
    test("fipT subsumption")
      expect(True)
        subsumes(NoFip(False), Fip(AllocAtMost(5))) && 
        subsumes(Fip(AllocAtMost(10)), Fip(AllocAtMost(5))) &&
        !subsumes(Fip(AllocAtMost(5)), Fip(AllocAtMost(10)))

  group("show-fip formatting")
    test("fipT formatting")
      val f1 = show-fip(Fip(AllocAtMost(5)))
      val f2 = show-fip(NoFip(True))
      expect(True)
        f1.contains("fip") && f2.contains("tail")

  group("fipt/max operation")
    test("fipT maximum")
      expect(True)
        fipt/max(NoFip(True), NoFip(True)) == NoFip(True) && 
        fipt/max(Fip(AllocAtMost(5)), Fip(AllocAtMost(10))) == Fip(AllocAtMost(10))

  group("fipa/max operation")
    test("fipAlloc maximum")
      expect(True)
        fipa/max(AllocAtMost(5), AllocAtMost(10)) == AllocAtMost(10) && 
        fipa/max(AllocAtMost(5), AllocFinitely) == AllocFinitely && 
        fipa/max(AllocFinitely, AllocUnlimited) == AllocUnlimited

  group("member-doc building")
    test("documentation generation")
      val doc = member-doc("", "Members", ["x: int", "y: string"])
      expect(True)
        doc.contains("Members") && doc.contains("x: int") && doc.contains("y: string")

fun main()
  run-tests(suite)
