// Ported as of 2026-01-17; approx upstream baseline commit d3b244c of Backend/C/FromCore.hs (backfilled 2026-07-23)
module compiler/backend/c/constructors

import compiler/core/core
import compiler/common/name
import compiler/common/syntax
import compiler/lib/pprint
import compiler/type/type
import compiler/backend/c/helpers
import compiler/backend/c/dup-drops
import compiler/common/failure
import compiler/platform/config
import std/data/sort

// Generate value constructors for each defined type

pub fun gen-typedefs(tds: typedef-groups): _ ()
  tds.map(gen-typedef-group)
  ()

fun gen-typedef-group(tds: typedef-group): _ ()
  tds.map(gen-typedef-pre)
  tds.map(gen-typedef-post)
  ()

fun gen-typedef-pre(td: typedef)
  match td
    Synonym -> ()
    Data(info) ->
      val isExtend = info.is-extend
      // generate the type constructor
      emit-to-h(linebreak |.| text("// " ++ (if info.is-value then "value type" else "type")) |+| info.name.pretty)
      val (dataRepr, conReprs) = info.data-repr(data/is-value)
      if dataRepr.is-dataEnum then
        val enumIntTp = match info.def
          DataDefValue(ValueRepr(n, 0, _)) ->
            if n <= 1 then "uint8_t" elif n <= 2 then "uint16_t" elif n <= 4 then "uint32_t" else "uint64_t"
          _ -> "kk_intb_t" // should not happen!
        fun pp-enum-constr((c: con-info, _)) c.name.cpp-name
        emit-to-h(info.vis.cpp-vis |.| "enum".text |+| info.name.type-class-name.cpp-name |.| "_e".text |+|
          block(if conReprs.is-nil then info.name.cpp-name |.| "_empty".text else vcat(info.constrs.zip(conReprs).map(pp-enum-constr).punctuate(comma))) |.| semi |-|
          "typedef".text |+| enumIntTp.text |+| info.name.type-class-name.cpp-name |.| semi |.| linebreak
          )
      elif dataRepr.is-value || isExtend then ()
      else
        emit-to-h(info.vis.cpp-vis |.| "struct".text |+| info.name.type-class-name.cpp-name |.| "_s".text |+| 
          block(vcat(["kk_block_t _block;".text] ++ (if dataRepr.is-dataOpen then ["kk_string_t _tag;".text] else []))) |.| semi |-|
          (if dataRepr.data-repr-may-have-singletons then "typedef kk_datatype_t".text |+| info.name.type-class-name.cpp-name |.| semi 
           else "typedef kk_datatype_ptr_t".text |+| info.name.type-class-name.cpp-name |.| semi)
          )

fun gen-typedef-post(td: typedef)
  match td
    Synonym -> ()
    Data(info) ->
      val isExtend = info.is-extend
      // Generate the type constructor
      val (dataRepr, conReprs) = info.data-repr(data/is-value)
      val noCons = conReprs.is-nil
      val nm = info.name

      // order fields of constructors to have their scan fields first
      val conInfoReprs = zip(info.constrs, conReprs)
      val conInfos = conInfoReprs.map fn((ci, crepr))
        val fields = ci.orderedParams
        val scan-count = ci.valueRepr.scan-count
        (ci, crepr, fields, scan-count)
      val maxSC = conInfos.max-scan-count-of
      val minSC = conInfos.min-scan-count-of

      // generate types for constructors
      if dataRepr.is-dataEnum then ()
      else 
        conInfos.map(_.gen-constructor-type(info, dataRepr))
        ()

      // wrap up the type definition
      if dataRepr.is-dataOpen && !isExtend then
        ()
      elif dataRepr.is-dataEnum || !dataRepr.is-value then
        ()
      else
        fun pp-struct-const-field(c: con-info)
          "struct".text |+| c.name.cpp-name |+| c.name.unqualify.cpp-name |.| semi
        if dataRepr.needsTagField then
          emit-to-h(
            info.vis.cpp-vis |.| "struct".text |+| nm.cpp-name |.| "_s".text |+|
            block("kk_value_tag_t _tag;".text |-| "union".text |+| 
              block(vcat(
                (info.constrs.map(pp-struct-const-field) ++ 
                 (if maxSC > 1 && minSC != maxSC then ["kk_box_t _fields[".text |.| (maxSC - 1).pretty |.| "]".text |.| semi] else []))
                )) |+| "_cons;".text) |.| semi
            |-| info.vis.cpp-vis |.| "typedef struct".text |+| nm.cpp-name |.| "_s".text |+| nm.type-class-name.cpp-name |.| semi
          )
        else
          emit-to-h(info.vis.cpp-vis |.| "typedef struct".text |+| (
            match (dataRepr, info.constrs)
              (DataIso, [c]) -> c.name.cpp-name
              (DataSingleStruct, [c]) -> c.name.cpp-name
              _ -> nm.cpp-name |.| "_s".text
            )
            |+| nm.type-class-name.cpp-name |.| semi
          )
      
      // generate functions for constructors
      val sconInfos = conInfos.sort(?(<) = fn(ci1, ci2) ci1.fst.params.length < ci2.fst.params.length) // singletons first
      sconInfos.map(_.gen-constructor(info, dataRepr, maxSC))
      sconInfos.map(_.gen-constructor-test(info, dataRepr))

      // generate functions for the data type
      if !isExtend then
        nm.type-class-name.gen-dup-drop(info, dataRepr, sconInfos)
        nm.gen-box-unbox(info, dataRepr)
      else
        ()

fun gen-constructor-type((ci, crepr, cfields, _): (con-info, con-repr, list<(name, ktype)>, int), info: data-info, drepr: data-repr)
  match crepr
    ConEnum -> () // already in enum declaration
    ConSingleton | !drepr.is-value -> ()
    _ ->
      val typeField = if drepr.is-value then [] else ["struct".text |+| info.name.type-class-name.cpp-name |.| "_s".text |+| "_base;".text]
      val fields = typeField ++ cfields.map(pp-con-field)
      emit-to-h(ci.vis.cpp-vis |.| "struct".text |+| ci.name.cpp-name |+| 
        block(if fields.is-nil then "kk_box_t _unused;".text else fields.vcat) // avoid empty struct
        |.| semi)

fun pp-con-field((nm, tp): (name, ktype))
  tp.cpp-type |+| nm.unqualify.cpp-name |.| semi

fun gen-constructor((ci, crepr, cfields, scan-count): (con-info, con-repr, list<(name, ktype)>, int), info: data-info, drepr: data-repr, maxScanCount: int)
  gen-constructor-base-cast(ci, crepr, info, drepr)
  gen-constructor-create(ci, crepr, cfields, scan-count, maxScanCount, info, drepr)
  gen-constructor-access(ci, crepr, info, drepr)

fun gen-constructor-test((ci, crepr, _, _): (con-info, con-repr, list<(name, ktype)>, int), info: data-info, drepr: data-repr)
  val nameDoc = ci.name.cpp-name
  val dataTypeTagDoc = "kk_datatype_tag".text |.| arguments(["x".text])
  val ctag = pp-con-tag(ci, crepr, drepr)
  val valueTagEq = "kk_value_tag_eq(x._tag,".text |+| ctag |.| ")".text

  val testDoc = match crepr
    ConEnum -> "x ==".text |+| ctag
    ConIso -> "true".text
    ConSingleton | drepr.is-value -> valueTagEq
    ConSingleton -> "kk_datatype_has_singleton_tag".text |.| ["x".text, ctag].tupled
    ConSingle -> "true".text
    ConStruct -> valueTagEq
    ConAsJust(asNothing=non) -> "!".text |.| con-test-nameX(non) |.| arguments(["x".text])
    ConAsCons(asNil=non) -> // TODO kk_datatype_is_ptr may be faster on arm64?
      "!".text |.| non.con-test-nameX |.| arguments(["x".text])
    ConNormal ->
      text(if drepr.data-repr-may-have-singletons then "kk_datatype_has_ptr_tag" else "kk_datatype_ptr_has_tag") |.| arguments(["x".text, ctag])
    ConOpen ->
      "kk_string_ptr_eq_borrow".text |.| tupled([
        parens("kk_datatype_as".text |.| arguments([
          "struct".text |+| info.name.type-class-name.cpp-name |.| "_s*".text,
          "x".text
        ])) |.| "->_tag".text
        ,ctag
      ])
  emit-to-h(
    "static inline bool".text |+| ci.con-test-name |.| parameters([info.name.type-class-name.cpp-name |+| "x".text])
    |+| block("return (".text |.| testDoc |.| ");".text)
  )

fun pp-con-tag(ci: con-info, crepr: con-repr, drepr: data-repr)
  match crepr 
    ConOpen -> "tag".make-hidden-name(ci.name).cpp-name
    ConEnum -> ci.name.cpp-name
    ConSingleton | drepr.is-dataAsMaybe -> "KK_TAG_NOTHING".text
    ConAsJust -> "KK_TAG_JUST".text
    _ | drepr.needsTagField -> "kk_value_tag(".text |.| crepr.tag.pretty |.| ")".text
    _ -> "(kk_tag_t)".text |.| crepr.tag.pretty.parens


fun gen-constructor-create(ci: con-info, crepr: con-repr, allFields: list<(name, ktype)>, scan-count: int, maxScanCount: int, info: data-info, drepr: data-repr)
  if drepr.is-dataOpen then
    emit-to-h("extern kk_string_t".text |+| ci.con-tag-name |.| semi)
  val at = "at".new-hidden-name
  val cpath = "cpath".new-hidden-name
  val hasCPath = crepr.has-ctx-path && allFields.is-cons
  val nameDoc = ci.name.cpp-name
  val ctag = pp-con-tag(ci, crepr, drepr)
  val (paddingFields, conFields) = allFields.partition(fn(f) f.fst.is-padding-name)
  emit-to-h("static inline".text |+| info.name.type-class-name.cpp-name |+| ci.con-create-name |.| 
   nt-parameters(
    (if drepr.is-value || conFields.is-nil || drepr.is-dataAsMaybe then [] else [(at, typeReuse)])
    ++ (if hasCPath then [(cpath, typeInt32)] else []) ++ ci.params
    ) |+|
    block(
      match crepr
        ConEnum -> "return".text |+| ctag |.| semi
        ConSingleton | !drepr.is-value -> "return kk_datatype_from_tag".text |.| ctag.parens |.| semi
        ConIso -> 
          val tmp = "_con".text
          vcat([
            info.name.type-class-name.cpp-name |+| tmp |+| "= {".text |+| conFields.head.unjust.fst.ppDefName |+| "};".text, 
            "return".text |+| tmp |.| semi])
        _ ->
          val tmp = "_con".text
          fun assignField((name, _), f)
            f(name.ppDefName) |+| "=".text |+| name.ppDefName |.| semi
          if drepr.is-value then
            vcat((
              if drepr.needsTagField then
               [info.name.type-class-name.cpp-name |+| tmp |.| semi,
                tmp |.| "._tag =".text |+| ctag |.| semi] ++
                conFields.map(_.assignField(fn(fld) tmp |.| "._cons.".text |.| ci.name.ppDefName |.| ".".text |.| fld))
                ++ paddingFields.map(fn((padding, _)) tmp |.| "._cons.".text |.| ci.name.ppDefName |.| ".".text |.| padding.ppDefName |+| "= kk_box_null();".text)
                ++ list(scan-count - 1, maxScanCount - 2).map(fn(i) tmp |.| "._cons._fields[".text |.| i.pretty |.| "] = kk_box_null();".text)
              else
               [info.name.type-class-name.cpp-name |+| tmp |.| semi] ++
                conFields.map(_.assignField(fn(fld) tmp |.| ".".text |.| fld))
                ++ paddingFields.map(fn((padding, _)) tmp |.| ".".text |.| padding.ppDefName |+| "= kk_box_null();".text)
              ) ++
              ["return".text |+| tmp |.| semi]
            )
          else
            vcat(
              // an eager `params.head.unjust` crashes on parameterless constructors
              // (e.g. open-data singletons, cgen/open1)
              (if !crepr.is-conAsJust then [] else {
                val arg = ci.params.head.unjust.fst.cpp-name
                ["if kk_likely(!kk_box_is_maybe".text |.| arguments([arg]) |.| ") { return kk_datatype_as_Just(".text |.| arg |.| "); }".text]
              })
              ++ ["struct".text |+| nameDoc |.| "*".text |+| tmp |+| "=".text |+| "kk_block_alloc_at_as".text |.|
                arguments([
                  "struct".text |+| nameDoc,
                  (if drepr.is-dataAsMaybe || conFields.is-nil /* open singleton */ then "kk_reuse_null".text else at.cpp-name),
                  scan-count.pretty |+| "/* scan count */".text,
                  (if hasCPath then cpath.cpp-name else "0".text),
                  (if !drepr.is-dataOpen then ctag else "KK_TAG_OPEN".text)
                ]) |.| semi]
              ++ (if !drepr.is-dataOpen then [] else [tmp |.| "->_base._tag = kk_string_dup".text |.| arguments([ctag]) |.| semi])
              ++ conFields.map(_.assignField(fn(fld) tmp |.| "->".text |.| fld))
              ++ paddingFields.map(fn((padding, _)) tmp |.| "->".text |.| padding.ppDefName |+| "= kk_box_null();".text)
              ++ ["return".text |+| ci.con-base-case-name |.| arguments([tmp]) |.| semi]
            )
    )
  )
  ()

fun gen-constructor-base-cast(ci: con-info, crepr: con-repr, info: data-info, drepr: data-repr)
  match crepr
    ConEnum -> ()
    ConSingleton -> ()
    ConIso -> ()
    _ | drepr.is-value -> ()
    _ ->
      emit-to-h("static inline".text |+| info.name.type-class-name.cpp-name |+| ci.con-base-case-name |.|
      parameters(["struct".text |+| ci.name.cpp-name |.| "* _x".text]) |+|
      block("return".text |+| "kk_datatype_from_base".text |.| arguments(["&_x->_base".text]) |.| semi))

fun gen-constructor-access(ci: con-info, crepr: con-repr, info: data-info, drepr: data-repr)
  if drepr.is-value || crepr.is-conSingleton then ()
  else
    emit-to-h("static inline struct".text |+| ci.name.cpp-name |.| "*".text |+| ci.con-as-name |.|
      parameters([info.name.type-class-name.cpp-name |+| "x".text]) |+|
      block(
        "return".text |+| "kk_datatype_as_assert".text |.|
        arguments(["struct".text |+| ci.name.cpp-name |.| "*".text, "x".text, (if drepr.is-dataOpen then "KK_TAG_OPEN".text else pp-con-tag(ci, crepr, drepr))]) 
        |.| semi
      )
    )
