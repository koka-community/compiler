module compiler/kind/repr

import std/core/undiv
import compiler/common/name
import compiler/common/name-prim
import compiler/common/syntax
import compiler/common/failure
import compiler/type/type
import compiler/lib/pprint
import compiler/type/pretty
// Updated 7/23/26; Commit #6fe38b8

// Create a datadef and elaborate conInfo's with a ValueRepr
// and correctly ordered fields depending on alignment
// constraints and platform sizes.

// value types
pub fun create-data-def(
    emit-error: (doc) -> _ (), 
    emit-warning: (doc) -> _ (), 
    lookup-datainfo: (name) -> _ maybe<data-info>, 
    platform: platform, nm:name, 
    resultHasKindStar: bool, isRec: bool, sort: data-kind, extraFields: int, 
    defaultDef:data-def, conInfos0: list<con-info>): _ (data-def, list<con-info>)
  val isVal = defaultDef.is-value
  fun create-con-info-repr(c: con-info)
    val (orderedFields, vrepr) = order-con-fields(emit-error, "constructor".text |+| (c.name:name).pretty, lookup-datainfo, platform, extraFields, c.params)
    c(orderedParams=orderedFields, valueRepr=vrepr)
  
  // (m = raw, n = scan)
  fun max-data-def(ddfs)
    match ddfs
      Nil ->
        if !isVal then DataDefNormal // reference type no constructors
        else
          val size = 
            if nm == nameTpChar || nm == nameTpInt32 || nm == nameTpFloat32 || nm == nameTpMarker then 4
            elif nm == nameTpFloat || nm == nameTpInt64 then 8
            elif nm == nameTpInt8 || nm == nameTpByte then 1
            elif nm == nameTpInt16 || nm == nameTpFloat16 then 2
            elif nm == nameTpAny || nm == nameTpFieldAddr || nm == nameTpIntPtrT then platform.ptrSize
            elif nm == nameTpSSizeT then platform.sizeSize
            else 0
          val m =
            if size <= 0 then
              emit-warning("is declared as a primitive value type but has no known compilation size, assuming size".text |+| platform.ptrSize.pretty)
              platform.ptrSize
            else size
          DataDefValue(ValueRepr(m, 0, m))
      [vr] -> DataDefValue(vr)
      Cons(vr, vrs) ->
        val dd = vrs.max-data-def
        match (vr, dd)
          (ValueRepr(0, 0), DataDefValue(v)) -> DataDefValue(v)
          (v, DataDefValue(ValueRepr(0, 0))) -> DataDefValue(v)
          (ValueRepr(m1, 0, a1), DataDefValue(ValueRepr(m2, 0, a2))) ->
            DataDefValue(ValueRepr(m1.max(m2), 0, a1.max(a2)))
          (ValueRepr(0, n1, a1), DataDefValue(ValueRepr(0, n2, a2))) ->
            DataDefValue(ValueRepr(0, n1.max(n2), a1.max(a2)))
          (ValueRepr(m1, n1, a1), DataDefValue(ValueRepr(m2, n2, a2))) 
            // equal scan fields
            | n1 == n2 -> DataDefValue(ValueRepr(m1.max(m2), n1, a1.max(a2)))
            | True ->
              if isVal then
                emit-error("is declared as a value type but has".text|+|
                  "multiple constructors with different number of regular types overlapping with value types.".text |-|
                  "hint: value types with multiple constructors must all use the same number of regular types (use 'box' to use a value type as a regular type).".text )
              DataDefNormal
          _ -> DataDefNormal

  fun create-max-data-def(ci: list<con-info>)
    val vreprs = ci.map(valueRepr)
    val ddef = max-data-def(vreprs)
    match ddef
      DataDefValue(ValueRepr(0, 0, 0)) -> // enum
        val n = ci.length
        if n < 256 then DataDefValue(value-repr-raw(1)) // uint8
        elif n < 65536 then DataDefValue(value-repr-raw(2)) // uint16
        else DataDefValue(value-repr-raw(4)) // uint32
      _ -> ddef

  // calculate the value repr of each constructor
  val conInfos = conInfos0.map(create-con-info-repr)

  // datadef
  val maxMembers = conInfos.map(_.params.length).maximum()
  val conCount = conInfos.length
  val canbeValue = resultHasKindStar && !sort.is-retractive
  val isEnum = canbeValue && maxMembers == 0 && conCount >= 1
  val isIso = canbeValue && maxMembers == 1 && conCount == 1
  
  val ddef = match defaultDef
    DataDefOpen(isExtend) -> DataDefOpen(isExtend)
    DataDefLazy(fip) -> DataDefLazy(fip)
    DataDefNormal -> 
      val dd = conInfos.create-max-data-def
      // match dd
      //   DataDefValue | isEnum -> dd // allow allocated enums
      //   DataDefValue | isIso -> dd // iso type are always value types
      DataDefNormal
    DataDefAuto ->
      val dd = conInfos.create-max-data-def
      match dd
        DataDefValue | isEnum -> dd
        DataDefValue | isIso -> dd // iso types are preferred as value types
        DataDefValue ->
          // val wouldGetTagField = conCount > 1 && !isEnum
          // val size = platform.size(vr) + (if wouldGetTagField then platform.fieldSize else 0)
          // if (size <= 2*platform.ptrSize && (maxMembers < 3 && canbeValue)) then
          //   emitWarning("may be better declared as a value type for efficiency (e.g. 'value type/struct'),".text |-|
          //     "or declared as a reference type to suppress this warning (e.g. 'reference type/struct')".text)
          DataDefNormal
        _ -> DataDefNormal
    DataDefValue | isRec ->
      emit-error("cannot be declared as value type since it is recursive.".text)
      DataDefNormal
    DataDefValue | !resultHasKindStar ->
      emit-error("is declared as a value type but does not have value kind ('V').".text)
      DataDefNormal
    DataDefValue | !sort.is-inductive ->
      emit-error("is declared as a value type but is not inductive.".text)
      DataDefNormal
    DataDefValue ->
      val dd = conInfos.create-max-data-def()
      match dd
        DataDefValue(vr) ->
          val size = platform.size(vr)
          if size > 4*platform.ptrSize then
            emit-warning("requires".text |+| size.pretty |+| " bytes which is rather large for a value type".text)
          if isEnum then
            emit-warning("is an enumeration -- there is not need to declare it as a value type".text)
          dd
        _ ->
          // should never happen
          emit-error("cannot be used as a value type.".text) 
          DataDefNormal
  (ddef, conInfos)

// Determine the size of a constructor
//  order constructor fields of constructors with raw field so the regular fields come first to be scanned.
// return the ordered fields, and a ValueRepr (raw size part, the scan count (including tags), align, and full size)
// The size is used for reuse and should include all needed fields including the tag field for "open" datatypes 
pub fun order-con-fields(emit-error: (doc) -> _ (), nameDoc: doc, get-datainfo: (name) -> _ maybe<data-info>, platform: platform, extraPreScan: int, fields: list<(name, ktype)>): _ (list<(name, ktype)>, value-repr)
  // insert raw fields in (reversed) order of alignment so they align to the smallest total size in a datatype
  fun insert-raw(field: (name, ktype), vr: value-repr, rraw0: list<((name, ktype), value-repr)>): list<((name, ktype), value-repr)>
    match rraw0
      Cons((f, vrf), rs) ->
        if vr.alignment <= vrf.alignment then Cons((field, vr), Cons((f, vrf), rs))
        else Cons((f, vrf), insert-raw(field, vr, rs.pretend-decreasing))
      Nil -> [(field, vr)]
  fun visit(rraw: list<((name, ktype), value-repr)>, rmixed: list<((name, ktype), value-repr)>, rscan: list<(name, ktype)>, scan-count0: int, alignment0: int, l: list<(name, ktype)>): _ (list<(name, ktype)>, value-repr)
    match l
      // classify each field: raw (unboxed bits), scan (heap-traced), or mixed
      Cons(field, fs) ->
        match get-data-def(get-datainfo, field.snd)
          Just(DataDefValue(ValueRepr(rw, sc, al))) ->
            val vr = ValueRepr(rw, sc, al)
            val alignment = al.max(alignment0)
            if rw > 0 && sc > 0 then
              // mixed raw/scan: put it at the head of the raw fields (there
              // should be only one of these as checked in Kind/Infer)
              visit(rraw, Cons((field, vr), rmixed), rscan, scan-count0, alignment, fs.pretend-decreasing)
            elif rw > 0 then
              visit(insert-raw(field, vr, rraw), rmixed, rscan, scan-count0, alignment, fs.pretend-decreasing)
            else
              visit(rraw, rmixed, Cons(field, rscan), scan-count0 + sc, alignment, fs.pretend-decreasing)
          _ -> visit(rraw, rmixed, Cons(field, rscan), scan-count0 + 1, alignment0, fs.pretend-decreasing)
      Nil ->
        if rmixed.length > 1 then
          emit-error(nameDoc |+| " has multiple value type fields that each contain both raw types and regular types".text |-|
            "hint: use 'box' on either field to make it a non-value type.".text)
        // size before any mixed and raw fields
        val preSize = platform.headerSize + scan-count0 * platform.fieldSize
        // if there is a mixed value member (with scan fields) we may need to add padding scan fields (!)
        // (or otherwise the C compiler may insert uninitialized padding)
        val (padding, mixedScan) =
          match rmixed
            Cons((_, ValueRepr(_, scan, ralign))) ->
              val padSize = preSize % ralign
              val padCount = padSize / platform.fieldSize
              if (padSize % platform.fieldSize) != 0 then
                trace("kind/info order-con-fields: illegal alignment " ++ ralign.show)
              (list(1, padCount).map(fn(i) ((new-padding-name(scan-count0 + i), typeAny), value-repr-scan(1))), scan + padCount)
            _ -> (Nil, 0)
        // calculate the rest now
        val scan-count = scan-count0 + mixedScan
        val alignment = if scan-count > 0 then alignment0.max(platform.fieldSize) else alignment0
        val rest = padding ++ rmixed ++ rraw.reverse
        val restSizes = rest.map(fn((_, vr)) platform.size(vr))
        val restFields = rest.map(fst)
        val size = aligned/sum(preSize, restSizes)
        val rawSize = size - platform.headerSize - (scan-count * platform.fieldSize)
        val vrepr = ValueRepr(rawSize, scan-count, alignment)
        (rscan.reverse ++ restFields, vrepr)
  visit([], [], [], extraPreScan, 0, fields)

// Expand type SYNONYMS first otherwise the resulting WRONG scan count is
// baked into the constructor's `kk_block_alloc_at_as(...)` call, and
// `kk_block_mark_shared_rec` walking that "scan" slot as a `kk_box_t` (when
// it's actually raw struct bytes) reads a garbage pointer and segfaults.
// Found via std/time/timestamp.kk
fun extract-datadef-type(tp0: ktype): div maybe<name>
  match tp0.expand-syn
    TApp(t) -> t.extract-datadef-type
    TForAll(_, t) -> t.extract-datadef-type
    TCon(tc) -> Just(tc.name)
    _ -> Nothing

// Return the DataDef for a type.
// This may be 'Nothing' for abstract types.
fun get-data-def(lookupDI: (name) -> _ maybe<data-info>, tp: ktype): _ maybe<data-def>
  match tp.extract-datadef-type
    Nothing -> Just(DataDefNormal)
    Just(nm) | nm == nameTpBox -> Just(DataDefNormal)
    Just(nm) ->
      val mdi = lookupDI(nm)
      match mdi
        Nothing -> Nothing
        Just(di) -> Just(di.def)
