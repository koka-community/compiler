// Ported as of 2026-01-29; approx upstream baseline commit d3b244c of Backend/C/FromCore.hs (backfilled 2026-07-23)
module compiler/backend/c/dup-drops

import compiler/core/core
import compiler/lib/pprint
import compiler/type/type
import compiler/common/name
import compiler/backend/c/helpers
import compiler/common/failure
import compiler/platform/config
import compiler/common/syntax
import std/data/sort

pub fun gen-box-unbox(nm: name, info: data-info, drepr: data-repr)
  val tname = nm.type-class-name
  tname.gen-box(info, drepr)
  tname.gen-unbox(info, drepr)

pub fun gen-box-call(tp: ktype, arg: doc)
  val prim = "box"
  match tp.c-type
    CFun -> prim-name-type(prim, "function_t") |.| tupled([arg, contextDoc])
    CPrim(v) | v == "kk_unit_t" || v == "bool" || v == "kk_string_t" || v == "kk_bytes_t" -> prim-name-type(prim, v) |.| parens(arg)
    CData(nm) -> prim-name(prim, nm.cpp-name) |.| tupled([arg, contextDoc])
    _ -> prim-name-type(prim, tp.cpp-type.show) |.| tupled([arg, contextDoc])

pub fun gen-unbox-call-owned(tp: ktype, arg: doc)
  gen-unbox-call(tp, arg, "KK_OWNED".text)

pub fun gen-unbox-call-borrowed(tp: ktype, arg: doc)
  gen-unbox-call(tp, arg, "KK_BORROWED".text)

fun gen-unbox-call(tp: ktype, arg: doc, argBorrow: doc)
  val prim = "unbox"
  match tp.c-type
    CFun -> prim-name-type(prim, "function_t") |.| tupled([arg, contextDoc]) // no borrow
    CPrim(v) | v == "kk_unit_t" || v == "bool" || v == "kk_string_t" || v == "kk_bytes_t" -> prim-name-type(prim, v) |.| arg.parens // no borrow, no context
    CPrim(v) -> prim-name-type(prim, v) |.| tupled(if v.cprim-can-be-boxed then [arg, argBorrow, contextDoc] else [arg, contextDoc])
    CData(nm) -> prim-name(prim, nm.cpp-name) |.| tupled([arg, argBorrow, contextDoc])
    CBox -> prim-name-type(prim, tp.cpp-type.show) |.| tupled([arg, contextDoc])

fun data-struct-as-maybe-split(l: list<con-info>)
  match l
    Cons(ci1, Cons(ci2, Nil)) -> if ci1.params.is-nil then (ci1, ci2) else (ci2, ci1)
    _ -> failure/fail("backend/c/from-core data-struct-as-maybe-split: expected two constructors for a maybe like type, got: " ++ l.show-list(show))

fun gen-box(nm: name, info: data-info, drepr: data-repr)
  val initDoc = "static inline kk_box_t".text |+| nm.cpp-name |.| "_box".text |.| parameters([nm.cpp-name |+| "_x".text])
  val restDoc = match drepr
    DataEnum -> "return".text |+| "kk_enum_box".text |.| tupled(["_x".text]) |.| semi
    DataIso ->
      val conInfo = info.constrs.head.unjust
      val (isoName, isoTp) = conInfo.params.head.unjust
      "return".text |+| gen-box-call(isoTp, "_x.".text |.| isoName.unqualify.cpp-name) |.| semi
    DataStructAsMaybe ->
      val (conNothing, conJust) = info.constrs.data-struct-as-maybe-split
      val (conJustFieldName, conJustFieldTp) = conJust.params.head.unjust
      val boxField = gen-box-call(conJustFieldTp, "_x._cons.".text |.| conJust.name.ppDefName |.| ".".text |.| conJustFieldName.unqualify.cpp-name)
      "if".text |+| parens(conNothing.con-test-name |.| arguments(["_x".text])) |+| "{ return kk_box_Nothing(); }".text |-|
      "  else".text |+| "{ return kk_box_Just".text |.| arguments([boxField]) |.| semi |+| "}".text
    _ ->
      match info.def
        DataDefValue(ValueRepr(_, scancount, _)) ->
          val docScanCount = scancount.pretty |+| "/* scan count */".text
          vcat(["kk_box_t _box;".text, "kk_valuetype_box".text |.| arguments([nm.cpp-name, "_box".text, "_x".text, docScanCount]) |.| semi, "return _box;".text])
        _ -> "return".text |+| (if drepr.data-repr-may-have-singletons then "kk_datatype_box" else "kk_datatype_ptr_box").text |.| tupled(["_x".text]) |.| semi
  emit-to-h(initDoc |+| block(restDoc))

fun gen-unbox(nm: name, info: data-info, drepr: data-repr)
  val initDoc = "static inline".text |+| nm.cpp-name |+| nm.cpp-name |.| "_unbox".text |.| parameters(["kk_box_t _x".text, "kk_borrow_t _borrow".text])
  val restDoc = match drepr
    DataEnum -> "return".text |+| nm.cpp-name.parens |.| "kk_enum_unbox".text |.| tupled(["_x".text])
    DataIso ->
      val conInfo = info.constrs.head.unjust
      val isoTp = conInfo.params.head.unjust.snd
      "return".text |+| conInfo.con-create-name |.| arguments([gen-unbox-call(isoTp, "_x".text, "_borrow".text)])
    DataStructAsMaybe ->
      val (conNothing, conJust) = info.constrs.sort(?(<)=fn(ci1:con-info, ci2:con-info) ci1.params.length < ci2.params.length).data-struct-as-maybe-split
      val (_, conJustFieldTp) = conJust.params.head.unjust
      "if (kk_box_is_Nothing(_x))".text |+| "{ return".text |+| conNothing.con-create-name |.| arguments([]) |.| semi |+| "}".text
      |-| "  else".text |+| (
        "{ return".text |+| conJust.con-create-name |.| arguments([
            gen-unbox-call(conJustFieldTp, "kk_unbox_Just".text |.| arguments(["_x".text, "_borrow".text]), "_borrow".text)])
          |.| semi |+| "}".text
      )
    _ | drepr.is-value -> [nm.cpp-name |+| "_unbox;".text, "kk_valuetype_unbox".text |.| arguments([nm.cpp-name, "_unbox".text, "_x".text, "_borrow".text]) |.| semi, "return _unbox".text].vcat
    _ -> "return".text |+| (if drepr.data-repr-may-have-singletons then "kk_datatype_unbox" else "kk_datatype_ptr_unbox").text |.| tupled(["_x".text])
  emit-to-h(initDoc |+| block(restDoc |.| semi))

// con infos are sorted with singletons first
pub fun gen-dup-drop(nm: name, info: data-info, drepr: data-repr, conInfos: list<(con-info, con-repr, list<(name, ktype)>, int)>)
  gen-dup-dropX(True, nm, info, drepr, conInfos)
  gen-dup-dropX(False, nm, info, drepr, conInfos)

fun gen-dup-dropX(isDup: bool, nm: name, info: data-info, drepr: data-repr, conInfos: list<(con-info, con-repr, list<(name, ktype)>, int)>)
  val ret = if isDup then ["return _x;".text] else []
  val dupDropTests =
    if drepr.is-dataEnum then ret
    elif conInfos.all(fn((_, cr, _, _)) cr.is-conSingleton) then ret
    elif drepr.is-dataIso then [gen-dup-drop-iso(isDup, conInfos.head.unjust)] ++ ret
    elif drepr.is-value then
      conInfos.map(gen-dup-drop-tests(isDup, drepr, _)).gen-dup-drop-match ++ ret
    else
      if isDup then ["return".text |+| (
        if drepr.data-repr-may-have-singletons then "kk_datatype_dup".text |.| arguments(["_x".text])
        else "kk_datatype_ptr_dup".text |.| arguments(["_x".text])) |.| semi]
      // danger: we must never generate constructors with more than 128 fields in order to use _small
      else [
        (if drepr.data-repr-may-have-singletons then "kk_datatype_drop_small" else "kk_datatype_ptr_drop_small").text |.|
        arguments(["_x".text]) |.| semi]
  emit-to-h("static inline".text |+| 
    (if isDup then nm.cpp-name |+| nm.cpp-name |.| "_dup".text else "void".text |+| nm.cpp-name |.| "_drop".text) |.| 
    parameters([nm.cpp-name |+| "_x".text]) |+| block(vcat(dupDropTests)))

fun gen-dup-drop-iso(isDup: bool, (_, _, tnames, _): (con-info, con-repr, list<(name, ktype)>, int))
  match tnames
    [(name, tp)] -> gen-dup-drop-call(isDup, tp, "_x.".text |.| name.cpp-name).map(_ |.| semi).hcat
    _ -> failure/fail("backend/c/gen-dup-drop-iso: invalid arguments")

// coninfos are sorted with singletons first
fun gen-dup-drop-maybe(isDup: bool, l: list<(con-info, con-repr, list<(name, ktype)>, int)>)
  match l
    [(conNothing, _, _, _), (conJust, _, [(fname, ftp)], _)] ->
      "if".text |+| parens("!".text |.| conNothing.con-test-name |.| arguments(["_x".text])) |+|
      block(vcat(gen-dup-drop-call(isDup, ftp, "_x._cons.".text |.| conJust.name.ppDefName |.| dot |.| fname.cpp-name)) |.| semi)

fun gen-dup-drop-match(branches0: list<(doc, list<doc>)>)
  val branches = branches0.filter(_.snd.is-cons)
  val complete = branches.length == branches0.length
  fun gen-branch(iff0, (test, stats))
    iff0.text |+| test.parens |+| block1(stats)
  match branches
    [] -> []
    [(_, stats)] | stats.is-nil || complete -> stats
    Cons(b, bs) -> 
      [gen-branch("if", b)] ++ 
      (if complete then bs.init else bs).map(fn(b') gen-branch("else if", b')) ++
      (if complete then ["else".text |+| block1(bs.last.unjust.snd)] else [])

fun gen-dup-drop-tests(isDup: bool, drepr: data-repr, (ci, cr, cfields, _): (con-info, con-repr, list<(name, ktype)>, int))
  val dupdropfields = gen-dup-drop-fields(isDup, drepr, ci, cr, cfields)
  (ci.con-test-name |.| arguments(["_x".text]), dupdropfields)

fun gen-dup-drop-testsX(isDup: bool, drepr: data-repr, lastIdx: int, ((ci, cr, cfields, _), idx): ((con-info, con-repr, list<(name, ktype)>, int), int))
  val stats = gen-dup-drop-fields(isDup, drepr, ci, cr, cfields)
  if lastIdx == idx then 
    if stats.is-nil then pprint/empty elif lastIdx == 1 then stats.vcat else "else".text |+| stats.vcat.block
  else
    val t = if idx == 1 then "if".text else "else if".text
    t |+| parens(ci.con-test-name |.| arguments(["_x".text])) |+| (if stats.is-nil then "{ }".text else stats.vcat.block)

fun gen-dup-drop-fields(isDup: bool, drepr: data-repr, ci: con-info, cr: con-repr, cfields: list<(name,ktype)>)
  if drepr.isDataStructOrLess then
    // value types
    cfields.map(fn((nm, tp)) gen-dup-drop-call(isDup, tp, (if drepr.needsTagField then "_x._cons.".text |.| ci.name.ppDefName else "_x".text) |.| dot |.| nm.cpp-name)).concat.map(_ |.| semi)
  elif cr.is-conSingleton then []
  else
    // reference types
    (["struct".text |+| ci.name.cpp-name |.| "* _con =".text |+| ci.con-as-name |.| arguments(["_x".text])] ++
     cfields.map(fn((nm, tp)) gen-dup-drop-call(isDup, tp, "_con->".text |.| nm.cpp-name)).concat ++
     ["kk_constructor_free_small".text |.| arguments(["_con".text])]).map(_ |.| semi)

fun gen-dup-drop-callx(prim: string, tp: ktype, args: doc)
  match tp.c-type
    CFun -> [prim-name-type(prim, "function_t") |.| args]
    CBox -> [prim-name-type(prim, "box_t") |.| args]
    CPrim(v) | v == "kk_integer_t" || v == "kk_bytes_t" || v == "kk_string_t" || v == "kk_vector_t" || v == "kk_evv_t" || v == "kk_ref_t" || v == "kk_reuse_t" || v == "kk_box_t"
      -> [prim-name-type(prim, v) |.| args]
    CPrim -> [text("kk_skip_" ++ prim) |.| args] // [] // text "value" |.| args
    CData(nm) -> [prim-name(prim, nm.cpp-name) |.| args]

pub fun gen-dup-call(tp: ktype, arg: doc)
  gen-dup-drop-call(True, tp, arg).hcat

fun gen-drop-call(tp: ktype, arg: doc)
  gen-dup-drop-call(False, tp, arg).hcat

pub fun gen-dup-drop-call(isDup: bool, tp: ktype, arg: doc)
  if isDup then gen-dup-drop-callx("dup", tp, arguments([arg]))
  else gen-dup-drop-callx("drop", tp, arguments([arg]))

// The following functions are generated during "drop specialization" and "reuse specialization", 
// and only generated for heap allocated constructors so we can always use the `datatype_ptr` calls at runtime.
pub fun gen-unique-call(tp: ktype, arg: doc)
  ["kk_likely".text |.| parens("kk_datatype_ptr_is_unique".text |.| arguments([arg]))]

// danger: we assume we never generate free or decref for bytes, strings or vectors!
pub fun gen-free-call(tp: ktype, arg: doc)
  ["kk_datatype_ptr_free_small".text |.| arguments([arg])]

pub fun gen-decref-call(tp: ktype, arg: doc)
  ["kk_datatype_ptr_decref_small".text |.| arguments([arg])]

pub fun gen-drop-reuse-call(tp: ktype, arg: list<doc>)
  ["kk_datatype_ptr_dropn_reuse".text |.| arguments(arg)]

pub fun gen-reuse-call(tp: ktype, arg: doc)
  ["kk_datatype_ptr_reuse".text |.| arguments([arg])]

pub fun gen-dropn-call(tp: ktype, args: list<doc>)
  ["kk_datatype_ptr_dropn".text |.| arguments(args)]

pub fun gen-hole-call(tp: ktype)
  match tp.c-type
    CPrim("kk_integer_t") -> "kk_integer_zero".text
    CPrim("kk_string_t") -> "kk_string_empty()".text
    CPrim("kk_bytes_t") -> "kk_bytes_empty()".text
    CPrim("kk_vector_t") -> "kk_vector_empty()".text
    _ -> "kk_datatype_null()".text
