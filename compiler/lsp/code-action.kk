// `textDocument/codeAction`.
//
// Ports upstream `LanguageServer/Handler/CodeAction.hs`: with the cursor on a
// data type, offer to GENERATE the definitions one usually writes by hand for
// it -- `show`, `(==)`, `cmp`, `order2`, `map`, and a general overloaded
// traversal. Each action is a workspace edit inserting the generated definition
// just after the type declaration.
//
// The generators build a `def<user-type>` -- SOURCE syntax, not core -- and the
// syntax pretty-printer renders it. That is what makes the output something a
// human would have written: it goes through the same printer as any other Koka
// source.
//
// Two scaffolds do the structural work:
//   `syn-general-unary` -- one argument (`show`, `map`, overloaded)
//   `syn-binary-op`     -- two arguments (`==`, `cmp`, `order2`)
// Each takes a callback that builds the per-constructor branches; everything
// else (type parameters, implicit dictionary parameters for polymorphic
// fields, the enclosing lambda and its annotation) is shared.
module compiler/lsp/code-action

import std/os/path
import std/core/undiv
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/syntax
import compiler/common/unique
import compiler/common/nice
import compiler/kind/kind
import std/data/rb-map
import compiler/kind/newtypes
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/lib/pprint
import compiler/lib/json
import compiler/lsp/jsonrpc
import compiler/lsp/conversions
import compiler/lsp/state

//----------------------------------------------------------------------
// small helpers over user types
//----------------------------------------------------------------------

val rng0 = range/null

fun tp-var(n: name): user-type
  TpVar(n, rng0)

fun tp-con(n: name): user-type
  TpCon(n, rng0)

// Quantify over the given type variables
fun tp-forall(tps: list<user-type>, tp: user-type): user-type
  tps.foldr(tp) fn(t, acc)
    match t
      TpVar(nm) -> TpQuan(QForall, TypeBinder(nm, KindNone, rng0, rng0), acc, rng0)
      _ -> acc

fun tp-var-name(t: user-type): name
  match t
    TpVar(x) -> x
    _ -> name/nil

// upstream's hand-written `Eq (KUserType k)` instance -- used to decide whether
// a field has the SAME type as the datatype being generated for, in which case
// the generated function recurses on itself rather than calling a parameter.
fun ut/(==)(a: user-type, b: user-type): div bool
  match (a, b)
    (TpVar(x), TpVar(y)) -> x == y
    (TpCon(x), TpCon(y)) -> x == y
    (TpApp(x, xs), TpApp(y, ys)) ->
      x == y && xs.length == ys.length && xs.zip(ys).all(fn((p, q)) p == q)
    (TpFun(xs, e1, r1), TpFun(ys, e2, r2)) ->
      xs.length == ys.length && xs.zip(ys).all(fn(((_, p), (_, q))) p == q) &&
      e1 == e2 && r1 == r2
    (TpQuan(q1, b1, t1), TpQuan(q2, b2, t2)) ->
      q1.uq/int == q2.uq/int && b1.name == b2.name && t1 == t2
    _ -> False

fun uq/int(q: user-quantifier): int
  match q
    QForall -> 0
    QExists -> 1
    QSome -> 2

fun is-tp-var(t: user-type): bool
  match t
    TpVar -> True
    _ -> False

// a `*`-kinded type variable is one the generated function can recurse into;
// higher-kinded ones get no dictionary parameter
fun is-star-type-var(tv: type-var): bool
  tv.kind.has-kind-star-result

fun mk-bind(arg: name, r: range): value-binder<maybe<user-type>, maybe<user-expr>>
  ValueBinder(arg, Nothing, Nothing, r, r)

fun mk-bindt(arg: name, tp: user-type, r: range): value-binder<maybe<user-type>, maybe<user-expr>>
  ValueBinder(arg, Just(tp), Nothing, r, r)

fun is-fun-tp(tp: ktype): div bool
  match tp.expand-syn
    TFun -> True
    TForAll(_, t) -> t.is-fun-tp
    _ -> False

// A checked type back into SOURCE syntax, using the nice
// names so the printed result reads `a`/`b`/`e` rather than raw ids.
fun user-tp(tp: ktype): _ user-type
  match tp
    TVar(tv) -> tp-var(tv.show-tv)
    TCon(TypeCon(x)) -> tp-con(x)
    TApp(f, xs) -> TpApp(f.user-tp, xs.map(user-tp), rng0)
    TSyn(syn, xs) -> TpApp(tp-con(syn.name), xs.map(user-tp), rng0)
    TFun(xs, eff, y) -> TpFun(xs.map(fn((n, t)) (n, t.user-tp)), eff.user-tp, y.user-tp, rng0)
    TForAll(tvs, t) -> tp-forall(tvs.map(fn(tv) tp-var(tv.show-tv)), t.user-tp)

fun show-tv(tv: type-var): _ name
  tv.get-nice.new-name

//----------------------------------------------------------------------
// expression helpers
//----------------------------------------------------------------------

fun evar(n: name, r: range): user-expr
  Var(n, False, r)

fun eop(n: name, r: range): user-expr
  Var(n, True, r)

fun app(f: user-expr, args: list<user-expr>, r: range): user-expr
  App(f, args.map(fn(a) (Nothing, a)), r)

fun lstring(s: string, r: range): user-expr
  Literal(LitString(s, r))

val append-op-name = "++".new-name

// Fold string pieces together, merging adjacent literals
// so the generated source reads `"Con(" ++ ...` rather than a chain of joins.
fun append-str(e1: user-expr, e2: user-expr): div user-expr
  match (e1, e2)
    (Literal(LitString(s1)), App(Var(op), Cons((_, Literal(LitString(s2))), Cons((_, s3), Nil)))) | op == append-op-name ->
      append-str(lstring(s1 ++ s2, rng0), s3)
    _ -> App(eop(append-op-name, rng0), [(Nothing, e1), (Nothing, e2)], rng0)

fun guard-true(): user-expr
  evar(nameTrue, rng0)

fun branch1(pat: user-pattern, body: user-expr): user-branch
  Branch(pat, [Guard(guard-true(), body)])

fun pat-var(n: name, r: range): user-pattern
  PatVar(ValueBinder(n, Nothing, PatWild(r), r, r))

//----------------------------------------------------------------------
// the unary scaffold
//----------------------------------------------------------------------

// `mk-branches` receives the datatype's own user-type, the constructor, a
// `recur` that applies the right function to a field (this definition when the
// field's type is the datatype, the matching dictionary parameter when it is a
// type variable, the general name otherwise), a predicate for type variables,
// and the fields as (is-not-a-function, (name, type)).
pub fun syn-general-unary(general-name: name, doc: string, info: data-info,
                          eff-tp: user-type, result-tp: (bool, user-type, int) -> _e user-type,
                          mk-branches: (user-type, con-info,
                                        (user-expr, user-type) -> _e user-expr,
                                        (user-type) -> bool,
                                        list<(bool, (name, user-type))>) -> _e list<user-branch>
                          ): _e user-def
  val drng = info.range
  val ty-params = info.params
  val data-name = info.name
  val tp-params = ty-params.map(fn(tv) tp-var(tv.show-tv))
  val data-tp = TpApp(tp-con(data-name), tp-params, drng)
  // upstream names the receiver after the type when that reads as an
  // identifier, else `this`
  val self-arg = if data-name.show-plain.list.all(fn(c) c.is-alpha-num) then data-name else "this".new-name
  fun tvar-name(t: user-type): _ name
    to-implicit-param-name(new-locally-qualified("", t.tp-var-name.nameStem, general-name.nameStem))
  val star-tvs = ty-params.filter(is-star-type-var).map(fn(tv) tp-var(tv.show-tv))
  // one implicit dictionary parameter per `*`-kinded type variable
  val tv-args = star-tvs.list/map-indexed fn(i, x)
    (x.tvar-name, TpFun([(prepend-raw("tv", x.tp-var-name), x)], eff-tp, result-tp(False, x, i), rng0))
  val tv-binds = tv-args.map(fn((x, tp)) mk-bindt(x, tp, drng))
  val full-tp = tp-forall(tp-params ++ [eff-tp],
                          TpFun(Cons((self-arg, data-tp), tv-args), eff-tp, result-tp(True, data-tp, 0), rng0))
  val def-name = new-locally-qualified("", data-name.nameStem, general-name.nameStem)

  fun make-branch(ci: con-info): _ list<user-branch>
    val crng = ci.range
    fun get-tv(ty: user-type): _ maybe<name>
      match ty
        TpVar(x) -> match star-tvs.find(fn(t) t.tp-var-name == x)
          Just(tvar) -> Just(tvar.tvar-name)
          Nothing -> Nothing
        _ -> Nothing
    fun tp-app-name(ty: user-type): _ user-expr
      match ty.get-tv
        Just(x) -> evar(x.split-implicit-param-name.fst, crng)
        Nothing -> evar(general-name, crng)
    fun recur(ex: user-expr, ty: user-type): _ user-expr
      // the datatype itself recurses on the definition being generated
      if ty == data-tp then app(evar(def-name, crng), [ex], crng)
      else app(ty.tp-app-name, [ex], crng)
    val fields = ci.params.map fn((nm, tp))
      (!tp.is-fun-tp, (nm, tp.user-tp))
    mk-branches(data-tp, ci, recur, is-tp-var, fields)

  val branches = info.constrs.flatmap(make-branch)
  val case-expr = Case(evar(self-arg, drng), branches, False, drng)
  val body = Ann(Lam(Cons(mk-bindt(self-arg, data-tp, drng), tv-binds), case-expr, True, drng), full-tp, drng)
  Def(ValueBinder(def-name, (), body, drng, drng), drng, info.vis,
      DefFun([Borrow], NoFip(False)), InlineAlways, doc)

//----------------------------------------------------------------------
// `show`
//----------------------------------------------------------------------

fun any-function-fields(info: data-info): div bool
  info.constrs.any(fn(c) c.params.any(fn((_, tp)) tp.is-fun-tp))

pub fun syn-show-string(info: data-info): _ user-def
  val doc = "// Automatically generated.\n// Shows a string representation of the `" ++
            info.name.nameStem ++ "` type" ++
            (if info.any-function-fields then " (ignores function fields).\n" else ".\n")
  syn-general-unary("show".new-name, doc, info, tp-var("e".new-name),
                    fn(_a, _b, _c) tp-con(nameTpString)) fn(_dtp, ci, recur, _is-tv, fields)
    val crng = ci.range
    fun pv((keep, (nm, _)): (bool, (name, user-type))): _ user-pattern
      if keep then pat-var(nm, crng) else PatWild(crng)
    val patterns = fields.map(fn(f) (Nothing, f.pv))
    val con-match = PatCon(ci.name, patterns, crng, crng)
    val non-fun = fields.filter(fst).map(snd)
    if fields.is-nil then
      [branch1(con-match, lstring(ci.name.nameStem, crng))]
    else
      fun show-field((fld-n, fld-tp): (name, user-type)): _ list<user-expr>
        [lstring(fld-n.nameStem ++ ": ", crng), recur(evar(fld-n, crng), fld-tp)]
      val start = lstring(ci.name.nameStem ++ "(", crng)
      val parts = non-fun.map(show-field).list/intersperse([lstring(", ", crng)]).concat
      val body = append-str(start, parts.foldr(lstring(")", crng), append-str))
      [branch1(con-match, body)]


//----------------------------------------------------------------------
// `map` and the overloaded traversal (upstream `synMap` / `synOverloaded`)
//----------------------------------------------------------------------

fun con-pattern(ci: con-info, fields: list<(bool, (name, user-type))>, suffix: string,
                wild-functions: bool): _ user-pattern
  val crng = ci.range
  val pats = fields.map fn((keep, (nm, _)))
    // a function field cannot be shown/compared, so it is matched by `_`
    if wild-functions && !keep then (Nothing, PatWild(crng))
    else (Nothing, pat-var(nm.postpend-raw(suffix), crng))
  PatCon(ci.name, pats, crng, crng)

// A skeleton that recurses into every field and
// returns unit -- the starting point for writing a traversal by hand.
pub fun syn-overloaded(info: data-info, general: string): _ user-def
  val doc = "// " ++ general ++ " function for `" ++ info.name.nameStem ++ "` type.\n"
  syn-general-unary(general.new-name, doc, info, tp-var("e".new-name),
                    fn(_a, _b, _c) tp-var("a".new-name)) fn(_dtp, ci, recur, _is-tv, fields)
    val crng = ci.range
    val defs = fields.map fn((_keep, (nm, tp)))
      Def(ValueBinder(prepend-raw("rec", nm), (), recur(evar(nm, crng), tp), crng, crng),
          crng, Private, DefVal, InlineAlways, "")
    val pat = con-pattern(ci, fields, "", False)
    [branch1(pat, Let(DefRec(defs), evar(nameUnit, crng), crng))]

// Rebuild the value, recursing into every field whose type is
// the datatype itself or one of its type parameters. The RESULT type uses fresh
// type variables, so `map` can change the element type.
pub fun syn-map(info: data-info, general: string): _ user-def
  val drng = info.range
  val doc = "// " ++ general ++ " function for `" ++ info.name.nameStem ++ "` type.\n"
  // one fresh `*`-kinded variable per star parameter, for the result type
  val fresh-stars = info.params.filter(is-star-type-var).map(fn(_tv) fresh-typevar(kindStar, Bound))
  fresh-stars.foreach(extend-nice)
  val new-params = info.params.map fn(tv)
    if tv.is-star-type-var then
      // positionally paired with `fresh-stars`
      match fresh-stars.drop(info.params.take-while(fn(t) t.id != tv.id).filter(is-star-type-var).length).head
        Just(f) -> tp-var(f.show-tv)
        Nothing -> tp-var(tv.show-tv)
    else tp-var(tv.show-tv)
  fun result-tp(is-data: bool, tp: user-type, i: int): _ user-type
    if is-data then TpApp(tp-con(info.name), new-params, drng)
    else match fresh-stars.drop(i).head
      Just(f) -> tp-var(f.show-tv)
      Nothing -> tp
  syn-general-unary(general.new-name, doc, info, tp-var("e".new-name), result-tp) fn(data-tp, ci, recur, is-tv, fields)
    val crng = ci.range
    val new-fields = fields.map fn((_keep, (nm, tp)))
      if tp == data-tp || tp.is-tv then recur(evar(nm, crng), tp) else evar(nm, crng)
    val pat = con-pattern(ci, fields, "", False)
    [branch1(pat, app(evar(ci.name, crng), new-fields, crng))]

//----------------------------------------------------------------------
// the binary scaffold
//----------------------------------------------------------------------

// A two-argument generated function: `this` and `other`, matched as a pair so a
// single `match` covers both constructor positions. `mk-branch` receives the
// constructor's INDEX (upstream uses it to decide whether the catch-all
// less/greater branches are still needed) alongside the same recursion helper.
pub fun syn-binary-op(general-name: name, is-op: bool, doc: string, info: data-info,
                      eff-tp: user-type, result-tp: (user-type) -> _e user-type,
                      default-branch: list<user-branch>,
                      mk-branch: (int, user-type, con-info,
                                  (user-expr, user-expr, user-type) -> _e user-expr,
                                  list<(bool, (name, user-type))>) -> _e list<user-branch>
                      ): _e user-def
  val drng = info.range
  val data-name = info.name
  val tp-params = info.params.map(fn(tv) tp-var(tv.show-tv))
  val star-tvs = info.params.filter(is-star-type-var).map(fn(tv) tp-var(tv.show-tv))
  val self-arg = "this".new-name
  val other-arg = "other".new-name
  val data-tp = TpApp(tp-con(data-name), tp-params, drng)
  fun tvar-name(t: user-type): _ name
    to-implicit-param-name(new-locally-qualified("", t.tp-var-name.nameStem, general-name.nameStem))
  // an implicit comparison per `*`-kinded parameter, taking BOTH sides
  val tv-args = star-tvs.map fn(x)
    (x.tvar-name, TpFun([(prepend-raw("this", x.tp-var-name), x), (prepend-raw("other", x.tp-var-name), x)],
                        eff-tp, result-tp(x), rng0))
  val tv-binds = tv-args.map(fn((x, tp)) mk-bindt(x, tp, drng))
  val full-tp = tp-forall(tp-params ++ [eff-tp],
    TpFun(Cons((self-arg, data-tp), Cons((other-arg, data-tp), tv-args)), eff-tp, result-tp(data-tp), rng0))
  val def-name = new-locally-qualified("", data-name.nameStem, general-name.nameStem)

  fun make-branch(ci: con-info, i: int): _ list<user-branch>
    val crng = ci.range
    fun get-tv(ty: user-type): _ maybe<name>
      match ty
        TpVar(x) -> match star-tvs.find(fn(t) t.tp-var-name == x)
          Just(tvar) -> Just(tvar.tvar-name)
          Nothing -> Nothing
        _ -> Nothing
    fun tp-app-name(ty: user-type): _ user-expr
      match ty.get-tv
        Just(x) -> Var(x.split-implicit-param-name.fst, is-op, crng)
        Nothing -> Var(general-name, is-op, crng)
    fun recur(l: user-expr, r: user-expr, ty: user-type): _ user-expr
      if ty == data-tp then app(Var(def-name, is-op, crng), [l, r], crng)
      else app(ty.tp-app-name, [l, r], crng)
    val fields = ci.params.map(fn((nm, tp)) (!tp.is-fun-tp, (nm, tp.user-tp)))
    mk-branch(i, data-tp, ci, recur, fields)

  val branches = info.constrs.list/map-indexed(fn(i, ci) make-branch(ci, i)).concat
  val case-arg = app(evar(name-tuple(2), drng), [evar(self-arg, drng), evar(other-arg, drng)], drng)
  val case-expr = Case(case-arg, branches ++ default-branch, False, drng)
  val body = Ann(Lam(Cons(mk-bindt(self-arg, data-tp, drng),
                          Cons(mk-bindt(other-arg, data-tp, drng), tv-binds)),
                     case-expr, True, drng), full-tp, drng)
  Def(ValueBinder(def-name, (), body, drng, drng), drng, info.vis,
      DefFun([Borrow], NoFip(False)), InlineAlways, doc)

// Match both sides at once
fun tuple-branch(p1: user-pattern, p2: user-pattern, res: user-expr, r: range): user-branch
  branch1(PatCon(name-tuple(2), [(Nothing, p1), (Nothing, p2)], r, r), res)

fun has-single-con(info: data-info): bool
  info.constrs.length == 1

//----------------------------------------------------------------------
// `==`
//----------------------------------------------------------------------

pub fun syn-equality(info: data-info): _ user-def
  val drng = info.range
  val doc = "// Automatically generated.\n// Equality comparison of the `" ++
            info.name.nameStem ++ "` type" ++
            (if info.any-function-fields then " (ignores function fields).\n" else ".\n")
  // with more than one constructor, any mismatched pair is simply not equal
  val default-branch = if info.has-single-con then []
                       else [tuple-branch(PatWild(drng), PatWild(drng), evar(nameFalse, drng), drng)]
  syn-binary-op("==".new-name, True, doc, info, tp-var("e".new-name),
                fn(_t) tp-con(nameTpBool), default-branch) fn(_i, _dtp, ci, recur, fields)
    val crng = ci.range
    val non-fun = fields.filter(fst).map(snd)
    val body = match non-fun
      Nil -> evar(nameTrue, crng)
      _ ->
        val cmps = non-fun.map fn((nm, tp))
          recur(evar(nm, crng), evar(nm.postpend-raw("0"), crng), tp)
        // fold with `&&` so a mismatch short-circuits
        cmps.foldr1-and(crng)
    [tuple-branch(con-pattern(ci, fields, "", True), con-pattern(ci, fields, "0", True), body, crng)]

fun foldr1-and(es: list<user-expr>, r: range): _ user-expr
  match es
    Nil -> evar(nameTrue, r)
    Cons(e, Nil) -> e
    Cons(e, rest) -> app(eop("&&".new-name, r), [e, rest.foldr1-and(r)], r)

//----------------------------------------------------------------------
// `cmp`
//----------------------------------------------------------------------

pub fun syn-ord(info: data-info): _ user-def
  val drng = info.range
  val doc = "// Automatically generated.\n// Comparison of the `" ++
            info.name.nameStem ++ "` type" ++
            (if info.any-function-fields then " (ignores function fields).\n" else ".\n")
  val n-cons = info.constrs.length
  syn-binary-op("cmp".new-name, False, doc, info, tp-var("e".new-name),
                fn(_t) tp-con("order".new-name), []) fn(i, _dtp, ci, recur, fields)
    val crng = ci.range
    val non-fun = fields.filter(fst).map(snd)
    // compare field by field, stopping at the first difference
    fun chain(fs: list<(name, user-type)>): _ user-expr
      match fs
        Nil -> evar("Eq".new-name, crng)
        Cons((nm, tp), Nil) -> recur(evar(nm, crng), evar(nm.postpend-raw("0"), crng), tp)
        Cons((nm, tp), rest) ->
          val this-cmp = recur(evar(nm, crng), evar(nm.postpend-raw("0"), crng), tp)
          val neq = nm.postpend-raw("_order")
          Case(this-cmp, [
            branch1(PatCon("Eq".new-name, [], crng, crng), chain(rest)),
            branch1(pat-var(neq, crng), evar(neq, crng))], False, crng)
    val eq-branch = tuple-branch(con-pattern(ci, fields, "", True),
                                 con-pattern(ci, fields, "0", True), chain(non-fun), crng)
    // constructors are ordered by declaration: everything before this one is
    // less, everything after is greater. The last constructor needs neither.
    if i == n-cons - 1 then [eq-branch]
    else
      val lt = tuple-branch(PatCon(ci.name, [], crng, crng), PatWild(crng), evar("Lt".new-name, crng), crng)
      val gt = tuple-branch(PatWild(crng), PatCon(ci.name, [], crng, crng), evar("Gt".new-name, crng), crng)
      [eq-branch, lt, gt]


//----------------------------------------------------------------------
// `order2`
//----------------------------------------------------------------------

// The fip-friendly comparison: instead of returning a plain `order`, it returns
// `order2<a>` carrying the two values back, so the caller can keep using them
// without re-allocating. Each field comparison therefore has THREE outcomes,
// and the ones that differ must rebuild both sides from the fields compared so
// far plus the field that differed plus the remainder.
pub fun syn-order2(info: data-info): _ user-def
  val drng = info.range
  val doc = "// Automatically generated.\n// Fip comparison of the `" ++
            info.name.nameStem ++ "` type" ++
            (if info.any-function-fields then " (ignores function fields).\n" else ".\n")
  val n-cons = info.constrs.length
  val nm-eq2 = "Eq2".new-name
  val nm-lt2 = "Lt2".new-name
  val nm-gt2 = "Gt2".new-name
  fun result-tp(tp: user-type): user-type
    TpApp(tp-con("order2".new-name), [tp], drng)
  syn-binary-op("order2".new-name, False, doc, info, tp-var("e".new-name), result-tp, []) fn(i, _dtp, ci, recur, fields)
    val crng = ci.range
    val non-fun = fields.filter(fst).map(snd)
    fun con-of(args: list<name>): _ user-expr
      app(evar(ci.name, crng), args.map(fn(a) evar(a, crng)), crng)
    // named sub-patterns bind the values the comparison handed back
    fun pat-eq(nm: name): user-pattern
      PatCon(nm-eq2, [(Just((nm.postpend-raw("_eq"), crng)), PatWild(crng))], crng, crng)
    fun pat-lt(nm: name): user-pattern
      PatCon(nm-lt2, [(Just((nm.postpend-raw("_lt"), crng)), PatWild(crng)),
                      (Just((nm.postpend-raw("_gt"), crng)), PatWild(crng))], crng, crng)
    fun pat-gt(nm: name): user-pattern
      PatCon(nm-gt2, [(Just((nm.postpend-raw("_lt"), crng)), PatWild(crng)),
                      (Just((nm.postpend-raw("_gt"), crng)), PatWild(crng))], crng, crng)
    // `eq-so-far` is reversed as it accumulates
    fun chain(fs: list<(name, user-type)>, eq-so-far: list<name>): _ user-expr
      match fs
        Nil -> app(evar(nm-eq2, crng), [con-of(eq-so-far.reverse)], crng)
        Cons((nm, tp), rest) ->
          val this-cmp = recur(evar(nm, crng), evar(nm.postpend-raw("'"), crng), tp)
          val rest-this = rest.map(fst)
          val rest-other = rest.map(fn((n, _)) n.postpend-raw("'"))
          Case(this-cmp, [
            branch1(pat-eq(nm), chain(rest, Cons(nm.postpend-raw("_eq"), eq-so-far))),
            branch1(pat-lt(nm),
              app(evar(nm-lt2, crng),
                  [con-of(eq-so-far.reverse ++ [nm.postpend-raw("_lt")] ++ rest-this),
                   con-of(eq-so-far.reverse ++ [nm.postpend-raw("_gt")] ++ rest-other)], crng)),
            branch1(pat-gt(nm),
              app(evar(nm-gt2, crng),
                  [con-of(eq-so-far.reverse ++ [nm.postpend-raw("_lt")] ++ rest-other),
                   con-of(eq-so-far.reverse ++ [nm.postpend-raw("_gt")] ++ rest-this)], crng))
          ], False, crng)
    val eq-branch = tuple-branch(con-pattern(ci, fields, "", True),
                                 con-pattern(ci, fields, "'", True), chain(non-fun, []), crng)
    if i == n-cons - 1 then [eq-branch]
    else
      // a different constructor: this one sorts before, and the whole other
      // value is handed back untouched
      val other' = "other'".new-name
      val this' = "this'".new-name
      val lt = tuple-branch(con-pattern(ci, fields, "", True), pat-var(other', crng),
                 app(evar(nm-lt2, crng), [con-of(fields.map(fn((_, (n, _))) n)), evar(other', crng)], crng), crng)
      val gt = tuple-branch(pat-var(this', crng), con-pattern(ci, fields, "'", True),
                 app(evar(nm-gt2, crng), [con-of(fields.map(fn((_, (n, _))) n.postpend-raw("'"))), evar(this', crng)], crng), crng)
      [eq-branch, lt, gt]

//----------------------------------------------------------------------
// the handler
//----------------------------------------------------------------------

// The data type whose declaration contains either end of
// the requested range -- i.e. the one the cursor is in.
fun find-type(nts: newtypes, r: range): _ maybe<data-info>
  nts.rb-map/list.map(snd).find fn(di)
    di.range.range/contains(r.end) || di.range.range/contains(r.start)

pub fun code-actions(st: server-state, ps: json): _ json
  with with-pretty-env
  val duri = ps.field("textDocument").field-of("uri").as-string.default("")
  match st.find-doc(duri)
    Nothing -> JSList([])
    Just(d) ->
      val src = Source(duri.uri-to-path.string, "")
      val r = ps.field("range").range/from-lsp(src)
      match d.ntypes.find-type(r)
        Nothing -> JSList([])
        Just(info) ->
          // Each generator mints fresh type variables, so each gets its own
          // unique counter -- upstream runs every action in its own
          // `Core.runCorePhase 0`.
          val actions = [
            ("Generate show function", info.gen(syn-show-string)),
            ("Generate (==) function", info.gen(syn-equality)),
            ("Generate cmp (comparison) function", info.gen(syn-ord)),
            ("Generate order2 (fip comparison) function", info.gen(syn-order2)),
            ("Generate a map function", info.gen(fn(i) syn-map(i, "map"))),
            ("Generate an overloaded function", info.gen(fn(i) syn-overloaded(i, "overloaded")))]
          JSList(actions.map(fn((title, d0)) to-code-action(title, duri, info.range, d0)))

// A fresh unique counter per action, and the
// data type's own type parameters registered with the nice-name environment so
// the generated source uses `a`/`b`/`e`.
fun gen(info: data-info, f: (data-info) -> _ user-def): _ user-def
  with run-unique(0)
  info.params.foreach(extend-nice)
  f(info)

// The edit inserts the generated definition just AFTER the type declaration,
// separated by a blank line.
fun to-code-action(title: string, uri: string, drng: range, def: user-def): _ json
  val at = drng.range/just-after.range/to-lsp
  val text = "\n\n" ++ def.userdef/pretty.pprint/show
  JSObj([
    ("title", JSString(title)),
    ("kind", JSString("quickfix")),
    ("edit", JSObj([("changes", JSObj([(uri, JSList([
        JSObj([("range", at), ("newText", JSString(text))])]))]))]))])
