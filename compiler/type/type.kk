module compiler/type/type

import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/id
import compiler/common/range
import compiler/common/failure
import compiler/kind/kind
import std/data/sort
import std/core/unsafe
import std/core/undiv
// Updated to #7083c02 on 12/19/25

pub type ktype
  // forall a b c. phi, psi => rho 
  // - There is at least one variable
  // - Every variable occurs at least once in rho
  // - Variables are canonically ordered
  // - Rho has kind *
  TForAll(vars: list<type-var>, r: ktype) 
  // (x:a, y:b, z:c) -> m d
  TFun(args: list<(name, ktype)>, e: ktype, t: ktype) // keffect
  // Type constant (primitive, label, or newtype; not -> or =>)
  TCon(constant: type-con)
  // Type variable (cannot instantiate to -> or =>)
  TVar(variable: type-var)
  // Application of datatypes
  TApp(t: ktype, args: list<ktype>)
  // Type synonym indirection
  // first `list<ktype>` is the actual arguments
  // final `ktype` is the "real" type (expanded)
  TSyn(syn: type-syn, args: list<ktype>, t: ktype)

pub fun ktype/show(tp: ktype): div string
  match tp
    TForAll(vars, t) -> "forall " ++ vars.show-list(show) ++ " => " ++ t.show
    TFun(args, eff, t) -> "(" ++ args.show-list(fn((name, tp1)) name.name/name/show ++ tp1.pretend-decreasing.show) ++ " -> " ++ eff.show ++ " " ++ t.show ++ ")"
    TCon(c) -> c.name.name/name/show
    TVar(v) -> v.tid.show-id
    TApp(t, args) -> t.show ++ " " ++ args.show
    TSyn(syn, args, t) -> syn.name.name/name/show ++ " " ++ args.show ++ " " ++ t.show
  
// Various synonyms of types
pub alias scheme = ktype
pub alias sigma = ktype // polymorphic type
pub alias tau = ktype // monomorphic type 
pub alias rho = ktype // unqualified type
pub alias keffect = tau

// An inference type can contain type variables of flavour 'Meta' or 'Skolem'
// pub alias inferType = ktype;

// Variables in a type which have an identifier and kind
// One can ask for the free type variables in a type, and substitute them with 'Tau' types.
pub type type-var
  TypeVar(
    tid: id,
    kind: kind,
    flavour: flavour
  )

pub fun show(t: type-var): string
  t.tid.show-id ++ "::" ++ t.kind.show

pub fun tv/(==)(t1: type-var, t2: type-var): bool
  t1.tid == t2.tid // also flavours?

pub fun tv/cmp(t1: type-var, t2: type-var)
  cmp(t1.tid, t2.tid) // also flavours?

// The flavour of a type variable. Types in a "Type.Assumption" (Gamma) and inferred types in "Core.Core"
// are always of the 'Bound' flavour. 'Meta' and 'Skolem' type variables only ever occur during type inference.
// Kind and Type variables come in three flavours: 'Unifiable'
// variables can be unified, 'Skolem's are non-unifiable (fresh)
// variables, and 'Bound' variables are bound by a quantifier.
pub type flavour
  Bound
  Skolem
  Meta 

pub fun flavour/(==)(f1: flavour, f2: flavour): bool
  match (f1, f2)
    (Meta, Meta) -> True
    (Skolem, Skolem) -> True
    (Bound, Bound) -> True
    _ -> False

// Type constants have a name and a kind
pub type type-con
  TypeCon(
    name: name,
    kind: kind
  )

pub fun typecon/(==)(t1: type-con, t2: type-con): bool
  name/(==)(t1.name, t2.name)

pub fun typecon/cmp(t1: type-con, t2: type-con): order
  t1.name.name/name/cmp(t2.name)

// Type synonyms have an identifier, kind, and rank (= partial ordering among type synonyms)
pub type type-syn
  TypeSyn(
    name: name,
    kind: kind,
    rank: synonym-rank,
    info: maybe<syn-info>
  )

pub fun typesyn/(==)(t1: type-syn, t2: type-syn): bool
  name/(==)(t1.name, t2.name)

pub fun typesyn/cmp(t1: type-syn, t2: type-syn): order
  t1.name.name/name/cmp(t2.name)

// The rank of a type synonym gives a relative ordering among them. This is used
// during unification to increase the chance of matching up type synonyms.
pub alias synonym-rank = int

pub fun max-synonym-rank(t: ktype): synonym-rank
  fun max-synonym-ranks(tps: list<ktype>): int
    tps.foldr(0) fn(t1, r) 
      max(r, max-synonym-rank(t1.pretend-decreasing))
  match t
    TForAll(_, r) -> max-synonym-rank(r.pretend-decreasing)
    TFun(args, eff, ty) -> max-synonym-ranks(Cons(ty, Cons(eff, args.map(fn (f) -> f.snd))).pretend-decreasing)
    TCon(_) -> 0
    TVar(_) -> 0
    TApp(ty, tps) -> max-synonym-ranks(Cons(ty, tps).pretend-decreasing)
    TSyn(syn, args, ty) -> max(syn.rank, max-synonym-ranks(Cons(ty, args).pretend-decreasing))

// Information about types
// Defined here to avoid circular dependencies
// Data type information: name, kind, type arguments, and constructors
pub type data-info
  DataInfo(
    sort: data-kind,
    name: name,
    kind: kind,
    params: list<type-var>, // arguments
    constrs: list<con-info>,
    range: range,
    def: data-def, // value(raw,scan), normal, lazy, open, linear
    deffect: data-effect,
    is-rec: bool, // recursive datatype?
    vis: visibility,
    doc: string
  )

pub fun datainfo/(==)(d1: data-info, d2: data-info): bool
  name/(==)(d1.name, d2.name)

pub fun datainfo/show(d: data-info): string
  d.name.name/name/show

pub fun is-extend(d: data-info): bool
  d.def.is-extend

pub fun is-open(d: data-info): bool
  d.def.is-open

pub fun is-literal(d: data-info): bool
  val n = d.name
  n == nameTpInt || n == nameTpChar || n == nameTpString || n == nameTpFloat

pub fun di/is-lazy(d: data-info): bool
  d.def.datadef/is-lazy

pub fun lazy-name(di: data-info, stem: string): exn name
  type-qualified-name(di.name, "lazy-" ++ stem).unqualify

// Constructor information: constructor name, name of the newtype, field types, and the full type of the constructor
pub type con-info
  ConInfo(
    name: name,
    typeName: name,
    // sort: name
    foralls: list<type-var>, // quantifiers
    existentials: list<type-var>, // existentials
    params: list<(name, ktype)>, // field types
    typeScheme: ktype, // scheme
    typeSort: data-kind, // inductive, coinductive, retractive
    range: range,
    paramRanges: list<range>,
    paramVis: list<visibility>,
    singleton: bool, // only constructor of this type
    orderedParams: list<(name, ktype)>, // fields ordered by size
    valueRepr: value-repr,
    mblazy: maybe<fipT>, // also Just for indirection nodes
    tag: int,
    vis: visibility,
    doc: string
  )

pub fun coninfo/(==)(c1: con-info, c2: con-info): bool
  name/(==)(c1.name, c2.name)

pub fun coninfo/show(c: con-info): string
  c.name.name/name/show

pub fun coninfo/size(c: con-info, p: platform)
  p.size(c.valueRepr)

pub fun coninfo/scan-count(c: con-info)
  c.valueRepr.scan-count

pub fun coninfo/is-lazy(c: con-info): bool
  c.mblazy.is-just

pub fun coninfo/lazy-fip(c: con-info): fipT
  match c.mblazy
    Just(fp) -> fp
    Nothing -> noFip

// A type synonym is quantified by type parameters
pub type syn-info
  SynInfo(
    name: name,
    kind: kind,
    params: list<type-var>, // type parameters
    tp: ktype, // result type
    rank: synonym-rank,
    range: range,
    pub vis: visibility,
    doc: string
  )

pub fun syninfo/(==)(s1: syn-info, s2: syn-info): bool
  name/(==)(s1.name, s2.name)

pub fun syninfo/show(s: syn-info): string
  s.name.name/name/show

// Is a type variable 'Bound'
pub fun tv/is-bound(t: type-var): bool
  t.flavour == Bound

// Is a type variable 'Meta' (e.g. unifiable)
pub fun tv/is-meta(t: type-var): bool
  t.flavour == Meta

// Is a type variable a 'Skolem' (e.g. not unifiable)
pub fun tv/is-skolem(t: type-var): bool
  t.flavour == Skolem

pub fun is-mono-type(tp: ktype): bool
  match tp.expand-syn
    TForAll -> False
    _ -> True


// Split / add quantifiers

// Split type into a list of universally quantified type variables and a rho type
pub fun split-type-scheme(tp: ktype): (list<type-var>, rho)
  // We must split a synonym if its expansion includes further quantifiers
  fun must-split(tp': ktype)
    match tp'
      TForAll -> True
      TSyn(_, _, tp'') -> tp''.must-split
      _ -> False
  match tp
    TForAll(vars, t) -> (vars, t)
    _ -> if tp.must-split then tp.pretend-decreasing.split-type-scheme else ([], tp)

fun split-con-tp(tp: ktype): (list<(name, ktype)>, keffect, ktype)
  match tp.expand-syn
    TFun(args, eff, res) -> (args, eff, res)
    res -> ([], typeTotal, res)

// Find all quantified type variables, but do not expand synonyms
fun shallow-split-vars(tp: ktype)
  match tp
    TForAll(vars, t) -> (vars, t)
    _ -> ([], tp)

pub fun expand-syn(tp: ktype): ktype
  match tp
    TSyn(_, _, t) -> expand-syn(t)
    _ -> tp

// A type in canonical form has no type synonyms and expanded effect types.
pub fun canonical-form(tp: ktype): pure ktype
  match tp
    TSyn(_, _, t) -> canonical-form(t)
    TForAll(vars, t) -> TForAll(vars, canonical-form(t))
    TApp(t, ts) -> TApp(canonical-form(t), ts.map(canonical-form))
    TFun(args, eff, res) -> TFun(args.map(fn((name, t)) (name, t.canonical-form)), order-effect(eff.canonical-form), res.canonical-form)
    _ -> tp

// A type in minimal form is canonical and has no named function arguments
pub fun minimal-form(tp: ktype): pure ktype
  match tp
    TSyn -> tp.canonical-form
    TForAll(vars, t) -> TForAll(vars, t.canonical-form)
    TApp(t, ts) -> TApp(t.canonical-form, ts.map(canonical-form))
    TFun(args, eff, res) -> TFun(args.map(fn((_, t)) (name/nil, t.canonical-form)), order-effect(eff.canonical-form), res.canonical-form)

// Create a type scheme from a list of quantifiers
pub fun make-scheme(vars: list<type-var>, rho: rho): scheme
  val (vars0, _) = rho.split-type-scheme
  tForall(vars ++ vars0, rho)

pub fun quantify-type(vars: list<type-var>, tp: scheme): scheme
  val (vars0, rho) = tp.split-type-scheme
  tForall(vars ++ vars0, rho)

fun tForall(vars: list<type-var>, rho: rho): scheme
  match vars
    Nil -> rho
    _ -> TForAll(vars, rho)

pub fun apply-type(tp1: ktype, tp2: ktype): ktype
  fun must-split(tp: ktype): bool
    match tp
      TApp -> True
      TSyn(_, _, tp) -> tp.must-split
      _ -> False
  match tp1
    TApp(tp, tps) -> TApp(tp, tps ++ [tp2])
    TSyn(_, _, tp) | tp.must-split -> apply-type(tp, tp2)
    _ -> TApp(tp1, [tp2])

pub fun type-arities(tp: ktype): (int, int)
  match tp.split-fun-scheme
    Just((tvars, pars, _, _)) -> (tvars.length, pars.length)
    Nothing -> (0, 0)

pub fun split-fun-scheme(tp: scheme): maybe<(list<type-var>, list<(name, tau)>, keffect, tau)>
  val (tvars, rho) = tp.split-type-scheme
  match rho.split-fun-type
    Just((pars, eff, res)) -> Just((tvars, pars, eff, res))
    Nothing -> Nothing

// Assertions
// Is this a type variable?
pub fun tp/is-tvar(tp: ktype): bool
  match tp
    TVar -> True
    TSyn(_, _, t) -> t.tp/is-tvar
    _ -> False

// Is this a type constant?
pub fun tp/is-tcon(tp: ktype): bool
  match tp
    TCon -> True
    TSyn(_, _, t) -> t.tp/is-tcon
    _ -> False

// Is this a rho type? (i.e. no outermost quantifiers)
pub fun is-rho(tp: ktype): bool
  match tp
    TForAll -> False
    TSyn(_, _, t) -> t.is-rho
    _ -> True

// Is this a tau type? (i.e. no quantifiers anywhere)
pub fun is-tau(tp: ktype): bool
  match tp
    TForAll -> False
    TFun(xs, e, r) -> xs.all(_.snd.pretend-decreasing.is-tau) && e.is-tau && r.is-tau
    TCon -> True
    TVar -> True
    TApp(a, b) -> a.is-tau && b.all(_.pretend-decreasing.is-tau)
    TSyn(_, _, t) -> t.is-tau

// Is this a function type?
pub fun is-fun(tp: ktype): bool
  match split-fun-type(tp)
    Just(_) -> True
    Nothing -> False

// Split function type into argument list, effect type, and result type
pub fun split-fun-type(tp: ktype): maybe<(list<(name, ktype)>, ktype, ktype)>
  match tp
    TFun(args, eff, res) -> Just((args, eff, res))
    TSyn(_, _, t) -> t.split-fun-type
    _ -> Nothing

// Primitive types
pub val typeInt = TCon(tconInt)
pub val tconInt = TypeCon(nameTpInt, kindStar)
pub fun is-type-int(t: ktype): bool
  match t
    TCon(c) -> c == tconInt
    _ -> False

pub val typeInt32 = TCon(TypeCon(nameTpInt32, kindStar))
pub val typeEvIndex = TSyn(TypeSyn(nameTpEvIndex, kindStar, 0, Nothing), [], typeSSizeT)
pub val typeSSizeT = TCon(TypeCon(nameTpSSizeT, kindStar))
pub val typeFloat = TCon(TypeCon(nameTpFloat, kindStar))
pub val typeChar = TCon(tconChar)
pub val tconChar = TypeCon(nameTpChar, kindStar)
pub fun is-type-char(t: ktype): bool
  match t
    TCon(c) -> c == tconChar
    _ -> False

pub val typeString = TCon(tconString)
pub val tconString = TypeCon(nameTpString, kindStar)
pub fun is-type-string(t: ktype): bool
  match t
    TCon(c) -> c == tconString
    _ -> False

pub fun type-resume-context(b: tau, e: keffect, e0: keffect, r: tau): tau
  val tcon = TypeCon(nameTpResumeContext, kind-fun(kindStar, kind-fun(kindEffect, kind-fun(kindEffect, kind-fun(kindStar, kindStar)))))
  TApp(TCon(tcon), [b, e, e0, r])

pub val typeRef = TCon(TypeCon(nameTpRef, kind-fun(kindHeap, kind-fun(kindStar, kindStar))))
pub val tconLocalVar = TypeCon(nameTpLocalVar, kind-fun(kindHeap, kind-fun(kindStar, kindStar)))
pub fun is-type-localvar(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon(TypeCon(name)), [_, _]) -> name == nameTpLocalVar
    _ -> False

pub fun is-value-operation(tp: ktype): bool
  match tp.split-type-scheme
    // TSyn(syn, [_]) -> syn.name == nameTpValueOp
    (_, TApp(TCon(TypeCon(nm)), [_, _])) -> nm == nameTpValueOp
    _ -> False

pub fun make-value-operation(eff: ktype, tp: ktype)
  val k = kind-fun(kindEffect, kind-fun(kindStar, kindStar))
  TApp(TCon(TypeCon(nameTpValueOp, k)), [eff, tp])

pub fun order-effect(tp: tau): <exn,div> tau
  val (ls, tl) = extract-ordered-effect(tp)
  ls.foldr(tl, effect-extend)

pub fun extract-ordered-effect(tp: tau): pure (list<tau>, tau)
  val (labs, tl) = extract-effect-extend(tp)
  fun expand(l)
    val (ls, tl') = extract-effect-extend(l)
    if tl'.is-effect-empty && !ls.is-nil then ls else [l]
  val labss = labs.map(expand).concat
  fun label/(<)(l1: tau, l2: tau) 
    label-name/cmp(l1.label-name, l2.label-name).is-lt
  val slabs = labss.sort()
  (slabs, tl)

pub fun contains-local-effect(eff: tau): pure bool
  val (ls,_) = eff.extract-ordered-effect
  ls.any(_.label-name == nameTpLocal)

pub fun label-name(tp: tau): exn name
  tp.label-name-ex.fst

pub fun label-name-full(tp: tau): pure name
  val (name, i, _) = tp.label-name-ex
  val ids = i.show-id
  postpend(name, "$" ++ ids)

pub fun label-name-ex(tp: tau): exn (name, int, list<tau>)
  match tp.expand-syn
    TCon(tc) -> (tc.name, 0, [])
    TApp(TCon(TypeCon(name)), [htp]) | name == nameTpHandled || name == nameTpHandled1 || name == nameTpNHandled || name == nameTpNHandled1 -> 
      // use the handled effect name for handled<htp> types.
      htp.pretend-decreasing.label-name-ex
    TApp(TCon(tc), targs as Cons(TVar(TypeVar(id, kind, Skolem)), _)) | kind == kindScope -> 
      (tc.name, id, targs)
    TApp(TCon(tc), targs) -> 
      if (tc.name == nameEffectExtend) then 
        throw("non-expanded type synonym used as label") 
      else (tc.name, 0, targs)
    _ -> throw("type/type labelNameEx: label is not a constant")

pub val typePartial = TApp(tconHandled, [TCon(TypeCon(nameTpPartial, kindHandled))])
pub val typeLocal = TCon(TypeCon(nameTpLocal, kindLocal))
pub fun is-type-local(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon(c)) -> c.name == nameTpLocal
    _ -> False

pub val tconHandled = TCon(TypeCon(nameTpHandled, kind-fun(kindHandled, kindLabel)))
pub val tconHandled1 = TCon(TypeCon(nameTpHandled1, kind-fun(kindHandled1, kindLabel)))

pub fun wrap-handled-from-data-effect(de: data-effect, eff: ktype)
  match de
    DataEffect(is-named, is-linear) ->
      val name = make-tp-handled(is-named, is-linear)
      val kind = kind-fun(kindHandled, kindLabel)
      TApp(TCon(TypeCon(name, kind)), [eff])
    DataNoEffect -> eff

fun is-async-function(tp: ktype): pure bool
  val rho = tp.split-type-scheme.snd
  match rho.split-fun-type
    Just((_, eff, _)) ->
      val (ls, _) = eff.extract-effect-extend
      ls.any(is-effect-async)
    _ -> False

fun is-effect-async(tp: tau): div bool
  match tp.expand-syn
    TForAll(_, rho) -> rho.is-effect-async
    TFun(_, eff) -> eff.is-effect-async
    TApp(TCon(TypeCon(name)), [t]) | name == nameTpHandled -> t.is-effect-async
    TCon(TypeCon(hxName)) -> hxName == nameTpAsync
    _ -> False

pub fun is-effect-tyvar(tp: tau): bool
  match tp
    TVar(v) -> v.kind == kindEffect
    _ -> False

pub val effectEmpty = TCon(TypeCon(nameEffectEmpty, kindEffect))
pub fun is-effect-empty(tp: tau): bool
  match tp.expand-syn
    TCon(tc) -> tc.name == nameEffectEmpty
    _ -> False

pub fun effect-extend-no-dup(label: tau, eff: tau): pure tau
  val (ls, _) = label.extract-effect-extend
  match ls
    Nil ->
      val (els, _) = eff.extract-effect-extend
      if els.any(_.eq-type(label)) then eff // (label `elem` els)
      else app-effect-extend(label, eff)
    _ -> ls.effect-extend-no-dups(eff)

pub fun effect-extend-no-dups(labels: list<tau>, eff: tau): pure tau
  labels.foldr(eff, effect-extend-no-dup)

pub fun effect-extend(label: tau, eff: tau): pure tau
  val (ls, _) = label.extract-effect-extend
  match ls
    Nil -> app-effect-extend(label, eff)
    _ -> effect-extends(ls, eff)

pub val tconEffectExtend = TypeCon(nameEffectExtend, kind-fun(kindLabel, kind-fun(kindEffect, kindEffect)))

pub fun effect-extends(labels: list<tau>, eff: tau): pure tau
  // prevent over expansion of type synonyms here (see also: core/parse/teffect)
  match labels
    Cons(lab as TSyn(TypeSyn(_, kind)), _) | eff.is-effect-empty && kind == kindEffect -> lab
    _ -> labels.foldr(eff, effect-extend)

pub fun effect-fixed(labels: list<tau>): pure tau
  effect-extends(labels, effectEmpty)

pub fun is-effect-fixed(tp: tau): pure bool
  tp.extract-effect-extend.snd.is-effect-empty

pub fun extract-effect-extend(t: tau): pure (list<tau>, tau)
  fun extractLabel(l: tau): pure list<tau>
    match l.expand-syn
      TApp(TCon(tc), [_, _]) | tc.name == nameEffectExtend ->
        val (ls, tl) = l.pretend-decreasing.extract-effect-extend
        if (!tl.is-effect-fixed) then throw("label was not a fixed effect type alias")
        else ls
      _ -> [l]
  match t.expand-syn
    TApp(TCon(tc), [l, e]) | tc.name == nameEffectExtend ->
      val (ls, tl) = e.pretend-decreasing.extract-effect-extend
      (l.extractLabel ++ ls, tl)
    _ -> ([], t)

pub fun shallow-extract-effect-extend(t: tau): (list<tau>, tau)
  match t
    TApp(TCon(tc), [l,e]) | tc.name == nameEffectExtend ->
      val (ls, tl) = e.shallow-extract-effect-extend
      (Cons(l, ls), tl)
    _ -> ([], t)

pub fun shallow-effect-extend(label: tau, eff: tau): pure tau
  // We do not expand type synonyms in the label here by using the 'shallow' version of extract
  // this means that type synonyms of kind E (ie. a fixed effect row) could stay around in
  // the label (which should have kind X).
  // We use this to keep type synonyms around longer -- but during unification we got to be
  // careful to expand such synonyms
  val (ls, _) = label.shallow-extract-effect-extend
  match ls
    Nil -> app-effect-extend(label, eff)
    _ -> effect-extends(ls, eff)

pub fun app-effect-extend(label: ktype, eff: ktype)
  fun has-kind-label(l)
    val k = l.expand-syn.kind-of
    k == kindLabel || k == kindEffect
  if !has-kind-label(label) then
    throw("label has not kind X: " ++ label.show ++ " " ++ eff.show ++ " " ++ label.expand-syn.kind-of.show)
  TApp(TCon(tconEffectExtend), [label, eff])

pub fun kind-of(tau: ktype)
  fun kind-apply(args: list<ktype>, k: kind)
    match (args, k)
      (Nil, k') -> k'
      (Cons(_, rst), KApp(KApp, k2)) -> kind-apply(rst, k2)
      (args, k) -> fail("type/type/kind-of: illegal kind in application? " ++ k.show ++ " to " ++ args.show ++ "\n  " ++ tau.show)
  match tau
    TForAll(_, tp) -> tp.kind-of
    TFun -> kindStar
    TVar(v) -> v.kind
    TCon(c) -> c.kind
    TSyn(syn) -> syn.kind
    TApp(tp, args) -> kind-apply(args, tp.kind-of)

fun unsafe-type(f: () -> pure tau): tau
  unsafe-total
    try(f) fn(e) // TODO: Replace this with exit
      TCon(TypeCon("error".new-name, kindStar))

pub val typeDivergent = unsafe-type({single-eff(nameTpDiv)})
fun single-eff(nm:name)
  effect-extend(TCon(TypeCon(nm, kindLabel)), effectEmpty)
pub val typeTotal = effectEmpty
pub val tconTotal = TypeCon(nameEffectEmpty, kindEffect)

pub fun is-type-total(t: tau): bool
  match t
    TCon(c) -> c == tconTotal
    _ -> False

pub val typePure = unsafe-type({effect-fixed([typePartial, typeDivergent])})
pub val typeBool = TCon(tconBool)
pub fun is-type-bool(t: tau): bool
  match t
    TCon(c) -> c == tconBool
    _ -> False
pub val tconBool = TypeCon(nameTpBool, kindStar)
pub fun is-type-unit(t: tau): bool
  match t
    TCon(c) -> c == tconUnit
    _ -> False
// Type of ctail
pub fun type-cctx(tp: tau)
  TSyn(tsynCCtx, [tp], TApp(typeCCtxx, [tp, tp]))
pub val tsynCCtx = TypeSyn(nameTpCCtx, kind-fun(kindStar, kindStar), 0, Nothing)
pub val typeCCtxx = TCon(tconCCtxx)
pub val tconCCtxx = TypeCon(nameTpCCtxx, kind-fun(kindStar, kind-fun(kindStar, kindStar)))
// Type of cfield
pub val typeFieldAddr = TCon(tconFieldAddr)
pub val tconFieldAddr = TypeCon(nameTpFieldAddr, kind-fun(kindStar, kindStar))
pub val typeVector = TCon(TypeCon(nameTpVector, kind-fun(kindStar, kindStar)))
pub val typeList = TCon(tconList)
pub val tconList = TypeCon(nameTpList, kind-fun(kindStar, kindStar))
pub val typeEv = TCon(tconEv)
pub val tconEv = TypeCon(nameTpEv, kind-fun(kindStar, kindStar))
pub fun is-ev-type(tp: tau): bool
  match tp
    TCon(c) -> c == tconEv
    _ -> False
pub fun make-ev-type(arg: tau): tau
  type-app(typeEv, [arg])
// Create an application (reduced form)
pub fun type-app(tau: tau, args: list<tau>): tau
  match args
    Nil -> tau
    _ -> match tau
      TApp(tau', ts0) -> TApp(tau', ts0 ++ args)
      _ -> TApp(tau, args)

pub val typeUnit = TCon(tconUnit)
pub val tconUnit = TypeCon(nameTpUnit, kindStar)
pub val typeVoid = TCon(TypeCon(nameTpVoid, kindStar))
pub val typeReuse = TCon(TypeCon(nameTpReuse, kindStar))
pub val typeAny = TCon(TypeCon(nameTpAny, kindStar))
pub fun type-make-tuple(tps)
  match tps
    Nil -> typeUnit
    [tp] -> tp
    _ -> type-app(type-tuple(tps.length), tps)

pub fun type-tuple(n: int)
  TCon(TypeCon(name-tuple(n), kind-fun-n(kindStar.replicate(n), kindStar)))
pub val typeOptional = TCon(tconOptional)
pub val tconOptional = TypeCon(nameTpOptional, kind-fun(kindStar, kindStar))
pub fun is-optional(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon(tc), [_]) -> tc == tconOptional
    _ -> False
pub fun make-optional(tp: ktype): ktype
  TApp(typeOptional, [tp])

pub fun un-optional(tp: ktype): ktype
  match tp.expand-syn
    TApp(TCon(tc), [t]) | tc == tconOptional -> t
    _ -> tp

// From Infer.hs
// A delay ?type
pub fun is-delay(tp: ktype): bool
  match tp
    TSyn(syn, [_, _], _) -> syn.name == nameTpDelay
    _ -> False
// A unit function type
pub fun is-delayed-type(tp: ktype): bool
  match tp.expand-syn
    TFun([]) -> True
    _ -> False
pub fun get-type-name(tp: ktype, ?kk-file-line: string): pure name
  match tp.expand-syn
    TApp(TCon(tc)) -> tc.name 
    TCon(tc) -> tc.name
    _ -> fail("compiler/compiler/type/get-type-name " ++ tp.show ++ " : " ++ ?kk-file-line)
pub fun type-is-case-legal(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon()) -> True
    TCon() -> True
    _ -> False
pub fun effect-name-from-label(eff: keffect): pure name
  match eff.expand-syn
    TApp(TCon(tc), [hx]) | tc.name == nameTpHandled || tc.name == nameTpHandled1 || tc.name == nameTpNHandled || tc.name == nameTpNHandled1 -> hx.effect-name-from-label
    TCon(tc) -> tc.name
    TSyn(syn) -> syn.name
    TApp(TCon(tc)) -> tc.name
    _ -> fail("compiler/type/type/effect-name-from-label: invalid effect: " ++ eff.show) 


// Remove type synonym indirections
fun prune-syn(rho: rho): rho
  match rho
    TSyn(_, _, t) -> t.prune-syn
    TApp(t1, ts) -> TApp(t1.prune-syn, ts.map(_.pretend-decreasing.prune-syn))
    _ -> rho

fun tv/to-type(v: type-var)
  TVar(v)

fun tcon/to-type(c: type-con)
  TCon(c)

// fun ktype/(==)(t1: ktype, t2: ktype): pure bool
//   eq-type(t1, t2)

fun elem-type(t: ktype, ts: list<ktype>)
  ts.any(fn(t1) t.eq-type(t1))

pub fun eq-type(tp1: ktype, tp2: ktype)
  match (tp1.expand-syn, tp2.expand-syn)
    (TForAll(vs1, t1), TForAll(vs2, t2)) -> 
      vs1 == vs2 && eq-type(t1, t2)
    (TFun(pars1, eff1, res1), TFun(pars2, eff2, res2)) -> 
      pars1.map(snd).eq-types(pars2.map(snd))
        && eff1.match-effect(eff2) && res1.eq-type(res2)
    (TCon(c1), TCon(c2)) -> c1 == c2
    (TVar(v1), TVar(v2)) -> v1 == v2
    (TApp(t1, ts1), TApp(t2, ts2)) -> t1.eq-type(t2) && eq-types(ts1, ts2)
    _ -> False

pub fun eq-types(t1: list<ktype>, t2: list<ktype>): pure bool
  t1.zipwith(t2, eq-type).all(id)

fun match-effect(eff1: tau, eff2: tau): pure bool
  eq-type(eff1.order-effect, eff2.order-effect)
