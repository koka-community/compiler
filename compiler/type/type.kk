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
  TForAll(vars: list<typeVar>, r: ktype) 
  // (x:a, y:b, z:c) -> m d
  TFun(args: list<(name, ktype)>, e: ktype, t: ktype) // keffect
  // Type constant (primitive, label, or newtype; not -> or =>)
  TCon(constant: typeCon)
  // Type variable (cannot instantiate to -> or =>)
  TVar(variable: typeVar)
  // Application of datatypes
  TApp(t: ktype, args: list<ktype>)
  // Type synonym indirection
  // first `list<ktype>` is the actual arguments
  // final `ktype` is the "real" type (expanded)
  TSyn(syn: typeSyn, args: list<ktype>, t: ktype)

fun ktype/show(tp: ktype): div string
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
pub value struct typeVar
  tid: id
  kind: kind
  flavour: flavour;

fun show(t: typeVar): string
  t.tid.show-id ++ "::" ++ t.kind.show

fun tv/(==)(t1: typeVar, t2: typeVar): bool
  t1.tid == t2.tid // also flavours?

fun tv/cmp(t1: typeVar, t2: typeVar)
  cmp(t1.tid, t2.tid) // also flavours?

// The flavour of a type variable. Types in a "Type.Assumption" (Gamma) and inferred types in "Core.Core"
// are always of the 'Bound' flavour. 'Meta' and 'Skolem' type variables only ever occur during type inference.
// Kind and Type variables come in three flavours: 'Unifiable'
// variables can be unified, 'Skolem's are non-unifiable (fresh)
// variables, and 'Bound' variables are bound by a quantifier.
type flavour
  Bound
  Skolem
  Meta 

fun flavour/(==)(f1: flavour, f2: flavour): bool
  match (f1, f2)
    (Meta, Meta) -> True
    (Skolem, Skolem) -> True
    (Bound, Bound) -> True
    _ -> False

// Type constants have a name and a kind
value struct typeCon
  name: name
  kind: kind;

fun typecon/(==)(t1: typeCon, t2: typeCon): bool
  name/(==)(t1.name, t2.name)

fun typecon/cmp(t1: typeCon, t2: typeCon): order
  t1.name.name/name/cmp(t2.name)

// Type synonyms have an identifier, kind, and rank (= partial ordering among type synonyms)
pub struct typeSyn
  name: name
  kind: kind
  rank: synonymRank
  info: maybe<synInfo>

fun typesyn/(==)(t1: typeSyn, t2: typeSyn): bool
  name/(==)(t1.name, t2.name)

fun typesyn/cmp(t1: typeSyn, t2: typeSyn): order
  t1.name.name/name/cmp(t2.name)

// The rank of a type synonym gives a relative ordering among them. This is used
// during unification to increase the chance of matching up type synonyms.
pub alias synonymRank = int

pub fun max-synonym-rank(t: ktype): synonymRank
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
pub struct dataInfo
  sort: dataKind
  name: name
  kind: kind
  params: list<typeVar> // arguments
  constrs: list<conInfo>
  range: range
  def: dataDef // value(raw,scan), normal, lazy, open, linear
  deffect: dataEffect
  is-rec: bool // recursive datatype?
  vis: visibility
  doc: string

fun datainfo/(==)(d1: dataInfo, d2: dataInfo): bool
  name/(==)(d1.name, d2.name)

fun datainfo/show(d: dataInfo): string
  d.name.name/name/show

pub fun is-extend(d: dataInfo): bool
  d.def.is-extend

pub fun is-open(d: dataInfo): bool
  d.def.is-open

pub fun is-literal(d: dataInfo): bool
  val n = d.name
  n == nameTpInt || n == nameTpChar || n == nameTpString || n == nameTpFloat

pub fun di/is-lazy(d: dataInfo): bool
  d.def.datadef/is-lazy

fun lazy-name(di: dataInfo, stem: string): exn name
  type-qualified-name(di.name, "lazy-" ++ stem).unqualify

// Constructor information: constructor name, name of the newtype, field types, and the full type of the constructor
pub struct conInfo
  name: name
  typeName: name
  // sort: name
  foralls: list<typeVar> // quantifiers
  existentials: list<typeVar> // existentials
  params: list<(name, ktype)> // field types
  typeScheme: ktype // scheme
  typeSort: dataKind // inductive, coinductive, retractive
  range: range
  paramRanges: list<range>
  paramVis: list<visibility>
  singleton: bool // only constructor of this type
  orderedParams: list<(name, ktype)> // fields ordered by size
  valueRepr: valueRepr
  mblazy: maybe<fipT> // also Just for indirection nodes
  tag: int
  vis: visibility
  doc: string;

fun coninfo/(==)(c1: conInfo, c2: conInfo): bool
  name/(==)(c1.name, c2.name)

fun coninfo/show(c: conInfo): string
  c.name.name/name/show

fun coninfo/size(c: conInfo, p: platform)
  p.size(c.valueRepr)

fun coninfo/scan-count(c: conInfo)
  c.valueRepr.scan-count

fun coninfo/is-lazy(c: conInfo): bool
  c.mblazy.is-just

fun coninfo/lazy-fip(c: conInfo): fipT
  match c.mblazy
    Just(fp) -> fp
    Nothing -> noFip

// A type synonym is quantified by type parameters
pub struct synInfo
  name: name
  kind: kind
  params: list<typeVar> // type parameters
  t: ktype // result type
  rank: synonymRank
  range: range
  pub vis: visibility
  doc: string;

fun syninfo/(==)(s1: synInfo, s2: synInfo): bool
  name/(==)(s1.name, s2.name)

fun syninfo/show(s: synInfo): string
  s.name.name/name/show

// Is a type variable 'Bound'
fun tv/is-bound(t: typeVar): bool
  t.flavour == Bound

// Is a type variable 'Meta' (e.g. unifiable)
fun tv/is-meta(t: typeVar): bool
  t.flavour == Meta

// Is a type variable a 'Skolem' (e.g. not unifiable)
fun tv/is-skolem(t: typeVar): bool
  t.flavour == Skolem

fun is-mono-type(tp: ktype): bool
  match tp.expand-syn
    TForAll -> False
    _ -> True


// Split / add quantifiers

// Split type into a list of universally quantified type variables and a rho type
fun split-type-scheme(tp: ktype): (list<typeVar>, rho)
  // We must split a synonym if its expansion includes further quantifiers
  fun must-split(tp': ktype)
    match tp'
      TForAll -> True
      TSyn(_, _, tp'') -> tp''.must-split
      _ -> False
  match tp
    TForAll(vars, t) -> (vars, t)
    _ -> if tp.must-split then tp.pretend-decreasing.split-type-scheme else ([], tp)

// Find all quantified type variables, but do not expand synonyms
fun shallow-split-vars(tp: ktype)
  match tp
    TForAll(vars, t) -> (vars, t)
    _ -> ([], tp)

fun expand-syn(tp: ktype): ktype
  match tp
    TSyn(_, _, t) -> expand-syn(t)
    _ -> tp

// A type in canonical form has no type synonyms and expanded effect types.
fun canonical-form(tp: ktype): pure ktype
  match tp
    TSyn(_, _, t) -> canonical-form(t)
    TForAll(vars, t) -> TForAll(vars, canonical-form(t))
    TApp(t, ts) -> TApp(canonical-form(t), ts.map(canonical-form))
    TFun(args, eff, res) -> TFun(args.map(fn((name, t)) (name, t.canonical-form)), order-effect(eff.canonical-form), res.canonical-form)
    _ -> tp

// A type in minimal form is canonical and has no named function arguments
fun minimal-form(tp: ktype): pure ktype
  match tp
    TSyn -> tp.canonical-form
    TForAll(vars, t) -> TForAll(vars, t.canonical-form)
    TApp(t, ts) -> TApp(t.canonical-form, ts.map(canonical-form))
    TFun(args, eff, res) -> TFun(args.map(fn((_, t)) (name/nil, t.canonical-form)), order-effect(eff.canonical-form), res.canonical-form)

// Create a type scheme from a list of quantifiers
fun make-scheme(vars: list<typeVar>, rho: rho): scheme
  val (vars0, _) = rho.split-type-scheme
  tForall(vars ++ vars0, rho)

fun quantify-type(vars: list<typeVar>, tp: scheme): scheme
  val (vars0, rho) = tp.split-type-scheme
  tForall(vars ++ vars0, rho)

fun tForall(vars: list<typeVar>, rho: rho): scheme
  match vars
    Nil -> rho
    _ -> TForAll(vars, rho)

fun apply-type(tp1: ktype, tp2: ktype): ktype
  fun must-split(tp: ktype): bool
    match tp
      TApp -> True
      TSyn(_, _, tp) -> tp.must-split
      _ -> False
  match tp1
    TApp(tp, tps) -> TApp(tp, tps ++ [tp2])
    TSyn(_, _, tp) | tp.must-split -> apply-type(tp, tp2)
    _ -> TApp(tp1, [tp2])

fun type-arities(tp: ktype): (int, int)
  match tp.split-fun-scheme
    Just((tvars, pars, _, _)) -> (tvars.length, pars.length)
    Nothing -> (0, 0)

fun split-fun-scheme(tp: scheme): maybe<(list<typeVar>, list<(name, tau)>, keffect, tau)>
  val (tvars, rho) = tp.split-type-scheme
  match rho.split-fun-type
    Just((pars, eff, res)) -> Just((tvars, pars, eff, res))
    Nothing -> Nothing

// Assertions
// Is this a type variable?
fun tp/is-tvar(tp: ktype): bool
  match tp
    TVar -> True
    TSyn(_, _, t) -> t.tp/is-tvar
    _ -> False

// Is this a type constant?
fun tp/is-tcon(tp: ktype): bool
  match tp
    TCon -> True
    TSyn(_, _, t) -> t.tp/is-tcon
    _ -> False

// Is this a rho type? (i.e. no outermost quantifiers)
fun is-rho(tp: ktype): bool
  match tp
    TForAll -> False
    TSyn(_, _, t) -> t.is-rho
    _ -> True

// Is this a tau type? (i.e. no quantifiers anywhere)
fun is-tau(tp: ktype): bool
  match tp
    TForAll -> False
    TFun(xs, e, r) -> xs.all(_.snd.pretend-decreasing.is-tau) && e.is-tau && r.is-tau
    TCon -> True
    TVar -> True
    TApp(a, b) -> a.is-tau && b.all(_.pretend-decreasing.is-tau)
    TSyn(_, _, t) -> t.is-tau

// Is this a function type?
fun is-fun(tp: ktype): bool
  match split-fun-type(tp)
    Just(_) -> True
    Nothing -> False

// Split function type into argument list, effect type, and result type
fun split-fun-type(tp: ktype): maybe<(list<(name, ktype)>, ktype, ktype)>
  match tp
    TFun(args, eff, res) -> Just((args, eff, res))
    TSyn(_, _, t) -> t.split-fun-type
    _ -> Nothing

// Primitive types
val typeInt = TCon(tconInt)
val tconInt = TypeCon(nameTpInt, kindStar)
fun is-type-int(t: ktype): bool
  match t
    TCon(c) -> c == tconInt
    _ -> False

val typeInt32 = TCon(TypeCon(nameTpInt32, kindStar))
val typeEvIndex = TSyn(TypeSyn(nameTpEvIndex, kindStar, 0, Nothing), [], typeSSizeT)
val typeSSizeT = TCon(TypeCon(nameTpSSizeT, kindStar))
val typeFloat = TCon(TypeCon(nameTpFloat, kindStar))
val typeChar = TCon(tconChar)
val tconChar = TypeCon(nameTpChar, kindStar)
fun is-type-char(t: ktype): bool
  match t
    TCon(c) -> c == tconChar
    _ -> False

val typeString = TCon(tconString)
val tconString = TypeCon(nameTpString, kindStar)
fun is-type-string(t: ktype): bool
  match t
    TCon(c) -> c == tconString
    _ -> False

fun type-resume-context(b: tau, e: keffect, e0: keffect, r: tau): tau
  val tcon = TypeCon(nameTpResumeContext, kind-fun(kindStar, kind-fun(kindEffect, kind-fun(kindEffect, kind-fun(kindStar, kindStar)))))
  TApp(TCon(tcon), [b, e, e0, r])

val typeRef = TCon(TypeCon(nameTpRef, kind-fun(kindHeap, kind-fun(kindStar, kindStar))))
val tconLocalVar = TypeCon(nameTpLocalVar, kind-fun(kindHeap, kind-fun(kindStar, kindStar)))
fun is-type-localvar(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon(TypeCon(name)), [_, _]) -> name == nameTpLocalVar
    _ -> False

fun is-value-operation(tp: ktype): bool
  match tp.split-type-scheme
    // TSyn(syn, [_]) -> syn.name == nameTpValueOp
    (_, TApp(TCon(TypeCon(nm)), [_, _])) -> nm == nameTpValueOp
    _ -> False

fun make-value-operation(eff: ktype, tp: ktype)
  val k = kind-fun(kindEffect, kind-fun(kindStar, kindStar))
  TApp(TCon(TypeCon(nameTpValueOp, k)), [eff, tp])

fun order-effect(tp: tau): <exn,div> tau
  val (ls, tl) = extract-ordered-effect(tp)
  ls.foldr(tl, effect-extend)

fun extract-ordered-effect(tp: tau): pure (list<tau>, tau)
  val (labs, tl) = extract-effect-extend(tp)
  fun expand(l)
    val (ls, tl') = extract-effect-extend(l)
    if tl'.is-effect-empty && !ls.is-nil then ls else [l]
  val labss = labs.map(expand).concat
  fun label/(<)(l1: tau, l2: tau) 
    label-name/cmp(l1.label-name, l2.label-name).is-lt
  val slabs = labss.sort()
  (slabs, tl)

fun label-name(tp: tau): exn name
  tp.label-name-ex.fst

fun label-name-full(tp: tau): pure name
  val (name, i, _) = tp.label-name-ex
  val ids = i.show-id
  postpend(name, "$" ++ ids)

fun label-name-ex(tp: tau): exn (name, int, list<tau>)
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

val typePartial = TApp(tconHandled, [TCon(TypeCon(nameTpPartial, kindHandled))])
val typeLocal = TCon(TypeCon(nameTpLocal, kindLocal))
fun is-type-local(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon(c)) -> c.name == nameTpLocal
    _ -> False

val tconHandled = TCon(TypeCon(nameTpHandled, kind-fun(kindHandled, kindLabel)))
val tconHandled1 = TCon(TypeCon(nameTpHandled1, kind-fun(kindHandled1, kindLabel)))

fun wrap-handled-from-data-effect(de: dataEffect, eff: ktype)
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

fun is-effect-tyvar(tp: tau): bool
  match tp
    TVar(v) -> v.kind == kindEffect
    _ -> False

val effectEmpty = TCon(TypeCon(nameEffectEmpty, kindEffect))
fun is-effect-empty(tp: tau): bool
  match tp.expand-syn
    TCon(tc) -> tc.name == nameEffectEmpty
    _ -> False

fun effect-extend-no-dup(label: tau, eff: tau): pure tau
  val (ls, _) = label.extract-effect-extend
  match ls
    Nil ->
      val (els, _) = eff.extract-effect-extend
      if els.any(_.eq-type(label)) then eff // (label `elem` els)
      else app-effect-extend(label, eff)
    _ -> ls.effect-extend-no-dups(eff)

fun effect-extend-no-dups(labels: list<tau>, eff: tau): pure tau
  labels.foldr(eff, effect-extend-no-dup)

fun effect-extend(label: tau, eff: tau): pure tau
  val (ls, _) = label.extract-effect-extend
  match ls
    Nil -> app-effect-extend(label, eff)
    _ -> effect-extends(ls, eff)

val tconEffectExtend = TypeCon(nameEffectExtend, kind-fun(kindLabel, kind-fun(kindEffect, kindEffect)))

fun effect-extends(labels: list<tau>, eff: tau): pure tau
  // prevent over expansion of type synonyms here (see also: core/parse/teffect)
  match labels
    Cons(lab as TSyn(TypeSyn(_, kind)), _) | eff.is-effect-empty && kind == kindEffect -> lab
    _ -> labels.foldr(eff, effect-extend)

fun effect-fixed(labels: list<tau>): pure tau
  effect-extends(labels, effectEmpty)

fun is-effect-fixed(tp: tau): pure bool
  tp.extract-effect-extend.snd.is-effect-empty

fun extract-effect-extend(t: tau): pure (list<tau>, tau)
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

fun shallow-extract-effect-extend(t: tau): (list<tau>, tau)
  match t
    TApp(TCon(tc), [l,e]) | tc.name == nameEffectExtend ->
      val (ls, tl) = e.shallow-extract-effect-extend
      (Cons(l, ls), tl)
    _ -> ([], t)

fun shallow-effect-extend(label: tau, eff: tau): pure tau
  // We do not expand type synonyms in the label here by using the 'shallow' version of extract
  // this means that type synonyms of kind E (ie. a fixed effect row) could stay around in
  // the label (which should have kind X).
  // We use this to keep type synonyms around longer -- but during unification we got to be
  // careful to expand such synonyms
  val (ls, _) = label.shallow-extract-effect-extend
  match ls
    Nil -> app-effect-extend(label, eff)
    _ -> effect-extends(ls, eff)

fun app-effect-extend(label: ktype, eff: ktype)
  fun has-kind-label(l)
    val k = l.expand-syn.kind-of
    k == kindLabel || k == kindEffect
  if !has-kind-label(label) then
    throw("label has not kind X: " ++ label.show ++ " " ++ eff.show ++ " " ++ label.expand-syn.kind-of.show)
  TApp(TCon(tconEffectExtend), [label, eff])

fun kind-of(tau: ktype)
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

val typeDivergent = unsafe-type({single-eff(nameTpDiv)})
fun single-eff(nm:name)
  effect-extend(TCon(TypeCon(nm, kindLabel)), effectEmpty)
val typeTotal = effectEmpty
val tconTotal = TypeCon(nameEffectEmpty, kindEffect)

fun is-type-total(t: tau): bool
  match t
    TCon(c) -> c == tconTotal
    _ -> False

val typePure = unsafe-type({effect-fixed([typePartial, typeDivergent])})
val typeBool = TCon(tconBool)
fun is-type-bool(t: tau): bool
  match t
    TCon(c) -> c == tconBool
    _ -> False
val tconBool = TypeCon(nameTpBool, kindStar)
fun is-type-unit(t: tau): bool
  match t
    TCon(c) -> c == tconUnit
    _ -> False
// Type of ctail
fun type-cctx(tp: tau)
  TSyn(tsynCCtx, [tp], TApp(typeCCtxx, [tp, tp]))
val tsynCCtx = TypeSyn(nameTpCCtx, kind-fun(kindStar, kindStar), 0, Nothing)
val typeCCtxx = TCon(tconCCtxx)
val tconCCtxx = TypeCon(nameTpCCtxx, kind-fun(kindStar, kind-fun(kindStar, kindStar)))
// Type of cfield
val typeFieldAddr = TCon(tconFieldAddr)
val tconFieldAddr = TypeCon(nameTpFieldAddr, kind-fun(kindStar, kindStar))
val typeVector = TCon(TypeCon(nameTpVector, kind-fun(kindStar, kindStar)))
val typeList = TCon(tconList)
val tconList = TypeCon(nameTpList, kind-fun(kindStar, kindStar))

val typeEv = TCon(tconEv)
val tconEv = TypeCon(nameTpEv, kind-fun(kindStar, kindStar))
fun is-ev-type(tp: tau): bool
  match tp
    TCon(c) -> c == tconEv
    _ -> False
fun make-ev-type(arg: tau): tau
  type-app(typeEv, [arg])
// Create an application (reduced form)
fun type-app(tau: tau, args: list<tau>): tau
  match args
    Nil -> tau
    _ -> match tau
      TApp(tau', ts0) -> TApp(tau', ts0 ++ args)
      _ -> TApp(tau, args)

val typeUnit = TCon(tconUnit)
val tconUnit = TypeCon(nameTpUnit, kindStar)
val typeVoid = TCon(TypeCon(nameTpVoid, kindStar))
val typeReuse = TCon(TypeCon(nameTpReuse, kindStar))
val typeAny = TCon(TypeCon(nameTpAny, kindStar))
fun type-make-tuple(tps)
  match tps
    Nil -> typeUnit
    [tp] -> tp
    _ -> type-app(type-tuple(tps.length), tps)

fun type-tuple(n: int)
  TCon(TypeCon(name-tuple(n), kind-fun-n(kindStar.replicate(n), kindStar)))
val typeOptional = TCon(tconOptional)
val tconOptional = TypeCon(nameTpOptional, kind-fun(kindStar, kindStar))
fun is-optional(tp: ktype): bool
  match tp.expand-syn
    TApp(TCon(tc), [_]) -> tc == tconOptional
    _ -> False
fun make-optional(tp: ktype): ktype
  TApp(typeOptional, [tp])

fun un-optional(tp: ktype): ktype
  match tp.expand-syn
    TApp(TCon(tc), [t]) | tc == tconOptional -> t
    _ -> tp

// Remove type synonym indirections
fun prune-syn(rho: rho): rho
  match rho
    TSyn(_, _, t) -> t.prune-syn
    TApp(t1, ts) -> TApp(t1.prune-syn, ts.map(_.pretend-decreasing.prune-syn))
    _ -> rho

fun tv/to-type(v: typeVar)
  TVar(v)

fun tcon/to-type(c: typeCon)
  TCon(c)

// fun ktype/(==)(t1: ktype, t2: ktype): pure bool
//   eq-type(t1, t2)

fun elem-type(t: ktype, ts: list<ktype>)
  ts.any(fn(t1) t.eq-type(t1))

fun eq-type(tp1: ktype, tp2: ktype)
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

fun eq-types(t1: list<ktype>, t2: list<ktype>): pure bool
  t1.zipwith(t2, eq-type).all(id)

fun match-effect(eff1: tau, eff2: tau): pure bool
  eq-type(eff1.order-effect, eff2.order-effect)
