import compiler/lib/pprint
import compiler/common/range
import compiler/common/failure
import compiler/common/name
import compiler/common/name-prim
import compiler/common/syntax
import compiler/common/unique
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/unify
import compiler/type/type
import compiler/type/typevar
import compiler/type/kind
import compiler/type/pretty
import compiler/type/operations
import compiler/core/core
import std/data/linearset
import std/data/linearmap
// Updated 12/19/25 to commit #f2a9c90

/// Do two types overlap on the argument types? Used to check for overlapping definitions of overloaded identifiers.
fun overlaps(rng: range, free: tvs, tp1: ktype, tp2: ktype): _ ()
  val rho1 = instantiate(tp1, rng)
  val rho2 = instantiate(tp2, rng)
  match (rho1.split-fun-type, rho2.split-fun-type)
    // Values always overlap
    (Nothing, _) -> ()
    (_, Nothing) -> ()
    // rest
    (Just((pars1, _, _)), Just((pars2, _, _))) ->
      val (fixed1, optional1, implicit1) = pars1.split-optional-implicit
      val (fixed2, optional2, implicit2) = pars2.split-optional-implicit
      val hi = max(fixed1.length, fixed2.length)
      val fo1 = (fixed1.map(snd) ++ optional1.map(_.snd.un-optional) ++ implicit1.map(snd)).take(hi)
      val fo2 = (fixed2.map(snd) ++ optional2.map(_.snd.un-optional) ++ implicit2.map(snd)).take(hi)
      if fo1.length != fo2.length then unify-error(NoMatchType) // one has more fixed arguments than the other can ever get
      else
        unifies(fo1, fo2)
        ()


/// Does a type have the given named arguments? Return the instantiated type if successful
fun match-named(match-some: bool, rng: range, free: tvs, tp: ktype, n: int, namedArgs : list<name>, mb-res-tp: maybe<ktype>): _ rho
  val rho1 = instantiate(tp, rng)
  match rho1.split-fun-type
    Nothing -> unify-error(NoMatchType)
    Just((pars, _, res-tp)) ->
      if n + namedArgs.length > pars.length then unify-error(NoMatchType)
      else
        val npars = pars.drop(n)
        val names = npars.map(fst)
        if namedArgs.all(fn(nm) names.any(fn(n') nm == n')) then 
          match mb-res-tp 
            Nothing -> ()
            Just(exp-tp) -> 
              subsume(rng, free, exp-tp, res-tp)
              ()
          val rest = npars.filter(fn((nm, _)) !namedArgs.any(_ == nm))
          if match-some || rest.all(is-optional-or-implicit) then 
            subst(rho1)
          else unify-error(NoMatchType)
        else unify-error(NoMatchType)

/// Does a function type match the given arguments? if the first argument `matchSome` is `True`,
/// it is considered a match even if not all arguments to the function are supplied
fun match-arguments(matchSome: bool, rng: range, free: tvs, tp: ktype, fixed: list<ktype>, namedArgs: list<(name,ktype)>, mb-res-tp: maybe<ktype>): _ rho
  val rho1 = instantiate(tp, rng)
  match rho1.split-fun-type
    Nothing -> 
      val res-tp = match mb-res-tp
        Nothing -> fresh-star()
        Just(t) -> t
      val eff-tp = fresh-effect()
      val fun-tp = TFun(fixed.map(fn(t) (name/nil, t)) ++ namedArgs, eff-tp, res-tp)
      subsume(rng, free, tp, fun-tp)
      subst(fun-tp)
    Just((pars, _, res-tp)) ->
      if fixed.length + namedArgs.length > pars.length then unify-error(NoMatchType)
      else 
        // subsume fixed parameters
        val pars-not-named = pars.filter(fn((nm, _)) !(namedArgs.map(fst).any(_ == nm)))
        val (fpars, rest) = pars-not-named.split(fixed.length)
        fpars.map(snd).zipwith(fixed) fn(tpar, targ) 
          subsume(rng, free, tpar.un-optional, targ)
        // subsume named parameters
        namedArgs.map fn((name, targ))
          match pars.lookup(_ == name) // TODO: Should this be rest?
            Nothing -> unify-error(NoMatchType)
            Just(tpar) -> subsume(rng, free, tpar.un-optional, targ)
        // check if the result type matches
        match mb-res-tp
          Nothing -> ()
          Just(exp-tp) -> 
            subsume(rng, free, exp-tp, res-tp)
            ()
        // check the rest is optional or implicit
        if matchSome || rest.all(is-optional-or-implicit) then 
          rho1.subst
        else unify-error(NoMatchType)


fun subsume-subst(rng: range, free: tvs, tp1: ktype, tp2: ktype): _ (ktype, rho, expr -> _ expr)
  subsume(rng, free, tp1.subst, tp2.subst)

// See if two types match exactly up to renaming of free type variables
fun match-shape(tp1: ktype, tp2: ktype): _ ()
  unify(tp1, tp2)
  val s = get-subst()
  val dom = s.dom.list
  val codomDup = s.list.map fn((_, t))
    match t 
      TVar(tv) -> tv
      _ -> unify-error(NoMatchType)
  val codom = codomDup.linear-set
  if dom.length == codom.length then ()
  else unify-error(NoMatchType)

fun pure-match-shape(tp1: ktype, tp2: ktype): _ bool
  match run-unify({match-shape(tp1, tp2)})
    (Right(_), _) -> True
    _ -> False

// Subsumption
// subsume(free, t1, t2) holds if `t2` can be instantiated to `t1` where
// `free` are the free type variables in the assumption.
// Returns a core transformer that needs to be
// applied to the expression of type `t2`. Also returns a new type for the expected type `tp1` where 'some'
// types have been properly substituted (and may be quantified).
fun subsume(rng: range, free: tvs, tp1: ktype, tp2: ktype): _ (ktype, rho, expr -> _ expr)
  // skolemize, instantiate and unify
  val (sks, rho1, _) = skolemize-ex(tp1, rng)
  val (tvs, rho2, _) = skolemize-ex(tp2, rng)
  unify(rho2, rho1)
  // escape check: no skolems should escape into the environment
  val sub = get-subst()
  val tvs1 : tvs = (free + tp1.free-type-vars)
  val allfree = tvs1.list
  val escaped = sub.list.filter(fn((tv, _)) allfree.any(_ == tv)).map(snd).fsv
  if escaped.disjoint(sks.new/tvs) then ()
  else unify-error(NoSubsume)
  // final type
  val (vars, ssub) = fresh-sub(Bound, sks)
  val subx = ssub.compose(sub)
  val tp = quantify-type(vars, subx |-> rho1) // TODO: do rho1 and we get skolem errors: see Prelude.choose
  fun core-next(expr) 
    add-type-lambdas(vars, // generalize 
                subx |-> add-type-apps(tvs, expr))
  // return
  (tp, subx |-> rho2, core-next) // instantiate

/////////////////
// Unification
/////////////////

// Unify two types
fun unify(t1: ktype, t2: ktype): _ ()
  match (t1, t2)
    // effects
    (TApp(TCon(tc1)), TApp(TCon(tc2))) | tc2 == tconEffectExtend && tc1 == tconEffectExtend ->
      unify-effect(t1, t2)
    (TApp(TCon(tc1)), TVar(tv2)) | tc1 == tconEffectExtend && tv2.flavour.is-meta ->
      unify-effect-var(tv2, t2)
    (TVar(tv1), TApp(TCon(tc2))) | tc2 == tconEffectExtend && tv1.flavour.is-meta ->
      unify-effect-var(tv1, t1)
    // type variables
    (TVar(v1), TVar(v2)) | v1 == v2 -> () // TODO: Kind check?
    (TVar(tv as TypeVar(_, _, Meta)), _) -> unify-tvar(tv, t2)
    (_, TVar(tv as TypeVar(_, _, Meta))) -> unify-tvar(tv, t1)
    // constants
    (TCon(tc1), TCon(tc2)) | tc1 == tc2 -> ()
    // type applications
    (TApp(t1, ts1), TApp(u1, us2)) ->
      val len1 = ts1.length
      val len2 = us2.length
      if len1 == len2 then 
        unify(t1, u1)
        unifies(ts1, us2)
      elif len1 < len2 then
        unify(t1, TApp(u1, us2.take(len2 - len1)))
        unifies(ts1, us2.drop(len2 - len1))
      else 
        unify(TApp(t1, ts1.take(len1 - len2)), u1)
        unifies(ts1.drop(len1 - len2), us2)
    // functions
    (TFun(args1, eff1, res1), TFun(args2, eff2, res2)) | args1.length == args2.length ->
      unifies([res1] ++ args1.map(snd), [res2] ++ args2.map(snd))
      fun effErr(e: unify-error)
        match e
          NoMatchType  -> NoMatchEffect(eff1, eff2)
          NoMatchEffect -> NoMatchEffect(eff1, eff2)
          _ -> e
      with with-err(effErr)
      unify(eff1, eff2)
    // quantified types
    (TForAll(vars1, tp1), (TForAll(vars2, tp2))) | vars1.length == vars2.length ->
      // match kinds of quanitifers
      val kinds1 = vars1.map(kind)
      match-kinds(kinds1, vars2.map(kind))
      // replace with shared bound variables in both types
      // note: assumes ordered quantifiers and ordered predicates
      // note: we don't use Skolem as a Meta variable can unify with a Skolem but not with a Bound one
      val vars = kinds1.map(fresh-tvar(_, Bound))
      val sub1 = vars1.zip(vars).new/sub
      val sub2 = vars2.zip(vars).new/sub
      val stp1 = sub1 |-> tp1
      val stp2 = sub2 |-> tp2
      // and unify the results
      unify(stp1, stp2)
      // No need to check for escaping skolems as we don't unify to bound variables
    // synonyms
    (TSyn(syn1, _, tp1), TSyn(syn2, _, tp2)) ->
      if syn1.rank > syn2.rank then unify(tp1, t2) else unify(t1, tp2)
    (TSyn(_, _, tp1), tp2) -> unify(tp1, tp2)
    (tp1, TSyn(_, _, tp2)) -> unify(tp1, tp2)
    // No match
    (TVar(TypeVar(_, kind, Skolem)), TVar(TypeVar(_, _, Skolem))) ->
      unify-error(NoMatchSkolem(kind))
    _ -> unify-error(NoMatchType)

// Unify a type variable with a type
fun unify-tvar(tv: type-var, tp: ktype): _ ()
  match tv
    TypeVar(id, k, Meta) -> 
      val etp = tp.expand-syn
      if etp.fuv.list.any(fn(tv') tv == tv') then
        match etp
          TVar(tv') | tv == tv' -> () // i.e. a ~ id<a>
          _ -> unify-error(Infinite)
      else
        match etp
          TVar(TypeVar(_, _, Bound)) -> unify-error(NoMatchType) // can't unify with bound variables
          TVar(tv2 as TypeVar(id2, _, Meta)) | id <= id2 ->
            if id < id2 then unify-tvar(tv2, TVar(tv)) else () // TODO: Kind Check?
          _ ->
            if !match-kind(k, tp.kind) then
              trace("unify-tvar: kinds: typevar var:\n" ++ k.show ++ "\nand:\n" ++ tp.kind.show ++ "\ntype:\n" ++ tp.show)
              unify-error(NoMatchKind)
            else
              extend-sub(tv, tp)
    _ -> throw("type/unify unify-tvar: valued with skolem or bound variable")


// Unify two equal length lists of types, and apply a substitution before each unification
fun unifies(l1: list<ktype>, l2: list<ktype>): _ ()
  match (l1, l2)
    (Nil, Nil) -> ()
    (Cons(t1, ts1), Cons(t2, ts2)) ->
      unify(t1.subst, t2.subst)
      unifies(ts1, ts2)
    _ -> throw("type/unify unifies")

// Unify effects
fun unify-effect(tp1: ktype, tp2: ktype): _ ()
  val (ls1, tl1) = tp1.extract-normalize-effect
  val (ls2, tl2) = tp2.extract-normalize-effect
  val (ds1, ds2) = unify-labels(ls1, ls2, tl1.is-effect-empty, tl2.is-effect-empty)
  match (tl1.expand-syn, tl2.expand-syn)
    (TVar(TypeVar(id1, _, Meta)), TVar(TypeVar(id2, _, Meta))) | id1 == id2 && !(ds1.is-empty && ds2.is-empty) -> 
      unify-error(Infinite)
    _ ->
      val tail1 = if ds1.is-empty then tl1 else
        val tv1 = fresh-effect()
        unify(tl1, ds1.effect-extends(tv1))
        tv1
      val stl2 = tl2.subst
      val tail2 = if ds2.is-empty then stl2 else
        val tv2 = fresh-effect()
        unify(stl2, ds2.effect-extends(tv2))
        tv2
      val stail1 = tail1.subst
      unify(stail1, tail2)
      tp1.subst
      tp2.subst
      ()

fun extract-normalize-effect(tp: ktype): _ (list<ktype>, ktype)
  tp.subst.extract-ordered-effect

fun unify-effect-var(tv1: type-var, tp2: ktype): _ ()
  val (ls2, tl2) = tp2.extract-ordered-effect // ls2 must be non-empty
  match tl2.expand-syn 
    // e ~ <div,exn|e> ~> e := <div,exn|e'>
    TVar(tv2) | tv1 == tv2 -> unify-error(Infinite)
    _ ->
      unify-tvar(tv1, effect-extends(ls2, tl2))

// Unify lists of ordered labels; return the difference
fun unify-labels(ls1: list<ktype>, ls2: list<ktype>, closed1: bool, closed2: bool): _ (list<ktype>, list<ktype>)
  match (ls1, ls2)
    (Nil, Nil) -> (Nil, Nil)
    (Cons, Nil) -> ([], ls1)
    (Nil, Cons) -> (ls2, [])
    (Cons(l1, ll1), Cons(l2, ll2)) ->
      val (name1, _, args1) = l1.label-name-ex
      val (name2, _, args2) = l2.label-name-ex
      match name1.label-name/cmp(name2)
        Lt -> 
          val (ds1, ds2) = unify-labels(ll1, ls2, closed1, closed2)
          (ds1, Cons(l1, ds2))
        Gt ->
          val (ds1, ds2) = unify-labels(ls1, ll2, closed1, closed2) // TODO: In Haskell it uses closed2 in both places!
          (Cons(l2, ds1), ds2)
        Eq -> // labels are equal
          match (args1, args2)
            ([TVar(TypeVar(id1, kind1, sort1))], ([TVar (TypeVar(id2, kind2, sort2))]))
              | kind1 == kindScope && kind2 == kindScope && id1 != id2 && sort1.is-skolem && sort2.is-skolem ->
                if (id1 < id2) then
                  val (ds1, ds2) = unify-labels(ll1, ls2, closed1, closed2)
                  (ds1, Cons(l1, ds2))
                else
                  val (ds1, ds2) = unify-labels(ls1, ll2, closed1, closed2) // TODO: In Haskell it uses ls2!
                  (Cons(l2, ds1), ds2)
            _ ->
              unify(l1, l2) // for heap effects and kind checks
              unify-labels(ll1.subst, ll2.subst, closed1, closed2)

fun compare-label(l1: ktype, l2: ktype)
  val name1 = l1.label-name-ex.fst
  val name2 = l2.label-name-ex.fst
  name1.label-name/cmp(name2)

// Match a list of kinds
fun match-kinds(kinds1: list<kind>, kinds2: list<kind>): _ ()
  match (kinds1, kinds2)
    (Nil, Nil) -> ()
    (Cons(k1, k1s), Cons(k2, k2s)) -> 
      if match-kind(k1, k2) then 
        match-kinds(k1s, k2s)
      else
        unify-error(NoMatchKind)
    _ -> unify-error(NoMatchKind)

effect unify
  final ctl unify-error(e: unify-error): a
  fun extend-sub(tv: type-var, t: ktype): ()
  fun add-sub(sub: sub): ()
  fun get-subst(): sub

fun with-err(e: unify-error -> unify-error, f: () -> _ a): _ a
  with override
    final ctl unify-error(er) unify-error(e(er))
    fun extend-sub(tv, t) extend-sub(tv, t)
    fun add-sub(sub) add-sub(sub)
    fun get-subst() get-subst() 
  f()

fun run-unify(action: () -> _ a): _ (either<unify-error, a>, sub)
  var subst := sub/null
  with handler
    return(x) (Right(x), subst)
    final ctl unify-error(e) (Left(e), subst)
    fun extend-sub(tv, t) 
      subst := subst.extend(tv, t)
    fun add-sub(sub) 
      subst := subst.compose(sub)
    fun get-subst() subst
  action()

fun substitute/subst(x: a, ?substitute: (sub, a) -> _ a): _ a
  substitute(get-subst(), x)

type unify-error
  NoMatchType
  NoMatchKind
  NoMatchSkolem(k: kind)
  NoMatchEffect(e1: ktype, e2: ktype)
  NoSubsume
  Infinite
  NoArgMatch(i1: int, i2: int)

pub fun show(e: unify-error): string
  match e
    NoMatchType -> "types do not match"
    NoMatchKind -> "kinds do not match"
    NoMatchSkolem(k) -> "skolem variables do not match (kind " ++ k.show ++ ")"
    NoMatchEffect() -> "effects do not match" // ++ e1.show ++ " and " ++ e2.show
    NoSubsume -> "types do not subsume"
    Infinite -> "infinite type"
    NoArgMatch() -> "argument types do not match"

