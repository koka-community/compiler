module compiler/core/analysis-match

import compiler/lib/pprint
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import compiler/common/failure
import compiler/common/unique
import compiler/common/syntax
import compiler/common/error
import compiler/kind/newtypes
import compiler/kind/kind
import compiler/type/type
import compiler/type/typevar
import compiler/type/pretty
import compiler/type/unify
import compiler/core/core
import compiler/platform/config
import compiler/lib/core
// Analyze partiality of core match statements
// Commit #f4e4050

pub fun branches/analyze(def-name: name, rng: range, branches: list<branch>, tps: list<ktype>, infos: list<data-info>, is-lazy-match: bool): _ (bool, list<branch>)
  match-branches(def-name, rng, branches, tps, infos, is-lazy-match)

type kmatch
  Match(con-infos: list<con-info>, cmatches: list<(con-info, list<kmatch>)>)
  MatchComplete(con-infos: list<con-info>)

fun ci/is-complete((_, cmatches): (con-info, list<kmatch>)): bool
  cmatches.all(is-matchComplete)

fun show(m: kmatch)
  m.pretty.show

fun pretty(m: kmatch)
  match m
    MatchComplete(_) -> "<complete>".text
    Match(cinfos, cmatches) -> 
      "match:".text |+| cinfos.map(_.name.pretty).list |-|
        cmatches.map fn((ci, ms)) 
          ci.name.pretty |.| colon |-| 
          ms.map-indexed fn(i, cmatch)
            i.pretty |.| dot |.| cmatch.pretty
          .vcat.indent(2)
        .vcat.indent(2)

fun match-branches(def-name: name, rng: range, branches0: list<branch>, tps: list<ktype>, data-infos: list<data-info>, is-lazy-match: bool): _ (bool, list<branch>)
  fun fold(matches, acc, branches)
    match branches
      [] -> (matches.all(is-matchComplete), acc.reverse)
      Cons(b, bs) -> 
        val (matches', b') = match-branch(def-name, rng, matches, tps, b)
        fold(matches', Cons(b', acc), bs)
  val matches = data-infos.map(fn(di) Match(di.get-con-infos(is-lazy-match), []))
  fold(matches, [], branches0)

fun match-branch(def-name: name, rng: range, matches: list<kmatch>, patTps: list<ktype>, branch: branch): _ (list<kmatch>, branch)
  if !branch.guards.any(fn(Guard(t)) -> t.is-true) then
    // since every guard more complex than 'true', we have no idea if it matches anything
    (matches, branch) 
  else 
    // some guard matches for sure; analyze the pattern
    val (matches', patterns') = match-patterns(def-name, rng, True, matches, patTps, branch.patterns)
    analyze-guards(rng, branch.guards)
    (matches', Branch(patterns', branch.guards))

fun analyze-guards(rng: range, guards: list<guard>): _ ()
  match guards
    Cons(Guard(t), Cons()) | t.is-true ->
      add-warning(rng, "Some guards in the branches will never be reached".text)
    Cons(Guard(t)) | t.is-false -> 
      add-warning(rng, "Some guard condition in the branches is never true".text) 
    Cons(_, gs) -> analyze-guards(rng, gs)
    Nil -> ()

fun match-pattern(def-name: name, rng: range, top: bool, (m, t, pat): (kmatch, ktype, pattern)): _ (kmatch, pattern)
  match m
    MatchComplete() -> // already fully matched
      if top then add-warning(rng, "Some branches in the match will never be reached:".text |+| pat.show.text)
      (m, pat)
    Match(cinfos, cmatches) -> 
      match pat
        PatWild -> 
          val pat' = 
            match cinfos.remove(cmatches.filter(is-complete).map(fst))
              [c] | c.existentials.is-empty ->
                // one constructor unmatched: replace wild with the constructor to improve reuse
                match c.typeName.newtypes-lookup-any
                  Just(di) | !di.di/is-lazy ->
                    match t.instantiate-pat-con(c.params, c.typeScheme)
                      Nothing -> PatWild
                      Just((targs, tres)) -> // only for constructors with arguments
                        PatCon(TName(c.name, c.typeScheme), c.params.map(fn(_) PatWild), di.con-repr(c), targs, [], tres, c, True) // skip
                  _ -> PatWild
              _ -> PatWild 
          (MatchComplete(cinfos), pat')
        PatVar(tname, arg) -> 
          val (m2, arg2) = match-pattern(def-name, rng, top, (m, tname.type-of, arg))
          (m2, PatVar(tname, arg2))
        PatLit() -> (m, pat)
        PatCon(cname, args, repr, targs, tvars, tret, cinfo, _) -> 
          match cmatches.span(fn((ci, _)) -> cname.get-name != ci.name)
            (pre, Cons((ci, arg-matches), post)) -> 
              // matched before
              val skip = !cinfos.is-empty && cinfos.length == cmatches.length && (pre ++ post).all(is-complete) // all other constructors matched!
              val (arg-matches', args') = match-patterns(def-name, rng, False, arg-matches, targs, args)
              (make-match(cinfos, pre ++ Cons((ci, arg-matches'), post)), PatCon(cname, args', repr, targs, tvars, tret, cinfo, skip))
            _ -> // first match 
              val skip = !cinfos.is-empty && cinfos.length == cmatches.length + 1 && cmatches.all(is-complete) // all other constructors matched!
              val (arg-matches', args') = match-patterns(def-name, rng, False, targs.map(fn(tp) make-match(lookup-con-infos(tp), [])), targs, args)
              (make-match(cinfos, cmatches ++ [(cinfo, arg-matches')]), PatCon(cname, args', repr, targs, tvars, tret, cinfo, skip))

fun match-patterns(def-name: name, rng: range, top: bool, matches: list<kmatch>, tps: list<ktype>, pats: list<pattern>): _ (list<kmatch>, list<pattern>)
  val (matches1, patterns1) = matches.zip3(tps, pats).map(match-pattern(def-name, rng, top, _)).unzip
  val matches2 = 
    if matches1.length <= 1 then matches1 
    else 
      match matches1.filter(!_.is-matchComplete)
        [] -> matches1 // all matched fully 
        [_] -> update-one-match(matches, matches1) // one was matched while all others were complete matches; info on m is valid
        _ -> matches // multiple matches: discard the info to be conservative
  (matches2, patterns1)

fun update-one-match(ms1: list<kmatch>, ms2: list<kmatch>): _ list<kmatch>
  match (ms1, ms2)
    (Cons(m1, m1s), Cons(m2, m2s)) -> 
      if is-matchComplete(m2) then 
        Cons(m1, m1s.update-one-match(m2s))
      else 
        Cons(m2, m1s.update-one-match(m2s))
    ([], _) -> []
    _ -> failure/fail("core/analysis-match/update-one-match: no matching lists")

fun make-match(cinfos: list<con-info>, cmatches: list<(con-info, list<kmatch>)>): kmatch 
  if !cinfos.is-empty && cinfos.length == cmatches.length && cmatches.all(is-complete) then
    MatchComplete(cinfos)
  else
    Match(cinfos, cmatches)
 
fun instantiate-pat-con(tp-res: ktype, con-params: list<(name, ktype)>, con-tp: scheme): _ maybe<(list<ktype>, ktype)>
  match con-params
    [] -> Just(([], tp-res))
    _ -> 
      match con-tp.split-fun-scheme
        Nothing -> Nothing
        Just((_, tpars, _, tres)) -> 
          match run-unify({unify(tp-res, tres)})
            (Right(_), sub) -> Just((tpars.map(fn((_, tpar)) sub |-> tpar), sub |-> tres))
            _ -> Nothing

fun remove(cinfos1: list<con-info>, cinfos2: list<con-info>): list<con-info>
  val cnames = cinfos2.map(name)
  cinfos1.filter(fn(ci) !cnames.contains(ci.name))

fun data-info/get-con-infos(di: data-info, is-lazy-match: bool): list<con-info>
  if di.is-open || di.is-literal then []
  elif !is-lazy-match && di.di/is-lazy then di.constrs.filter(!_.coninfo/is-lazy)
  else di.constrs

fun lookup-con-infos(tp: ktype): _ list<con-info>
  match tp.expand-syn
    TCon(tc) -> 
      match newtypes-lookup-any(tc.name)
        Just(di) -> di.get-con-infos(False) // [] for open or literals
        Nothing -> throw("core/analysis-match/lookup-con-infos: not found: " ++ tc.name.show)
    TApp(t) -> lookup-con-infos(t) // list<a>
    _ -> throw("core/analysis-match/lookup-con-infos: not a type constructor")

fun final-branch-is-catch-all(b: list<branch>): bool
  match b.reverse
    Cons(Branch([pat], [Guard(t)])) -> pat.always-matches && t.is-true
    _ -> False

// does a pattern always match?
fun always-matches(p: pattern): bool
  match p
    PatWild -> True
    PatLit() -> False
    PatVar(_, p') -> p'.always-matches
    PatCon(_, _, _, _, _, _, conInfo, _) -> conInfo.singleton
