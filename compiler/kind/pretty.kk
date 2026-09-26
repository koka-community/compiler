// Ported as of 2026-01-29; approx upstream baseline commit b8074c2 of Kind/Pretty.hs (backfilled 2026-07-23)
module compiler/kind/pretty

import compiler/common/color-scheme
import compiler/lib/pprint
import std/pretty/printer
import compiler/kind/kind
import compiler/kind/assumption
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import std/core/undiv
import std/data/sort
import std/data/rb-map
import compiler/common/name-collections

fun kind-colon()
  ":".text.color(colors.colorSep)

// Generate nice quantifier names
fun nice-kinds(kinds: list<kind>): _ list<doc>
  kinds.map(_.pp-kind(precTop))

pub fun pretty-kind(k: kind): _ doc
  k.pp-kind(precTop)

// Show
fun pretty(k: kind)
  k.pp-kind(precTop)

// precedence
pub alias prec = int
pub val precTop = 0
pub val precQuant = 1
pub val precArrow = 2
pub val precApp = 3
pub val precAtom = 4

pub fun pparens(d: doc, contextPrec: prec, prec: prec)
  // An arrow kind in arrow-argument position parenthesizes: 
  // `((E, V) -> V) -> X`, not `(E, V) -> V -> X`)
  if contextPrec >= prec then d.parens
  else d

pub fun comma-parens(xs, f)
  xs.map(f).tupled

pub fun collect-funargs(k: kind)
  match k
    KApp(KApp(KCon(name), k1), k2) | name == "->".new-name ->
      Cons(k1, k2.pretend-decreasing.collect-funargs)
    _ -> [k]

// collect an application spine `((k a) b)` as `[k, a, b]`
pub fun collect-args(k: kind): list<kind>
  match k
    KApp(k1, k2) -> k1.pretend-decreasing.collect-args ++ [k2]
    _ -> [k]

pub fun pp-kind(k: kind, prec: prec)
  val nm = match k
    KCon(n) -> name/pretty(n)
    KApp(KApp(KCon(name), k1), k2) | name == "->".new-name ->
      val x = match k2.collect-funargs
        [res] ->
          k1.pp-kind(precArrow) |+| "->".text |+|
          res.pp-kind(precArrow - 1)
        args ->
          Cons(k1, args.init).comma-parens(fn(k') k'.pp-kind(precTop)) |+|
          "->".text |+| args.last.unjust.pp-kind(precArrow - 1)
      x.pparens(prec, precArrow)
    KApp ->
      val x = match k.collect-args
        Cons(k', ks) ->
          k'.pp-kind(precApp - 1) |.|
          ks.comma-parens(_.pp-kind(precTop))
        _ -> failure/fail("kind/pretty pp-kind.KApp: match failure")
      x.pparens(prec, precApp)
  nm.color(colors.colorKind)

// Print each name's kind, one per line, (sorted map to match upstream results) 
// Names local to `context` print unqualified; 
// upstream's `importsAlias` handling for OTHER modules' names
// (only relevant if a foreign kGamma is ever printed, not the entry module's own) isn't ported.
fun pp-own-kname(n: name, ctxt: name): _ doc
  (if n.qualifier == ctxt then n.unqualify else n).pretty

pub fun pp-kgamma(kg: kGamma, ctxt: name): _ doc
  val nameSchemes = kg.list.flatmap(fn((_, xs)) xs).map(fn((n, tni)) (n, tni.kind))
                     .sort(fn((n1: name, _), (n2: name, _)) n1.show < n2.show)
  val maxwidth = nameSchemes.map(fn((n, _)) n.show.count).maximum(0).min(12)
  fun pp-one((n, k): (name, kind)): _ doc
    fill(pp-own-kname(n, ctxt), maxwidth) |.| kind-colon() |+| k.pretty-kind
  vcat(nameSchemes.map(pp-one))
