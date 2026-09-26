// Ported as of 2026-01-29; approx upstream baseline commit b8074c2 of Kind/Pretty.hs (backfilled 2026-07-23)
module compiler/kind/pretty

import compiler/common/color-scheme
import compiler/lib/pprint
import compiler/lib/printer
import compiler/kind/kind
import compiler/common/name
import compiler/common/failure
import compiler/platform/config
import std/core/undiv

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
  if contextPrec > prec then d.parens
  else d

pub fun comma-parens(xs, f)
  xs.map(f).tupled

pub fun collect-funargs(k: kind)
  match k
    KApp(KApp(KCon(name), k1), k2) | name == "->".new-name ->
      Cons(k1, k2.pretend-decreasing.collect-funargs)
    _ -> [k]

pub fun pp-kind(k: kind, prec: prec)
  val nm = match k
    KCon(n) -> name/pretty(n)
    KApp(KApp(KCon(name), k1), k2) | name == "->".new-name ->
      val x = match k2.collect-funargs
        [res] ->
          k1.pp-kind(precArrow) |+| 
          res.pp-kind(precArrow - 1)
        args ->
          Cons(k1, args.init).comma-parens(fn(k') k'.pp-kind(precTop)) |+|
          "->".text |+| args.last.unjust.pp-kind(precArrow - 1)
      x.pparens(prec, precArrow)
    KApp ->
      val x = match k.collect-funargs
        Cons(k', ks) ->
          k'.pp-kind(precApp - 1) |.|
          ks.comma-parens(_.pp-kind(precTop))
        _ -> failure/fail("kind/pretty pp-kind.KApp: match failure")
      x.pparens(prec, precApp)
  nm.color(colors.colorKind)
