// Ported as of 2026-01-17; approx upstream baseline commit a6b4e3e of Common/Unique.hs (backfilled 2026-07-23)

module compiler/common/unique

import compiler/common/name
import compiler/common/id

pub effect unique
  fun get-unique(): int
  fun set-unique(i: int): ()
  fun update-unique(f: (int) -> int): int

pub fun run-unique(start: int, f: () -> <unique|e> a): e a 
  var u := start
  with handler
    fun get-unique() u
    fun set-unique(i) u := i
    fun update-unique(g) 
        u := g(u) 
        u
  f() 

pub fun new-unique(): _ int 
  update-unique(_ + 1)

pub fun uniques(n: int): _ list<int>
  list(1, n).map(fn(_) new-unique())

pub fun unique-id(s: string): _ id
  gen-id(s, new-unique())

pub fun unique-ids(s: string, n: int): _ list<id>
  uniques(n).map(gen-id(s, _))

pub fun unique-name(s: string): _ name
  new-hidden-name-ex(s, new-unique().int/show)

// the result must be HIDDEN (`@uniq-<stem>@<i>`) -- `ppParam` suppresses
// hidden names, so specialize/lift signatures render nameless params like
// upstream (`(list<int>) -> ...`, not `(xs@8016 : list<int>) -> ...`)
pub fun unique-name-from(nm: name): _ name
  to-hidden-unique-name(new-unique(), "uniq", nm)

pub fun fresh-name(pfx: string)
  new-name(pfx ++ "@" ++ new-unique().int/show)
