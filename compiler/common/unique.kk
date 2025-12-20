
import compiler/common/name
import compiler/common/id

effect unique
  fun get-unique(): int
  fun set-unique(i: int): ()
  fun update-unique(f: (int) -> int): int

fun run-unique(start: int, f: () -> <unique|e> a): e a 
  var u := start
  with handler
    fun get-unique() u
    fun set-unique(i) u := i
    fun update-unique(g) 
        u := g(u) 
        u
  f() 

fun new-unique(): <unique> int 
  update-unique(_ + 1)

fun uniques(n: int): <unique> list<int>
  list(1, n).map(fn(_) new-unique())

fun unique-id(s: string): <unique> id
  gen-id(s, new-unique())

fun unique-ids(s: string, n: int): <unique> list<id>
  uniques(n).map(gen-id(s, _))

fun unique-name(s: string): <unique> name
  new-hidden-name(s ++ "." ++ new-unique().int/show)

fun unique-name-from(nm: name): <unique> name
  new-unique().to-unique-name(nm)

fun fresh-name(pfx: string)
  new-name(pfx ++ "." ++ get-unique().int/show)
