import compiler/lib/scc
import std/test

fun suite()
  test("scc")
    // 1 -> 2 (from 1's edge list) and 2 -> 1, so {1,2} is a single strongly
    // connected component; the previous expectation split them, which is not
    // an SCC decomposition of this graph. Order is dependencies-first:
    // 3, then {1,2} (which needs 3), then 0 (which needs 1), then isolated 4.
    expect([[3], [1, 2], [0], [4]])
      scc([(0,[1]),(1,[1,2,3]),(2,[1]),(3,[]),(4,[])])
    expect([['j'], ['i'], ['f'], ['a', 'b', 'g'], ['h'], ['d'], ['e'], ['c']])
      scc([('a',"jg".list)
        ,  ('b',"ia".list)
        ,  ('c',"he".list)
        ,  ('d',"".list)
        ,  ('e',"jhd".list)
        ,  ('f',"i".list)
        ,  ('g',"fb".list)
        ,  ('h',"".list)])

fun main()
  run-tests(suite)