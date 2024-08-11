import compiler/lib/scc
import std/test

fun test()
  basic/test("scc")
    expect([[2], [3], [1], [0], [4]])
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
