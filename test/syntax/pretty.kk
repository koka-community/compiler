import compiler/syntax/pretty
import compiler/syntax/syntax
import compiler/common/name
import compiler/common/range
import compiler/common/syntax
import compiler/lib/pprint
import std/test

fun test()
  basic/test("pretty")
    expect("v()")
      App(Var("v".new-name, False, null), [], null).pretty(?pretty=fn(t) empty).show
