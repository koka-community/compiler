import compiler/syntax/parse
import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/lib/pprint
import std/os/path
import std/os/dir

fun main()
  "../compiler/test/tests/parse/".path.list-directory.foreach fn(f)
    parse-program-from-file(f, True, True).pretty.show.println

fun test()
  "/Users/timwhiting/koka/lib/std/".path.list-directory-recursive.foreach fn(f)
    if f.is-file && f.string.ends-with(".kk").bool then
      parse-program-from-file(f, True, True).pretty.show.println

fun test-x1()
  val f = "/Users/timwhiting/koka/lib/std/core.kk".path
  parse-program-from-file(f, True, True).pretty.show.println
