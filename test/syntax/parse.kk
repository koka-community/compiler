import compiler/syntax/parse
import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/lib/pprint
import std/os/path
import std/os/dir

fun main()
  "../compiler/test/tests/parse/".path.list-directory.foreach fn(f)
    parse-program-from-file(f, True, True).pretty.show.println