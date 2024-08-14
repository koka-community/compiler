import compiler/syntax/parse
import compiler/syntax/syntax
import std/os/path

fun main()
  parseProgramFromFile("compiler/syntax/parse.kk".path, True, True).show