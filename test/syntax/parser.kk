import compiler/syntax/parse
import compiler/syntax/syntax
import std/os/path

fun main()
  parseProgramFromFile("test/syntax/parser.kk".path, True, True).show