import std/os/file
import std/os/path
import compiler/common/range
import compiler/syntax/lexer
import compiler/syntax/lexeme

fun main()
  val files =  [
    "../compiler/compiler/syntax/lex",
    "../compiler/compiler/syntax/lexer",
    "../compiler/compiler/syntax/lexeme"
  ]
  
  files.foreach fn(f)
    with handler
      final ctl throw-exn(e)
        e.trace-show
    val s = read-text-file((f ++ ".kk").path)
    val source = Source(f ++ ".kk", s)
    lexing(source, 1, s).trace-show
    ()