import compiler/syntax/lexeme
import compiler/syntax/lex
import compiler/common/range
import std/core-extras
import std/core/unsafe

fun lex(str: string, pos: pos): pure list<lexeme>
  val src = pos.source
  var lexemes := []
  var slices := []
  var raw-delim := 0
  with handler
    fun do-start-chunked(s: string, start: alex-pos)
      slices := Cons((s, start), slices)
    fun end-chunked()
      match slices
        Cons((s, start), rst) -> 
          slices := rst
          (s, start)
        Nil -> throw("end-chunked when no chunked input")
    fun add-chunk(f)
      match slices
        Cons((s, st), rst) -> 
          slices := Cons((s ++ f.string, st), rst)
        Nil -> 
          throw("add-chunk when no chunked input")
    fun get-rawdelim()
      raw-delim
    fun set-rawdelim(i)
      raw-delim := i
    fun do-emit(l, lstart, lend)
      val Alex-pos(off, line, col) = lstart
      val Alex-pos(eoff, eline, ecol) = lend
      lexemes := Cons(Lexeme(make-range(Pos(src, off, line, col), Pos(src, eoff, eline, ecol)), l), lexemes)
  alex-scan(str.slice, 0)
  lexemes.reverse

fun lexer(path: string, line: int, input: string): pure list<lexeme>
  lexing(Source(path, input), line, input)

fun lexing(source: source, line: int, input: string): pure list<lexeme>
  val init-pos = Pos(source, 0, 0, 1)
  lex(input, init-pos)

