// Updated as of 7/24/26: Commit dd91082
module compiler/syntax/lexer

import compiler/syntax/lexeme
import compiler/syntax/lex
import compiler/common/range
import std/core-extras
import std/core/unsafe

fun lex(str: string, pos: pos): _ list<lexeme>
  val src = pos.source
  var lexemes := []
  var slices := []
  var raw-delim := 0
  var col-off-line := pos.line
  var line-off := pos.line
  var col-off := pos.col
  with handler
    fun do-start-chunked(s: string, start: alex-pos)
      slices := Cons((s.string/bytes, start), slices)
    fun end-chunked()
      match slices
        Cons((s, start), rst) -> 
          slices := rst
          (s.string, start)
        Nil -> throw("end-chunked when no chunked input")
    fun add-chunk(f)
      match slices
        Cons((s, st), rst) -> 
          slices := Cons((s ++ f.bytes, st), rst)
        Nil ->
          throw("add-chunk when no chunked input")
    fun get-rawdelim()
      raw-delim
    fun set-rawdelim(i)
      raw-delim := i
    fun check-linedir(l, start: alex-pos, end: alex-pos)
      match l
        LexComment(s) -> 
          if s.starts-with("#line").bool then
            val lineadj = s.list.drop(6).drop-while(is-white)
            match lineadj
              Cons('(', rst) -> 
                val linecol = rst.take-while(_ != ')').string.split(",")
                match linecol
                  Cons(ln, Cons(col)) -> 
                    line-off := ln.list.get-int - start.line
                    col-off-line := start.column
                    col-off := col.list.get-int - start.column
                  _ -> ()
              _ -> line-off := lineadj.get-int - start.line
          else
            ()
        _ -> ()
      l
    fun do-emit(l, lstart, lend)
      val AlexPos(soff, sline, scol) = lstart.adjust(line-off, if col-off-line == lstart.line then col-off else 0)
      val AlexPos(eoff, eline, ecol) = lend.adjust(line-off, if col-off-line == lend.line then col-off else 0)
      lexemes := Cons(Lexeme(make-range(Pos(src, soff, sline, scol), Pos(src, eoff, eline, ecol)), l), lexemes)
  alex-scan(str.bytes.slice, 0)
  lexemes.reverse

fun adjust(pos: alex-pos, l: int, c: int): alex-pos
  match pos
    AlexPos(off, line, col) -> AlexPos(off, line + l, col + c)

fun get-int(l: list<char>): int
  l.drop-while(is-white).take-while(is-digit).string.parse-int.default(0)

pub fun lexer(path: string, line: int, input: string): _ list<lexeme>
  lexing(Source(path, input), line, input)

pub fun lexing(source: source, line: int, input: string): _ list<lexeme>
  val init-pos = Pos(source, 0, 0, 1)
  lex(input, init-pos)

