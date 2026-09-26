// Updated as of 7/24/26: Commit dd91082
module compiler/syntax/lexer

import compiler/syntax/lexeme
import compiler/syntax/lex
import compiler/common/range
import std/core/unsafe

// An open chunk: a SPAN of the input, plus any earlier spans already cut out
// (see `extend-chunk`). A struct rather than a tuple -- five fields do not
// pattern-match as a tuple.
struct chunk
  opening: string   // `prefix` is reserved (operator fixity)
  span-start: int
  span-end: int
  earlier: list<string>
  start-pos: alex-pos

fun lex(str: string, pos: pos): _ list<lexeme>
  val src = pos.source
  // taken ONCE: cutting a chunk out is then a slice of this, not a re-encode
  // of the whole input per chunk
  val input-bytes = str.string/bytes
  fun input-slice(start: int, end: int): string
    if end <= start then "" else input-bytes.subbytes(start, end - start).string
  var lexemes := []
  var slices := []
  var raw-delim := 0
  var col-off-line := pos.line
  var line-off := pos.line
  var col-off := pos.col
  with handler
    // A chunk is a SPAN of the input
    //
    // The scanner calls the extend once per CHARACTER inside a comment or string 
    //
    // So extending is two integer writes, and the text is cut out of the input exactly once, when the chunk is finalised.
    //
    // `parts` exists because a chunk is not always ONE span: a non-contiguous
    // match (nested block comments can produce one, see koka.x's `TODO?` on the
    // "*/" rule) flushes the span held so far and starts a fresh one. The
    // handler decides that by comparing the incoming match's start against the
    // span's end, so it cannot get this wrong by construction.
    //
    // UTF-8 is safe: every offset is an alex match boundary and `@utf8` matches
    // a COMPLETE sequence, so a span never cuts a character in half.
    fun do-start-chunked(s: string, start: alex-pos, content-off: int)
      slices := Cons(Chunk(s, content-off, content-off, [], start), slices)
    fun end-chunked()
      match slices
        Cons(Chunk(opening, sstart, send, parts, start), rst) ->
          slices := rst
          val all = Cons(input-slice(sstart, send), parts).reverse
          (opening ++ all.join, start)
        Nil -> throw("end-chunked when no chunked input")
    fun extend-chunk(start-off: int, end-off: int)
      match slices
        Cons(Chunk(opening, sstart, send, parts, st), rst) ->
          val entry = if start-off == send
                        then Chunk(opening, sstart, end-off, parts, st)   // contiguous: O(1)
                        else Chunk(opening, start-off, end-off,           // gap: keep what we had
                                   Cons(input-slice(sstart, send), parts), st)
          slices := Cons(entry, rst)
        Nil ->
          throw("extend-chunk when no chunked input")
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
      // token ranges END on their last character (inclusive), not one past it;
      // `before` only decrements the column (offset and line are unchanged)
      lexemes := Cons(Lexeme(make-range(Pos(src, soff, sline, scol), Pos(src, eoff, eline, max(1, ecol - 1))), l), lexemes)
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

