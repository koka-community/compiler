import compiler/common/range

import compiler/common/name

import compiler/syntax/layout

import compiler/syntax/lexer

import compiler/syntax/lexeme

import compiler/lib/pprint

import std/os/file

import std/os/path

// The idea is to first do tokenization, and then layout to get implicitly added braces etc.
// Then based on some user parameters we can format the code in different ways as a transformation on the lexemes.
// These transformations have to uphold the following properties:
// - Only add / remove whitespace (spaces, tabs, newlines), braces, and semicolons.
// - Only affect whitespace that will not change the layout of the code. Some whitespace is significant and should not be removed.
// - TODO: Allow transforming comments in the future (for changing comments to doc comments if immediately prior to a declaration, and nested in markdown comments).
// Finally we print out the lexemes.

// We should design this with the language server protocol in mind, so we can implement formatting requests.
// (We need to keep track of deleted ranges, and added ranges, relative to the last version of the document)

effect val format-opts: formatting-options

value struct formatting-options
  indent-size: int = 2
  use-tabs: bool = False // TODO: Implement this
  add-braces: bool = False // TODO: Implement this
  remove-braces: bool = False // TODO: Implement this -- might be tricky?
  add-semicolons: bool = False // TODO: Implement this
  remove-semicolons: bool = False // TODO: Implement this -- might be tricky?
  show-full-names: bool = False

// TODO: Implement this

fun file/format(f: path): <format-opts,io> ()
  val file = read-text-file(f)
  // Keeping comments causes issues with layout algorithm, so we need better comment integration into keywords, or better layout
  val l = lex-source(Source(f.string, file), 0, True, True, id)
  write-text-file(f, format(l).show)

fun list/format(l: list<lexeme>): <format-opts,pure> doc
  // trace("Previous lexemes: " ++ l.show)
  val integrated = l.integrate-comments(ctx _)
  // trace("Integrated lexemes: " ++ integrated.show)
  var current-indent := 0
  with handler
    fun increase-indentation()
      current-indent := current-indent + format-opts.indent-size
    fun decrease-indentation()
      current-indent := current-indent - format-opts.indent-size
    fun next-line(next)
      match next
        Cons(Lexeme(_, LexKeyword("import"))) ->
          // Put imports on the next line
          "\n".text |.| spaces(current-indent).text
        _ ->
          if current-indent == 0 then
            // All other top level declarations should be separated by two newlines
            "\n\n".text |.| spaces(current-indent).text
          else
            // Otherwise just one newline
            "\n".text |.| spaces(current-indent).text
    fun remove-range(r: range)
      ()
    fun insert-range(r: range, text: string)
      ()
  pretty(integrated)

effect format-eff
  fun increase-indentation(): ()
  fun decrease-indentation(): ()
  fun next-line(l: list<lexeme>): doc
  fun remove-range(r: range): () // For language server reporting
  fun insert-range(r: range, text: string): () // For language server reporting

// We need to take the comments back out of keywords, and put them before any keyword modifiers

fun integrate-comments(l: list<lexeme>, acc: ctx<list<lexeme>>): list<lexeme>
  match l
    Cons(lexeme as Lexeme(r, LexKeyword(k, d)), rest) | k.is-doc-keyword && !d.is-empty ->
      Cons(Lexeme(r, LexComment(d)), acc ++. Cons(lexeme, integrate-comments(rest, ctx _)))
    Cons(lexeme as Lexeme(r, LexCons(_, d)), rest) | !d.is-empty ->
      Cons(Lexeme(r, LexComment(d)), acc ++. Cons(lexeme, integrate-comments(rest, ctx _)))
    Cons(lexeme as Lexeme(_, lex), rest) | lex.is-valid-prefix ->
      integrate-comments(rest, acc ++ ctx Cons(lexeme, _))
    Cons(lexeme, rest) ->
      acc ++. Cons(lexeme, integrate-comments(rest, ctx _))
    Nil ->
      acc ++. Nil

fun pretty(l: list<lexeme>)
  match l
    Cons(comment, rest) | comment.lex.is-lexComment ->
      comment.pretty |.| next-line(rest) |.| pretty(rest)
    Cons(lexeme, rest) | lexeme.lex.is-open-brace ->
      increase-indentation()
      lexeme.pretty |.| next-line(rest) |.| pretty(rest)
    Cons(lexeme, Cons(next, rest)) | lexeme.lex.is-close-brace ->
      decrease-indentation()
      if lexeme.range.end.line < next.range.start.line then
        lexeme.pretty |.| next-line(Cons(next, rest)) |.| pretty(Cons(next, rest))
      elif lexeme.range.end.col != next.range.start.col then
        lexeme.pretty |+| pretty(Cons(next, rest))
      else
        lexeme.pretty |.| pretty(Cons(next, rest))
    Cons(lex, Cons(next, rest)) ->
      if lex.range.end.line < next.range.start.line then
        lex.pretty |.| next-line(rest) |.| pretty(Cons(next, rest))
      elif lex.range.end.col != next.range.start.col then
        lex.pretty |+| pretty(Cons(next, rest)) // TODO: Strings have bad ranges
      else
        lex.pretty |.| pretty(Cons(next, rest))
    Cons(lex, Nil) -> lex.pretty
    Nil -> pprint/empty

fun lex/pretty(lexeme: lexeme): div doc
  match lexeme.lex
    LexInt(_, s) -> s.text
    LexFloat(_, s) -> s.text
    LexChar(c) -> c.show.text // TODO Better character showing?
    LexString(s) -> ("\"" ++ s ++ "\"").text // Show has the problem of double escaping
    LexId(n) -> n.pretty-full-name
    LexOp(n) -> n.pretty-local-name
    LexPrefix(n) -> n.pretty-local-name
    LexIdOp(n) -> n.pretty-local-name
    LexWildCard(n) -> n.pretty-local-name
    LexModule(_, full) -> full.pretty-full-name
    LexKeyword(k) -> k.text
    LexSpecial(s) -> s.text
    LexComment(s) -> format-comment(s)
    LexWhite -> empty
    LexInsLCurly -> empty
    LexInsRCurly -> empty
    LexInsSemi -> empty
    LexError -> empty
    LexCons(n) -> n.pretty-local-name
    LexTypedId(n) -> n.pretty-local-name

fun format-comment(s: string): doc
  s.split("//").drop-while(is-empty).map(fn(l) "//".text |+| l.trim.text).vcat