//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated to commit #a22ccc2 (of Parse.hs) + extras for Koka parsing framework

import compiler/syntax/layout
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/syntax/syntax
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import std/core/debug

effect parse-error
  final ctl parse-error(e: string, r: range): a

linear effect token-parse
  val source-info: source
  fun add-warning(w: string, r: range): ()
  fun ppeek(): maybe<lexeme>
  fun undelimit(msg: string): ()
  fun reset(msg: string): ()
  fun delimit(msg: string): ()
  fun pnext(): maybe<lexeme>
  fun took-input(msg: string): bool
  fun ptrace(s: string): ()
  fun take-all(): list<lexeme>
  fun put-all(lexemes: list<lexeme>): ()
  fun get-lexemes_(): list<lexeme>

fun parse-delimited(msg: string, f: () -> _ a): _ a
  delimit(msg)
  with override
    final ctl parse-error(e, r) 
      undelimit(msg)
      parse-error("\nWhen parsing " ++ msg ++ " " ++ e, r)
  val x = f()
  undelimit(msg)
  x

fun peek(): _ lexeme
  val p = ppeek()
  match p
    Just(l) -> l
    Nothing -> parse-error("unexpected end of file", null)

fun next(): _ lexeme
  val p = pnext()
  match p
    Just(l) -> l
    Nothing -> parse-error("unexpected end of file", null)

fun lex-parse(allow-at: bool, insert-semis: bool, preprocess: list<lexeme> -> pure list<lexeme>, p: () -> _ a, sourceName: string, input: string): _ a
  val src = Source(sourceName, input)
  val lexes = lexing(src, 1, input)
  // trace(lexes.map(show).join("\n"))
  val lexes' = preprocess(layout(lexes, allow-at, insert-semis))
  // trace(lexes'.map(show).join("\n"))
  with parse-lexemes(src, lexes')
  p()
  
fun parse-lexemes(src: source, lexemes0: list<lexeme>, p: () -> _ a): _ a
  var lexemes := lexemes0
  // trace(lexemes0.show)
  var history := Cons(([], "top", 0), Nil)
  val debug = True
  with override
    final ctl parse-error(e: string, r: range)
      parse-error("Got error: " ++ e ++ "\n" ++ " when parsing:\n\t" ++ lexemes.take(2).map(show).join("\n\t"), r)
  with handler
    val source-info = src
    fun get-lexemes_() lexemes
    fun take-all()
      val l = lexemes
      lexemes := Nil // TODO: This ruins the history -- especially with delimiting
      // history := Cons((ctx hole, "top", 0), Nil)
      l
    fun put-all(lexemes': list<lexeme>)
      lexemes := lexemes' // TODO: This ruins the history -- especially with delimiting
      // history := Cons((ctx hole, "top", 0), Nil)
    fun add-warning(w: string, r: range)
      ()
    fun pnext()
      match lexemes
        Cons(l, rst) ->
          lexemes := rst 
          match history
            Cons((h, msg, i), tl) ->
              history := Cons((Cons(l, h), msg, i + 1), tl)
            Nil -> 
              impossible("unexpected top of context")
          Just(l)
        Nil -> Nothing
    fun reset(msg)
      match history
        Cons((h, str, _), rst) -> 
          if str != msg then
            // trace("Resetting " ++ str ++ " but expected " ++ msg)
            impossible("Reset error")
          else
            lexemes := h.reverse ++ lexemes
            history := rst
            // if debug then
            //   trace("Resetting " ++ str ++ "\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ " at " ++ lexemes.head.map(show).default("eof") ++ "\nputting back:\n\t" ++ (h ++. Nil).map(show).join("\n\t"))
        Nil ->
          impossible("mismatched reset")
    fun delimit(msg)
      history := Cons(([], msg, 0), history)
    fun undelimit(msg)
      match history
        Cons((lexes, str, _), Cons((lexes2, str2, i2), rst)) ->
          if str == msg then
            history := Cons((lexes ++ lexes2, str2, i2), rst)
          else
            trace("Undelimiting " ++ str ++ " but expected " ++ msg)
            impossible("Undelimit error")
        _ ->
          impossible("Undelimiting from top")
    fun ppeek()
      match lexemes
        Cons(l, _) -> Just(l)
        Nil -> Nothing
    fun took-input(str)
      match history
        Cons((_, msg, i), _) ->
          if str != msg then
            trace("Checking if input was taken for " ++ str ++ " but expected " ++ msg)
            impossible("Take input error")
          else
            i != 0
        Nil ->
          False
    fun ptrace(s: string)
      if debug then
        trace(s ++ "\n  " ++ history.map(fn(x) "When parsing " ++ x.snd).join("\n\t") ++ " next parse-token: " ++ lexemes.take(1).map(show).join(","))
  mask<local>{p()}


fun peof()
  // if debug then
  //   trace("Parsing eof\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ "\n\nHad leftovers: " ++ lexemes.map(fn(x) x.show).join("\n"))
  match get-lexemes_()
    Cons(l, _) -> parse-error("peof expected end of file", l.range)
    Nil -> ()
fun parse-many(kind: string, l: () -> _ a): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> Cons(r, parse-many(kind, l))
    Nothing -> Nil

fun parse-many1(kind: string, l: () -> _ a): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> Cons(r, parse-many(kind, l))
    Nothing -> parse-error("at least 1 of " ++ kind, peek().range)

fun parse-many-end(kind: string, l: () -> _ a, p: () -> _ b): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> 
      match parse-maybe-nb("sep " ++ kind, p)
        Just(_) -> Cons(r, parse-many-end(kind, l, p))
        Nothing -> Cons(r, Nil)
    Nothing -> Nil

fun parse-many-end1(kind: string, l: () -> _ a, p: () -> _ b): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> 
      match parse-maybe-nb("sep " ++ kind, p)
        Just(_) -> Cons(r, parse-many-end(kind, l, p))
        Nothing -> Cons(r, [])
    Nothing -> parse-error("at least 1 of " ++ kind, peek().range)

fun parse-token(msg: string, f: (lexeme) -> _ maybe<a>): _ a
  val t = peek()
  match f(t) 
    Just(a) -> 
      next() 
      // ptrace("Consuming " ++ t.show)
      a
    Nothing ->
      parse-error("expecting " ++ msg, peek().range)

// Version of maybe that does backtrack
fun parse-maybe<e>(str: string, p: () -> _ a): _ maybe<a>
  delimit(str)
  with override
    return(r)
      undelimit(str)
      Just(r)
    final ctl parse-error(e, r) 
      reset(str)
      Nothing
  p()

fun parse-maybe-list(p: () -> _ list<a>): _ list<a>
  match parse-maybe("list", p)
    Just(r) -> r
    Nothing -> []

fun parse-try(p: () -> _ a, ?kk-file-line: string): _ a
  delimit(kk-file-line)
  with override
    return(r) 
      undelimit(kk-file-line)
      r
    final ctl parse-error(e, r) 
      reset(kk-file-line)
      parse-error(e,r)
  p()
  

// Version of maybe that doesn't backtrack
fun parse-maybe-nb(str: string, p: () -> _ a): _ maybe<a>
  delimit(str)
  with override
    return(r)
      undelimit(str)
      Just(r)
    final ctl parse-error(e, r)
      if took-input(str) then
        undelimit(str)
        parse-error("\nWhen parsing " ++ str ++ " " ++ e, r)
      else
        undelimit(str)
        Nothing 
  p()

// Parse parse-choices without backtracking. 
// Make sure that all parse-choices start differently or is the last choice.
fun parse-choices-nb(str: string, ps: list<() -> _ a>): _ a
  with parse-delimited(str)
  fun find(ps': list<() -> _ a>): _ a
    match ps'
      Cons(p, rst) -> 
        match parse-maybe-nb(str, p)
          Just(r) -> r
          Nothing -> find(rst)
      Nil -> parse-error("expected " ++ str, peek().range)
  find(ps)

// Parse parse-choices with backtracking
fun parse-choices(str: string, ps: list<() -> _ a>): _ a
  fun find(ps': list<() -> _ a>): _ a
    match ps'
      Cons(p, rst) -> 
        match parse-maybe(str, p)
          Just(r) -> r
          Nothing -> find(rst)
      Nil -> parse-error("expected " ++ str, peek().range)
  find(ps)

val parse-sep-by = parse-many-end
val parse-sep-by1 = parse-many-end1

fun make-parse-error(r: range, e: string): _ a
  parse-error("invalid syntax" ++ e.list.drop-while(fn(x) x != ':').string, r)

fun bracketed(open: () -> _ range, close: () -> _ range, f: (a, range) -> _ b, p: () -> _ a): _ b
  val rng1 = open()
  val x = p()
  val rng2 = close()
  f(x, rng1.range/combine(rng2))

fun braced(p: () -> _ a): _ a
  parse-choices("braced", [{
      parse-left-curly() // TODO: Make sure right is same as left? (inserted versus actual)
      parse-many("semicolons", parse-semicolon)
      val x = p()
      parse-many("semicolons", parse-semicolon)
      parse-right-curly()
      x
    }, p])

fun parse-semi-braces(kind: string, p: () -> _ a): _ list<a>
  parse-semi-braces-ranged(kind, p).fst

fun parse-semi-braces-ranged(kind: string, p: () -> _ a): _ (list<a>, range)
  val rng1 = parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val xs = parse-many-end(kind, p, parse-semi1)
  val rng2 = parse-right-curly()
  (xs, rng1.combine(rng2))

fun parse-semi-braces-ranged1(kind: string, p: () -> _ a): _ (list<a>, range)
  val rng1 = parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val xs = parse-many-end1(kind, p, parse-semi1)
  val rng2 = parse-right-curly()
  (xs, rng1.combine(rng2))

fun parse-semi-braced(kind: string, p: () -> _ a): _ a
  parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val x = p()
  parse-many("semicolons", parse-semicolon)
  parse-right-curly()
  x

fun semis(kind: string, p: () -> _ a): _ list<a>
  parse-many-end(kind, p, parse-semi1)

fun semis1(kind: string): _ list<range>
  parse-many1("semicolons", parse-semicolon)

fun parse-semi1(): _ list<range>
  parse-many1("semicolons", parse-semicolon)

fun angles-ranged(p: () -> _ a): _ (a, range)
  bracketed(parse-left-angle, parse-right-angle, fn(x, r) (x,r), p)

fun angles(p: () -> _ a): _ a
  bracketed(parse-left-angle, parse-right-angle, fn(x, r) x, p)

fun parse-parens-commas(p: () -> _ a): _ list<a>
  parensx(parse-left-paren, fn(a, r) a)
    parse-sep-by("comma", p, parse-comma)

fun parens-ranged(p: () -> _ a): _ (a, range)
  parensx(parse-left-paren, fn(a, b) (a, b), p) 

fun parens(p: () -> _ a): _ a
  parensx(parse-left-paren, fn(a, b) a, p) 

fun parse-parens-commas-ranged(p: () -> _ a): _ (list<a>, range)
  parensx(parse-left-paren, fn(a, r) (a, r))
    parse-sep-by("comma", p, parse-comma)

fun parensx(l: () -> _ range, f: (a, range) -> _ b, p: () -> _ a): _ b
  bracketed(l, parse-right-paren, f, p)

fun parse-range(msg: string, f: (lexeme) -> _ bool): _ range
  parse-token(msg, fn(x) if f(x) then Just(x) else Nothing).range

inline fun parse-vertical-bar(): _ range
  parse-keyword("|")

inline fun parse-comma(): _ range
  parse-special(",")

inline fun parse-semicolon(): _ range
  parse-range("semicolon", is-semicolon)

fun parse-left-curly(): _ range
  parse-range("{", _.lex.is-lcurly)

fun parse-right-curly(): _ range
  parse-range("}", _.lex.is-rcurly)

fun parse-left-bracket(): _ range
  parse-range("[", _.lex.is-lbracket)

fun parse-right-bracket(): _ range
  parse-range("]", _.lex.is-rbracket)

fun parse-left-paren(): _ range
  parse-range("(", _.lex.is-lparen)

fun parse-right-paren(): _ range
  parse-range(")", _.lex.is-rparen)

fun parse-left-angle(): _ range
  parse-range("<", _.lex.is-langle)

fun parse-right-angle(): _ range
  parse-range(">", _.lex.is-rangle)

fun parse-type-binder-id(): _ (name, range)
  parse-choices("tBinderId", [parse-type-ident])

fun parse-import-alias(): _ (name, name, range, range)
  val (name1, rng1) = parse-module-path()
  val r = parse-maybe("import alias")
    parse-keyword("=")
    parse-module-path()
  match r
    Just((name2, rng2)) -> (name1, name2, rng1, rng2)
    Nothing -> (name1, name1, rng1, rng1)

fun parse-param-id(): _ (name, range)
  parse-choices("param id", [parse-identifier, parse-wildcard])

fun parse-param-info(): _ param-info
  parse-choices("param info", [{
    parse-special-op("^")
    Borrow
  }, {Own}])

fun parse-identifier(): _ (name, range)
  ensure-unqualified("identifier", parse-qualified-identifier)

fun parse-fip-alloc(): _ (fip-alloc, range)
  parse-choices("alloc", [
    {
      parens
        parse-choices("alloc", [
          { val (i, lex) = parse-integer(); (AllocAtMost(i), lex.range) },
          { val rng = parse-special-id("n"); (AllocFinitely, rng) },
        ])
      },
   { (AllocAtMost(0), null) }
  ])

fun parse-tail-fip(): _ (fipT, range)
  val (isTail, rng) = parse-choices("tail", [{(True, parse-special-id("tail"))}, {(False, null)}])
  parse-fip-ex(rng, isTail)

fun parse-fip-ex(rng0: range, isTail: bool): _ (fipT, range)
  parse-choices("fip", [{
      val rng1 = parse-special-id("fip")
      val (alloc, rng2) = parse-fip-alloc()
      if isTail then
        add-warning("fip function already implies 'tail'", rng1)
      (Fip(alloc), combine([rng0, rng1, rng2]))
    }, 
    {
      val rng1 = parse-special-id("fbip")
      val (alloc, rng2) = parse-fip-alloc()
      (Fbip(alloc, isTail), combine([rng0, rng1, rng2]))
    }, 
    { (NoFip(isTail), null) }
  ])

fun parse-inline(): _ def-inline
  parse-choices("inline", [{
      parse-special-id("inline")
      InlineAlways
    }, {
      parse-special-id("noinline")
      InlineNever
    }, 
    { InlineAuto }
  ])

fun parse-idcon(): _ user-expr
  val (name, rng) = parse-choices("", [parse-qualified-identifier, parse-qualified-constructor])
  Var(name, False, rng)

inline fun parse-qualified-identifier(): _ (name, range)
  parse-choices("qidentifier", [parse-qualified-var-id, parse-qualified-op-id])

inline fun parse-qualified-constructor(): _ (name, range)
  parse-qualified-constructor-id()

inline fun parse-qualified-operator(): _ (name, range)
  parse-qualified-op()

fun parse-fun-id(): _ (name, range)
  parse-locally-qualified-identifier() // [] doesn't work with local qualification

fun parse-locally-qualified-identifier(): _ (name, range)
  val (name, rng) = parse-qualified-identifier()
  (name.requalify-locally, rng)

fun parse-var-id(): _ (name, range)
  ensure-unqualified("variable id", parse-qualified-var-id)

fun parse-op-id(): _ (name, range)
  ensure-unqualified("operator", parse-qualified-op-id)

fun parse-constructor-id(): _ (name, range)
  ensure-unqualified("constructor", parse-qualified-constructor-id)
    // { val (s, rng) = parse-string-literal(); (new-name(s), rng)}

fun parse-op(): _ (name, range)
  ensure-unqualified("operator", parse-qualified-op)

fun parse-type-ident(): _ (name, range)
  val (name, rng) = parse-qualified-type-id()
  if name.is-qualified then
    parse-error("expected unqualified type name", rng)
  else
    (name, rng)

fun ensure-unqualified(str: string, p: () -> _ (name, range)): _ (name, range)
  val (n, r) = p()
  if n.is-qualified then 
    parse-error("expected unqualified " ++ str, r)
  else
    (n, r)

fun parse-qualified-type-id(): _ (name, range)
  with parse-try()
  val (name, range) = parse-choices("qTypeId", [parse-qualified-var-id, parse-type-id-context])
  if !name.is-type-var then 
    (name, range)
  else // TODO: This isn't quite the right hack.
    parse-error("type name (and not type variable)", range)

fun parse-type-id-context(): _ (name, range)
  ("ctx".new-name, parse-keyword("ctx"))

fun parse-qualified-op(): _ (name, range)
  parse-token("operator") fn(a)
    match a
      Lexeme(rng, LexOp(id)) -> Just((id, rng))
      _ -> Nothing

fun parse-prefix-op(): _ expr<a>
  parse-token("prefix operator") fn(a)
    match a
      Lexeme(rng, LexPrefix(id)) -> Just(Var(id, True, rng))
      _ -> Nothing

// is really qvarid, varid, from the spec
fun parse-qualified-var-id(): _ (name, range)
  parse-token("variable id") fn(a)
    match a
      Lexeme(rng, LexId(id)) -> Just((id.show-plain.new-name, rng))
      _ -> Nothing

// is really qidop and idop from the spec
fun parse-qualified-op-id(): _ (name, range)
  parse-token("operator id") fn(a)
    match a
      Lexeme(rng, LexIdOp(id)) -> Just((id, rng))
      _ -> Nothing

// is really qconid and conid in the spec
fun parse-qualified-constructor-id(): _ (name, range)
  parse-token("constructor id") fn(a)
    match a
      Lexeme(rng, LexCons(id)) -> Just((id, rng))
      _ -> Nothing

fun parse-module-path(): _ (name, range)
  parse-token("module path") fn(x)
    match x 
      Lexeme(rng, LexId(id)) -> Just((id.name-as-module-name, rng)) // return the entire module path as one identifier
      _ -> Nothing

fun parse-wildcard(): _ (name, range)
  parse-token("wildcard") fn(a)
    match a
      Lexeme(rng, LexWildCard(id)) -> 
        if id.show-plain == "_" then 
          Just((unique-range-name(rng, "_w"), rng))
        else Just((id, rng))
      _ -> Nothing

fun parse-integer(): _ (int, lexeme)
  parse-token("integer") fn(l)
    match l
      Lexeme(_, LexInt(i)) -> Just((i, l))
      _ -> Nothing

fun parse-float(): _ (float64, lexeme)
  parse-token("float") fn(l)
    match l
      Lexeme(_, LexFloat(d)) -> Just((d, l))
      _ -> Nothing

fun parse-char-literal(): _ (char, range)
  parse-token("char literal") fn(x) 
    match x
      Lexeme(rng, LexChar(c)) -> Just((c, rng))
      _ -> Nothing

fun parse-string-literal(): _ (string, range)
  parse-token("string literal") fn(x) 
    match x
      Lexeme(rng, LexString(s)) -> Just((s, rng))
      _ -> Nothing

fun parse-special-op(s: string): _ range
  parse-token(s) fn(x)
    match x.lex
      LexOp(s') | s == s'.show-plain -> Just(x.range)
      _ -> Nothing

fun default/parse-special-id(s: string): _ range
  parse-token(s) fn(x)
    match x.lex
      LexId(id) | id.show-plain == s -> Just(x.range)
      _ -> Nothing

fun parse-special-id(s: string, alternates: list<string>): _ range
  parse-token(s) fn(x)
    match x.lex
      LexId(id) | id.show-plain == s -> Just(x.range)
      LexId(id) | alternates.any(_ == id.show-plain) -> 
        add-warning("using deprecated keyword " ++ id.show-plain ++ ", use " ++ s ++ " instead", x.range)
        Just(x.range)
      _ -> Nothing

fun parse-special-con-id(s: string): _ range
  parse-token(s) fn(x)
    match x.lex
      LexCons(s') | s == s'.show-plain -> Just(x.range)
      _ -> Nothing

inline fun default/parse-special(s: string): _ range
  parse-special(s, [])

fun parse-special(s: string, alternates: list<string>): _ range
  parse-token(s) fn(x)
    match x.lex
      LexSpecial(s') | s == s' -> Just(x.range)
      LexSpecial(s') | alternates.any(_ == s') -> 
        add-warning("using deprecated keyword " ++ s' ++ ", use " ++ s ++ " instead", x.range)
        Just(x.range)
      _ -> Nothing

inline fun default/parse-keyword(s: string): _ range
  parse-keyword_(s, []).range

inline fun range/parse-keyword(s: string, alts: list<string>): _ range
  parse-keyword_(s, alts).range

fun parse-keyword_(s: string, alternates: list<string>): _ lexeme
  parse-token("keyword " ++ s) fn(x)
    match x.lex
      LexKeyword(s', _) | s == s' -> Just(x)
      LexKeyword(s', _) | alternates.any(_ == s') -> 
        add-warning("using deprecated keyword " ++ s' ++ ", use " ++ s ++ " instead", x.range)
        Just(x)
      _ -> Nothing

fun default/parse-doc-keyword(s: string): _ (range, string)
  parse-doc-keyword(s, [])

fun parse-doc-keyword(s: string, alternates: list<string>): _ (range, string)
  match parse-keyword_(s, alternates)
    Lexeme(rng, LexKeyword(_, doc)) -> (rng, doc)
    _ -> parse-error("expected " ++ s, null)

fun parse-doccon-id(): _ (name, (range, string))
  parse-token("constructor") fn(x)
    match x.lex
      LexCons(id, doc) -> Just((id.requalify-locally, (x.range, doc)))
      _ -> Nothing 

fun unique-range-hidden-name(pre: string, rng: range): name
  val pos = rng.start
  new-hidden-name-ex(pre, pos.line.show ++ "_" ++ pos.col.show)

fun unique-range-name(rng: range, pre: string): name
  val pos = rng.start
  new-name(pre ++ "-l" ++ pos.line.show ++ "-c" ++ pos.col.show)

fun expr/adjust-range(ue: user-expr, r: range): user-expr
  Parens(ue, nil, "", r)

fun tp/adjust-range(ut: user-type, r: range): user-type
  TpParens(ut, r)

fun unimplemented(): _ a
  parse-error("unimplemented", peek().range)

fun main()
  "Compiles".println