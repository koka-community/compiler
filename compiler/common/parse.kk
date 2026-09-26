//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 8/3/26: Commit eb98b61d (of Parse.hs) + extras for Koka
// parsing framework -- content-verified identical modulo the single-line
// error-message wording fix (upstream eb98b61dc "better grammar")

module compiler/common/parse

import std/core/unsafe
import compiler/syntax/layout
import compiler/syntax/lexer
import compiler/syntax/lexeme
import compiler/syntax/syntax
import compiler/common/syntax
import compiler/common/name
import compiler/common/name-prim
import compiler/common/range
import std/core/debug
import std/os/env

pub effect parse-error
  final ctl parse-error(e: string, r: range): a

pub linear effect token-parse
  val source-info: source
  val ptarget-platform: target-platform
  // KOKA_PARSE_CONTEXT=1: report errors with the full "When parsing ..."
  // context stack + surrounding lexemes (richer than upstream, whose Parsec
  // errors show only the failure point). Off by default so error-expectation
  // tests match the upstream-recorded outputs.
  val perr-context: bool
  fun add-warning(w: string, r: range): ()
  fun ppeek(): maybe<lexeme>
  fun pnext(): maybe<lexeme>
  // One handler round-trip per token ATTEMPT, instead of peek-then-next on
  // success and peek-then-peek-again on failure. `Right` consumed, `Left(Just)`
  // did not and hands back the lexeme it looked at (so the caller needs no
  // second `ppeek` for the range), `Left(Nothing)` is end of input.
  fun ptoken(f: (lexeme) -> maybe<a>): either<maybe<lexeme>, a>
  // Backtracking state is saved LEXICALLY by the combinator that needs it (see
  // `parse-maybe`), not pushed on a shared history stack. `get-pos` is what
  // makes Parsec's consumed-input test possible without a frame.
  fun get-pos(): int
  fun set-pstate(l: list<lexeme>, p: int): ()
  // parsec-style farthest-failure tracking: token-level parsers record what
  // they EXPECTED at the position they failed; the outermost handler reports
  // the farthest such failure ("unexpected X\n expecting A, B or C") like
  // upstream's Parsec errors, instead of whichever error happened to
  // propagate out of the backtracking structure last
  // Carries the LEXEME, not a rendered string: `parse-token` records an
  // expectation on every failed token match, and in a backtracking combinator
  // parser that is normal control flow -- `parse-choices` fails its way down
  // the alternatives. Only the FARTHEST failure is ever printed, so rendering
  // here formatted a lexeme per failure and discarded nearly all of them
  // (`lexeme/show` was 2.6% of a warm no-op build). Render at the point of use.
  fun precord-expect(lbl: string, unexp: maybe<lex>, r: range): ()
  fun pfar-snapshot(): (range, maybe<lex>, list<string>)
  fun pfar-restore(snap: (range, maybe<lex>, list<string>)): ()
  fun take-all(): list<lexeme>
  fun put-all(lexemes: list<lexeme>): ()
  fun get-lexemes_(): list<lexeme>

// Context only -- it adds "When parsing X" to an error under
// KOKA_PARSE_CONTEXT=1. It used to push a backtrack frame as well, which bought
// nothing: it never rewinds.
inline fun parse-delimited(msg: string, f: () -> _ a): _ a
  with override
    final ctl parse-error(e, r)
      // default: re-raise UNCHANGED (upstream Parsec errors report only the
      // failure point, and the error-expectation tests match that); with
      // KOKA_PARSE_CONTEXT=1 keep the richer "When parsing" context stack
      if perr-context && msg != ""
        then parse-error("\nWhen parsing " ++ msg ++ " " ++ e, r)
        else parse-error(e, r)
  f()

pub inline fun peek(): _ lexeme
  val p = ppeek()
  match p
    Just(l) -> l
    Nothing -> parse-error("unexpected end of file", null)

pub inline fun next(): _ lexeme
  val p = pnext()
  match p
    Just(l) -> l
    Nothing -> parse-error("unexpected end of file", null)

pub fun lex-parse(allow-at: bool, insert-semis: bool, preprocess: list<lexeme> -> pure list<lexeme>, p: () -> _ a, tpl: target-platform, sourceName: string, input: string): _ a
  val src = Source(sourceName, input)
  val lexes = lexing(src, 1, input)
  // trace(lexes.map(show).join("\n"))
  val lexes' = preprocess(layout(lexes, allow-at, insert-semis))
  // trace(lexes'.map(show).join("\n"))
  with parse-lexemes(src, lexes', tpl)
  p()

// first occurrence wins, order preserved -- the accumulation side is now a
// plain cons (see `precord-expect`), so this is where duplicates are removed
fun dedup-first(xs: list<string>): list<string>
  xs.foldl([]) fn(acc: list<string>, x: string)
    if acc.any(fn(y) y == x) then acc else Cons(x, acc)
  .reverse

// parsec `showErrorMessages` list format: "A, B or C"
fun expects-join(ls: list<string>): string
  match ls
    Nil -> ""
    [l] -> l
    Cons(l, rest) -> match rest.reverse
      Cons(lst, mid) -> (Cons(l, mid.reverse)).join(", ") ++ " or " ++ lst
      Nil -> l

// read once; `unsafe-total` keeps `ndet` out of every parse's row
val parse-stats-flag : bool = unsafe-total{ get-env-value("KOKA_PARSE_STATS").is-just }
// KOKA_KIND_TRACE=1: trace the `local kind` section -- what the emitter
// declares, what the reader parses, and every use site that falls back and
// finds nothing. Lives here because `core/parse` cannot import `std/os/env`:
// that module exports `get-env`, which collides with the parser's own `eenv`
// operation of the same name.
pub val kind-trace-flag : bool = unsafe-total{ get-env-value("KOKA_KIND_TRACE").is-just }
pub fun kind-trace-on(): bool
  kind-trace-flag
fun parse-stats-on(): bool
  parse-stats-flag

pub fun parse-lexemes(src: source, lexemes0: list<lexeme>, tpl: target-platform, p: () -> _ a): _ a
  // A backtrack frame records the not-yet-consumed SUFFIX of the (immutable)
  // lexeme list at its `delimit`, plus the absolute token position, so
  // delimit/undelimit/reset/took-input are all O(1) and frames share the
  // token list instead of copying it. (The previous representation kept a
  // consumed-lexeme list per frame which `pnext` consed onto and `undelimit`
  // merged into its parent with `++` -- O(n^2) time and memory on deeply
  // nested frames, e.g. nested parens or core inline sections.)
  var lexemes := lexemes0
  var pos := 0
  val debug = True
  val verbose-errors = get-env-value("KOKA_PARSE_CONTEXT").is-just
  // farthest-failure record (see the token-parse effect doc)
  var far-rng := range/null
  var far-unexp : maybe<lex> := Nothing
  var far-msgs : list<string> := []
  // DIAGNOSTIC (KOKA_PARSE_STATS=1): rewinds against tokens, the number that says
  // how close this parser is to Parsec's non-backtracking `<|>`. Reported with
  // `trace`, NOT `println`: trace carries no effect, so it cannot leak `console`
  // into this function's row (which would break the closure type `build.kk`
  // annotates on `parse-core`).
  var n-restore := 0
  var n-tokens := 0
  // The metric that actually matters: TOKENS THROWN AWAY. A 1-token rewind costs
  // almost nothing now that saving is lexical; a 50-token rewind wastes 50
  // token-parses. Rewind COUNT is a poor proxy -- cutting it 17% moved no time.
  var n-rewound := 0
  // `precord-expect` fires on every FAILED token match. At one position it
  // dedups with a linear scan of string compares and appends with `++ [lbl]`,
  // which copies -- so k alternatives failing at the same spot cost O(k^2).
  var n-expect := 0
  with override
    final ctl parse-error(e: string, r: range)
      // default: re-raise unchanged (upstream reports only the failure
      // message); KOKA_PARSE_CONTEXT=1 adds the upcoming-lexeme context
      if verbose-errors
        then parse-error("Got error: " ++ e ++ "\n" ++ " when parsing:\n\t" ++ lexemes.take(2).map(show).join("\n\t"), r)
      // report the FARTHEST recorded expectation when it lies beyond the
      // propagated error (Parsec merge semantics: furthest failure wins)
      elif !far-rng.is-null && far-msgs.is-cons && far-rng.start.off > r.start.off then
        val unexpLine = match far-unexp
          Just(u) -> "unexpected " ++ u.show ++ "\n"
          Nothing -> ""
        parse-error(unexpLine ++ "expecting " ++ expects-join(far-msgs.reverse.dedup-first), far-rng)
      else parse-error(e, r)
  with handler
    val source-info = src
    val ptarget-platform = tpl
    val perr-context = verbose-errors
    fun get-lexemes_() lexemes
    fun take-all()
      val l = lexemes
      lexemes := Nil // note: outer frames keep their own saved suffixes
      l
    fun put-all(lexemes': list<lexeme>)
      lexemes := lexemes' // note: outer frames keep their own saved suffixes
    fun add-warning(w: string, r: range)
      ()
    fun pnext()
      match lexemes
        Cons(l, rst) ->
          n-tokens := n-tokens + 1
          lexemes := rst
          pos := pos + 1
          Just(l)
        Nil -> Nothing
    fun get-pos() pos
    fun set-pstate(l, p0)
      n-restore := n-restore + 1
      n-rewound := n-rewound + (pos - p0)
      lexemes := l
      pos := p0
    fun ppeek()
      match lexemes
        Cons(l, _) -> Just(l)
        Nil -> Nothing
    fun ptoken(f)
      match lexemes
        Cons(l, rst) ->
          match f(l)
            Just(a) ->
              n-tokens := n-tokens + 1
              lexemes := rst
              pos := pos + 1
              Right(a)
            Nothing -> Left(Just(l))
        Nil -> Left(Nothing)
    fun pfar-snapshot()
      (far-rng, far-unexp, far-msgs)
    fun pfar-restore(snap)
      val (r0, u0, m0) = snap
      far-rng := r0
      far-unexp := u0
      far-msgs := m0
    fun precord-expect(lbl: string, unexp: maybe<lex>, r: range)
      if far-rng.is-null || r.start.off > far-rng.start.off then
        far-rng := r
        far-unexp := unexp
        far-msgs := (if lbl == "" then [] else [lbl])
      elif r.start.off == far-rng.start.off then
        val _ = match unexp
          Just(u) -> far-unexp := Just(u)
          Nothing -> ()
        // Just CONS it. This fires on every failed token match -- 11.5M times in
        // one warm build -- and it used to dedup by scanning the list with string
        // compares and appending with `++ [lbl]`, which copies: 33M string
        // compares and 11.5M list copies, O(k^2) in the alternatives tried at a
        // position. Parsec does not dedup as it accumulates either; it merges
        // and only tidies up in `showErrorMessages`. So do the same and dedup
        // when the message is RENDERED, which happens at most once per parse.
        if lbl != "" then far-msgs := Cons(lbl, far-msgs)
  // NB: keep this row free of `console`/`ndet` -- `build.kk` annotates the
  // closure `parse-core` returns, and a stray effect here breaks that
  // annotation. Counting instrumentation must not live in this function.
  val presult = mask<local>{p()}
  if parse-stats-on() then
    trace("PARSE-STATS " ++ src.name ++ " tokens=" ++ n-tokens.show ++ " restore=" ++ n-restore.show ++ " rewound=" ++ n-rewound.show ++ " expect=" ++ n-expect.show)
  presult


pub fun peof()
  // if debug then
  //   trace("Parsing eof\n" ++ history.map(fn(x) "\tWhen parsing " ++ x.snd).join("\n") ++ "\n\nHad leftovers: " ++ lexemes.map(fn(x) x.show).join("\n"))
  match get-lexemes_()
    Cons(l, _) -> parse-error("peof expected end of file", l.range)
    Nil -> ()
pub fun parse-many(kind: string, l: () -> _ a): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> Cons(r, parse-many(kind, l))
    Nothing -> Nil

pub fun parse-many1(kind: string, l: () -> _ a): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> Cons(r, parse-many(kind, l))
    Nothing -> parse-error("at least 1 of " ++ kind, peek().range)

fun parse-many-end(kind: string, l: () -> _ a, p: () -> _ b): _ list<a>
  parse-many-endx(kind, l, p, True)

fun parse-many-endx(kind: string, l: () -> _ a, p: () -> _ b, isFirst: bool): _ list<a>
  val snap = pfar-snapshot()
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> 
      // parsec `sepBy1 p sep = p >>= many (sep >> p)`: `many` DISCARDS the
      // expectation records of a successful (consuming) iteration; only the
      // FIRST element's failed-alternative expectations merge into the final
      // error (compare `Cons(x -> ...` which lists "as"/":" vs
      // `Cons(x,xx -> ...` which lists only ","/")" upstream)
      if !isFirst then pfar-restore(snap)
      match parse-maybe-nb("sep " ++ kind, p)
        Just(_) -> Cons(r, parse-many-endx(kind, l, p, False))
        Nothing -> Cons(r, Nil)
    Nothing -> Nil

fun parse-many-end1(kind: string, l: () -> _ a, p: () -> _ b): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> 
      match parse-maybe-nb("sep " ++ kind, p)
        Just(_) -> Cons(r, parse-many-end(kind, l, p))
        Nothing -> Cons(r, [])
    Nothing -> parse-error("at least 1 of " ++ kind, peek().range)

pub inline fun parse-token(msg: string, f: (lexeme) -> _ maybe<a>): _ a
  match ptoken(f)
    Right(a) -> a
    Left(Just(t)) ->
      precord-expect(msg, Just(t.lex), t.range)
      parse-error("expecting " ++ msg, t.range)
    Left(Nothing) -> parse-error("unexpected end of file", null)

// Version of maybe that does backtrack
pub inline fun parse-maybe<e>(str: string, p: () -> _ a): _ maybe<a>
  val saved = get-lexemes_()
  val saved-pos = get-pos()
  with override
    return(r) Just(r)
    final ctl parse-error(e, r)
      set-pstate(saved, saved-pos)
      Nothing
  p()

pub fun parse-maybe-list(p: () -> _ list<a>): _ list<a>
  match parse-maybe("list", p)
    Just(r) -> r
    Nothing -> []

pub inline fun parse-try(p: () -> _ a, ?kk-file-line: string): _ a
  val saved = get-lexemes_()
  val saved-pos = get-pos()
  with override
    final ctl parse-error(e, r)
      set-pstate(saved, saved-pos)
      parse-error(e, r)
  p()
  

// Version of maybe that doesn't backtrack
pub inline fun parse-maybe-nb(str: string, p: () -> _ a): _ maybe<a>
  val saved-pos = get-pos()
  with override
    return(r) Just(r)
    final ctl parse-error(e, r)
      // consumed input => propagate (Parsec consumed-input semantics);
      // consumed nothing => the position is already where we started, so there
      // is nothing to restore
      if get-pos() != saved-pos then
        // context only under KOKA_PARSE_CONTEXT=1 (see parse-delimited)
        if perr-context && str != ""
          then parse-error("\nWhen parsing " ++ str ++ " " ++ e, r)
          else parse-error(e, r)
      else Nothing
  p()

// Parse parse-choices without backtracking. 
// Make sure that all parse-choices start differently or is the last choice.
pub fun parse-choices-nb(str: string, ps: list<() -> _ a>): _ a
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
pub fun parse-choices(str: string, ps: list<() -> _ a>): _ a
  fun find(ps': list<() -> _ a>): _ a
    match ps'
      Cons(p, rst) -> 
        match parse-maybe(str, p)
          Just(r) -> r
          Nothing -> find(rst)
      Nil -> parse-error("expected " ++ str, peek().range)
  find(ps)

pub val parse-sep-by = parse-many-end
pub val parse-sep-by1 = parse-many-end1

fun make-parse-error(r: range, e: string): _ a
  parse-error("invalid syntax" ++ e.list.drop-while(fn(x) x != ':').string, r)

fun bracketed(open: () -> _ range, close: () -> _ range, f: (a, range) -> _ b, p: () -> _ a): _ b
  val rng1 = open()
  val x = p()
  val rng2 = close()
  f(x, rng1.range/combine(rng2))

pub fun braced(p: () -> _ a): _ a
  // upstream is a plain <|> chain (Parse.hs:320-335): once the `{` alternative
  // consumes input, an inner error must PROPAGATE. Full backtracking here made
  // the whole module body a backtracking boundary -- any unrecovered parse
  // error re-ran the bare `p` alternative (succeeding on zero tokens) and got
  // masked as `peof expected end of file`.
  parse-choices-nb("braced", [{
      parse-left-curly() // TODO: Make sure right is same as left? (inserted versus actual)
      parse-many("semicolons", parse-semicolon)
      val x = p()
      parse-many("semicolons", parse-semicolon)
      parse-right-curly()
      x
    }, p])

pub fun parse-semi-braces(kind: string, p: () -> _ a): _ list<a>
  parse-semi-braces-ranged(kind, p).fst

pub fun parse-semi-braces-ranged(kind: string, p: () -> _ a): _ (list<a>, range)
  val rng1 = parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val xs = parse-many-end(kind, p, parse-semi1)
  val rng2 = parse-right-curly()
  (xs, rng1.combine(rng2))

pub fun parse-semi-braces-ranged1(kind: string, p: () -> _ a): _ (list<a>, range)
  val rng1 = parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val xs = parse-many-end1(kind, p, parse-semi1)
  val rng2 = parse-right-curly()
  (xs, rng1.combine(rng2))

pub fun parse-semi-braced(kind: string, p: () -> _ a): _ a
  parse-left-curly()
  parse-many("semicolons", parse-semicolon)
  val x = p()
  parse-many("semicolons", parse-semicolon)
  parse-right-curly()
  x

pub fun semis(kind: string, p: () -> _ a): _ list<a>
  // SepEndBy is RECURSIVE
  // (each element heads its own sepEndBy1), so every element's failed
  // continuation expectations merge into the final error -- unlike sepBy's
  // many-based tail (see parse-many-endx)
  parse-sep-end-by(kind, p, parse-semi1)

fun parse-sep-end-by(kind: string, l: () -> _ a, p: () -> _ b): _ list<a>
  match parse-maybe-nb("many " ++ kind, l)
    Just(r) -> 
      match parse-maybe-nb("sep " ++ kind, p)
        Just(_) -> Cons(r, parse-sep-end-by(kind, l, p))
        Nothing -> Cons(r, Nil)
    Nothing -> Nil

pub fun semis1(kind: string): _ list<range>
  parse-many1("semicolons", parse-semicolon)

fun parse-semi1(): _ list<range>
  parse-many1("semicolons", parse-semicolon)

pub fun angles-ranged(p: () -> _ a): _ (a, range)
  bracketed(parse-left-angle, parse-right-angle, fn(x, r) (x,r), p)

pub fun angles(p: () -> _ a): _ a
  bracketed(parse-left-angle, parse-right-angle, fn(x, r) x, p)

pub fun parse-parens-commas(p: () -> _ a): _ list<a>
  parensx(parse-left-paren, fn(a, r) a)
    parse-sep-by("comma", p, parse-comma)

pub fun parens-ranged(p: () -> _ a): _ (a, range)
  parensx(parse-left-paren, fn(a, b) (a, b), p) 

pub fun parens(p: () -> _ a): _ a
  parensx(parse-left-paren, fn(a, b) a, p) 

pub fun parse-parens-commas-ranged(p: () -> _ a): _ (list<a>, range)
  parensx(parse-left-paren, fn(a, r) (a, r))
    parse-sep-by("comma", p, parse-comma)

fun parensx(l: () -> _ range, f: (a, range) -> _ b, p: () -> _ a): _ b
  bracketed(l, parse-right-paren, f, p)

fun parse-range(msg: string, f: (lexeme) -> _ bool): _ range
  parse-token(msg, fn(x) if f(x) then Just(x) else Nothing).range

pub inline fun parse-vertical-bar(): _ range
  parse-keyword("|")

pub inline fun parse-comma(): _ range
  parse-special(",")

pub inline fun parse-semicolon(): _ range
  parse-range("\";\"", is-semicolon)

pub fun parse-left-curly(): _ range
  parse-range("\"{\"", _.lex.is-lcurly)

pub fun parse-right-curly(): _ range
  parse-range("\"}\"", _.lex.is-rcurly)

pub fun parse-left-bracket(): _ range
  parse-range("\"[\"", _.lex.is-lbracket)

pub fun parse-right-bracket(): _ range
  parse-range("\"]\"", _.lex.is-rbracket)

pub fun parse-left-paren(): _ range
  parse-range("\"(\"", _.lex.is-lparen)

pub fun parse-right-paren(): _ range
  parse-range("\")\"", _.lex.is-rparen)

pub fun parse-left-angle(): _ range
  parse-range("<", _.lex.is-langle)

pub fun parse-right-angle(): _ range
  parse-range(">", _.lex.is-rangle)

pub fun parse-type-binder-id(): _ (name, range)
  parse-choices("tBinderId", [parse-type-ident])

// Returns `Nothing` if this is a conditional import with no matching target
// Plain <|> (a malformed `{...}` conditional-import
// block must error, not silently degrade into the "unsupported target"
// warning path -- audit #18)
pub fun parse-import-alias(): _ maybe<(name, name, range, range)>
  val (name1, rng1) = parse-module-path()
  parse-choices-nb("import alias", [
    {
      parse-keyword("=")
      val (name2, rng2) = parse-module-path()
      Just((name1, name2, rng1, rng2))
    },
    {
      val mbentry = firstof(parse-semi-braces("conditional imports", parse-import-conditional))
      match mbentry
        Nothing ->
          pwarning-message("unsupported target in conditional import " ++ name1.show, rng1)
          Nothing
        Just((name2, rng2)) -> Just((name1, name2, rng1, rng2))
    },
    { Just((name1, name1, rng1, rng1)) }
  ])

fun parse-import-conditional(): _ maybe<(name, range)>
  val matches = parse-target-guard()
  val namerng = parse-module-path()
  if matches then Just(namerng) else Nothing

pub fun firstof(mbs: list<maybe<a>>): maybe<a>
  match mbs.drop-while(is-nothing)
    Cons(x, _) -> x
    Nil -> Nothing

pub fun pwarning-message(msg: string, rng: range): _ ()
  add-warning("warning " ++ rng.start.show ++ ": " ++ msg, rng)

// Parse a target guard like `c` or `js [os=windows,arch="x64"|"arm64"]` and
// return whether it matches the current target platform.
pub fun parse-target-guard(): _ bool
  val backend = parse-external-backend()
  val attrs = parse-external-attrs()
  (backend ++ attrs).map(match-attrs).all(fn(b) b)

fun parse-external-backend(): _ list<(string, list<(string, range)>, range)>
  parse-choices("backend", [
    {val rng = parse-special-id("c"); [("backend", [("c", rng)], rng)]},
    {val rng = parse-special-id("js"); [("backend", [("js", rng)], rng)]},
    {val rng = parse-special-id("cs"); [("backend", [("cs", rng)], rng)]},
    {val rng = parse-special-id("default"); [("backend", [("default", rng)], rng)]},
    {[]}
  ])

fun parse-external-attrs(): _ list<(string, list<(string, range)>, range)>
  parse-choices("target attributes", [
    {
      parse-special("[")
      val attrs = parse-sep-by("target attribute", parse-external-attr, parse-comma)
      parse-special("]")
      attrs
    },
    {[]}
  ])

fun parse-external-attr(): _ (string, list<(string, range)>, range)
  val (attr, rng) = parse-strid()
  parse-keyword("=")
  val vals = parse-sep-by1("attribute value", parse-strid, parse-vertical-bar)
  (attr, vals, rng)

fun parse-strid(): _ (string, range)
  parse-choices("identifier or string", [
    {val (id, rng) = parse-var-id(); (id.show, rng)},
    {parse-string-literal()}
  ])

fun match-attrs((attr, vals, rng): (string, list<(string, range)>, range)): _ bool
  vals.map(fn(v) match-attr(attr, v, rng)).any(fn(b) b)  // vals is OR of potential matches

fun match-attr(attr: string, (v, valrng): (string, range), rng: range): _ bool
  val tpl = ptarget-platform
  match attr
    "os" -> match-os(v, tpl.tpl-os)
    "arch" -> match-arch(v, tpl.tpl-arch)
    "host" ->
      match target-from-host(v)
        Just(tgt) -> match-target(tgt, tpl.tpl-target)
        Nothing ->
          pwarning-message("unknown host: " ++ v.show, valrng)
          False
    "backend" ->
      match target-from-backend(v)
        Just(tgt) -> match-target(tgt, tpl.tpl-target)
        Nothing ->
          pwarning-message("unknown backend: " ++ v.show, valrng)
          False
    "target" ->
      match target-platform-from-string(v)
        Just(tpl') -> match-target-platform(tpl', tpl)
        Nothing ->
          pwarning-message("unknown target: " ++ v.show, valrng)
          False
    "platform" ->
      match platform-from-string(v)
        Just(pl) -> match-platform(pl, tpl.tpl-platform)
        Nothing ->
          pwarning-message("unknown platform: " ++ v.show, valrng)
          False
    "buildcfg" -> match-build-defs(v.split(",").map(trim), tpl.tpl-build-defs)
    _ ->
      pwarning-message("unknown attribute for target: " ++ attr.show, rng)
      True

pub fun parse-param-id(): _ (name, range)
  parse-choices("param id", [parse-identifier, parse-wildcard])

pub fun parse-param-info(): _ param-info
  parse-choices("param info", [{
    parse-special-op("^")
    Borrow
  }, {Own}])

pub fun parse-identifier(): _ (name, range)
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

pub fun parse-tail-fip(): _ (fipT, range)
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

pub fun parse-inline(): _ def-inline
  parse-choices("inline", [{
      parse-special-id("inline")
      InlineAlways
    }, {
      parse-special-id("noinline")
      InlineNever
    }, 
    { InlineAuto }
  ])

pub fun parse-idcon(): _ user-expr
  val (name, rng) = parse-choices("", [parse-qualified-identifier, parse-qualified-constructor])
  Var(name, False, rng)

pub inline fun parse-qualified-identifier(): _ (name, range)
  parse-choices("qidentifier", [parse-qualified-var-id, parse-qualified-op-id])

pub inline fun parse-qualified-constructor(): _ (name, range)
  parse-qualified-constructor-id()

pub inline fun parse-qualified-operator(): _ (name, range)
  parse-qualified-op()

pub fun parse-fun-id(): _ (name, range)
  parse-locally-qualified-identifier() // [] doesn't work with local qualification

pub fun parse-locally-qualified-identifier(): _ (name, range)
  val (name, rng) = parse-qualified-identifier()
  (name.requalify-locally, rng)

pub fun parse-var-id(): _ (name, range)
  ensure-unqualified("variable id", parse-qualified-var-id)

pub fun parse-op-id(): _ (name, range)
  ensure-unqualified("operator", parse-qualified-op-id)

fun parse-constructor-id(): _ (name, range)
  ensure-unqualified("constructor", parse-qualified-constructor-id)
    // { val (s, rng) = parse-string-literal(); (new-name(s), rng)}

fun parse-op(): _ (name, range)
  ensure-unqualified("operator", parse-qualified-op)

pub fun parse-type-ident(): _ (name, range)
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

pub fun parse-qualified-type-id(): _ (name, range)
  with parse-try()
  val (name, range) = parse-choices("qTypeId", [parse-qualified-var-id, parse-type-id-context])
  if !name.is-type-var then 
    (name, range)
  else // TODO: This isn't quite the right hack.
    precord-expect("type name (and not type variable)", Nothing, range)
    parse-error("type name (and not type variable)", range)

pub fun parse-type-id-context(): _ (name, range)
  ("ctx".new-name, parse-keyword("ctx"))

fun parse-qualified-op(): _ (name, range)
  parse-token("operator") fn(a)
    match a
      Lexeme(rng, LexOp(id)) -> Just((id, rng))
      _ -> Nothing

pub fun parse-prefix-op(): _ expr<a>
  parse-token("prefix operator") fn(a)
    match a
      Lexeme(rng, LexPrefix(id)) -> Just(Var(id, True, rng))
      _ -> Nothing

// is really qvarid, varid, from the spec
pub fun parse-qualified-var-id(): _ (name, range)
  parse-token("variable id") fn(a)
    match a
      Lexeme(rng, LexId(id)) -> Just((id, rng))
      _ -> Nothing

// is really qidop and idop from the spec
pub fun parse-qualified-op-id(): _ (name, range)
  parse-token("operator id") fn(a)
    match a
      Lexeme(rng, LexIdOp(id)) -> Just((id, rng))
      _ -> Nothing

// is really qconid and conid in the spec
pub fun parse-qualified-constructor-id(): _ (name, range)
  parse-token("constructor id") fn(a)
    match a
      Lexeme(rng, LexCons(id)) -> Just((id, rng))
      _ -> Nothing

pub fun parse-module-path(): _ (name, range)
  parse-token("module path") fn(x)
    match x 
      Lexeme(rng, LexId(id)) -> Just((id.name-as-module-name, rng)) // return the entire module path as one identifier
      _ -> Nothing

pub fun parse-wildcard(): _ (name, range)
  parse-token("wildcard") fn(a)
    match a
      Lexeme(rng, LexWildCard(id)) -> 
        if id.show-plain == "_" then 
          Just((unique-range-name(rng, "_w"), rng))
        else Just((id, rng))
      _ -> Nothing

pub fun parse-integer(): _ (int, lexeme)
  parse-token("integer") fn(l)
    match l
      Lexeme(_, LexInt(i)) -> Just((i, l))
      _ -> Nothing

pub fun parse-float(): _ (float64, lexeme)
  parse-token("float") fn(l)
    match l
      Lexeme(_, LexFloat(d)) -> Just((d, l))
      _ -> Nothing

pub fun parse-char-literal(): _ (char, range)
  parse-token("char literal") fn(x) 
    match x
      Lexeme(rng, LexChar(c)) -> Just((c, rng))
      _ -> Nothing

pub fun parse-string-literal(): _ (string, range)
  parse-token("string literal") fn(x) 
    match x
      Lexeme(rng, LexString(s)) -> Just((s, rng))
      _ -> Nothing

pub fun parse-special-op(s: string): _ range
  parse-token(s) fn(x)
    match x.lex
      LexOp(s') | s == s'.show-plain -> Just(x.range)
      _ -> Nothing

pub fun default/parse-special-id(s: string): _ range
  parse-token(s) fn(x)
    match x.lex
      LexId(id) | id.show-plain == s -> Just(x.range)
      _ -> Nothing

// The matcher must stay TOTAL so it can go through `ptoken` (one handler
// round-trip instead of two): it reports a deprecated spelling by returning a
// flag, and the warning -- an effect -- is raised out here.
pub fun parse-special-id(s: string, alternates: list<string>): _ range
  val (r, deprecated) = parse-token(s) fn(x)
    match x.lex
      LexId(id) | id.show-plain == s -> Just((x.range, ""))
      LexId(id) | alternates.any(_ == id.show-plain) -> Just((x.range, id.show-plain))
      _ -> Nothing
  if deprecated != "" then
    add-warning("using deprecated keyword " ++ deprecated ++ ", use " ++ s ++ " instead", r)
  r

pub fun parse-special-con-id(s: string): _ range
  parse-token(s) fn(x)
    match x.lex
      LexCons(s') | s == s'.show-plain -> Just(x.range)
      _ -> Nothing

pub inline fun default/parse-special(s: string): _ range
  parse-special(s, [])

pub fun parse-special(s: string, alternates: list<string>): _ range
  val (r, deprecated) = parse-token("\"" ++ s ++ "\"") fn(x)
    match x.lex
      LexSpecial(s') | s == s' -> Just((x.range, ""))
      LexSpecial(s') | alternates.any(_ == s') -> Just((x.range, s'))
      _ -> Nothing
  if deprecated != "" then
    add-warning("using deprecated keyword " ++ deprecated ++ ", use " ++ s ++ " instead", r)
  r

pub inline fun default/parse-keyword(s: string): _ range
  parse-keyword_(s, []).range

pub inline fun range/parse-keyword(s: string, alts: list<string>): _ range
  parse-keyword_(s, alts).range

fun parse-keyword_(s: string, alternates: list<string>): _ lexeme
  val (x, deprecated) = parse-token("\"" ++ s ++ "\"") fn(x)
    match x.lex
      LexKeyword(s', _) | s == s' -> Just((x, ""))
      LexKeyword(s', _) | alternates.any(_ == s') -> Just((x, s'))
      _ -> Nothing
  if deprecated != "" then
    add-warning("using deprecated keyword " ++ deprecated ++ ", use " ++ s ++ " instead", x.range)
  x

pub fun default/parse-doc-keyword(s: string): _ (range, string)
  parse-doc-keyword(s, [])

pub fun parse-doc-keyword(s: string, alternates: list<string>): _ (range, string)
  match parse-keyword_(s, alternates)
    Lexeme(rng, LexKeyword(_, doc)) -> (rng, doc)
    _ -> parse-error("expected " ++ s, null)

pub fun parse-doccon-id(): _ (name, (range, string))
  parse-token("constructor") fn(x)
    match x.lex
      LexCons(id, doc) -> Just((id.requalify-locally, (x.range, doc)))
      _ -> Nothing 

pub fun unique-range-hidden-name(pre: string, rng: range): name
  val pos = rng.start
  new-hidden-name-ex(pre, pos.line.show ++ "_" ++ pos.col.show)

fun unique-range-name(rng: range, pre: string): name
  val pos = rng.start
  new-name(pre ++ "-l" ++ pos.line.show ++ "-c" ++ pos.col.show)

pub fun expr/adjust-range(ue: user-expr, r: range): user-expr
  Parens(ue, nil, "", r)

pub fun tp/adjust-range(ut: user-type, r: range): user-type
  TpParens(ut, r)

fun unimplemented(): _ a
  parse-error("unimplemented", peek().range)

fun main()
  "Compiles".println