// Ported as of 2026-01-18; approx upstream baseline commit b8074c2 of Lib/JSON.hs (backfilled 2026-07-23)
//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------

// JSON parsing.
//
// `std/data/json` supplies the `json` type and the encoders/decoders; what it
// has no parser for is TEXT -> `json`, which is what the LSP transport needs.
//
// The alex-generated parsers in `../parsing` are not usable for that:
// `parsers/alex/json-parse-eff` mis-parses object members (`{"a":1}` comes back
// as `{"a":":1}`) and fails outright on a nested object, and
// `parsers/alex/json-parse` trips an internal error in the REFERENCE compiler
// (`Core.Core.splitTForall: Expected forall`). So this is a plain
// recursive-descent parser instead -- small, and it removes an external
// dependency from the language-server path.
//
// `//` line comments are accepted (not JSON, but `test/lib/json-test.kk`
// expects them and clients occasionally emit them in config files).
module compiler/lib/json

pub import std/data/json
pub import compiler/lib/pprint
import std/num/float64

pub fun parse-json(s: string): <exn,div> json
  val (j, rest) = s.list.skip-ws.value
  match rest.skip-ws
    Nil -> j
    cs -> throw("parse-json: trailing input at " ++ cs.take(20).string.show)

alias cursor = list<char>

fun skip-ws(cs: cursor): div cursor
  match cs
    Cons(c, r) | c.is-white -> r.skip-ws
    // `//` line comment
    Cons('/', Cons('/', r)) -> r.drop-while(fn(c) c != '\n').skip-ws
    _ -> cs

fun value(cs: cursor): <exn,div> (json, cursor)
  match cs
    Cons('{', r) -> r.skip-ws.members([])
    Cons('[', r) -> r.skip-ws.elements([])
    Cons('"', r) ->
      val (str, r2) = r.chars([])
      (JSString(str), r2)
    Cons('t', Cons('r', Cons('u', Cons('e', r)))) -> (JSBool(True), r)
    Cons('f', Cons('a', Cons('l', Cons('s', Cons('e', r))))) -> (JSBool(False), r)
    Cons('n', Cons('u', Cons('l', Cons('l', r)))) -> (JSNull, r)
    _ -> cs.number
    
fun members(cs: cursor, acc: list<(string, json)>): <exn,div> (json, cursor)
  match cs
    Cons('}', r) -> (JSObj(acc.reverse), r)
    Cons('"', r) ->
      val (key, r2) = r.chars([])
      match r2.skip-ws
        Cons(':', r3) ->
          val (v, r4) = r3.skip-ws.value
          match r4.skip-ws
            Cons(',', r5) -> r5.skip-ws.members(Cons((key, v), acc))
            Cons('}', r5) -> (JSObj(Cons((key, v), acc).reverse), r5)
            other -> throw("parse-json: expecting ',' or '}' at " ++ other.take(20).string.show)
        other -> throw("parse-json: expecting ':' at " ++ other.take(20).string.show)
    other -> throw("parse-json: expecting a member name at " ++ other.take(20).string.show)

fun elements(cs: cursor, acc: list<json>): <exn,div> (json, cursor)
  match cs
    Cons(']', r) -> (JSList(acc.reverse), r)
    _ ->
      val (v, r2) = cs.value
      match r2.skip-ws
        Cons(',', r3) -> r3.skip-ws.elements(Cons(v, acc))
        Cons(']', r3) -> (JSList(Cons(v, acc).reverse), r3)
        other -> throw("parse-json: expecting ',' or ']' at " ++ other.take(20).string.show)

// the opening quote is already consumed
fun chars(cs: cursor, acc: list<char>): <exn,div> (string, cursor)
  match cs
    Nil -> throw("parse-json: unterminated string")
    Cons('"', r) -> (acc.reverse.string, r)
    Cons('\\', Cons(e, r)) ->
      match e
        'n' -> r.chars(Cons('\n', acc))
        't' -> r.chars(Cons('\t', acc))
        'r' -> r.chars(Cons('\r', acc))
        'b' -> r.chars(Cons('\x08', acc))
        'f' -> r.chars(Cons('\x0c', acc))
        'u' ->
          val hex = r.take(4)
          if hex.length < 4 then throw("parse-json: bad \\u escape")
          else match hex.string.parse-hex
            Just(code) -> r.drop(4).chars(Cons(code.char, acc))
            Nothing -> throw("parse-json: bad \\u escape: " ++ hex.string)
        _ -> r.chars(Cons(e, acc))     // \" \\ \/ and anything else: literal
    Cons(c, r) -> r.chars(Cons(c, acc))

fun number(cs: cursor): <exn,div> (json, cursor)
  val (tok, rest) = cs.span-number
  if tok.is-nil then throw("parse-json: unexpected input at " ++ cs.take(20).string.show)
  else
    val str = tok.string
    if tok.any(fn(c) c == '.' || c == 'e' || c == 'E')
      then match str.parse-float64
        Just(d) -> (JSNum(d), rest)
        Nothing -> throw("parse-json: bad number " ++ str.show)
      else match str.parse-int
        Just(i) -> (JSInt(i), rest)
        Nothing -> throw("parse-json: bad number " ++ str.show)

fun span-number(cs: cursor): div (list<char>, cursor)
  fun go(xs: cursor, acc: list<char>): div (list<char>, cursor)
    match xs
      Cons(c, r) | c.is-digit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' ->
        go(r, Cons(c, acc))
      _ -> (acc.reverse, xs)
  go(cs, [])

fun parse-hex(s: string): maybe<int>
  s.list.foldl(Just(0)) fn(acc, c)
    match acc
      Nothing -> Nothing
      Just(n) ->
        val cv = c.char/int
        val d = if c.is-digit then Just(cv - '0'.char/int)
                elif c >= 'a' && c <= 'f' then Just(cv - 'a'.char/int + 10)
                elif c >= 'A' && c <= 'F' then Just(cv - 'A'.char/int + 10)
                else Nothing
        match d
          Just(v) -> Just(n * 16 + v)
          Nothing -> Nothing
