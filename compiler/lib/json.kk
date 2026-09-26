//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------

// using alex lexing in community libraries, instead of direct translation
pub import parsers/alex/json-parse-eff
pub import std/data/json
pub import std/pretty/pprint

fun test()
  val s = r#"{"hello":"world" // a comment here
    }"#
  s.parse-json.pretty.show.println

// The direct translation from Koka's Haskell compiler is below
// import std/text/parse
// import std/data/linear-map
// import std/text/regex
// import std/num/float64

// type jsValue
//   JsNull
//   JsBool(b: bool)
//   JsInt(s: string, i:int)
//   JsDouble(s: string, d:float64)
//   JsString(s: string)
//   JsArray(l: list<jsValue>)
//   JsObject(o: jsObject<jsValue>)

// alias jsObject<a> = linear-map<string, a>
    
// fun toString(v: jsValue)
//   match v
//     JsString(s) -> s
//     _ -> v.show

// fun show(v: jsValue)
//   match v
//     JsNull -> "null"
//     JsBool(b) -> if b then "true" else "false"
//     JsInt(i) -> i.show
//     JsDouble(d) -> d.show
//     JsString(s) -> s.show
//     JsArray(l) -> "[" ++ l.map(show).join(", ") ++ "]"
//     JsObject(o) -> "{" ++ o.list.map(fn ((k, v1)) k ++ ": " ++ v1.show).join(",\n ") ++ "}"

// fun jsLookup(v: jsValue, keys: list<string>): jsValue
//   match keys
//     Nil -> v
//     Cons(k, ks) ->
//       match v
//         JsObject(o) -> 
//           match o.lookup(k)
//             Just(v1) -> jsLookup(v1, ks)
//             Nothing -> JsNull
//         JsArray(vs) -> 
//           match k.parse-int
//             Just(i) -> 
//               match vs[i] 
//                 Just(v1) -> jsLookup(v1, ks)
//                 Nothing -> JsNull
//             Nothing -> JsNull
//         _ -> JsNull

// fun jsFind(v: jsValue, def: jsValue, keys: list<string>): jsValue
//   match v.jsLookup(keys)
//     JsNull -> def
//     v1 -> v1

// val hexLeadRegex = r"0[xX]".regex();
// fun hexadecimal()
//   take-pattern(leadingRegex).string ++ take-pattern(hexLeadRegex).string ++ take-pattern(integerRegex).string

// val leadingHexDotRegex = r"^.[0-9a-fA-F_]+([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
// val wholeHexFloatRegex = r"^[0-9a-fA-F_]+(\.[0-9a-fA-F_]+)?([eEpP][+-]?[0-9a-fA-F_]+)?".regex() 
// val integerRegex = r"^[0-9a-fA-F_]+".regex() 
// fun integer()
//   take-pattern(leadingRegex).string ++ take-pattern(integerRegex).string

// val leadingRegex = r"[+-]".regex()
// fun exp()
//   take-pattern(leadingRegex).string ++ integer()
  
// fun decfloat()
//   take-pattern(leadingRegex).string ++ (fn() take-pattern(wholeHexFloatRegex).string).or({take-pattern(leadingHexDotRegex).string})

// fun hexfloat()
//   take-pattern(leadingRegex).string++ hexadecimal() ++ (fn() take-pattern(wholeHexFloatRegex).string).or({take-pattern(leadingHexDotRegex).string})

// fun pLit()
//   with scope("plit")
//   ors([{text("true"); JsBool(True)},{text("false"); JsBool(False)},{text("null"); JsNull}])

// fun parse-float()
//   with atomic
//   val d = or({decfloat().split("_").join}, {hexfloat().split("_").join})
//   JsDouble(d, d.parse-float64.unjust)

// fun parse-integer()
//   with atomic
//   val d = integer().split("_").join
//   JsInt(d, d.parse-int.unjust)

// val stringRegex = "^\"[^\\\\\"]*(?:\\\\.[^\"\\\\]*)*\"".regex()

// inline fun parse-str(): parse<string> sslice
//   take-pattern(stringRegex)

// fun parse-string()
//   with scope("parse-string")
//   val s = parse-str()
//   JsString(s.subslice(1, s.count - 1).string)

// fun parse-array()
//   with scope("parse-array")
//   parse-token("[")
//   val xs = parse-sep-trailing(pValue,{parse-token(",")})
//   optional(parse-whitespace)
//   parse-token("]")
//   JsArray(xs)

// fun pMember(): <pure,parse<string>> (string, jsValue)
//   with scope("pmember")
//   val k = parse-str()
//   optional(parse-whitespace)
//   parse-token(":")
//   val v = pValue()
//   (k.string, v)

// fun parse-object()
//   with scope("parse-object")
//   parse-token("{")
//   val members = parse-sep-trailing(pMember, {parse-token(",")})
//   optional(parse-whitespace)
//   val o = JsObject(LinearMap(members))
//   parse-token("}")
//   o

// fun pValue(): <pure,parse<string>> jsValue
//   with scope("pvalue")
//   val v = ors([parse-array,parse-object,pLit,pFloat,parse-integer,parse-string])
//   optional(parse-whitespace)
//   v

// val spacesRegex = r"^([ \n\t\r]|\/\/[^\n]+)+".regex()
// fun parse-whitespace()
//   spacesRegex.take-pattern()

// fun parse-token(s: string)
//   text(s)
//   optional(parse-whitespace)

// fun parse(s: string): <console,pure> ()
//   match run(s,pValue)
//     Right(e) -> e.show.println
//     Left(err) -> ("Error:\n" ++ err.show(s)).println
//   ()
  
// fun parse2(p: parser<string,a,pure>, s: string, ?show: (a) -> string): <console,pure> ()
//   s.println
//   val x = match run(s,p)
//     Right(e) -> e.show
//     Left(err) -> "Error:\n" ++ err.show(s)
//   x.println
  
// fun test()
//   parse(r#"{
//   "hello":"world", // Something here
// }"#
//   )
  