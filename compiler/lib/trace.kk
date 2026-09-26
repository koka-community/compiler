//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/24/26: Commit 32ada87

module compiler/lib/trace

import std/core/unsafe
pub import std/pretty/printer

fun color/trace(s: string, a: a, ?kk-file-line: string): a
  ctrace(DarkGray, s, a)

fun unit/trace(s: string, ?kk-file-line: string): ()
  trace(s, ())

fun trace-id(s: string, ?kk-file-line: string): string
  trace(s, s)
  
fun unit/trace-show(a: a, ?show: a -> e string, ?kk-file-line: string): e ()
  color/trace(a.show, ())

fun id/trace-show(a: a, ?show: a -> e string, ?kk-file-line: string): e a
  color/trace(a.show, a)

fun trace-eq(s: string, a: a, ?show: (a) -> string, ?kk-file-line: string): a
  trace(s ++ " = " ++ a.show, a)

fun ctrace(c: color, message: string, a: a, ?kk-file-line: string): a
  // trace to stderr without color: the language server must not print to stdout
  // since stdout is used for the jsonrpc protocol (the color argument is kept for API compatibility)
  std/core/debug/trace(?kk-file-line ++ ": " ++ message)
  a