// ---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
// 
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
// ---------------------------------------------------------------------------
// Updated as of 7/23/24: Commit 48b9d26

module compiler/common/failure
pub import compiler/platform/config

// ------------------------------------------
// Internal errors and assertions
// ------------------------------------------

pub fun fail(s: string): exn a
  raise(s)

pub fun assert(msg: string, test: bool, x: a): exn a
  if test then x else fail(msg)

pub fun todo(msg: string): exn a
  fail("todo: " ++ msg)

pub fun match-failure(msg: string, ?kk-file-line: string): exn a
  fail("unmatched pattern: " ++ msg ++ " at " ++ kk-file-line)

pub fun raise(s: string): exn a
  // Figure out stack traces
  throw(s)

pub fun catch(hndl: string -> e a, f: () -> <exn|e> a): e a
  fun adjust(s: string): string
    s // TODO: Adjust any errors if needed
  with handler final ctl throw-exn(e)
    hndl(e.message.adjust)
  f()