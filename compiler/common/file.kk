//-----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/23/24, though parts are incomplete (Commit: 336bf9b)

module compiler/common/file

import std/os/path
import std/os/file
import compiler/platform/config
import std/os/env
import std/core/unsafe
import std/os/process

fun is-literal-doc(fname: path)
  fname.string.ends-with(source-ext ++ ".md").bool ||
  fname.string.ends-with(source-ext ++ ".mdk").bool

// -------------------------
// File names
// -------------------------
pub alias fileName = path

// Remove the extension and directory part
fun basename(p: fileName): fileName
  p.nodir.noext

// extname - Get the file extension (already part of std/os/path)

fun ensure-ext(p: fileName, ext: string): fileName
  p.change-ext(ext)

// dirname - Return the directory prefix (including last separator if present) (already part of std/os/path)

// notdir -- Remove the directory prefix (already part of std/os/path as nodir)

// notext -- Remove the extension (already part of std/os/path as noext)

// undelim-paths - Split a string of paths into a list of file names (already part of std/os/path as paths)

// split-path - Split a path into its directory parts (already part of std/os/path as dirparts)

fun on-windows(): bool
  with unsafe-total
  get-os-name() == "windows"

// join-path / join-paths - Join a list of file names into a single path (already part of std/os/path as (/))

// normalize - Normalize path separators (.path on string already does this)

// normalize-with 
pub fun normalize-with(p: fileName, sep: char): string
  p.dirparts.join(sep.string)

// is-path-sep - Is this a file separator? - regardless of host OS 
pub fun is-path-sep(c: char): bool
  c == '/' || c == '\\'

// is-path-delimiter - Is this a path delimiter? - regardless of host OS
fun is-path-delimiter(c: char): bool
  c == ':' || c == ';'

// run-system-raw 
fun run-system-raw(cmd: string): _ ()
  val res = process/run-system(cmd)
  if res == 0 then ()
  else
    throw("Command failed: " ++ cmd)

fun run-system(cmd: string): _ ()
  val res = run-system-ex(cmd)
  if res == 0 then ()
  else
    throw("Command failed: " ++ cmd)

fun run-system-ex(cmd: string): _ int
  cmd.path.normalize-with(pathsep().head-char.default('/')).process/run-system

fun run-cmd(cmd: string, args: list<string>): _ ()
  val res = process/run-system(cmd ++ " " ++ args.join(" "))
  if res == 0 then ()
  else
    throw("Command failed: (exit code " ++ res.show ++ ")")

// TODO: Need stderr in the output, and setting the child processes environment - not supported by the koka std libraries yet
fun run-cmd-read(env: env, cmd: string, args: list<string>): _ string
  val res = process/run-system-read(cmd ++ " " ++ args.join(" "))
  match res
    Ok(s) -> s 
    Error(s) -> throw("Command failed: (exit code " ++ s.show ++ ")")

// TODO: Need setting the child processes environment - not supported by the koka std libraries yet
fun run-cmd-env(env: env, cmd: string, args: list<string>): _ ()
  val res = process/run-system(cmd ++ " " ++ args.join(" "))
  if res == 0 then ()
  else
    throw("Command failed: (exit code " ++ res.show ++ ")")

fun build-env(env: env): _ maybe<env>
  if env.is-empty then return Nothing
  val old = get-env()
  Just(env ++ old.filter(fn((k,_)) env.lookup(_ == k).is-nothing))

// File modification time, in epoch seconds.
//
// A direct `stat(2)`. This used to shell out (`sh -c 'stat -f %m ... || stat -c
// %Y ...'`), which cost a fork+exec per query -- MEASURED AT 8ms EACH. That is
// paid per module AND per dependency by `stale-p`, so a warm build spent
// seconds doing nothing but asking the shell for timestamps. Cheap mtimes are
// also what makes it viable to check interface freshness before deciding
// whether a source needs scanning at all.
//
// A missing or unreadable file reports 0, which makes a missing artifact
// infinitely stale without needing a special case at the call sites.
extern import
  c file "file-inline.c"

extern file-mtime-prim( p : string ) : ndet int
  c "kk_compiler_file_mtime"

pub fun file-mtime( p : path ) : io int
  file-mtime-prim(p.string)

// Read at most `max-bytes` from the head of a file. For scanning a header out
// of a file whose tail is irrelevant -- an interface's import block is the
// first thing in it, and interfaces run to megabytes.
extern read-head-prim( p : string, max-bytes : int ) : ioc string
  c "kk_compiler_read_head"

pub fun read-head( p : path, max-bytes : int = 65536 ) : io string
  read-head-prim(p.string, max-bytes)

// Monotonic-ish CPU millisecond clock for coarse timing (KOKA_TIMING).
// Named `now-ms` to avoid clashing with driver.kk's private `cpu-ms`.
extern import
  c include-inline "#include <time.h>"

pub extern now-ms(): ndet int
  c inline "kk_integer_from_int((kk_intx_t)(clock()/(CLOCKS_PER_SEC/1000)), kk_context())"

// Wall-clock epoch NANOSECONDS -- the same unit and origin as `file-mtime`, so
// the two are directly comparable. An in-memory source (a language server's
// edited buffer) needs a timestamp on this scale or staleness comparisons
// against on-disk interfaces are meaningless.
pub extern epoch-nanos(): ndet int
  c "kk_compiler_epoch_nanos"

// Atomic text-file write: write to a unique temp file in the target
// directory, then rename over the destination. `rename(2)` within one
// filesystem is atomic, so concurrent koka processes sharing a build cache
// never observe a half-written interface or C file (8 sweep workers do exactly
// this).
//
// One `mkstemp`+`rename` syscall pair, not `mktemp` and `mv -f`. The shell
// version cost TWO fork+execs per file -- ~8ms each -- and this runs three
// times per compiled module (.kki, .c, .h), so it was six spawns per module
// sitting inside the codegen phase. It also built its command lines by
// pasting paths into single quotes, which a path containing a quote would
// have broken.
extern write-atomic-prim( p : string, content : string ) : ioc bool
  c "kk_compiler_write_atomic"

pub fun write-text-file-atomic( p : path, content : string ) : io ()
  // false on any failure; fall back to a direct (non-atomic) write, as the
  // shell version did when `mktemp` was unavailable
  if write-atomic-prim(p.string, content) then ()
  else write-text-file(p, content)

// TODO: Missing file time and exists functions - in koka std core - though the libuv branch would have it
// Compare to file modification times (uses 0 for non-existing files)
// fun file-time-compare(p1: fileName, p2: fileName): io order
// fun max-file-time
// fun max-file-times
// fun does-file-exist-and-not-empty

// read-text-file (already part of std/os/file)
// write-text-file (already part of std/os/file)

fun copy-text-file(src: path, dest: path): _ ()
  file/write-text-file(dest, file/read-text-file(src))

fun copy-text-file-with(src: path, dest: path, transform: (string) -> _ string): _ ()
  file/write-text-file(dest, transform(file/read-text-file(src)))

// binary modes are not supported in koka std lib yet - but are in libuv branch
// copy-binary-file
// copy-binary-if-newer

// Don't have file times / file exists except in libuv branch
// fun copy-text-if-newer
// fun copy-text-if-newer-with
// fun remove-file-if-exists

// get-program-path (already in std/os/path as app-path())

fun common-path-prefix(p1: path, p2: path): _ string
  p1.dirparts.zip(p2.dirparts).take-while(fn((a,b)) a == b).map(fst).join(pathsep())

fun default/relative-to-path(pprefix: path, p: path): ndet path
  match maybe/relative-to-path(pprefix, p)
    Just(r) -> r
    Nothing -> p

fun maybe/relative-to-path(pprefix: path, p: path): ndet maybe<path>
  if pprefix.string == "" then Just(p)
  else
    val prefs = pprefix.dirparts
    val ps = p.dirparts
    if prefs.is-prefix-of(ps) then
      Just(ps.drop(prefs.length).join(pathsep()).path)
    else
      Nothing

// is-absolute (already part of std/os/path)

// Find a maximal prefix path given a path and a list of root paths. Returns the root path and relative path.
fun find-maximal-prefix-path(p: path, roots: list<path>): ndet maybe<(path, path)>
  val rels = roots.map(fn(r) 
        match r.maybe/relative-to-path(p)
          Just(rel) -> [(r, rel)]
          Nothing -> []
      ).concat
  match rels
    [] -> Nothing
    xs -> xs.maximum-by(fn((r1, _), (r2, _)) r1.path/show.cmp(r2.path/show))

// Get the maximal relative path
fun get-maximal-prefix-path(p: path, roots: list<path>): ndet (path, path)
  match find-maximal-prefix-path(p, roots)
    Just(rel) -> rel
    Nothing -> ("".path,p)

//----------------------------------
// File searching
//----------------------------------
// TODO: Need file exists function
// fun search-paths
// fun search-paths-suffixes
// fun search-paths-canonical

// Make a file path relative to a set of given paths: return the (maximal) root and stem
// if it is not relative to the paths, return dirname/notdir 
fun make-relative-to-paths(p: path, roots: list<path>): ndet (path, path)
  match find-maximal-prefix-path(p, roots)
    Just(rel) -> rel
    Nothing -> (p.dirname.path, p.nodir)


// TODO: More
fun get-env-paths(n: string): _ list<path>
  get-env-value(n).default("").paths

// get-env-var (already part of std/os/env as get-env-value)

// real-path (already part of std/os/path as realpath I think - may not have same behavior)

// TODO: Need file exists function
// fun search-program
