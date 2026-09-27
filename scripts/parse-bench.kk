// Parse benchmark harness: times lex+layout+parse (parse-core) over every
// .kki interface file in a directory (default: the std interface cache).
//
// Usage (with the reference compiler wrapper):
//   ./koka -e --include=. scripts/parse-bench.kk [-- <kki-dir>]
//
// Prints a per-file table (name, lexeme-equivalent size in bytes, wall ms,
// parsed decl counts as a result fingerprint) and the total parse time.
// The decl-count fingerprint (imports/typedefs/defs/externals) must be
// identical before and after any parser optimization.
import std/os/path
import std/os/dir
import std/os/env
import std/os/file
import std/time/timer
import std/time/duration
import std/num/float64
import std/data/sort
import compiler/common/range
import compiler/common/parse
import compiler/core/parse
import compiler/core/core
import compiler/syntax/lexer
import compiler/syntax/layout

// Lex (and lay out) ONLY -- no parsing. Splitting the two says which half of
// the ~5us per token is the scanner and which is the combinators.
fun lex-only(f: path): _ int
  val input = read-text-file(f)
  val src = Source(f.string, input)
  lexing(src, 1, input).layout(True, False).length

fun try-parse-core(f: path): _ maybe<core>
  with final ctl parse-error(e: string, r: range)
    println("PARSE ERROR " ++ f.string ++ ": " ++ e)
    Nothing
  val (c, _mkInlines) = parse-core(f)
  Just(c)

fun fingerprint(c: core): string
  "imp=" ++ c.imports.length.show ++
  " tdefs=" ++ c.typedefs.length.show ++
  " defs=" ++ c.defs.length.show ++
  " extern=" ++ c.externals.length.show

fun pad(s: string, n: int): string
  s ++ "                                                            ".first(max(0, n - s.count)).string

fun main()
  val args = get-args()
  val dir = match args
    Cons(d, _) -> d.path
    // pass a build output directory, e.g. .koka/v3.2.7/clang-release-<hash>
    Nil -> ".koka/v3.2.7/clang-release".path
  val files = list-directory(dir)
                .filter(fn(p) p.string.ends-with(".kki").bool)
                .map(fn(p) p.string).sort.map(fn(s) s.path)
  var total-ms := 0.0
  var lex-ms := 0.0
  var nlexemes := 0
  var nfiles := 0
  var nfail := 0
  files.foreach fn(f)
    val sz = read-text-file(f).count
    val (dl, nlex) = elapsed { lex-only(f) }
    val (d, res) = elapsed { try-parse-core(f) }
    lex-ms := lex-ms + dl.nano-seconds.float64 / 1.0e6
    nlexemes := nlexemes + nlex
    val ms = d.nano-seconds.float64 / 1.0e6
    total-ms := total-ms + ms
    nfiles := nfiles + 1
    match res
      Just(c) ->
        println(pad(f.nodir.string, 40) ++ pad(sz.show ++ "b", 10) ++ pad(ms.show-fixed(2) ++ "ms", 12) ++ fingerprint(c))
      Nothing ->
        nfail := nfail + 1
        println(pad(f.nodir.string, 40) ++ pad(sz.show ++ "b", 10) ++ pad(ms.show-fixed(2) ++ "ms", 12) ++ "FAILED")
  println("")
  println("files: " ++ nfiles.show ++ " (failed: " ++ nfail.show ++ ")")
  println("TOTAL lex+parse : " ++ total-ms.show-fixed(1) ++ " ms")
  println("  of which LEX  : " ++ lex-ms.show-fixed(1) ++ " ms  ("
          ++ (100.0 * lex-ms / total-ms).show-fixed(0) ++ "% -- lexing is also counted inside the parse figure)")
  println("  lexemes       : " ++ nlexemes.show)
  println("  ns per lexeme : lex " ++ (lex-ms * 1.0e6 / nlexemes.float64).show-fixed(0)
          ++ "   lex+parse " ++ (total-ms * 1.0e6 / nlexemes.float64).show-fixed(0))
