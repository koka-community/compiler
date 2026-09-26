// Parser stress probe: measures growth of parse time on synthetic inputs to
// expose super-linear (O(n^2)) behavior in the backtracking/token-history
// machinery of compiler/common/parse.kk.
//
// Usage: ./koka -e --include=. scripts/parse-stress.kk
//
// Two shapes:
//  - deep: nested parenthesized expression ((((...1...)))) -- every nesting
//    level is a delimit/undelimit frame, so with list-based history each
//    close copies the consumed-lexeme list of the inner frame: O(n^2).
//  - wide: n sequential small function declarations -- linear check.
import std/os/path
import std/os/env
import std/time/timer
import std/time/duration
import std/num/float64
import compiler/syntax/parse
import compiler/syntax/syntax

fun repeat-str(s: string, n: int): div string
  if n <= 0 then "" else s ++ repeat-str(s, n - 1)

fun deep-input(n: int): div string
  "fun main()\n  val x =\n    " ++ repeat-str("(", n) ++ "1" ++ repeat-str(")", n) ++ "\n  x\n"

fun wide-input(n: int): string
  "fun main()\n  1\n" ++
    list(1, n).map(fn(i) "fun f" ++ i.show ++ "()\n  val x = (1 + 2) * 3\n  x\n").join("")

fun bench(label: string, input: string): _ ()
  val (d, r0) = elapsed
    try
      parse-program-from-string(input, "stress.kk".path, False)
      "ok"
  val r = match r0
    Error(_) -> "error"
    Ok(s) -> s
  println(label ++ ": " ++ (d.nano-seconds.float64 / 1.0e6).show-fixed(1) ++ " ms (" ++ r ++ ", " ++ input.count.show ++ " bytes)")

fun main()
  val sizes = match get-args().filter-map(fn(a) a.parse-int)
    Nil -> [250, 500, 1000, 2000, 4000]
    ns -> ns
  println("deep nesting (delimit-frame depth):")
  sizes.foreach fn(n)
    bench("  deep n=" ++ n.show, deep-input(n))
  println("wide (sequential decls):")
  sizes.foreach fn(n)
    bench("  wide n=" ++ n.show, wide-input(n))
