import std/os/file
import std/os/path
import std/os/dir
import compiler/common/range
import compiler/syntax/lexer
import compiler/syntax/lexeme

fun main()
  val files =  [
    "../compiler/compiler/syntax/lex",
    "../compiler/compiler/syntax/lexer",
    "../compiler/compiler/syntax/lexeme"
  ]
  
  files.foreach fn(f)
    with handler
      final ctl throw-exn(e)
        e.trace-show
    val s = read-text-file((f ++ ".kk").path)
    val source = Source(f ++ ".kk", s)
    lexing(source, 1, s).trace-show
    ()

fun test()
  "/Users/timwhiting/koka/lib/std/".path.list-directory-recursive.foreach fn(f)
    if f.is-file && f.string.ends-with(".kk").bool then
      val s = read-text-file(f)
      lexing(Source(f.string, s), 1, s)
      println("Lexed ... " ++ f.show)
  println("Done")


fun test-unicode()
  ["/Users/timwhiting/koka/lib/std/time/locale.kk".path].foreach fn(f)
    if f.is-file && f.string.ends-with(".kk").bool then
      val s = read-text-file(f)
      // s.println
      val res = lexing(Source(f.string, s), 1, s)
      println("Lexed ... " ++ f.show ++ "\n" ++ res.show(?show = fn(l) l.lex.show))
  println("Done")

fun test-raw()
  val p = "../compiler/test/tests/lex/raw.kk".path
  val s = read-text-file(p)
  println(lexing(Source(p.string, s), 1, s).map(show).join("\n"))