import compiler/syntax/parse
import compiler/syntax/syntax
import compiler/syntax/pretty
import compiler/lib/pprint
import std/os/path
import std/os/dir

fun main()
  "/Users/timwhiting/koka/lib/std/".path.list-directory-recursive.foreach fn(f)
    if f.is-file && f.string.ends-with(".kk").bool then
      println("Parsing... " ++ f.show)
      with catch fn(err) err.show.trace 
      parse-program-from-file(f, True, True)
      println("Parsed " ++ f.show)

fun test-x1()
  val f = "/Users/timwhiting/koka/lib/std/num/random.kk".path
  parse-program-from-file(f, True, True).pretty.show.println

fun test-x2()
  val f = "../compiler/test/tests/parse/indentation.kk".path
  parse-program-from-file(f, True, True).pretty.show.println

fun test-units()
  "../compiler/test/tests/parse/".path.list-directory.foreach fn(f)
    parse-program-from-file(f, True, True).pretty.show.println

fun test-in-memory()
  r#"
fun ptime(date : date, cal : calendar) : <parse,utc> time
  one-of("T ")
  val hour = num(2)
  colon()
  val min = optional(0){num(2)}
  colon()
  val secs = optional(ddouble/zero) { val s = num(2) 
                                      val f = optional(""){ one-of(".,"); digits() }
                                      (s.ddouble + (if f.is-empty then zero else ("0." ++ f).parse-ddouble.default(zero))) } 
  val tzone = choose([
                { val sign = one-of("+-")
                  val tzhour = num(2)
                  colon()
                  val tzmin = num(2)
                  tz-fixed( if sign=='-' then tzhour.negate else tzhour, tzmin )
                }, 
                { optional('Z'){ char('Z') }; tz-utc }
              ])
  val clk = Clock(hour,min,secs)
  time(date,clk,tz=tzone,cal=cal)
  "#.parse-program-from-string("empty".path, True).pretty.show.println