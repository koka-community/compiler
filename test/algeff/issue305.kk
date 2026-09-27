import std/text/parse
import std/core/undiv

fun test(): parse char
  fun test2(): parse char
    char('r')
  pretend-no-div(test2)

pub fun main()
  val code = "hi"
  val mb = parse(code.slice, test)
  println("success")
