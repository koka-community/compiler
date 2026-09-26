import compiler/core/parse
import compiler/common/name
import compiler/common/range
import compiler/common/parse
import compiler/core/core
import std/os/path
import std/os/dir

fun main()
  val dir = "/Users/timwhiting/koka/.worktrees/dev-compiler/.koka/v3.2.7/js-debug-1761cf".path
  val files = list-directory(dir).filter(fn(p) p.string.ends-with(".kki").bool)
  var okc := 0
  var failc := 0
  files.foreach fn(f)
    with handler
      final ctl parse-error(e: string, r: range)
        failc := failc + 1
        println("FAIL " ++ f.basename ++ " at " ++ r.show ++ ": " ++ e.split("\n").head.default(""))
    val (c, _) = parse-core(f)
    okc := okc + 1
    println("OK   " ++ f.basename ++ " tdefs=" ++ c.typedefs.length.show ++ " defs=" ++ c.defs.length.show)
  println(okc.show ++ " ok, " ++ failc.show ++ " failed")
