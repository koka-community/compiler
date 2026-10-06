// Runs the unit tests: every `test/**/*-test.kk` that defines `pub fun suite()`.
//
//   ./koka -e run-tests.kk [-- <std/test options>]
//   KOKA=<a built driver> <a built driver> -e run-tests.kk
//
// A generated module imports every suite and runs them with `std/test/run`, so a
// new suite needs no registration. `KOKA` selects the compiler that builds the
// generated module (default `./koka`, the reference compiler wrapper); the exit
// code is nonzero when a test fails.
import std/os/path
import std/os/dir
import std/os/file
import std/os/env
import std/os/process

fun suites(): io list<path>
  "test".path.list-directory-recursive.filter fn(p)
    p.string.ends-with("-test.kk").bool && p.read-text-file.contains("pub fun suite()")

fun runner-source(files: list<path>): string
  val mods = files.map(fn(p) p.string.replace-all("\\", "/")).map(fn(s) s.ends-with(".kk").map(string).default(s))
  val imports = mods.map-indexed(fn(i, m) "import t" ++ i.show ++ " = " ++ m ++ "\n").join
  val calls = mods.map-indexed(fn(i, _) "    t" ++ i.show ++ "/suite()\n").join
  "import std/test\nimport std/test/run\n" ++ imports ++
    "\npub fun main()\n  run-tests\n" ++ calls

pub fun main()
  val files = suites()
  val runner = ".koka/unit-tests/run-all.kk".path
  write-text-file(runner, runner-source(files))
  val koka = get-env-value("KOKA").default("./koka")
  val args = get-args().map(fn(a) "'" ++ a ++ "'").join(" ")
  val cmd = koka ++ " -i. -e " ++ runner.string ++ " -- " ++ args
  println("running " ++ files.length.show ++ " suites: " ++ cmd)
  exit(run-system(cmd))
