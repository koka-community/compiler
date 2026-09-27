import std/test/detect
import std/os/path
import std/os/env
import std/os/process
import std/core-extras

pub fun main()
  val test-path = generate-test-runner()

  // run the generated tests, passing through any arguments
  val args = get-args().map fn(arg)
    // basic escaping effort, TODO a version of run-system that accepts a list of args
    "'" ++ arg ++ "'"
  .join(" ")
  // Which koka to use: `KOKA=/path/to/koka ./koka -e run-tests.kk`.
  // Defaults to whatever is on PATH, which on this machine is an older
  // system install whose std lacks modules this repo needs -- so the fork's
  // koka must be selected explicitly.
  val koka-exe = get-env-value("KOKA").default("koka")
  // Include the generated runner's own directory so koka can resolve it
  // regardless of where generate-test-runner put it.
  val cmd = koka-exe ++ " -e -i../std -i../parsing -i" ++ test-path.dirname
              ++ " " ++ test-path.string ++ " -- " ++ args

  println(" + " ++ cmd)
  val status = run-system(cmd)
  exit(status)
