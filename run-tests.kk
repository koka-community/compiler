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
  val cmd = "koka -e -i../std -i../parsing " ++ test-path.string ++ " -- " ++ args

  println(" + " ++ cmd)
  val status = run-system(cmd)
  exit(status)
