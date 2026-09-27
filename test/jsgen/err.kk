import std/os/env
import std/os/file
import std/os/path

fun main()
  val args = get-args()
  val file-path = match args
    Cons(file-path, Nil) -> file-path
    _ -> throw("Usage: program <file path>", ExnError)
  val file-contents = read-text-file(file-path.path)
  ()