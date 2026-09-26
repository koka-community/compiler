// Fixture for the language-server integration test: small enough that a check
// is fast, but it does import the standard library, which is what a broken
// share-dir resolution breaks first.
module hello

pub fun greet(name: string): string
  "hello " ++ name

pub fun main()
  println(greet("world"))
