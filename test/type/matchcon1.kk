// Issue: https://github.com/koka-lang/koka/issues/9

type bar
  bar/Foo

type foo
  foo/Foo

type bar2<a>
  bar2/Foo2(a: a)

type foo2<a>
  foo2/Foo2(a: a)

fun foo/to-int(x : foo): int
  match x
    Foo -> 1

fun foo2/to-int(x: foo2<int>): int
  match x
    Foo2(y) -> y

fun main()
  foo/Foo.to-int.println
  foo2/Foo2(0).to-int.println
