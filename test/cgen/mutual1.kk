//  mutual recursive functions (issue #596)

fun foo()
  bar()

fun bar()
  foo()

fun main()
  ()