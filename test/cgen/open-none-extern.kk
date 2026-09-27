// An external that calls a function it is passed runs Koka code, so calling it
// from an effectful context needs `open-none` even though its type is total:
// without it, `zz-inside` runs under the caller's `aa` evidence, and `zz()`
// finds that at `zz`'s static index and returns 1. (`aa` sorts before `zz`.)
effect aa
  fun aa() : int

effect zz
  fun zz() : int

inline extern apply-total( f : () -> int ) : int
  c inline "kk_function_call(kk_integer_t,(kk_function_t,kk_context_t*),#1,(#1,kk_context()),kk_context())"
  js inline "(#1)()"

noinline fun zz-inside() : int
  with handler
    fun zz() 42
  zz()

fun main()
  with handler
    fun aa() 1
  println(apply-total(fn() zz-inside()))
