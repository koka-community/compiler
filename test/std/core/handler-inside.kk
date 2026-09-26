// Helper for cgen/open-none-core.kk: a std/core function whose type is total
// but which installs a handler. Its type says nothing about that, so a call to
// it from an effectful context still needs `open-none`.
module std/core/handler-inside

import std/core/types
import std/core/hnd

// `aa` sorts before `zz`, so a caller's `aa` handler lands in front of `zz`
// in the evidence vector when the call is not opened.
pub effect aa
  fun aa() : int

pub effect zz
  fun zz() : int

pub noinline fun zz-inside() : int
  with handler
    fun zz() 42
  zz()
