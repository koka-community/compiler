// multimodule-gate.sh: `lib`'s extern comes from `lib-inline.c`, and editing only
// that file must recompile `lib`.
import lib

pub fun main()
  println(k())
