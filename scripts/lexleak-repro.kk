// MINIMIZED REPRO: one leaked 32-byte block per IDENTIFIER lexed.
//
// Build with the standard allocator so `leaks` can see the heap, then run:
//   koka -O2 --fstdalloc -c --target=c -i<repo> scripts/lexleak-repro.kk
//   leaks --atExit -- <built-exe>
//
// Measured (50,000 lexer() calls each):
//   "a"          1 token , 1 id  ->        23 leaks   (EOF-only edge case: no leak)
//   "a "         2 tokens, 1 id  ->    50,024 leaks   = 1 per call
//   " a"         2 tokens, 1 id  ->    50,024 leaks   = 1 per call
//   "aa aa"      3 tokens, 2 ids ->   100,025 leaks   = 2 per call
//   "a b c"      5 tokens, 3 ids ->   150,026 leaks   = 3 per call
//   "     "      1 token , 0 ids ->         7 leaks   (whitespace never leaks)
//   "+"          1 token , 0 ids ->        23 leaks   (operators never leak)
// => leaks == identifier count, exactly. Every block is 32 bytes.
//
// Identifier actions are the only ones that call `get-qname()`:
//   alex_action_6 = fn() { emit(LexId(get-qname())) }
//   get-qname()   = get-string().read-qualified-name
// `get-string()` alone is CLEAN (whitespace/special actions use it and do not
// leak), so the leak is inside common/name.kk `read-qualified-name`, whose
// last step is:
//     val (q, lq, id) = s0.split-name     // tuple3 of strings == 32 bytes
//     new-locally-qualified(q, lq, id)
// The 32-byte block size matches that tuple3 exactly -- prime suspect is the
// destructured tuple not being freed.
import compiler/syntax/lexer

pub fun main()
  println("tokens=" ++ lexer("t.kk", 1, "a b c").length.show)
  var n := 0
  repeat(50000)
    n := n + lexer("t.kk", 1, "a b c").length
  println(n)
