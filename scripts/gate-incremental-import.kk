// Fixture for scripts/multimodule-gate.sh's incremental step: std/async/thread
// imports relatively (`async/async`) and host-conditionally (`async/api/thread`),
// and is recompiled when its backend changes while its own interface is newer
// than its source.
import std/async
import std/async/thread

fun main()
  println(native-threads())
