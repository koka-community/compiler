import compiler/compile/phase
import compiler/common/name
import std/os/path
import std/test

pub fun suite()
  test("is-stale: source newer than output")
    expect(True)
      is-stale(200, 100, [])

  test("is-stale: output newer than source, no deps")
    expect(False)
      is-stale(100, 200, [])

  test("is-stale: a dependency is newer than our output")
    expect(True)
      is-stale(100, 200, [150, 300])

  test("is-stale: all dependencies older than our output")
    expect(False)
      is-stale(100, 200, [150, 199])

  test("is-stale: a missing output (time 0) is always stale")
    expect(True)
      is-stale(100, 0, [])

  test("is-stale: equal times do not trigger a rebuild")
    // Strict `>`: on a coarse-granularity filesystem an output written in the
    // same tick as its input will NOT rebuild. Documented in the spec as the
    // mtime-granularity pitfall.
    expect(False)
      is-stale(200, 200, [200])

  test("phase show")
    expect("typecheck")
      TypeCheck.show
    expect("codegen")
      CodeGen.show

  test("mod-status show carries the blocker")
    expect("skipped(dep)")
      Skipped("dep".new-name).show

  test("phases are ordered")
    expect(True)
      Lex <= TypeCheck && TypeCheck <= Link

  test("reached: a module at CodeGen has produced TypeCheck")
    expect(True)
      CodeGen.reached(TypeCheck)

  test("reached: a module at Parse has NOT produced Optimize")
    expect(False)
      Parse.reached(Optimize)

  test("mod-stale: a source module with a newer source rebuilds")
    expect(True)
      Mod-info("m".new-name, "m.kk".path, "m.kki".path, "".path, 300, 200, 0)
        .mod-stale([])

  test("mod-stale: a source module with a fresh interface is reused")
    expect(False)
      Mod-info("m".new-name, "m.kk".path, "m.kki".path, "".path, 100, 200, 0)
        .mod-stale([150])

  test("mod-stale: a source module rebuilds when a dependency is newer")
    expect(True)
      Mod-info("m".new-name, "m.kk".path, "m.kki".path, "".path, 100, 200, 0)
        .mod-stale([250])

  test("mod-stale: a precompiled library interface is trusted when present")
    // no source in the tree, so there is nothing to compare against
    expect(False)
      Mod-info("std".new-name, "".path, "".path, "std.kki".path, 0, 0, 500)
        .mod-stale([999])

  test("mod-stale: a missing library interface is stale")
    expect(True)
      Mod-info("std".new-name, "".path, "".path, "std.kki".path, 0, 0, 0)
        .mod-stale([])

fun main()
  run-tests(suite)
