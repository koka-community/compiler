import compiler/platform/config
import std/test

fun suite()
  group("platform/config")
    test("compilerFlags")
      expect("3.2.3")
        with @default-comp-flags
        comp-flags.version
    test("platform")
      expect(True)
        is-path-sep('/') && is-path-sep('\\')
    test("utils")
      expect(True)
        source-ext == ".kk"

fun main()
  run-tests(suite)