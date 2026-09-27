import compiler/common/failure
import std/test

fun suite()
  group("assert")
    test("assert succeeds when test is true")
      expect(42)
        failure/assert("should pass", True, 42)

    test("assert with different values")
      expect("hello")
        failure/assert("string assert", True, "hello")

  group("catch")
    test("catch returns success value")
      expect("success")
        failure/catch(fn(_) "error", fn() "success")

    test("catch handles raised exceptions")
      expect("my error")
        with failure/catch(fn(msg) msg)
        failure/raise("my error")
        "unreachable"

    test("catch can transform error message")
      expect(True)
        val result = 
          with failure/catch(fn(msg) "error: " ++ msg)
          failure/raise("oops")
          "unreachable"
        result.starts-with("error:").is-just

fun main()
  run-tests(suite)
