import compiler/common/error
import compiler/common/range
import compiler/lib/pprint
import std/test

// Common test data
val src = Source("test.kk", "")
val p1 = Pos(src, 0, 1, 1)
val p2 = Pos(src, 5, 1, 6)
val rng = Range(p1, p2, False)

fun suite()
  group("error-severity comparison")
    test("SevInfo is lowest")
      expect(True)
        SevInfo.cmp(SevWarning) == Lt

    test("SevWarning is middle")
      expect(True)
        SevWarning.cmp(SevError) == Lt

    test("SevError is highest")
      expect(True)
        SevError.cmp(SevWarning) == Gt

    test("equal severities compare equal")
      expect(True)
        SevError.cmp(SevError) == Eq

    test("SevInfo less than SevWarning")
      expect(True)
        SevInfo.cmp(SevWarning) == Lt

    test("SevError greater than SevWarning")
      expect(True)
        SevError.cmp(SevWarning) == Gt

    test("SevWarning greater than SevInfo")
      expect(True)
        SevWarning.cmp(SevInfo) == Gt

  group("error-msg construction")
    test("error-message-kind creates error message")
      expect(True)
        val msg = error-message-kind(text("test error"), rng, ErrGeneral)
        msg.severity == SevError

    test("warning-message-kind creates warning message")
      expect(True)
        val msg = warning-message-kind(text("test warning"), rng, ErrGeneral)
        msg.severity == SevWarning

    test("info-message-kind creates info message")
      expect(True)
        val msg = info-message-kind(text("test info"), rng, ErrGeneral)
        msg.severity == SevInfo

  group("error predicates")
    test("is-warning for SevWarning")
      expect(True)
        val msg = warning-message-kind(text("warn"), rng)
        msg.is-warning

    test("is-warning false for SevError")
      expect(False)
        val msg = error-message-kind(text("err"), rng)
        msg.is-warning

    test("is-warning true for SevInfo")
      expect(True)
        val msg = info-message-kind(text("info"), rng)
        msg.is-warning

  group("error kinds")
    test("ErrGeneral kind works")
      expect(True)
        val msg = error-message-kind(text("test"), rng, ErrGeneral)
        msg.kind == ErrGeneral

    test("ErrParse kind works")
      expect(True)
        val msg = error-message-kind(text("test"), rng, ErrParse)
        msg.kind == ErrParse

    test("ErrType kind works")
      expect(True)
        val msg = error-message-kind(text("test"), rng, ErrType)
        msg.kind == ErrType

  group("error-msg range extraction")
    test("range extracts from single error")
      expect(True)
        val msg = error-message-kind(text("test"), rng)
        val errs = [msg]
        errs.compiler/common/error/range == rng

fun main()
  run-tests(suite)
