import compiler/common/resume-kind
import std/test

fun suite()
  group("resumeKind show")
    test("ResumeNever shows as never")
      expect("never") fn()
        ResumeNever.show

    test("ResumeTail shows as tail")
      expect("tail") fn()
        ResumeTail.show

    test("ResumeScopedOnce shows as scoped once")
      expect("scoped once") fn()
        ResumeScopedOnce.show

    test("ResumeScoped shows as scoped")
      expect("scoped") fn()
        ResumeScoped.show

    test("ResumeOnce shows as once")
      expect("once") fn()
        ResumeOnce.show

    test("ResumeNormal shows as normal")
      expect("normal") fn()
        ResumeNormal.show

    test("ResumeOnceRaw shows as once (no finalization)")
      expect("once (no finalization)") fn()
        ResumeOnceRaw.show

    test("ResumeNormalRaw shows as normal (no finalization)")
      expect("normal (no finalization)") fn()
        ResumeNormalRaw.show

  group("resumeKind index")
    test("ResumeNever has index 0")
      expect(0) fn()
        ResumeNever.index

    test("ResumeTail has index 1")
      expect(1) fn()
        ResumeTail.index

    test("ResumeScopedOnce has index 2")
      expect(2) fn()
        ResumeScopedOnce.index

    test("ResumeScoped has index 3")
      expect(3) fn()
        ResumeScoped.index

    test("ResumeOnce has index 4")
      expect(4) fn()
        ResumeOnce.index

    test("ResumeNormal has index 5")
      expect(5) fn()
        ResumeNormal.index

    test("ResumeOnceRaw has index 6")
      expect(6) fn()
        ResumeOnceRaw.index

    test("ResumeNormalRaw has index 7")
      expect(7) fn()
        ResumeNormalRaw.index

  group("resumeKind ordering")
    test("ResumeNever before ResumeTail by index")
      expect(True) fn()
        ResumeNever.index < ResumeTail.index

    test("ResumeTail before ResumeScopedOnce by index")
      expect(True) fn()
        ResumeTail.index < ResumeScopedOnce.index

    test("ResumeOnceRaw before ResumeNormalRaw by index")
      expect(True) fn()
        ResumeOnceRaw.index < ResumeNormalRaw.index

    test("ResumeNever index less-than-or-equal ResumeTail index")
      expect(True) fn()
        ResumeNever.index <= ResumeTail.index

    test("ResumeNever index equal to itself")
      expect(True) fn()
        ResumeNever.index <= ResumeNever.index

    test("ResumeNormalRaw index greater than ResumeOnceRaw index")
      expect(True) fn()
        ResumeNormalRaw.index > ResumeOnceRaw.index

    test("ResumeNormalRaw index greater-than-or-equal ResumeOnceRaw index")
      expect(True) fn()
        ResumeNormalRaw.index >= ResumeOnceRaw.index

  group("resumeKind ordering comparison")
    test("ResumeNever index cmp ResumeTail index returns Lt")
      expect(True) fn()
        ResumeNever.index.cmp(ResumeTail.index) == Lt

    test("ResumeTail index cmp ResumeTail index returns Eq")
      expect(True) fn()
        ResumeTail.index.cmp(ResumeTail.index) == Eq

    test("ResumeNormalRaw index cmp ResumeOnceRaw index returns Gt")
      expect(True) fn()
        ResumeNormalRaw.index.cmp(ResumeOnceRaw.index) == Gt

  group("Edge cases")
    test("all variants are distinct")
      val all = [ResumeNever, ResumeTail, ResumeScopedOnce, ResumeScoped, ResumeOnce, ResumeNormal, ResumeOnceRaw, ResumeNormalRaw]
      expect(True) fn()
        all.length == 8

    test("indices are sequential from 0 to 7")
      val indices = [ResumeNever.index, ResumeTail.index, ResumeScopedOnce.index, ResumeScoped.index, ResumeOnce.index, ResumeNormal.index, ResumeOnceRaw.index, ResumeNormalRaw.index]
      expect(True) fn()
        indices == [0, 1, 2, 3, 4, 5, 6, 7]

    test("show produces non-empty strings")
      expect(True) fn()
        ResumeNever.show.count > 0 && ResumeNormalRaw.show.count > 0


fun main()
  run-tests(suite)
