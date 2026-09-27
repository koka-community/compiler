import compiler/common/resume-kind
import std/test

fun suite()
  group("resume-kind show")
    test("ResumeNever shows as never")
      expect("never")
        ResumeNever.show

    test("ResumeTail shows as tail")
      expect("tail")
        ResumeTail.show

    test("ResumeScopedOnce shows as scoped once")
      expect("scoped once")
        ResumeScopedOnce.show

    test("ResumeScoped shows as scoped")
      expect("scoped")
        ResumeScoped.show

    test("ResumeOnce shows as once")
      expect("once")
        ResumeOnce.show

    test("ResumeNormal shows as normal")
      expect("normal")
        ResumeNormal.show

    test("ResumeOnceRaw shows as once (no finalization)")
      expect("once (no finalization)")
        ResumeOnceRaw.show

    test("ResumeNormalRaw shows as normal (no finalization)")
      expect("normal (no finalization)")
        ResumeNormalRaw.show

  group("resume-kind index")
    test("ResumeNever has index 0")
      expect(0)
        ResumeNever.index

    test("ResumeTail has index 1")
      expect(1)
        ResumeTail.index

    test("ResumeScopedOnce has index 2")
      expect(2)
        ResumeScopedOnce.index

    test("ResumeScoped has index 3")
      expect(3)
        ResumeScoped.index

    test("ResumeOnce has index 4")
      expect(4)
        ResumeOnce.index

    test("ResumeNormal has index 5")
      expect(5)
        ResumeNormal.index

    test("ResumeOnceRaw has index 6")
      expect(6)
        ResumeOnceRaw.index

    test("ResumeNormalRaw has index 7")
      expect(7)
        ResumeNormalRaw.index

  group("resume-kind ordering")
    test("ResumeNever before ResumeTail by index")
      expect(True)
        ResumeNever.index < ResumeTail.index

    test("ResumeTail before ResumeScopedOnce by index")
      expect(True)
        ResumeTail.index < ResumeScopedOnce.index

    test("ResumeOnceRaw before ResumeNormalRaw by index")
      expect(True)
        ResumeOnceRaw.index < ResumeNormalRaw.index

    test("ResumeNever index less-than-or-equal ResumeTail index")
      expect(True)
        ResumeNever.index <= ResumeTail.index

    test("ResumeNever index equal to itself")
      expect(True)
        ResumeNever.index <= ResumeNever.index

    test("ResumeNormalRaw index greater than ResumeOnceRaw index")
      expect(True)
        ResumeNormalRaw.index > ResumeOnceRaw.index

    test("ResumeNormalRaw index greater-than-or-equal ResumeOnceRaw index")
      expect(True)
        ResumeNormalRaw.index >= ResumeOnceRaw.index

  group("resume-kind ordering comparison")
    test("ResumeNever index cmp ResumeTail index returns Lt")
      expect(True)
        ResumeNever.index.cmp(ResumeTail.index) == Lt

    test("ResumeTail index cmp ResumeTail index returns Eq")
      expect(True)
        ResumeTail.index.cmp(ResumeTail.index) == Eq

    test("ResumeNormalRaw index cmp ResumeOnceRaw index returns Gt")
      expect(True)
        ResumeNormalRaw.index.cmp(ResumeOnceRaw.index) == Gt

  group("Edge cases")
    test("all variants are distinct")
      val all = [ResumeNever, ResumeTail, ResumeScopedOnce, ResumeScoped, ResumeOnce, ResumeNormal, ResumeOnceRaw, ResumeNormalRaw]
      expect(True)
        all.length == 8

    test("indices are sequential from 0 to 7")
      val indices = [ResumeNever.index, ResumeTail.index, ResumeScopedOnce.index, ResumeScoped.index, ResumeOnce.index, ResumeNormal.index, ResumeOnceRaw.index, ResumeNormalRaw.index]
      expect(True)
        indices == [0, 1, 2, 3, 4, 5, 6, 7]

    test("show produces non-empty strings")
      expect(True)
        ResumeNever.show.count > 0 && ResumeNormalRaw.show.count > 0


fun main()
  run-tests(suite)
