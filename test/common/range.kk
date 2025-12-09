import compiler/common/range
import std/test

// Shared test source
val src = Source("test.kk", "")

fun suite()
  group("Source and Position creation")
    test("source has name and contents")
      val src1 = Source("test.kk", "hello world")
      expect("test.kk") fn() src1.name
      expect("hello world") fn() src1.contents

    test("source/null is empty source")
      expect("") fn() source/null.name
      expect("") fn() source/null.contents

    test("pos with valid offset")
      val src1 = Source("test.kk", "hello world")
      val p = Pos(src1, 10, 1, 5)
      expect(10) fn() p.off
      expect(1) fn() p.line
      expect(5) fn() p.col

    test("pos/null has negative offset")
      expect(True) fn() pos/null.off < 0

  group("Position comparison")
    val p1 = Pos(src, 0, 1, 5)
    val p2 = Pos(src, 0, 1, 10)
    val p3 = Pos(src, 0, 2, 1)
    
    test("equal positions are equal")
      expect(True) fn() p1 == p1

    test("positions on different lines compare by line")
      expect(True) fn() p2 < p3

    test("positions on same line compare by column")
      expect(True) fn() p1 < p2

    test("position less-than-or-equal")
      expect(True) fn() p1 <= p2

    test("position greater-than")
      expect(True) fn() p3 > p2

    test("position greater-than-or-equal")
      expect(True) fn() p1 >= p1

    test("position comparison order")
      expect(True) fn() p1.pos/cmp(p1) == Eq

    test("position cmp less-than")
      expect(True) fn() p1.pos/cmp(p3) == Lt

    test("position cmp greater-than")
      expect(True) fn() p3.pos/cmp(p1) == Gt

  group("Position formatting")
    test("show-pos formats position")
      val p = Pos(src, 0, 5, 10)
      val str = p.show-pos(2)
      expect(True) fn() str.contains("5") && str.contains("10")

    test("show-line formats line numbers")
      expect("5") fn() 5.show-line

    test("show-line for line 0 shows 1")
      expect("1") fn() 0.show-line

    test("show-line for negative line shows 1")
      expect("1") fn() (-5).show-line

  group("Range creation and equality")
    val p1 = Pos(src, 0, 1, 1)
    val p2 = Pos(src, 5, 1, 6)
    val r = Range(p1, p2, False)
    
    test("range with start and end")
      expect(True) fn() r.start == p1 && r.end == p2

    test("range/null has negative offset")
      expect(True) fn() range/null.start.off < 0

    test("make-range orders positions")
      val r_ord = make-range(p2, p1)
      expect(True) fn() r_ord.start == p1 && r_ord.end == p2

    test("equal ranges are equal")
      val r2 = Range(p1, p2, False)
      expect(True) fn() r == r2

    test("ranges with different hidden flags not equal")
      val r2 = Range(p1, p2, True)
      expect(True) fn() r != r2

  group("Range operations")
    val p1 = Pos(src, 0, 1, 1)
    val p2 = Pos(src, 5, 1, 6)
    val p3 = Pos(src, 2, 1, 3)
    val p4 = Pos(src, 10, 2, 1)
    val r = Range(p1, p2, False)
    
    test("range/length calculates offset difference")
      expect(5) fn() r.range/length

    test("range/is-null for null range")
      expect(True) fn() range/null.range/is-null

    test("range/is-null false for valid range")
      expect(False) fn() r.range/is-null

    test("range/contains checks if position in range")
      expect(True) fn() r.range/contains(p3)

    test("range/contains false for position outside range")
      expect(False) fn() r.range/contains(p4)

    test("range/is-before checks if range ends before position")
      expect(True) fn() r.range/is-before(p4)

    test("range/starts-at checks start position")
      expect(True) fn() r.range/starts-at(p1)

    test("range/hide marks range as hidden")
      expect(True) fn() r.range/hide.hidden

    test("extend increases column of end position")
      val r_ext = r.extend(3)
      expect(True) fn() r_ext.end.col == p2.col + 3

    test("start-of-range creates range for first character")
      val r_start = r.start-of-range
      expect(True) fn() r_start.start == p1 && r_start.end == p1

    test("end-of-range creates range for last character")
      val r_end = r.end-of-range
      expect(True) fn() r_end.start == p2 && r_end.end == p2

    test("range/before creates range at start")
      val r_before = r.range/before
      expect(True) fn() r_before.start == p1 && r_before.end == p1

    test("range/after creates range at end")
      val r_after = r.range/after
      expect(True) fn() r_after.start == p2 && r_after.end == p2

  group("Range comparison")
    val p1 = Pos(src, 0, 1, 1)
    val p2 = Pos(src, 5, 1, 6)
    val p3 = Pos(src, 5, 2, 1)
    val p4 = Pos(src, 10, 2, 5)
    val r1 = Range(p1, p2, False)
    val r2 = Range(p3, p4, False)
    
    test("range comparison by start position")
      expect(True) fn() r1.range/cmp(r2) == Lt

    test("range/is-after checks if one range starts after another ends")
      expect(True) fn() r1.range/is-after(r2)

  group("Position movement")
    val p = Pos(src, 0, 1, 1)
    
    test("pos-move8 handles regular characters")
      val p_moved = pos-move8(p, 'a')
      expect(True) fn() p_moved.col == 2 && p_moved.line == 1

    test("pos-move8 handles newlines")
      val p_moved = pos-move8(p, '\n')
      expect(True) fn() p_moved.line == 2 && p_moved.col == 1

    test("pos-move8 handles tabs")
      val p_moved = pos-move8(p, '\t')
      expect(True) fn() p_moved.col > 1

    test("chars/pos-moves-8 with list of characters")
      val p_moved = chars/pos-moves-8(p, ['a', 'b', 'c'])
      expect(True) fn() p_moved.col == 4

  group("Position minimum and maximum")
    val p1 = Pos(src, 0, 1, 5)
    val p2 = Pos(src, 0, 2, 1)
    
    test("pos/min selects earlier position")
      val p_min = p1.pos/min(p2)
      expect(True) fn() p_min == p1

    test("pos/max selects later position")
      val p_max = p1.pos/max(p2)
      expect(True) fn() p_max == p2

    test("pos/min with null position returns other")
      val p_min = pos/null.pos/min(p1)
      expect(True) fn() p_min == p1

    test("pos/max with null position returns non-null")
      val p_max = pos/null.pos/max(p1)
      expect(True) fn() p_max == p1

  group("Range combination")
    val p1 = Pos(src, 0, 1, 1)
    val p2 = Pos(src, 5, 1, 6)
    val p3 = Pos(src, 6, 2, 1)
    val p4 = Pos(src, 10, 2, 5)
    val r1 = Range(p1, p2, False)
    val r2 = Range(p3, p4, False)
    
    test("combine merges two ranges")
      val r_combined = r1.combine(r2)
      expect(True) fn() r_combined.start == r1.start && r_combined.end == r2.end

    test("combine with hidden ranges")
      val r1_hidden = Range(p1, p2, True)
      val r_combined = r1_hidden.combine(r2)
      expect(True) fn() r_combined.hidden

  group("Make source range")
    test("make-source-range creates range with line/col")
      val r = make-source-range("test.kk", 1, 5, 2, 10)
      expect(True) fn() r.start.line == 1 && r.start.col == 5 && r.end.line == 2 && r.end.col == 10

  group("Edge cases")
    val p1 = Pos(src, 0, 1, 1)
    val p2 = Pos(src, 5, 1, 6)
    val r = Range(p1, p2, False)
    
    test("range containing its start position")
      expect(True) fn() r.range/contains(r.start)

    test("range containing its end position")
      expect(True) fn() r.range/contains(r.end)

    test("single character range")
      val r_single = Range(p1, p1, False)
      expect(0) fn() r_single.range/length


fun main()
  run-tests(suite)
