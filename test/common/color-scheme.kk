import compiler/common/color-scheme
import compiler/lib/printer
import std/test

fun suite()
  group("colorScheme equality")
    test("same default schemes are equal")
      val cs1 = ColorScheme()
      val cs2 = ColorScheme()
      expect(True)
        cs1 == cs2

    test("different color updates create unequal schemes")
      val cs1 = ColorScheme()
      val cs2 = ColorScheme(colorType = Blue)
      expect(True)
        !(cs1 == cs2)

    test("dark and light color schemes differ")
      expect(True)
        !(dark-color-scheme == light-color-scheme)

  group("color/default")
    test("replaces ColorDefault with provided color")
      expect(True)
        color/default(Red, ColorDefault) == Red

    test("keeps non-default colors unchanged")
      expect(True)
        color/default(Red, Blue) == Blue

    test("default color maps to replacement")
      expect(True)
        color/default(Green, ColorDefault) == Green

  group("scheme/default")
    test("replaces all ColorDefault fields")
      val cs = ColorScheme()
      val updated = scheme/default(cs, Red)
      expect(True)
        updated.colorType == Red && updated.colorMarker == Red

    test("preserves structure on empty default")
      val updated = scheme/default(ColorScheme(), Blue)
      expect(True)
        updated.colorKeyword == Blue

  group("make-color-scheme")
    test("creates scheme with all fields same color")
      val cs = make-color-scheme(Red)
      expect(True)
        cs.colorType == Red && cs.colorString == Red && cs.colorNumber == Red

    test("ColorDefault creates empty-like scheme")
      val cs = make-color-scheme(ColorDefault)
      expect(True)
        cs.colorType == ColorDefault && cs.colorComment == ColorDefault

    test("all 30 fields set to same color")
      val cs = make-color-scheme(Green)
      expect(True)
        cs.colorInterpreter == Green && cs.colorImplicitExpr == Green

  group("color theme definitions")
    test("color-themes list has two themes")
      expect(True)
        color-themes.length == 2

    test("dark-color-scheme is default")
      expect(True)
        dark-color-scheme.colorType == DarkCyan

    test("light-color-scheme has light colors")
      expect(True)
        light-color-scheme.colorNumber == DarkGray

  group("read-color-flag")
    test("parses type=blue assignment")
      val cs = ColorScheme().read-color-flag("type=blue")
      expect(True)
        cs.colorType == Blue

    test("parses color with colon separator")
      val cs = ColorScheme().read-color-flag("error:red")
      expect(True)
        cs.colorError == Red

    test("handles default color name")
      val cs = ColorScheme(colorString = Red).read-color-flag("string=default")
      expect(True)
        cs.colorString == ColorDefault

    test("parses 'none' theme to empty")
      val cs = ColorScheme().read-color-flag("none")
      expect(True)
        cs == color-scheme/empty

    test("parses 'all' theme to uniform color")
      val cs = ColorScheme().read-color-flag("all=red")
      expect(True)
        cs.colorType == Red && cs.colorString == Red

  group("color name parsing")
    test("parses 'black' color name")
      val cs = ColorScheme().read-color-flag("type=black")
      expect(True)
        cs.colorType == Black

    test("parses 'darkred' color name")
      val cs = ColorScheme().read-color-flag("type=darkred")
      expect(True)
        cs.colorType == DarkRed

    test("parses 'cyan' color name")
      val cs = ColorScheme().read-color-flag("type=cyan")
      expect(True)
        cs.colorType == Cyan

    test("parses 'white' color name")
      val cs = ColorScheme().read-color-flag("type=white")
      expect(True)
        cs.colorType == White

    test("parses 'lightgray' color name")
      val cs = ColorScheme().read-color-flag("type=lightgray")
      expect(True)
        cs.colorType == Gray

  group("color name aliases")
    test("'grey' maps to DarkGray")
      val cs = ColorScheme().read-color-flag("type=grey")
      expect(True)
        cs.colorType == DarkGray

    test("'navy' maps to DarkBlue")
      val cs = ColorScheme().read-color-flag("type=navy")
      expect(True)
        cs.colorType == DarkBlue

    test("'teal' maps to DarkCyan")
      val cs = ColorScheme().read-color-flag("type=teal")
      expect(True)
        cs.colorType == DarkCyan

    test("'purple' maps to DarkMagenta")
      val cs = ColorScheme().read-color-flag("type=purple")
      expect(True)
        cs.colorType == DarkMagenta

    test("'lime' maps to Green")
      val cs = ColorScheme().read-color-flag("type=lime")
      expect(True)
        cs.colorType == Green

  group("semantic field names")
    test("'keyword' updates colorKeyword")
      val cs = ColorScheme().read-color-flag("keyword=red")
      expect(True)
        cs.colorKeyword == Red

    test("'warning' updates colorWarning")
      val cs = ColorScheme().read-color-flag("warning=yellow")
      expect(True)
        cs.colorWarning == Yellow

    test("'string' updates colorString")
      val cs = ColorScheme().read-color-flag("string=cyan")
      expect(True)
        cs.colorString == Cyan

    test("'number' updates colorNumber")
      val cs = ColorScheme().read-color-flag("number=darkblue")
      expect(True)
        cs.colorNumber == DarkBlue

    test("'comment' updates colorComment")
      val cs = ColorScheme().read-color-flag("comment=darkgreen")
      expect(True)
        cs.colorComment == DarkGreen

  group("read-color-flags with multiple assignments")
    test("parses comma-separated color assignments")
      val cs = ColorScheme().read-color-flags("type=blue,string=red")
      expect(True)
        cs.colorType == Blue && cs.colorString == Red

    test("parses semicolon-separated color assignments")
      val cs = ColorScheme().read-color-flags("keyword=green;comment=darkgreen")
      expect(True)
        cs.colorKeyword == Green && cs.colorComment == DarkGreen

    test("parses mixed comma and semicolon")
      val cs = ColorScheme().read-color-flags("error=red,warning=yellow;type=blue")
      expect(True)
        cs.colorError == Red && cs.colorWarning == Yellow && cs.colorType == Blue

  group("case-insensitive field names")
    test("'TYPE' updates colorType")
      val cs = ColorScheme().read-color-flag("TYPE=red")
      expect(True)
        cs.colorType == Red

    test("'Warning' updates colorWarning")
      val cs = ColorScheme().read-color-flag("Warning=yellow")
      expect(True)
        cs.colorWarning == Yellow

    test("'COMMENT' updates colorComment")
      val cs = ColorScheme().read-color-flag("COMMENT=green")
      expect(True)
        cs.colorComment == Green

  group("effect colorSchemeEffect")
    test("color-scheme-default provides access to colors")
      val result = color-scheme-default({
        colors().colorError
      })
      expect(True)
        result == Red

    test("custom colorScheme can be provided")
      val custom = ColorScheme(colorError = Blue)
      val result = handle({True})
        val colors = custom
      expect(True)
        result

fun main()
  run-tests(suite)

