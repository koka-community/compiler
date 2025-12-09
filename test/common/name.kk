import compiler/common/name
import std/pretty/pprint
import std/pretty/printer
import std/test

// Common test names
val name-int = new-qualified("std/core", "int")
val name-int-local = new-locally-qualified("std/core", "types", "int")
val name-foo = "foo".new-name

fun suite()
  group("Name construction")
    test("new-name creates a simple name")
      expect("foo") fn() name-foo.nameStem
      expect("") fn() name-foo.nameModule
      expect("") fn() name-foo.nameLocalQual

    test("new-module-name creates a module name")
      expect("")
        "std/core".new-module-name.nameStem
      expect("std/core")
        "std/core".new-module-name.nameModule
      expect("")
        "std/core".new-module-name.nameLocalQual

    test("new-qualified creates a module-qualified name")
      expect("int") fn() name-int.nameStem
      expect("std/core") fn() name-int.nameModule
      expect("") fn() name-int.nameLocalQual

    test("new-locally-qualified creates a fully qualified name")
      expect("int") fn() name-int-local.nameStem
      expect("std/core") fn() name-int-local.nameModule
      expect("types") fn() name-int-local.nameLocalQual

  group("Name string conversion")
    test("show-plain shows full path")
      expect("std/core/types/int") fn() name-int-local.show-plain

    test("show-name without explicit local qualifier")
      expect("std/core/types/int") fn() name-int-local.show-name(False)

    test("show-name with explicit local qualifier")
      expect("std/core/#types/int") fn() name-int-local.show-name(True)

    test("show-fully-explicit with local qualifier")
      expect("std/core/#types/int") fn() name-int-local.show-fully-explicit

    test("show-fully-explicit without local qualifier")
      expect("std/core/#int") fn() name-int.show-fully-explicit

    test("show with empty module")
      expect("int")
        "int".new-name.show

    test("pretty-local-name shows only local part")
      expect("types/int")
        new-locally-qualified("std/core", "types", "int").pretty-local-name.show

    test("pretty-full-name shows complete path")
      expect("std/core/types/int")
        new-locally-qualified("std/core", "types", "int").pretty-full-name.show

  group("Name comparison and equality")
    test("equal names compare equal")
      expect(True)
        val n1 = new-qualified("std/core", "int")
        val n2 = new-qualified("std/core", "int")
        n1 == n2

    test("different stem names not equal")
      expect(True)
        val n1 = new-qualified("std/core", "int")
        val n2 = new-qualified("std/core", "string")
        n1 != n2

    test("different module names not equal")
      expect(True)
        val n1 = new-qualified("std/core", "int")
        val n2 = new-qualified("std/num", "int")
        n1 != n2

    test("name-case-equal for identical names")
      expect(True)
        val n1 = new-qualified("std/core", "Int")
        val n2 = new-qualified("std/core", "Int")
        n1.name-case-equal(n2)

    test("name-cmp orders by module")
      expect(True)
        val n1 = new-qualified("std/a", "int")
        val n2 = new-qualified("std/b", "int")
        n1.name/cmp(n2) == Lt

    test("name-cmp orders by stem when modules equal")
      expect(True)
        val n1 = new-qualified("std/core", "a")
        val n2 = new-qualified("std/core", "z")
        n1.name/cmp(n2) == Lt

  group("Module and qualification")
    test("is-module-name for module names")
      expect(True)
        val n = "std/core".new-module-name
        n.is-module-name

    test("is-module-name false for qualified names")
      expect(False)
        val n = "int".new-name
        n.is-module-name

    test("is-qualified for qualified names")
      expect(True)
        val n = new-qualified("std/core", "int")
        n.is-qualified

    test("is-qualified false for unqualified names")
      expect(False)
        val n = "int".new-name
        n.is-qualified

    test("is-locally-qualified")
      expect(True)
        val n = new-locally-qualified("std/core", "types", "int")
        n.is-locally-qualified

    test("is-locally-qualified false when no local qualifier")
      expect(False)
        val n = new-qualified("std/core", "int")
        n.is-locally-qualified

    test("split-module-name")
      expect(["std", "core", "types"])
        val n = "std/core/types".new-module-name
        n.split-module-name

    test("unqualify removes module")
      expect("")
        val n = new-qualified("std/core", "int")
        n.unqualify.nameModule
      expect("int")
        val n = new-qualified("std/core", "int")
        n.unqualify.nameStem

    test("unqualify-full keeps only stem")
      expect("")
        val n = new-locally-qualified("std/core", "types", "int")
        n.unqualify-full.nameModule
      expect("")
        val n = new-locally-qualified("std/core", "types", "int")
        n.unqualify-full.nameLocalQual
      expect("int")
        val n = new-locally-qualified("std/core", "types", "int")
        n.unqualify-full.nameStem

    test("qualifier extracts module")
      expect("std/core")
        val n = new-qualified("std/core", "int")
        n.qualifier.nameModule
      expect("")
        val n = new-qualified("std/core", "int")
        n.qualifier.nameStem

    test("requalify-locally moves module to local")
      expect("")
        val n = new-qualified("std/core", "int")
        n.requalify-locally.nameModule
      expect("std/core")
        val n = new-qualified("std/core", "int")
        n.requalify-locally.nameLocalQual
      expect("int")
        val n = new-qualified("std/core", "int")
        n.requalify-locally.nameStem

  group("Name predicates")
    test("is-symbol-name for operator names")
      expect(True)
        val n = "++".new-name
        n.is-symbol-name

    test("is-symbol-name false for alphanumeric names")
      expect(False)
        val n = "add".new-name
        n.is-symbol-name

    test("is-constructor-name for capitalized names")
      expect(True)
        val n = "Just".new-name
        n.is-constructor-name

    test("is-constructor-name false for lowercase names")
      expect(False)
        val n = "just".new-name
        n.is-constructor-name

    test("is-constructor-name for hidden constructor names")
      expect(True)
        val n = new-locally-qualified("std/core", "", "@Just")
        n.is-constructor-name

    test("is-wildcard for underscore names")
      expect(True)
        val n = "_".new-name
        n.is-wildcard

    test("is-wildcard false for normal names")
      expect(False)
        val n = "x".new-name
        n.is-wildcard

    test("is-hidden-name for hidden names")
      expect(True)
        val n = "@hidden".new-name
        n.is-hidden-name

    test("is-hidden-name false for normal names")
      expect(False)
        val n = "visible".new-name
        n.is-hidden-name

  group("Name modification")
    test("prepend adds prefix to stem")
      expect("prefoo")
        val n = "foo".new-name
        "pre".prepend(n).nameStem

    test("postpend adds suffix to stem")
      expect("foopost")
        val n = "foo".new-name
        n.postpend("post").nameStem

    test("to-constructor-name capitalizes stem")
      expect("Int")
        val n = "int".new-name
        n.to-constructor-name.nameStem

    test("to-var-name lowercases stem")
      expect("just")
        val n = "Just".new-name
        n.to-var-name.nameStem

    test("make-hidden creates hidden name")
      expect(True)
        val n = "foo".new-name
        n.make-hidden.is-hidden-name

    test("to-unique-name appends number")
      expect("foo@42")
        val n = "foo".new-name
        to-unique-name(42, n).nameStem

  group("Special names")
    test("is-padding-name for padding names")
      expect(True)
        val n = new-padding-name(1)
        n.is-padding-name

    test("is-field-name for field names")
      expect(True)
        val n = new-field-name(3)
        n.is-field-name

    test("is-implicit-typevar-name for type variable names")
      expect(True)
        val n = new-implicit-typevar-name(5)
        n.is-implicit-typevar-name

    test("is-creator-name for creator names")
      expect(True)
        val n = "Just".new-name.new-creator-name
        n.is-creator-name

    test("is-handler-con-name for handler constructor names")
      expect(True)
        val n = "Effect".new-name.to-handler-con-name
        n.is-handler-con-name

  group("Implicit parameters")
    test("is-implicit-param-name for implicit names")
      expect(True)
        val implicit_ns = implicit-namespace.new-module-name
        val n = implicit_ns.qualify-locally("x".new-name)
        n.is-implicit-param-name

    test("to-implicit-param-name creates implicit param")
      expect(True)
        val n = "x".new-name
        val i = n.to-implicit-param-name
        i.is-implicit-param-name

  group("Reading qualified names")
    test("read-qualified-name simple name")
      expect("foo")
        val n = "foo".read-qualified-name
        n.nameStem
      expect("")
        val n = "foo".read-qualified-name
        n.nameModule

    test("read-qualified-name module qualified")
      expect("int")
        val n = "std/core/int".read-qualified-name
        n.nameStem
      expect("std/core")
        val n = "std/core/int".read-qualified-name
        n.nameModule

    test("read-qualified-name operator in parentheses")
      expect("++")
        val n = "(++)".read-qualified-name
        n.nameStem
      expect("")
        val n = "(++)".read-qualified-name
        n.nameModule

    test("read-qualified-name module with operator")
      expect("++")
        val n = "std/core/(++)".read-qualified-name
        n.nameStem
      expect("std/core")
        val n = "std/core/(++)".read-qualified-name
        n.nameModule

    test("read-qualified-name locally qualified")
      expect("int")
        val n = "std/core/#types/int".read-qualified-name
        n.nameStem
      expect("std/core")
        val n = "std/core/#types/int".read-qualified-name
        n.nameModule
      expect("types")
        val n = "std/core/#types/int".read-qualified-name
        n.nameLocalQual

  group("ASCII encoding and file paths")
    test("module-name-to-path encodes module name")
      expect(True)
        val n = "std/core".new-module-name
        val path = n.module-name-to-path
        path.contains("_")

    test("path-to-module-name decodes path back")
      expect("std/core/types")
        val orig = "std/core/types".new-module-name
        val path = orig.module-name-to-path
        val decoded = path.path-to-module-name
        decoded.nameModule

  group("Name joining and splitting")
    test("name/local joins local qualifier and stem")
      expect("types/int")
        val n = new-locally-qualified("std/core", "types", "int")
        n.name/local

    test("full-qualifier gets module and local")
      expect("std/core/types")
        val n = new-locally-qualified("std/core", "types", "int")
        n.full-qualifier

    test("unqualify-locally moves local to module")
      expect("std/core/types")
        val n = new-locally-qualified("std/core", "types", "int")
        n.unqualify-locally.nameModule
      expect("")
        val n = new-locally-qualified("std/core", "types", "int")
        n.unqualify-locally.nameLocalQual
      expect("int")
        val n = new-locally-qualified("std/core", "types", "int")
        n.unqualify-locally.nameStem

  group("Name type operations")
    test("to-handler-name creates handler type name")
      expect(True)
        val n = new-qualified("std/core", "Effect")
        val h = n.to-handler-name
        h.is-handler-name

    test("to-operations-name creates operations type name")
      expect(True)
        val n = new-qualified("std/core", "Effect")
        val ops = n.to-operations-name
        ops.is-operations-name

  group("Name hash consistency")
    test("identical names have same hash")
      expect(True)
        val n1 = new-qualified("std/core", "int")
        val n2 = new-qualified("std/core", "int")
        n1.hashModule == n2.hashModule && n1.hashStem == n2.hashStem

    test("different stems have different hash")
      expect(True)
        val n1 = new-qualified("std/core", "int")
        val n2 = new-qualified("std/core", "string")
        n1.hashStem != n2.hashStem

    test("hash function handles empty strings")
      expect(0)
        val empty = "".new-name
        empty.hashStem

  group("Edge cases")
    test("nil-name is empty")
      expect(True)
        name/nil.is-nil

    test("name with special characters")
      expect("@special-name")
        val n = "@special-name".new-name
        n.nameStem

    test("very long module path")
      expect(["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"])
        val long_mod = "a/b/c/d/e/f/g/h/i/j".new-module-name
        long_mod.split-module-name

    test("name with apostrophe")
      expect("x'")
        val n = "x'".new-name
        n.nameStem


fun main()
  run-tests(suite)