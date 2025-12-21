import compiler/common/nice
import compiler/common/id
import compiler/type/type
import compiler/kind/kind
import std/test
import std/data/linearmap

fun suite()
  group("nice creation and lookup")
    test("empty nice map returns formatted id")
      expect("\"0\"")
        val n : nice = LinearMap([])
        n.show(0)

    test("nice extend adds mapping")
      expect("myvar")
        val n : nice = LinearMap([])
        val n' = extend(n, 5, "myvar")
        n'.show(5)

    test("nice show returns original id if not in map")
      expect("\"10\"")
        val n : nice = LinearMap([])
        val n' = extend(n, 5, "x")
        n'.show(10)

    test("multiple mappings in nice map")
      expect("alpha")
        val n : nice = LinearMap([])
        val n' = extend(n, 1, "alpha")
        val n'' = extend(n', 2, "beta")
        n''.show(1)

    test("show retrievable value from nice map")
      expect("beta")
        val n : nice = LinearMap([])
        val n' = extend(n, 1, "alpha")
        val n'' = extend(n', 2, "beta")
        n''.show(2)

  group("nice-eff effect handler")
    test("niceEnv handler manages type variable names")
      expect("a")
        niceEnv
          val tv = TypeVar(0, kindStar, Meta)
          extend-nice(tv)
          get-nice(tv)

fun main()
  run-tests(suite)
