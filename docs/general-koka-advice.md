A few coding standards for working with Koka

1. Use copy syntax `obj(field=new-value)`.
2. Let the compiler infer effect rows with `_` as much as possible.
3. Don't try too hard to remove `div`. Divergence is an undecidable problem, and the compiler's dismissal is best effort.
4. Prefer subsystem scoped / system scoped effects. Use of `exn` etc, is useful at the top level and interacting with common std library functions, but a `log` / `error` effect that is specific to your library will be easier to use than to use `println` everywhere which is not handleable.
5. Understand and use static overloading and implicits to your advantage. In particular functions are statically overloaded on multiple arguments - so the compiler can distinguish same-named functions far more than in typical languages. Definitions (both local and global) can be qualified using a `fully/qualified/name`, `name` is the name being overloaded, and the other aspects are module / local qualifiers. Implicits similarly disambiguate based on name and then type at the caller. See the samples and tests for additional understanding.
6. Understand and use async. Again, see the samples and tests.
7. Understand and use effects. See samples, tests, named effects, scoped effects, and more.
