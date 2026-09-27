# Backtracking audit: why the port's parsing is ~3x upstream's

Warm builds are the port's only real remaining loss against upstream (4.1x on
`driver.kk`), and essentially all of it is interface PARSING -- ~26s of a 75s
warm build, at roughly 1MB/s. Both compilers parse the same bytes, allocate
comparable token lists, and build comparable results, so this audits the one
structural difference: **Parsec vs this parser's backtracking model**.

It is not "effects are slow" -- the same effectful code beats upstream on every
cold benchmark. And it is not allocation per se. It is HOW MANY backtrack points
we create, which is a design difference, plus what each one costs.

## Measured, one warm build of `compiler/compile/build.kk` (366 parses)

```
tokens          9,351,876
delimit        37,574,846     4.02 backtrack frames pushed PER TOKEN
undelimit      20,109,817
reset          17,465,029     1.87 actual rewinds PER TOKEN
```
46.5% of saved frames are used to rewind.

**CORRECTION (measured after the fact): backtracking is NOT the parse gap.**
Rewind COUNT is a bad proxy for cost -- what matters is tokens THROWN AWAY, and
almost every rewind here is 0-1 tokens deep:

```
tokens consumed     10,850,744
tokens thrown away     777,057    0.07 per token
total token-visits  11,627,801    1.07x the minimum
```

So the parser re-parses 7% of its input, not 190%. The "~2.9 visits per token"
first written here was wrong: it multiplied rewind count by nothing. Converting 7
interface-parser choice sites to non-backtracking cut rewinds 1.84 -> 1.52 per
token and moved the clock not at all.

`KOKA_PARSE_STATS=1` prints these per parse.

## Where the points come from

Parsec's `<|>` saves NOTHING: state is threaded immutably, and an alternative is
only tried if the previous one failed without consuming. `try` is the sole
backtracking construct, and upstream uses it sparingly:

| | upstream (`try`) | port (backtracking sites) |
|---|---|---|
| interface parser | **12** in 1106 lines | **84** in 903 lines |
| source parser | **25** in 3322 lines | **122** in 1402 lines |

The port's `parse-choices` calls `parse-maybe` -- a full save/restore -- for
EVERY alternative. It is `try p1 <|> try p2 <|> ...` where upstream wrote
`p1 <|> p2`. `compiler/core/parse.kk`, the warm hot path, uses the
non-backtracking `parse-choices-nb` **zero** times against 33 `parse-choices`.

## Most of those frames cannot ever be needed

`parse-token` PEEKS and only consumes on success:

```koka
fun parse-token(msg, f)
  val t = peek()
  match f(t)
    Just(a) -> next(); a          // consumes only here
    Nothing -> parse-error(...)   // consumes NOTHING
```

So an alternative that is a single-token test (`parse-keyword`,
`parse-special-id`, ...) leaves the position untouched when it fails, and its
saved frame is pure overhead. Sites like

```koka
parse-choices("assoc", [ {parse-keyword("infixl"); AssocLeft}
                       , {parse-keyword("infixr"); AssocRight}
                       , {parse-keyword("infix");  AssocNone} ])
```
need no backtracking whatsoever. Genuine multi-token lookahead
(`parse-try({(parse-visibility(), parse-type-sort())})`) is the minority -- and
is exactly where upstream writes `try`.

## What each point costs, even when it is needed

1. `delimit` allocates a 3-tuple `(msg, lexemes, pos)` plus a cons cell.
2. `parse-maybe`/`-nb`/`parse-try` each install a `with override` handler.
3. `undelimit`/`reset`/`took-input` verify the frame tag with a STRING COMPARE.
   `_platform_memcmp` is 44ms of self time in the warm profile. The tag is a
   debug aid; an int (or nothing) would do.
4. `parse-many` tags every iteration `"many " ++ kind` -- a string ALLOCATION per
   list element parsed.
5. `parse-keyword_` builds `"\"" ++ s ++ "\""` on every call, success or not.
6. `parse-delimited` exists only to add "When parsing X" context, which is off
   unless `KOKA_PARSE_CONTEXT=1` -- yet it still pushes a frame and installs a
   handler on every call.

## Where the time actually goes

Measured properly: an ICF-off profile of a build that does NOTHING but load all
186 interfaces (so the percentages are of parsing, not of a whole build).

| | share | of which memory ops |
|---|---|---|
| `compiler/syntax/lex` (scanner actions) | 23.2% | 42% |
| `std/core/hnd` (effect/handler machinery) | 23.2% | 38% |
| `compiler/core/parse` | 13.7% | 53% |
| `compiler/common/parse` | 12.5% | 44% |
| `compiler/common/name` | 7.0% | 37% |

alloc 5.0%, free 13.3%, refcount 22.5% -- 41% memory traffic overall, plus
`_platform_memmove` at 8.3% of self time.

Two things dominate, and neither is backtracking: **lexing (~30% with `lexer`
and `layout`) and the effect machinery (23%)**. The latter is the number of
effect OPERATIONS in the hot loop, not effects being slow in general -- the same
effectful code wins every cold benchmark. `parse-token` performs `ppeek` and then
`pnext` (two handler round-trips per accepted token), plus a `precord-expect` on
every failed alternative: 11.5M of those in one warm build.

An earlier note that "the lexer owns 0.6%" came from profiling a whole warm build
of a TINY target, where loading is a sliver of the run. On the real interface
load it is the largest single module.

## Recommended order

1. ~~Stop backtracking where nothing can be consumed.~~ DONE for 7 sites, and
   measured worthless: rewinds 1.84 -> 1.52 per token, no time change. Worth
   keeping only because it is what Parsec's `<|>` means, not as an optimisation.
2. **Make a needed frame cheap**: drop the string tag (int or none), and hoist
   the constant label strings (4, 5) out of the hot path.
3. **Make `parse-delimited` free when context is off** -- it is a no-op by
   default today except for its cost.
4. **Cut effect operations per token** -- the real lever, and where the 23% in
   `std/core/hnd` lives. `parse-token` is two handler round-trips (`ppeek` then
   `pnext`) for every accepted token where one would do, and `precord-expect` is
   another on every failed alternative.
5. **Lexing** is the other 30%. Untouched so far.
