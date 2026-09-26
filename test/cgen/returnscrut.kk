// Issue: https://github.com/koka-lang/koka/issues/644
fun main()
  println("Compiled")

type token
  Int

value struct token-iter<h>
  chars: vector<char>
  idx: ref<h, int>

fun token-iter/next(token-iter: token-iter<h>): <div, read<h>, write<h>> maybe<(int, token)>
  // Strange code below to work around issues with early returns in Koka 3.1.2.
  // (https://github.com/koka-lang/koka/discussions/643)

  // Skip whitespace
  val next-char0 =
    match Nothing
      Just((_idx, _c)) ->
        if True then
          return token-iter.next
        else
          Nothing
      Nothing -> Nothing
  val tmp = match next-char0
          Nothing -> return Nothing
          Just(c) -> c
  val (_char-idx, _char) = tmp
  Nothing
