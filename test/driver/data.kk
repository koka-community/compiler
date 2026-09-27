type color
  Red
  Green
  Blue

type nat
  Zero
  Succ(pred: nat)

type pair
  Pair(fst-val: color, snd-val: nat)

fun pick(c: color, x, y)
  match c
    Red -> x
    Green -> y
    Blue -> x

fun walk(n: nat)
  match n
    Zero -> 0
    Succ(m) -> walk(m)

fun swap(p: pair)
  match p
    Pair(a, b) -> Pair(a, b)

fun second(p: pair)
  match p
    Pair(_, b) -> b
