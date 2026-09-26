type nat
  Zero
  Succ(pred: nat)

fun walk(n: nat)
  match n
    Zero -> 0
    Succ(m) -> walk(m)
