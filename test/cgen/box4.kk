
type reuse3
  Reuse3(a : pad, b : pad, c : pad)

type seq<a>
  Empty
  SUnit(a : a, b : pad, c : pad)
  More0(l : a, s : seq<a>, r : pad)

fun buncons(bs : seq<a>) : exn (a, reuse3, seq<a>)
  val (x, u3, s') = seq/uncons(bs)
  (x, u3, s')

fun seq/uncons(s : seq<a>) : exn (a, reuse3, seq<a>)
  match s
    SUnit(x, _, _) ->
      (x, Reuse3(Pad,Pad,Pad), Empty)
    More0(x, q, _) ->
      (x, Reuse3(Pad,Pad,Pad), q)

fun finger/uncons( q : seq<a> ) : pure maybe<(a,seq<a>)>
  match buncons(q)
    (x, _, q') -> Just((x, q'))

noinline val s = SUnit(1, Pad, Pad)

fun main()
  match finger/uncons(s)
    Just((x, _)) ->
      println(x)
    Nothing ->
      println(0)
