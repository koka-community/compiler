import compiler/lib/pprint
import compiler/common/name
import compiler/common/range
import compiler/common/message
import compiler/common/color-scheme
import compiler/common/error
import compiler/platform/config
import compiler/kind/kind
import compiler/kind/infer-kind
import compiler/kind/infer-effect
import std/data/linear-set

// Unify
type unify-ctx
  Check(s: string, r: range)
  Infer(r: range)

effect unify-context
  val uctx: unify-ctx

fun unify(rng: range, k1: inf-kind, k2: inf-kind)
  val sk1 = subst(k1)
  val sk2 = subst(k2)
  match mgu(sk1, sk2)
    UnifyKindOk(sub') -> extend-ksub(sub')
    err ->
      kind-error(rng, err, sk1, sk2)

fun kind-error(rng: range, err: unify, k1: inf-kind, k2: inf-kind)
  val message = match err
    InfiniteKind -> "Invalid type (due to an infinite kind)"
    _ -> "Invalid type"
  val inferExtra =
    if k1.is-infkind-scope || k2.is-infkind-scope then
      [("hint".text, "scoped effects need a first type parameter annoted with kind \"::S\"".text)]
    else
      []
  val (rangeContext, expected, extra) =
    match uctx
      Check(msg, range) -> (range, "expected kind", [("because".text, msg.text)])
      Infer(range) -> (range, "expected kind", inferExtra)
  val [niceKind1, niceKind2] = nice-infkinds([k1, k2])
  add-error(rng, message.text |-| 
    table([
      ("type context".text, doc-from-range(rangeContext)),
      ("type".text, doc-from-range(rng)),
      ("inferred kind".text, niceKind2),
      (expected.text, niceKind1)
  ] ++ extra))


// MGU
value type unify
  UnifyKindOk(ksub: ksub)
  InfiniteKind
  NoMatch

fun mgu(k1': inf-kind, k2': inf-kind)
  match (k1', k2')
    // Constants
    (KIVar(id1), KIVar(id2)) | id1 == id2 -> UnifyKindOk(ksubEmpty)
    (KICon(k1), KICon(k2)) -> 
      if match-kind(k1, k2) then UnifyKindOk(ksubEmpty) else NoMatch
    (KIApp(k1, k2), KIApp(l1, l2)) ->
      match mgu(k1, l1)
        UnifyKindOk(sub1) ->
          match mgu(sub1 |-> k2, sub1 |-> l2)
            UnifyKindOk(sub2) -> UnifyKindOk(sub2 |-> sub1)
            err -> err
        err -> err
    // pull up KApp's
    (KICon(KApp(k1, k2)), KIApp(l1, l2)) ->
      mgu(KIApp(KICon(k1), KICon(k2)), KIApp(l1, l2))
    (KIApp(k1, k2), KICon(KApp(l1, l2))) ->
      mgu(KIApp(k1, k2), KIApp(KICon(l1), KICon(l2)))
    // unify variables
    (KIVar(id), k) -> unify-var(id, k)
    (k, KIVar(id)) -> unify-var(id, k)
    _ -> NoMatch

fun unify-var(id: int, k: inf-kind)
  if k.fkv.member(id) then InfiniteKind else UnifyKindOk(ksub-single(id, k))

fun match-kind(k1': kind, k2': kind)
  match (k1', k2')
    (KCon(c1), KCon(c2)) -> c1 == c2
    (KApp(k1, k2), KApp(l1, l2)) -> match-kind(k1, l1) && match-kind(k2, l2)
    _ -> False