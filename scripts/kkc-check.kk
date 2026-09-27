// Round-trip gate: every interface the compiler writes must be readable by
// its own core parser -- INCLUDING the lazy inline section, where most
// printer/parser gaps hide (forall-dot, /# local qualifiers, local-val
// ranges were all inline-section bugs; parse-core alone reports such a cache
// as clean because mkInlines only runs on demand).
//
//   ./koka -e scripts/kkc-check.kk -- <cache-dir>
//
// Loads every .kkc/.kki in <cache-dir> (std included -- it is compiled from
// source into the same build directory), unions their gammas, then forces every module's inline
// section against that gamma. Exits 1 on any failure.
import std/os/path
import std/os/process
import std/os/dir
import std/os/env
import compiler/core/core
import compiler/core/parse
import compiler/core/inlines
import compiler/common/parse
import compiler/common/range
import compiler/common/name
import compiler/type/type
import compiler/type/assumption
import std/data/rb-map    // `list` on a name-map (extract-synonyms returns one)
import compiler/kind/synonyms
import compiler/compile/build
import compiler/compile/module
import compiler/common/syntax

pub fun main()
  val dirs = get-args()
  val dir = dirs.head.default(".koka/v3.2.3-self/clang-release").path
  val kkcs = dir.list-directory.filter(fn(p) p.string.ends-with(".kkc").is-just || p.string.ends-with(".kki").is-just)
  if kkcs.is-nil then
    println("kkc-check: no interfaces in " ++ dir.string)
    exit(1)
  // std compiles from source into the same build directory, so the listing
  // above already covers its interfaces.
  val kkis: list<path> = []

  // pass 1: declarations, parsed TWICE. Round 1 with an empty synonym env
  // harvests every module's own synonyms; round 2 re-parses seeded with the
  // full union -- the same information resolve-module supplies from loaded
  // dependencies -- so the audit below tests the real reader configuration
  // without needing dependency ordering (a directory listing has none).
  var decl-failures := 0
  var harvest : synonyms := synonyms/empty
  (kkis ++ kkcs).foreach fn(k)
    match try({parse-iface(k)})
      Error(_) -> ()   // reported in round 2
      Ok((c, _)) -> harvest := harvest.synonyms/compose(c.core/extract-synonyms)
  var mods : bmodules := rb-map/empty()
  // Inline sections are resolved eagerly at load time now, so ModIface carries a
  // plain list. Keep the unresolved closures aside: build's force-inlines
  // deliberately swallows parse failures (self-healing recompile), which would
  // make this gate blind -- pass 2 forces them strictly instead.
  var mks := []
  (kkis ++ kkcs).foreach fn(k)
    match try({parse-iface(k, harvest)})
      Error(exn) ->
        println("FAIL decl " ++ k.string ++ ": " ++ exn.message)
        decl-failures := decl-failures + 1
      Ok((c, mk)) ->
        mods := mods.set(c.coreName, ModIface(c, [], extract-gamma(data/is-value, False, c)))
        mks := Cons((c.coreName, mk), mks)

  // pass 2: force every inline section against the full gamma.
  val gamma0 = defs-of(mods.list).defs-gamma
  var inline-failures := 0
  mks.reverse.foreach fn((nm, mk))
    match try({force-strict(mk, gamma0, nm.show-plain)})
      Error(exn) ->
        println("FAIL inline " ++ nm.show-plain ++ ": " ++ exn.message)
        inline-failures := inline-failures + 1
      Ok(_) -> ()

  // pass 3: synonym-fidelity audit. A type that mentions a SYNONYM by name
  // must arrive as TSyn (or be expanded); a bare TCon whose name is a known
  // synonym will reach backend passes that look it up as a data type and
  // fail (Core.Parc.getDataDefInfo: cannot find type). Walk every gamma
  // entry's type and flag such TCons with their module of origin.
  val syn-names = mods.list.flatmap(fn((_, m)) m.bmod/core.extract-synonyms.list.map(fst))
  var tcon-failures := 0
  mods.list.foreach fn((nm, m))
    val bad = m.bmod/gamma.assumption/list.flatmap fn((qnm, info))
      val leaks = info.typ.tcons-in.filter(fn(c) syn-names.any(fn(sn) sn == c))
      if leaks.is-nil then [] else [(qnm, leaks)]
    bad.foreach fn((qnm, leaks))
      println("FAIL tcon-syn " ++ nm.show-plain ++ ": " ++ qnm.show-plain
              ++ " mentions synonym(s) as TCon: " ++ leaks.map(show-plain).join(", "))
      tcon-failures := tcon-failures + 1

  val total = kkcs.length + kkis.length
  println("kkc-check: " ++ (total - decl-failures).show ++ "/" ++ total.show ++ " decls, "
          ++ (mods.list.length - inline-failures).show ++ "/" ++ mods.list.length.show ++ " inline sections")
  println("kkc-check: " ++ tcon-failures.show ++ " synonym-as-TCon leaks")
  if decl-failures + inline-failures + tcon-failures > 0 then exit(1)

// All TCon names appearing anywhere in a type.
fun tcons-in(tp: ktype): div list<name>
  match tp
    TCon(TypeCon(nm)) -> [nm]
    TVar(_) -> []
    TApp(t, ts) -> t.tcons-in ++ ts.flatmap(tcons-in)
    TFun(args, eff, res) -> args.flatmap(fn((_, t)) t.tcons-in) ++ eff.tcons-in ++ res.tcons-in
    TForAll(_, t) -> t.tcons-in
    TSyn(_, ts, t) -> ts.flatmap(tcons-in) ++ t.tcons-in

fun force-inlines(mk: (gamma) -> <div,exn,ndet,parse-error> list<inline-def>, g: gamma): _ ()
  with handler
    final ctl parse-error(e: string, r: range)
      throw(r.show ++ ": " ++ e)
  val _ = mk(g)
  ()

// Resolve an inline section, turning a parse-error into a throw so the gate
// sees it (build's force-inlines returns [] instead, on purpose).
fun force-strict(mk, g: gamma, nm: string)
  with handler
    final ctl parse-error(e: string, r: range)
      throw(nm ++ " " ++ r.show ++ ": " ++ e)
  mk(g)

fun parse-iface(k: path, syns0: synonyms = synonyms/empty)
  with handler
    final ctl parse-error(e: string, r: range)
      throw(k.string ++ " " ++ r.show ++ ": " ++ e)
  parse-core(k, syns0 = syns0)
