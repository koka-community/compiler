import compiler/kind/kind
import compiler/common/name
import compiler/common/name-collections
import compiler/core/core
import compiler/type/type
import compiler/common/syntax
import compiler/common/failure
import compiler/platform/config
import std/data/linearmap
import std/data/sort

alias kGamma = qname-map<type-name-info>;

type type-name-info
  TypeNameInfo(
    kind: kind,
    doc: string
  )

effect kGammaEff
  fun kgamma-extend(name: name, k: kind, d: string): ()
  fun kgamma-lookup(ctxt: name, name: name): lookup<(kind,string)>
  fun kgamma-lookupQ(name: name): maybe<type-name-info>
  fun kgamma-find(ctxt: name, name: name): (name, kind, string)
  fun kgamma-list(): list<(name, list<(name, type-name-info)>)>
  fun kgamma-filter(modName: name): kGamma

fun withKGamma(kg0: kGamma, f: () -> <kGammaEff,exn,comp-flags|e> a): <exn,comp-flags|e> a
  var kg := kg0
  with handler
    fun kgamma-extend(name: name, k: kind, d: string) kg := kg.extend(name, k, d)
    fun kgamma-lookup(ctxt, name: name) 
      match kg.lookup(ctxt, name)
        Found((n, tni)) -> Found((n, (tni.kind, tni.doc)))
        NotFound -> NotFound
        Ambiguous(names) -> Ambiguous(names)
    fun kgamma-lookupQ(name: name) kg.lookup-qualified(name)
    fun kgamma-find(ctxt: name, name: name) kg.find(ctxt, name)
    fun kgamma-list() kg.list.sort(?(<) = fn((n1,_), (n2, _)) n1.show < n2.show)
    fun kgamma-filter(modName: name) kg.filter(modName)
  f()

fun kgamma/new-nub(xs: list<(name,kind,string)>): <comp-flags,exn> kGamma
  xs.foldl(empty, fn(m,(n,k,d)) if m.contains-key(n) then m else m.insert(n,TypeNameInfo(k,d)))
fun kgamma/extend(kg: kGamma, name: name, k: kind, doc: string)
  kg.insert(name, TypeNameInfo(k, doc))
fun kgamma/find(kg: kGamma, ctxt: name, name: name)
  match kg.lookup(ctxt, name)
    Found((qn, TypeNameInfo(k, doc))) -> (qn, k, doc)
    _ -> fail("kind lookup failed")
fun kgamma/filter(kg: kGamma, modName: name)
  kg.filter-names(_ == modName)

val kgamma/empty:kGamma = LinearMap([])

fun core/extract-typedefs(c: core): <exn,comp-flags> kGamma
  c.typedefs.map(extract-typedefs).qname-map/unions

fun tdg/extract-typedefs(g: typedef-group): <exn,comp-flags> kGamma
  g.map(extract-typedefs).qname-map/unions

fun td/extract-typedefs(d: typedef): kGamma
  match d
    Synonym(syn-info) | syn-info.vis.is-public -> single(syn-info.name, TypeNameInfo(syn-info.kind, syn-info.doc))
    Data(dataInfo) | dataInfo.vis.is-public && !dataInfo.is-extend -> single(dataInfo.name, TypeNameInfo(dataInfo.kind, dataInfo.doc))
    _ -> kgamma/empty

// TODO: Pretty print