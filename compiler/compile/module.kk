// Module loading for the mini Compile layer: locate and parse `.kki` core
// interface files for imported modules (transitively) and extract the
// definitions (gamma/kgamma/synonyms/newtypes) to seed checking a module.
module compiler/compile/module

import std/os/path
import std/os/file
import std/os/dir
import std/core/undiv
import compiler/common/name
import compiler/common/name-collections
import compiler/common/name-prim
import compiler/common/range
import compiler/common/syntax
import compiler/common/parse
import compiler/kind/kind
import compiler/kind/assumption
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/import-map
import compiler/type/type
import compiler/type/assumption
import compiler/core/core
import compiler/core/parse
import compiler/static/fixity-resolve
import compiler/core/borrowed
import std/data/rb-map

// the definitions imported from compiled module interfaces
pub struct definitions
  defs-gamma: gamma
  defs-kgamma: kGamma
  defs-synonyms: synonyms
  defs-newtypes: newtypes
  fixities: fixities = rb-map/empty()
  borrowed: borrowed = rb-map/empty()

pub fun defs-null(): definitions
  Definitions(assumption/empty, kgamma/empty, synonyms/empty, newtypes/empty)

// Load a module interface and (transitively) its imports from `.kki` files
// found in the given search directories. Returns the loaded cores by name.
// load modules transitively; also collects each interface's inline-section
// parser (applied later with the full gamma, upstream Compile/Module modInlines)
pub fun load-modules(search-dirs: list<path>, mods: list<name>, loaded0: name-map<core>)
  mods.foldl((loaded0, [])) fn((loaded, inlfs), nm)
    if loaded.contains-key(nm) then (loaded, inlfs)
    else match find-kki(search-dirs, nm)
      Nothing -> parse-error("cannot find compiled interface for module " ++ nm.show-plain ++ " (.kki)", range/null)
      Just(kki) ->
        val (c, mkInlines) = parse-core(kki)
        val loaded1 = loaded.set(nm, c)
        val (loaded2, inlfs2) = load-modules(search-dirs, c.imports.map(importName), loaded1.pretend-decreasing)
        (loaded2, Cons(mkInlines, inlfs ++ inlfs2))

pub fun find-kki(search-dirs: list<path>, nm: name): <fsys> maybe<path>
  val fname = (nm.module-name-to-path ++ ".kki").path
  fun probe(dir: path): <fsys> maybe<path>
    val p = dir / fname
    if p.is-file then Just(p)
    else Nothing
  search-dirs.filter-map(probe).head

// Extract the combined definitions of the loaded module cores
pub fun defs-from-modules(mods: list<core>): _ definitions
  defs-from-modules-g(mods.map(fn(c) (c, extract-gamma(data/is-value, False, c))))

// identical to `defs-from-modules` except the per-module gamma is supplied
// (cached on the bmodule) rather than extracted here -- every fold/union below
// is unchanged, so the resulting definitions are byte-identical
pub fun defs-from-modules-g(modgs: list<(core, gamma)>): _ definitions
  val mods = modgs.map(fst)
  Definitions(
    modgs.map(snd).type/assumption/unions,
    // upstream defsMerge folds with `kgammaUnionLeftBias g1 g2 =
    // unionLeftBias g2 g1` -- the LATER module's entries come FIRST in each
    // key's candidate list (visible in ambiguity hints, e.g.
    // static/wrong/alias1's "can refer to either" order)
    mods.map(core/extract-typedefs).foldl(rb-map/empty(), fn(acc, g) g.qname-map/union-left-bias(acc)),
    mods.map(core/extract-synonyms).foldl(synonyms/empty, synonyms/compose),
    mods.map(core/extract-newtypes).foldl(newtypes/empty, newtypes/compose),
    fixities-new(mods.flatmap(fn(c) c.fix-defs.map(fn(fd) (fd.def-name, fd.f)))),
    mods.foldl(rb-map/empty()) fn(b, c) c.core/extend(b))

// An import map where every loaded module maps to itself
pub fun import-map-from-modules(mods: list<name>): _ import-map
  mods.foldl(imports-empty) fn(im, nm)
    match im.extend(nm, nm)
      Just(im') -> im'
      Nothing -> im
