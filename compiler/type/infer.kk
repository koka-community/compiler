module compiler/type/infer

import compiler/common/range
import compiler/common/name
import compiler/common/name-prim
import compiler/common/name-collections
import compiler/common/syntax
import compiler/common/color-scheme
import compiler/common/failure
import compiler/common/unique
import compiler/common/message
import compiler/platform/config
import compiler/type/kind
import compiler/kind/kind
import compiler/kind/synonyms
import compiler/kind/newtypes
import compiler/kind/import-map
import compiler/type/type
import compiler/type/typevar
import compiler/type/assumption
import compiler/type/infgamma
import compiler/type/unify
import compiler/type/pretty
import compiler/type/operations
import compiler/syntax/syntax
import compiler/syntax/range-map
import compiler/core/core
import compiler/lib/pprint
import std/data/linearmap
import std/data/linearset
import std/data/sort
import std/core/undiv
import std/core/unsafe
import compiler/lib/core


pub fun remove-local-effect(ftp: ktype)
  match ftp.split-fun-scheme
    Just((foralls, args, eff, resTp)) -> 
      val (ls, tl) = eff.extract-ordered-effect
      quantify-type(foralls, TFun(args, ls.filter(_.label-name != nameTpLocal).foldr(tl, effect-extend), resTp))
    _ -> fail("type/infer/remove-local-effect: unexpected type: " ++ ftp.show)