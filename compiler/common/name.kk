//----------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//----------------------------------------------------------------------------
// Updated as of 7/23/26 Commit: 045e2dc

module compiler/common/name

import compiler/common/color-scheme
import compiler/common/range
import compiler/common/failure
import std/pretty/printer
import compiler/lib/pprint
import std/core/undiv
import std/num/int32
import std/data/rb-map


// | Names defined by the user.
// Uses a hash to speed up comparisons. The hash is constructed
// such that they can be compared too. (h1 > h2 => name1 > name2)
// The hash is case-insensitive, just like comparisons on names.
// Use 'name-case-equal' for case-sensitive comparisons.
//
// Notes:
// - We use `name/local` for the locally qualified name in the module (`int/show`)
// - The stem is the plain name and operators are not parenthesized (`++`)
// - The stem should always be a valid identifier; this means that an operator
//   must keep ending with symbols. When hiding names etc, we can get names like `@temp12-++` for example
// - We assume that users cannot start identifiers with an `@`. (We may in the future allow
//   user identifiers to contain `@` though after the first character.)
// - Plain module names have an empty local qualifier and stem
// - If there is a local qualifier, the stem cannot be empty
pub struct name
  pub nameModule: string // module name (`std/core`)
  pub hashModule: int
  pub nameLocalQual: string // local qualifier (`int`)
  pub hashLocalQual: int
  pub nameStem: string  // the stem (`show`)
  pub hashStem: int
  // strong case-insensitive hash of nameStem; equality filter + `nkey` bucket
  pub keyStem: int32

// names
pub alias names = list<name>

fun join(m: string, n: string): string
  if m == "" then n
  elif n == "" then m
  else m ++ "/" ++ n

fun joins(ms : list<string>): string
  ms.foldr("", join)

pub fun name/local(n: name): string
  join(n.nameLocalQual, n.nameStem)

pub fun name-case-equal(n1: name, n2: name): bool
  n1.local == n2.local && 
    n1.split-module-name.reverse.zipwith(n2.split-module-name.reverse, (==)).and

pub fun name-case-equal-prefix-of(n1: name, n2: name): bool
  n1.local.is-prefix-of(n2.local) &&
    n1.split-module-name.reverse.zipwith(n2.split-module-name.reverse, (==)).and

pub fun name-case-overlap(n1: name, n2: name): bool
  !n1.name-case-equal(n2) && n1.is-same-namespace(n2)

fun name-case-overlap-prefix-of(n1: name, n2: name): bool
  !n1.name-case-equal-prefix-of(n2) && n1.is-same-namespace(n2)

// Checks whether both names are in the same namespace, ie. constructors or not
pub fun is-same-namespace(n1: name, n2: name): bool
  n1.is-constructor-name == n2.is-constructor-name

// ASCII case-insensitive compare with no allocation. `cmp(a.to-lower, b.to-lower)`
// lowers (allocating) both sides on every call; this is one of the hottest functions in
// the compiler. `kk_string_icmp_borrow` folds with the SAME `kk_ascii_tolower`
// that `kk_string_to_lower` uses -- which is ASCII-only, byte-wise over UTF-8 --
// so it is equivalent by construction. A microbenchmark over 2M comparisons of
// prefix-sharing generated names agreed on every result and ran ~3x faster
// (160ms -> 56ms).
extern str-icmp(^s1: string, ^s2: string): int
  c  inline "kk_integer_from_int(kk_string_icmp_borrow(#1,#2,kk_context()),kk_context())"
  js inline "((#1).toLowerCase() < (#2).toLowerCase() ? -1 : ((#1).toLowerCase() > (#2).toLowerCase() ? 1 : 0))"

// Case-insensitive FNV-1a over the FULL stem, computed ONCE at construction.
//
// The three stored hashes are only the first FOUR characters, because
// `name/cmp` needs `h1 < h2 => name1 < name2` for `Ord Name` parity. That makes
// them near-useless as equality filters: every `compiler/...` module hashes to
// "comp", so 72.6% of comparisons over a real 44-module population fell through
// to `str-icmp`. Equality has no ordering obligation, so it can use a strong
// hash -- 0 collisions on that same population.
//
// `int32`, not `int`/`int64`: a microbenchmark over 8.8M triple comparisons
// measured int 52ms / int32 34ms / int64 46ms. Koka's `int` is a tagged bigint
// (comparison is a call) and `int64` cannot be tag-packed inside tuples.
//
// `kk_ascii_tolower` is static inside kklib's string.c, so its fold is
// replicated here verbatim -- byte-wise over UTF-8, matching `kk_memicmp`, so
// two names equal under `str-icmp` always hash alike.
extern import
  c include-inline "static int32_t kk_name_ikey(kk_string_t s, kk_context_t* ctx) {\n  kk_ssize_t len; const uint8_t* p = kk_string_buf_borrow(s, &len, ctx);\n  uint32_t h = 2166136261u;\n  for (kk_ssize_t i = 0; i < len; i++) {\n    uint8_t c = p[i]; c = (c >= 'A' && c <= 'Z' ? (uint8_t)(c - 'A' + 'a') : c);\n    h ^= (uint32_t)c; h *= 16777619u;\n  }\n  return (int32_t)(h & 0x7FFFFFFFu);\n}"

extern str-ikey(^s: string): int32
  c  inline "kk_name_ikey(#1,kk_context())"
  js inline "(function(s){var h=2166136261;for(var i=0;i<s.length;i++){var c=s.charCodeAt(i);if(c>=65&&c<=90)c+=32;h=(h^c)>>>0;h=Math.imul(h,16777619)>>>0;}return (h&0x7FFFFFFF)|0;})(#1)"

// Byte length, O(1) and non-allocating (`kk_string_len_borrow` reads the
// header). Only sound as an EQUALITY pre-filter, never for ordering: byte
// length says nothing about lexicographic order, but `kk_ascii_tolower` maps
// bytes to bytes, so two names equal ignoring ASCII case must have equal byte
// length. A mismatch is therefore a definitive "not equal".
extern str-len(^s: string): int
  c  inline "kk_integer_from_ssize_t(kk_string_len_borrow(#1,kk_context()),kk_context())"
  js inline "(#1).length"

fun icmp-order(s1: string, s2: string): order
  val r = str-icmp(s1, s2)
  if r < 0 then Lt elif r > 0 then Gt else Eq

fun lower-cmp(n1: name, n2: name): order
  match icmp-order(n1.nameModule, n2.nameModule)
    Eq -> match icmp-order(n1.nameLocalQual, n2.nameLocalQual)
      Eq -> icmp-order(n1.nameStem, n2.nameStem)
      lg -> lg
    lg -> lg

fun string/cmp-lower(s1: string, s2: string): order
  slice/cmp-lower(s1.slice,s2.slice)

fun slice/cmp-lower(s1: sslice, s2: sslice): order
  match (s1.next, s2.next)
    (Just((c1, r1)), Just((c2, r2))) -> 
      match c1.to-lower.cmp(c2.to-lower)
        Eq -> slice/cmp-lower(r1.pretend-decreasing, r2)
        lg -> lg
    (Just, _) -> Gt
    (_, Just) -> Lt
    (_, _) -> Eq

pub fun name/(==)(n1: name, n2: name): bool
  // NOTE: upstream has a hash-consistency `assertion` here that GHC compiles
  // out in release builds. The port's strict `assert` built FOUR
  // fully-explicit name strings on every call (message + condition) -- this
  // is the hottest function in the compiler, and that dominated whole-module
  // profiles (kk_bytes_cat/show-fully-explicit in lib/time*). Drop it.
  //
  // `hash` is only the FIRST FOUR characters (it must stay order-preserving for
  // `Ord Name` parity), so it barely discriminates module names: every
  // `compiler/...` module hashes to "comp" and every `std/...` to "std/". In a
  // `bmodules` scan that rejects almost nothing and each comparison falls
  // through to three `str-icmp` calls -- 5% of the whole compile sat in
  // `kk_memicmp`. Byte length costs O(1), needs no allocation, and is a sound
  // reject for case-insensitive equality (see `str-len`), so test it first.
  // `keyStem` first: one int32 compare, and a near-perfect discriminator (0
  // collisions over the real module population), so the three tagged-bigint
  // hash compares and the string work below almost never run.
  val eq = int32/(==)(n1.keyStem, n2.keyStem)
        && n1.hashStem == n2.hashStem && n1.hashModule == n2.hashModule && n1.hashLocalQual == n2.hashLocalQual
  eq && str-len(n1.nameStem) == str-len(n2.nameStem)
     && str-len(n1.nameModule) == str-len(n2.nameModule)
     && str-len(n1.nameLocalQual) == str-len(n2.nameLocalQual)
     && n1.lower-cmp(n2) == Eq

val nameEq = fn(n1: name, n2: name) n1 == n2

pub fun (!=)(n1: name, n2: name): bool
  !(n1 == n2)

pub fun name/cmp(n1: name, n2: name): order
  // Compare module, stem name, and then local name for dependencies
  match n1.hashModule.cmp(n2.hashModule)
    Eq -> match n1.hashStem.cmp(n2.hashStem)
      Eq -> match n1.hashLocalQual.cmp(n2.hashLocalQual)
        Eq -> n1.lower-cmp(n2)
        lg -> lg
      lg -> lg
    lg -> lg

// Effects compare by name first, then by local qualifier, then by module name.
// Labels are name@module, so if a name looks like name-x@module and name@module, we
// need to compare @ and - (which is what the runtime does).
//
// Unlike `name/cmp` above, this order is LOAD-BEARING: it fixes the layout of the
// evidence vector, so it has to agree both with upstream `labelNameCompare` and with
// the runtime's own `kk_string_cmp_borrow` over the htag strings. `name/cmp` compares
// hashes first because any total order will do for a map key; doing that here orders
// labels essentially arbitrarily and yields static evidence indices that do not match
// the vector the runtime actually builds.
pub fun label-cmp(n1: name, n2: name): order
  match (n1.nameStem ++ "@").cmp-lower(n2.nameStem ++ "@")
    Eq -> match string/cmp(n1.nameLocalQual, n2.nameLocalQual)
      Eq -> string/cmp(n1.nameModule, n2.nameModule)
      lg -> lg
    lg -> lg

fun stem-is-equal(n1 : name, n2 : name): bool
  n1.hashStem == n2.hashStem && n1.nameStem == n2.nameStem

fun is-id-char(c: char): bool
  c.is-alpha || c.is-digit || c == '_' || c == '-' || c == '@'

fun is-id-start-char(c: char): bool
  c.is-alpha || c == '_' || c == '@'

fun is-id-end-char(c: char): bool
  c != '-' && (c.is-id-char || c == '\'')

fun is-symbol-id(s: string): bool
  s != "" && 
    // The default cases shouldn't happen because of the check above
    (s.head-char.map(!_.is-id-start-char).default(False) ||
     s.last(1).next.map(!_.fst.is-id-end-char).default(False))

fun wrap-id(s: string): string
  if is-symbol-id(s) then "(" ++ s ++ ")" else s

pub fun name/show-name(Name(m, _, l, _, n, _, _): name, explicitLocalQualifier: bool): string
  val ln = l.join(n.wrap-id)
  if m == "" then ln 
  elif ln == "" then m
  else m ++ (if explicitLocalQualifier && l != "" then "/#" else "/") ++ ln

pub fun show-fully-explicit(Name(m, _, l, _, n, _, _): name): string
  val ln = l.join(n.wrap-id)
  if m == "" then "#" ++ ln
  elif ln == "" then m
  else m ++ "/#" ++ ln

pub fun show-explicit(n: name): string
  n.show-name(True)

pub fun show-plain(n: name): string 
  join(n.nameModule, join(n.nameLocalQual, n.nameStem))

pub fun name/show(n: name): string
  n.show-explicit()

// An implicit parameter must print with its `?` sugar: written out as its raw
// stem (`@implicit/a/show`) it is no longer an implicit parameter when the
// source is read back, so generated code -- the code-action definitions in
// particular -- would silently lose the implicit and require explicit passing.
// `pretty-name` already does this for the coloured printer; this is the plain
// one the syntax pretty-printer uses.
pub fun pretty(n: name): doc
  val s = n.show
  val pre = implicit-namespace ++ "/"
  if s.starts-with(pre).bool
    then ("?" ++ s.list.drop(pre.count).string).text
    else s.text

fun pretty-name-ex(Name(m, _, l, _, n, _, _): name, lsep: string, cs: colorScheme): doc // explicit /# if needed
  val ln = join(l, n.wrap-id)
  if m == "" then ln.text
  else 
   (m.text |.| (if ln.is-empty then pprint/empty elif l.is-empty then "/".text else lsep.text)).color(cs.colorModule)
           |.| ln.text

pub fun pretty-name(nm: name, cs: colorScheme): _ doc // not explicit /#
  if nm.is-implicit-param-name then "?".text |.| nm.from-implicit-param-name.requalify-locally.pretty-name-ex("/", cs)
  else nm.pretty-name-ex("/", cs)

pub fun pretty-core-name(nm: name, cs: colorScheme): doc // explicit /# if needed
  nm.pretty-name-ex("/#", cs)

pub fun pretty-local-name(Name(_, _, l, _, n, _, _): name): doc
  if l.is-empty then n.text else join(l, n.wrap-id).text

pub fun pretty-full-name(Name(m, _, l, _, n, _, _): name): doc
  join(m, join(l, n.wrap-id)).text

pub fun show-tupled(Name(m, _, l, _, n, _, _): name): string
  "(" ++ m ++ "," ++ l ++ "," ++ n ++ ")"

fun tupled/read(s: string): exn name
  val s' = s.slice.drop(1).extend(-1).string // Drop ()
  val Cons(m, Cons(l, Cons(n, Nil))) = s'.split(",")
  fun unquote(x: string): string
    if x.starts-with("\"").bool && x.ends-with("\"").bool
      then x.slice.drop(1).extend(-1).string
      else x
  new-locally-qualified(m.unquote, l.unquote, n.unquote)

pub fun qualified/read(s: string): _ name
  if s.starts-with("(").bool then tupled/read(s)
  else s.read-qualified-name

pub fun new-name(s: string): name
  new-qualified("", s)

pub fun new-module-name(s: string): name
  new-qualified(s, "")

pub fun new-qualified(mod: string, name: string): name
  new-locally-qualified(mod, "", name)

pub fun new-locally-qualified(m: string, l: string, n: string): name
  Name(m, m.hash, l, l.hash, n, n.hash, n.str-ikey)

// The hash function:
//  1) can be compared: h1 < h2  => name1 < name2 && h1 > h2 => name1 > name2
//  2) assumes 32 bit integers and no characters in strings >= \x128
//  3) is case in-sensitive (ie. does tolower first)
// The hash is done taking the first 4 characters. This is of course a
// terrible hash but we use it mostly to speed up *comparisons* for the nameMap
fun hash(s: string)
  if s.is-empty then 0
  else
    // upstream pads with '\0' (`take 4 (s ++ "\0\0\0\0")`), NOT '_' -- '_'
    // (95) sorts ABOVE digits/'-'/'/' so e.g. `st` vs `st2` compared
    // reversed relative to upstream's Ord Name
    val sn = (s.to-lower.list.map(fn(c) c.int) ++ [0,0,0,0]).take(4)
    // upstream: `foldl (\h c -> h*256 + fromEnum c) 0` -- the accumulator is
    // the FIRST parameter. The previous lambda had the parameters swapped
    // (`fn(c, h) h*256 + c` computes elem*256 + acc), making the hash
    // last-char-dominant so `name/cmp`'s hash-first ordering disagreed with
    // upstream's Ord Name (e.g. `std/core/console` sorted BELOW
    // `scratchpad/...`, breaking effect re-aliasing's subset walk).
    sn.foldl(0, fn(h, c) { h * 256 + c})

fun name-map-stem(Name(m, hm, l, hl, n, _, _): name, f: (string) -> e string): e name
  val n' = f(n)
  Name(m, hm, l, hl, n', n'.hash, n'.str-ikey)

pub fun read-qualified-name(s0: string): _ name
  if s0.starts-with("?").bool then s0.slice.drop(1).string.read-qualified-name.requalify-locally.to-implicit-param-name
  else
    fun split-qual-id-rev(rs: list<char>): (string, string)
      val (rid, rqual) = rs.span(_ != '/')
      match rqual
        Cons('/', rs1) -> (rs1.reverse.string, rid.reverse.string)
        _ -> ("", rid.reverse.string)
    fun split-id-name-rev(rs: list<char>): _ (string, string, string)
      val (rid, rest) = rs.span(_ != '#')
      match rest
        Cons('#', Cons('/', rs2)) ->
          val (qual, id) = rid.split-qual-id-rev
          (rs2.reverse.string, qual, id)
        Nil ->
          val (qual, id) = rid.split-qual-id-rev
          (qual, "", id)
        _ -> failure/fail("Name split-id-name-rev: illegal locally qualified name: " ++ rs.reverse.string)
    fun split-name(s: string): _ (string, string, string)
      match s.list.reverse
        Cons(')', rest) ->
          val (rop, rest2) = rest.span(_ != '(')
          match rest2
            Cons('(', rs2) ->
              val (qual, lqual, id) = rs2.split-id-name-rev
              (qual, lqual, id ++ rop.reverse.string)
            _ -> failure/fail("Name split-name: unmatched parenthesis in name: " ++ s)
        rs -> rs.split-id-name-rev
    val (q, lq, id) = s0.split-name
    new-locally-qualified(q,lq,id)

pub fun is-module-name(n: name): bool
  n.nameStem == ""

pub fun is-qualified(n: name): bool
  n.nameModule != ""

pub fun is-locally-qualified(n): bool
  n.nameLocalQual != ""

pub fun is-symbol-name(n: name): bool
  n.nameStem.is-symbol-id

pub fun is-constructor-name(n: name): bool
  match n.nameStem.slice.next
    Just((c, _)) | c.is-upper -> True
    Just(('@', r)) -> 
      match r.next
        Just((c, _)) | c.is-upper -> True
        _ -> False
    _ -> False

pub fun un-wildcard(n: name): name
  n.name-map-stem fn(stem)
    match stem.list
      Cons('@', Cons('_', rest)) -> "@wild" ++ rest.drop-while(fn(c) c == '_').string
      Cons('_', rest) -> "wild" ++ rest.drop-while(fn(c) c == '_').string
      _ -> stem

pub fun is-wildcard(n: name): bool
  match n.nameStem.slice.next
    Just(('_', _)) -> True
    Just(('@', r)) -> r.next.map(fn((c, _)) c == '_').default(False)
    _ -> False

pub fun name/is-eta-hole(n: name): bool
  is-wildcard(n)

pub fun is-hidden-name(n: name): bool
  n.nameStem.starts-with("@").bool

pub fun missing-qualifier(current-mod: name, n: name, qname: name): string
  val missing0 = qname.show-plain.list.reverse.drop(n.show-plain.count).reverse.string
  val standard = [current-mod.show, "std/core/types", "std/core/hnd", "std/core"]
  val missing = 
        match standard.filter(fn(std) (std ++ "/").is-prefix-of(missing0))
          Cons(std, _) -> missing0.list.drop(std.count + 1).string
          _ -> missing0
  if missing.starts-with(implicit-namespace ++ "/").bool then "?" ++ missing.list.drop(implicit-namespace.count + 1).string
  else missing

pub val name/nil = "".new-name

pub fun is-nil(Name(m, _, _, _, n, _, _)): bool
  n == "" && m == ""

pub fun qualify(a: name, b: name): name
  match (a, b)
    (Name(m, hm, _, 0, _, 0, _), Name(_, 0, l, hl, n, hn, kn)) -> Name(m, hm, l, hl, n, hn, kn)
    (Name(m1, _, _, 0, _, 0, _), name as Name(m2)) | m1 == m2 -> name
    _ ->
      trace("Cannot use qualify on qualified names " ++ a.show-fully-explicit ++ ", " ++ b.show-fully-explicit)
      new-name("")

pub fun unqualify(Name(_, _,l, hl, n, hn, kn)): name
  Name("", 0, l, hl, n, hn, kn)

pub fun qualifier(Name(m, hm)): name
  Name(m, hm, "", 0, "", 0, "".str-ikey)

pub fun name-as-module-name(n: name): name
  new-module-name(join(n.nameModule, join(n.nameLocalQual, n.nameStem)))

pub fun qualify-locally(nl: name, n: name): exn name
  match nl
    Name(l, _, _, 0, _, 0, _) ->
      new-locally-qualified(n.nameModule, join(l, n.nameLocalQual), n.nameStem)
    _ -> failure/fail("common/name/qualify-locally: illegal qualification: " ++ nl.show-explicit ++ ", " ++ n.show-explicit)

// Move the module qualifier to the local qualifier
pub fun requalify-locally(n: name): name
  if n.nameModule == "" then n else new-locally-qualified("", join(n.nameModule, n.nameLocalQual), n.nameStem)

pub fun qualify-unpacked(pname: name, fname: name)
  qualify-locally(pname.from-implicit-param-name.name-as-module-name, fname)

// Only keep the stem
pub fun unqualify-full(n: name): name
  Name("", 0, "", 0, n.nameStem, n.hashStem, n.keyStem)

// Full qualifier: module + local qualifier
pub fun full-qualifier(n: name): string
  n.unqualify-locally.nameModule

// Add the local qualifier to the module qualifier
pub fun unqualify-locally(n: name): name
  if n.nameLocalQual == "" then n else new-qualified(join(n.nameModule, n.nameLocalQual), n.nameStem)

pub fun unqualify-as-module-name(n: name): name
  new-module-name(join(n.nameModule, n.nameLocalQual))

// Module paths
pub fun split-module-name(n: name): list<string>
  if n.nameModule.is-empty then [] else n.nameModule.split("/")

pub fun unsplit-module-name(l: list<string>): name
  l.join("/").new-module-name

pub fun merge-common-path(n1: name, n2: name): name
  fun merge(l1: list<string>, l2: list<string>): list<string>
    match (l1, l2)
      (Cons(m, ms), Cons(n, ns)) -> 
        if m == n && ms.zipwith(ns, _ == _).all(id) then
          Cons(m, ms) ++ ns.drop(ms.length)
        else
          Cons(m, merge(pretend-decreasing(ms), Cons(n, ns)))
      (Cons(m, ms), ns) -> Cons(m, merge(pretend-decreasing(ms), ns))
      (_, ns) -> ns
  val ns = n2.split-module-name
  val ms = n1.split-module-name
  val new = ms.merge(ns).unsplit-module-name
  new

pub fun split-local-qual-name(n: name): list<string>
  if n.nameLocalQual.is-empty then [] else n.nameLocalQual.split("/")

pub fun is-in-special-namespace(n: name, ns: string): bool
  match n.split-local-qual-name
    Cons(first) -> first == ns
    _ -> False

pub fun is-in-default-namespace(n: name): bool
  n.is-in-special-namespace("default")

pub fun is-in-wrong-namespace(n: name): bool
  n.is-in-special-namespace("wrong")

// Remove the common module prefix of `mname` from `n`
pub fun remove-common-prefix(mname: name, n: name): name
  val ns = n.split-module-name
  val ms = mname.split-module-name
  val common = zip(ns, ms).take-while(fn((a, b)) a == b).length
  val ns' = ns.drop(common)
  if ns'.is-nil then n
  else qualify(ns'.unsplit-module-name, n.unqualify)

pub fun split-name(n: name): list<string>
  (n.split-module-name ++ n.split-local-qual-name ++ [n.nameStem]).filter(fn(x) x != "")

pub fun to-constructor-name(n: name): name
  n.name-map-stem fn(stem)
    match stem.list
      Cons('@', Cons(c, cs)) -> Cons('@', Cons(c.to-upper, cs)).string // keep hidden names hidden
      Cons(c, cs) -> Cons(c.to-upper, cs).string
      _ -> stem

pub fun to-var-name(n: name): name 
  fun to-lowers(l: list<char>): list<char>
    match l
      Cons(c, cs) | c.is-upper -> Cons(c.to-lower, to-lowers(cs))
      _ -> l
  n.name-map-stem fn(stem)
    match stem.list
      Cons('@', cs) -> Cons('@', cs.to-lowers).string // keep hidden names hidden
      cs -> cs.to-lowers.string

pub fun to-handler-con-name(n: name): name
  make-hidden-name("Hnd", n)

pub fun is-handler-con-name(n: name): bool
  n.hidden/starts-with("Hnd")

pub fun name/starts-with(n: name, s: string): bool
  n.nameStem.starts-with(s).bool

// append two identifier strings making sure dashes are correct
fun dash-append(s1: string, s2: string): string
  val pre = match s1.list
    Cons('-') -> "x" ++ s1
    _ -> s1
  match (pre.list.reverse, s2.list)
    (Cons('-'), Cons(c)) | !(c.is-alpha || c == '@') -> pre ++ "x" ++ s2
    _ -> pre ++ s2

pub fun prepend(s: string, n: name): name
  if s == "" then n else
    n.name-map-stem fn(stem)
      fun unhide(x: string): string
        match x.list
          Cons('@', t) -> t.string
          _ -> x
      match s.list
        Cons('@', Cons(c)) | c.is-digit -> dash-append("@x" ++ s.list.tail.string, stem.unhide) // make sure it stays lowercase
        Cons('@') -> dash-append(s, stem.unhide) // no need for duplicate '@'s
        _ -> match stem.list
          Cons('@') -> "@" ++ dash-append(s, stem.unhide) // keep hidden
          _ -> dash-append(s, stem)

pub fun prepend-raw(s: string, n: name): name
  n.name-map-stem fn(stem) s ++ stem

pub fun postpend-raw(n: name, post: string): name
  n.name-map-stem fn(stem) stem ++ post

pub fun postpend(n: name, post: string): name
  if n.is-symbol-name then
    // we must always end in symbols for operators so postpend inserts before the symbols
    prepend(post, n)
  else n.name-map-stem fn(stem)
    val (idChars, finalChars) = stem.list.reverse.span(fn(c) c == '?' || c == '\'')
    (idChars ++ post.list.reverse ++ finalChars).reverse.string

pub fun type-qualified-name(typeName : name, stem : string): exn name
  typeName.qualifier.qualify(typeName.unqualify.name-as-module-name.qualify-locally(stem.new-name))

pub fun type-qualified-name-of(typeName : name, stem: name): exn name
  typeName.type-qualified-name(stem.nameStem)

fun type-qualified-get-type-name(nm : name)
  match nm.split-local-qual-name.reverse
    Cons(m, ms) -> nm.nameModule.new-locally-qualified(ms.reverse.joins,m)
    [] -> failure/fail("common/name type-qualified-get-type-name: no locally qualified type: " ++ nm.show)

// Hidden names
fun make-hidden(n: name): name
  prepend("@", n)

pub fun make-hidden-name(s: string, n: name): name
  prepend("@" ++ s ++ "-", n)

fun unmake-hidden(n: name, pre: string): exn name
  n.name-map-stem fn(stem)
    if stem.starts-with("@" ++ pre ++ "-").bool then
      stem.slice.drop(2 + pre.count).string
    else failure/fail("common/name/unmake-hidden: expecting hidden name prefixed with @" 
              ++ pre ++ "-, but found: " ++ n.show)

pub fun new-hidden-name-ex(base: string, s: string): name
  make-hidden-name(base, s.new-name)

pub fun new-hidden-name(base: string): name
  make-hidden(base.new-name)

pub fun to-unique-name(i: int, n: name): name
  n.postpend("@" ++ i.show)

pub fun to-hidden-unique-name(i: int, pre: string, n: name): name
  make-hidden-name(pre, to-unique-name(i, n))

pub fun make-fresh-hidden-name(s: string, n: name, r: range)
  val idFromPos = fn(p) -> "-l" ++ p.line.show ++ "-c" ++ p.col.show
  make-hidden-name(s, n.postpend(r.start.idFromPos))

pub fun hidden/starts-with(n: name, pre: string): bool
  n.nameStem.starts-with("@" ++ pre).bool ||
    n.name/starts-with("@" ++ pre ++ "-")

// Various special names

pub fun new-padding-name(i: int): name
  new-hidden-name-ex("padding", i.show)

pub fun is-padding-name(n: name): bool
  n.hidden/starts-with("padding")

pub fun new-cctx-name(s: string): name
  new-hidden-name-ex("cctx", s)

pub fun is-cctx-name(n: name): bool
  n.hidden/starts-with("cctx")

pub fun new-field-name(i: int): name
  new-hidden-name-ex("field", i.show)

pub fun is-field-name(n: name): bool
  n.hidden/starts-with("field")

pub fun new-implicit-typevar-name(i: int): name
  new-hidden-name-ex("tv", i.show)

pub fun is-implicit-typevar-name(n: name): bool
  n.hidden/starts-with("tv")

pub fun new-hidden-external-name(n: name): name
  make-hidden-name("extern", n)

pub fun is-hidden-external-name(n: name): bool
  n.hidden/starts-with("extern")

// Create a constructor creator name from the constructor name.
// Used if special creation functions are used for the constructor.
// in particular for the case of optional arguments.
// Note: we cannot use `typeQualifiedName` as we need to use it in expressions for
// depedency analysis before we know its type.
pub fun new-creator-name(n: name): name
  make-hidden-name("create", n)

pub fun is-creator-name(n: name): bool
  n.hidden/starts-with("create")

pub val hndName = "hnd".new-hidden-name
pub val handleName = "handle".new-hidden-name
pub val effectTagName = "tag".new-hidden-name
pub val effectOpsName = "ops".new-hidden-name
pub val opsSelectName = "select".new-hidden-name

pub fun is-early-bind-name(n: name): bool
  n.is-handle-name || n.is-creator-name

// Create a handler type name from an effect type name.
pub fun to-handler-name(typeName: name): exn name
  typeName.type-qualified-name-of(hndName)

pub fun is-handler-name(n: name): bool
  n.stem-is-equal(hndName)

// Create an effect type name from an operations type name.
pub fun from-handler-name(n: name): exn name
  n.type-qualified-get-type-name

// Create a handle function name from an effect type name.
pub fun to-handle-name(typeName: name): exn name
  typeName.type-qualified-name-of(handleName)

pub fun is-handle-name(n: name): bool
  n.stem-is-equal(handleName)

// Create an operations type name from an effect type name.
pub fun to-operations-name(typeName: name): exn name
  typeName.type-qualified-name-of(effectOpsName)

// Is this an operations name?
pub fun is-operations-name(n: name): bool
  n.stem-is-equal(effectOpsName)

// Create an effect type name from an operations type name.
pub fun from-operations-name(n: name): exn name
  n.type-qualified-get-type-name

pub fun to-op-selector-name(typeName: name): exn name
  typeName.type-qualified-name-of(opsSelectName)

// Is this an operations name?
pub fun is-op-selector-name(n: name): bool
  n.stem-is-equal(opsSelectName)

//  Create an effect type name from an operations type name.
pub fun from-op-selector-name(n: name): exn name
  n.type-qualified-get-type-name

// Create an effect tag name from an effect type name.
pub fun to-effect-tag-name(typeName: name): exn name
  typeName.type-qualified-name-of(effectTagName)

// Create an operation type name from an operation name.
pub fun to-op-type-name(n: name): name
  make-hidden-name("op", n)

// Create an operation constructor name from an operation name.
pub fun to-op-con-name(n: name): name
  make-hidden-name("Op", n)

pub val indirectName = "Indirect".new-name

// Create a lazy indirect constructor name from a type name.
pub fun to-lazy-indirect-con-name(typeName: name): exn name
  typeName.type-qualified-name-of(indirectName)

pub fun is-lazy-indirect-con-name(n: name): bool
  n.stem-is-equal(indirectName)

// Create an open tag name from a constructor name in an open type
pub fun to-open-tag-name(n: name): name
  make-hidden-name("tag", n)

pub fun is-open-tag-name(n: name): bool
  n.hidden/starts-with("tag")

// Create a name for a value operation
pub fun to-value-operation-name(n: name): name
  make-hidden-name("val", n)

// Is this an name of a value operation?
pub fun is-value-operation-name(n: name): bool
  n.hidden/starts-with("val")

// Create an operation name from a value operation name
pub fun from-value-operation-name(n: name): exn name
  n.unmake-hidden("val")

// Create an operation name from either a value operation name or regular operations name
pub fun to-basic-operation-name(n: name): exn name
  if n.is-value-operation-name then n.from-value-operation-name else n

// Implicits

pub val implicit-namespace = "@implicit"
pub val implicit-namespace-name = implicit-namespace.new-module-name

pub fun is-implicit-param-name(n: name): bool
  match n.split-local-qual-name
    Cons(m, _) -> m == implicit-namespace
    _ -> False

pub fun to-implicit-param-name(n: name): exn name
  qualify-locally(implicit-namespace-name, n)

pub fun from-implicit-param-name(n: name): exn name
  match n.split-local-qual-name
    Cons(m, ms) | m == implicit-namespace -> qualify-locally(ms.unsplit-module-name, n.unqualify-full)
    _ -> n

pub fun split-implicit-param-name(n: name): (name, name)
  (n, n.unqualify-full)

// name to file path
pub fun module-name-to-path(n: name): string
  n.show.ascii-encode(True)

pub fun path-to-module-name(p: string): name
  fun decode(sl: list<char>): list<char> // TODO: Performance / do proper decoding
    val s = sl.string
    match sl
      _ | s.starts-with("_dash_").bool -> Cons('-', decode(pretend-decreasing(sl.drop(6))))
      Cons('_', Cons('_', t)) -> Cons('_', decode(pretend-decreasing(t)))
      Cons('_', t) -> Cons('/', decode(pretend-decreasing(t)))
      Cons('@', t) -> Cons('@', decode(pretend-decreasing(t)))
      Cons('.', t) -> decode(pretend-decreasing(t))
      Cons('\\', t) -> Cons('/', decode(pretend-decreasing(t)))
      Cons(c, t) -> Cons(c, decode(pretend-decreasing(t)))
      Nil -> Nil
  p.list.map(fn(c) if c.is-path-sep then '/' else c).decode.drop-while(fn(c) -> c == '_' || c == '.' || c == '/').string.new-module-name

// Ascii encode a name
// - on module names '/' becomes '_'
// - on normal names '-' becomes '_'
pub fun ascii-encode(n: string, is-module: bool): string
  fun encode-char(pre: char, c: char, post: char): string
    match c
      _ | c.is-alpha-num -> c.string
      '/' | is-module -> "_"
      '-' | !is-module && post.is-alpha-num -> "_"
      // note: `pre == '/'` covers locally-qualified hidden segments like
      // `assign/@index` -> `assign_fs__index` (matching the reference JS exports)
      '@' | post.is-digit || post == ' ' || pre == ' ' || pre == '/' -> "_"

      '_' -> "__"
      '.' -> "_dot_"
      '-' -> "_dash_"
      '/' -> "_fs_"

      '+' -> "_plus_"
      '*' -> "_star_"
      '&' -> "_amp_"
      '~' -> "_tilde_"
      '!' -> "_excl_"
      '@' -> "_at_"
      '#' -> "_hash_"
      '$' -> "_dollar_"
      '%' -> "_perc_"
      '^' -> "_hat_"
      '=' -> "_eq_"
      ':' -> "_colon_"
      '<' -> "_lt_"
      '>' -> "_gt_"
      '[' -> "_lb_"
      ']' -> "_rb_"
      '?' -> "_ques_"
      '\\'-> "_bs_"
      '(' -> "_lp_"
      ')' -> "_rp_"
      ',' -> "_comma_"
      ' ' -> "_space_"
      '\'' -> "_sq_"
      '\"' -> "_dq_"
      '`'  -> "_bq_"
      '{'  -> "_lc_"
      '}'  -> "_rc_"
      '|'  -> "_bar_"
      _ -> "_x" ++ c.int.show-hex(pre="", width=2) ++ "_"
  fun encode-chars2(s: list<char>): list<string>
    match s
      Cons(pre, Cons(c, Cons(post, rest))) -> Cons(encode-char(pre, c, post), encode-chars2(Cons(c, Cons(post, rest)).pretend-decreasing))
      Cons(pre, Cons(c, Nil)) -> Cons(encode-char(pre, c, ' '), Nil)
      Cons(pre, Nil) -> Cons(pre.string, Nil)
      Nil -> Nil
  fun encode-chars(s: string): string
    encode-chars2((" " ++ s).list).join
  if n.head-char.default(' ').is-alpha-num then
    return n.encode-chars
  match n
    ""      -> "_null_"
    "@<>"   -> "_total_"
    "@<|>"  -> "_extend_"
    "@()"   -> "_unit_"
    "@(,)"  -> "_tuple2_"
    "@(,,)" -> "_tuple3_"
    "@(,,,)"-> "_tuple4_"
    "()"    -> "_Unit_"
    "(,)"   -> "_Tuple2_"
    "(,,)"  -> "_Tuple3_"
    "(,,,)" -> "_Tuple4_"
    "[]"    -> "_index_"
    _ -> n.encode-chars
