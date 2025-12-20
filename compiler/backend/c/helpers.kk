import compiler/core/core
import compiler/common/syntax
import compiler/common/failure
import compiler/common/name
import compiler/common/nice
import compiler/common/name-prim
import compiler/common/unique
import compiler/core/corevar
import compiler/core/borrowed
import compiler/type/type
import compiler/type/pretty
import compiler/type/typevar
import compiler/kind/kind
import compiler/kind/newtypes
import compiler/lib/pprint
import compiler/platform/config
import compiler/common/file
import compiler/lib/printer
import compiler/common/color-scheme
import std/os/path
import std/num/float64
import std/core/undiv

alias asmEff = <pure,asm,comp-flags,unique,colorSchemeEffect,newtypesEff,printer,subst,documentation,niceEff<typeVar>,ppEnvEff,precEff,prettyTypeEff>

// Put the things that need overriding in here
effect subst
  val substEnv: list<(tName, doc)> // substituting names
  val cdef-name: name // current definition
  val cdefToHeader: bool // emit current def to header?

effect asm
  fun emit-to-h(d: doc): ()
  fun emit-to-c(d: doc): ()
  fun emitToInit(d: doc): ()
  fun emitToTop(d: doc): ()
  fun emitToDone(d: doc): ()
  fun getInit(): doc
  fun getDone(): doc
  fun getTop(): doc
  fun addCanonical(lam: canonicalLambda): bool // true if first instance, otherwise false
  // TODO: Canonical lambda
  val modName: name // current module
  val prettyModName: doc // pretty printed module name
  // TODO: Pretty.Env
  val targetPlatform: platform
  val eagerPatBind: bool
  val enableReuse: bool
  val enableSpecialize: bool
  val enableReuseSpecialize: bool
  val enableBorrowInference: bool
  val cTarget: cTarget
  val borrowed: borrowed
  val stackSize: int
  val buildType: buildType
  val sourceDir: path
  val debug: bool;

value struct canonicalLambda
  canonicalName : name
  fieldNames: list<(name, bool)>

fun can/(==)(c1: canonicalLambda, c2: canonicalLambda): pure bool
  c1.canonicalName == c2.canonicalName && c1.fieldNames == c2.fieldNames

fun can/show(c: canonicalLambda): string
  c.canonicalName.show ++ "(" ++ c.fieldNames.map(fn(n) n.fst.show ++ " " ++ n.snd.show).join(", ") ++ ")"

// Effect helpers
fun emit-to-current-def(d: doc)
  if cdefToHeader then emit-to-h(d)
  else emit-to-c(d)

fun set-name-substitutions(subs, f)
  with override
    val substEnv = subs
    val cdef-name = cdef-name
    val cdefToHeader = cdefToHeader
  f()

fun set-def(d: name, toHeader: bool, f)
  with override
    val substEnv = substEnv
    val cdef-name = d
    val cdefToHeader = toHeader
  f()

fun local-unique(f)
  val u = update-unique(id)
  val x = f()
  set-unique(u)
  x

fun new-var-name(s: string): asmEff name
  new-name("." ++ s ++ new-unique().show)

fun new-var-names(i: int): asmEff list<name>
  Cons(new-var-name("x"), new-var-names(i - 1))

fun newDefVarName(s: string)
  cdef-name.postpend("-" ++ s ++ new-unique().show)

fun new-canonical-var-name(s: string)
  modName.postpend("-" ++ s)

fun con-name(e: expr)
  pretend-no-div
    try({match e {Con(tn) -> tn}}) fn(_)
      trace("Failed in top level extracting con name of " ++ e.show)
      TName("error".new-name, typeAny)

fun get-format(tname: tName, formats: list<(target, string)>)
  match formats.find(fn((t, _)) t == C(cTarget))
    Nothing -> 
      trace("warning: C backend does not support external in " ++ tname.show)
      "kk_unsuported_external(\"" ++ tname.show ++ "\")"
    Just(x) -> x.snd

fun gen-def-name(tname: tName)
  tname.get-name.unqualify.cpp-name

fun gen-var-name(s: string)
  new-var-name(s).cpp-name

fun gen-var-names(i: int)
  new-var-names(i).map(cpp-name)

fun gen-comment-tname(tname: tName)
  tname.get-name.cpp-name |+| comment(tname.tNameType.pp-type)

// Classification
fun max-scan-count(l: list<(conInfo, conRepr, list<(name,ktype)>, int)>): int
  l.foldl(0, fn(m, (_, _, _, sc)) if sc > m then sc else m)

fun max-scan-count-of(l: list<(conInfo, conRepr, list<(name,ktype)>, int)>): int
  l.foldl(l.max-scan-count, fn(m, (_, _, _, sc)) if sc < m then sc else m)

fun data-repr-may-have-singletons(d: dataRepr): bool
  match d
    DataAsMaybe -> True
    DataAsList -> True
    DataSingleNormal -> True
    DataSingle(hasSingletons) -> hasSingletons
    DataNormal(hasSingletons) -> hasSingletons
    _ -> False

fun pattern-var-free(p)
  p.is-patWild

fun is-pat(q: pattern, b: bool): bool
  match q
    PatWild -> False
    PatLit -> False
    PatVar(_, q') -> q'.is-pat(b)
    PatCon(tn) -> tn.get-name == (if b then nameTrue else nameFalse)

fun extract-external(e: expr): asmEff maybe<(tName, string, list<expr>)>
  fun format(tn:tName, fs:list<(target,string)>)
    match lookup-target(C(cTarget), fs)
      Nothing -> fail("backend does not support external in " ++ tn.show ++ fs.show-list(fn((t,s)) t.show ++ ":" ++ s))
      Just(f) -> f
  match e
    App(TypeApp(Var(tname, InfoExternal(formats)), _), args) ->
      Just((tname, tname.format(formats), args))
    App(Var(tname, InfoExternal(formats)), args) ->
      Just((tname, tname.format(formats), args))
    _ -> Nothing

fun is-fun-expr(e: expr): bool
  match e
    TypeApp(e) -> e.is-fun-expr
    TypeLam(_, e) -> e.is-fun-expr
    Lam -> True
    _ -> False

fun is-reuse-null(e: expr)
  match e
    App(Var(v, InfoExternal), []) -> v.get-name == nameReuseNull
    _ -> False

fun is-inlineable-expr(ex: expr): pure bool
  match ex
    TypeApp(e) -> e.is-inlineable-expr
    TypeLam(_, e) -> e.is-inlineable-expr
    ELit(LitString) -> False
    // C has no guarantee on argument evaluation so we only allow a select few operations to be inlined
    App(Var(v, InfoExternal), []) -> 
      val n = v.get-name
      [nameYielding,nameReuseNull,nameCCtxHoleCreate].any(fn(n') n == n')
    // App (Var v (InfoExternal _)) [arg] | get-name v `elem` [nameBox,nameDup,nameInt32] -> is-inlineable-expr arg
    App(Var(v), [arg]) | [nameBox,nameInt32,nameReuse,nameReuseIsValid,nameIsUnique].any(fn(n') n' == v.get-name) ->
      arg.is-inlineable-expr
    // App (Var v (InfoExternal _)) args -> hasTotalEffect (typeOf v) &&  all is-pure-expr args  -- yielding() etc.

    // App (Var v _) [arg] | get-name v `elem` [nameBox,nameUnbox] -> is-inlineable-expr arg
    //
    // TODO: comment out for now as it may prevent a tailcall if inlined
    // App f args       -> -- trace ("is-inlineable f: " ++ show f) $
    //                      is-pure-expr f && all is-pure-expr args
    //                      -- all is-inlineable-expr (f:args)
    //                      && not (is-fun-expr f) -- avoid `fun() {}(a,b,c)` !
    //                      -- && getParamArityExpr f == length args
    _ -> ex.is-pure-expr

fun is-pure-expr(ex: expr): pure bool
  match ex
    TypeApp(e) -> e.is-pure-expr
    TypeLam(_, e) -> e.is-pure-expr
    Var(_, InfoExternal) -> False
    Var -> True
    Con -> ex.type-of.split-fun-scheme.is-nothing
    ELit(LitString) -> False // for our purposes, it's not pure (as it needs a declaration)
    ELit -> True
    Lam -> True
    _ -> False   

fun is-tail-calling(ex: expr, n: name): bool
  fun f2(g: guard)
    g.body.pretend-decreasing.is-tail-calling(n) // does the guarded expression tailcall?
  fun f1(b: branch)
    b.guards.any(f2) // does any of the guards tailcall?
  match ex
    TypeApp(e) -> is-tail-calling(e.pretend-decreasing, n) // trivial
    TypeLam(_, e) -> is-tail-calling(e.pretend-decreasing, n) // trivial
    Lam -> False // lambda body is a new context, can't tailcall
    Var -> False // variable is not a call
    Con -> False // constructor is not a call
    ELit -> False // literal is not a call
    App(Var(tn, info), args) | tn.get-name == n -> info.arity == args.length // direct application can be a tail call
    App(TypeApp(Var(tn, info)), args) | tn.get-name == n -> info.arity == args.length // polymorphic direct application can be a tail call
    App(Var(tn), [e]) | tn.get-name == nameReturn -> e.is-tail-calling(n) // return is transparent in terms of tail calling
    App -> False
    Let(_, e) -> e.pretend-decreasing.is-tail-calling(n) // tail calls can only happen in the actual body
    Case(_, bs) -> bs.any(f1)

type result
  ResultReturn(tn: maybe<tName>, args: list<tName>) // first field carries function name if not anonymous and second the arguments which are always known
  ResultAssign(tn: tName, label: maybe<name>) // variable name nad optional label to break

// Pretty printing

type cType
  CBox
  CFun(args: list<cType>, res: cType)
  CData(nm: name)
  CPrim(prim: string)

fun c-type(tp: ktype): cType
  match tp
    TForAll(_, t) -> t.c-type
    TFun(pars, _, res) -> CFun(pars.map(_.snd.pretend-decreasing.c-type), res.c-type)
    TApp(t) -> t.c-type
    TCon(c) -> c.c-type-con
    TVar -> CBox
    TSyn(_, _, t) -> t.c-type

fun c-type-con(tp: typeCon): cType
  val nm = tp.name
  if nm == nameTpInt then CPrim("kk_integer_t")
  elif nm == nameTpString then CPrim("kk_string_t")
  elif nm == nameTpVector then CPrim("kk_vector_t")
  elif nm == nameTpEvv then CPrim("kk_evv_t")
  elif nm == nameTpChar then CPrim("kk_char_t") // 32-bit unicode point
  elif nm == nameTpSSizeT then CPrim("kk_ssize_t")
  elif nm == nameTpIntPtrT then CPrim("intptr_t")
  elif nm == nameTpFloat then CPrim("double")
  elif nm == nameTpBool then CPrim("bool")
  elif nm == nameTpUnit then CPrim("kk_unit_t")
  elif nm == nameTpInt64 then CPrim("int64_t")
  elif nm == nameTpInt8 then CPrim("int8_t")
  elif nm == nameTpInt16 then CPrim("int16_t")
  elif nm == nameTpInt32 then CPrim("int32_t")
  elif nm == nameTpFloat32 then CPrim("float")
  elif nm == nameTpFloat16 then CPrim("float") // float16 is only used for storage
  elif nm == nameTpRef || nm == nameTpLocalVar then CPrim("kk_ref_t")
  elif nm == nameTpBox || nm == nameTpAny then CPrim("kk_box_t")
  elif nm == nameTpReuse then CPrim("kk_reuse_t")
  elif nm == nameTpFieldAddr then CPrim("kk_field_addr_t")
  else CData(nm.type-class-name)

fun type-class-name(n: name)
  prepend(".", n)

fun cpp-vis(v: visibility): doc
  empty

fun type-con-class-name(n: name)
  n

fun cprim-can-be-boxed(s: string): bool
  ["kk_char_t", "int64_t", "int16_t", "int32_t", "float", "double", "intptr_t", "kk_ssize_t"].any(_ == s)

fun cpp-type(tp: ktype): doc
  match tp.c-type
    CBox -> "kk_box_t".text
    CFun -> "kk_function_t".text
    CData(nm) -> cpp-name(nm)
    CPrim(prim) -> prim.text

fun ppVarDecl(TName(nm, tp): tName): doc
  tp.cpp-type |+| nm.cpp-name

fun ppDefName(n: name)
  cpp-name(n.unqualify)

val contextDoc = "_ctx".text
val contextParam = "kk_context_t* _ctx".text

val emptyArgs = arguments([])
val emptyParams = parameters([])

fun parameters(pars: list<doc>): doc
  tupled(pars ++ [contextParam])

fun arguments(args: list<doc>): doc
  tupled(args ++ [contextDoc])

fun ppLit(l: lit): <exn,comp-flags> doc
  match l
    LitInt(i) ->
      if i.is-small-int then text("kk_integer_from_small") |.| parens(i.pretty)
      elif i.is-small-int32 then text("kk_integer_from_int") |.| arguments([i.pretty])
      else "kk_integer_from_string".text |.| arguments([dquotes(i.pretty)])
    LitChar(c) ->
      val c' = c.head-char.unjust
      if c' >= ' ' && c' <= '~' then c.show.text
      else c'.int.show-hex(4).text
    LitFloat(d) -> d.show.text
    LitString(s) -> fail("backend/c/from-core: ppLit: cannot inline string literal: " ++ s.show)

fun cString(s: string)
  fun bytes(bs: list<int>)
    ("\" \"" ++ bs.map(_.show-hex(2, pre="\\x")).join ++ "\" \"").text
  fun escape(c: char): (doc, int)
    if c.int == 0 then (bytes([0xC0, 0x80]), 2) // embedded zero character
    elif c < ' ' then
      (if c == '\n' then "\\n".text
      elif c == '\t' then "\\t".text
      elif c == '\r' then "\\r".text
      else bytes([c.int]), 1)
    elif c <= '\x7F' then
      (if c == '\"' then "\\\"".text
      elif c == '\\' then "\\\\".text
      elif c == '?' then "\\?".text // avoid accidental trigraphs
      else c.char, 1)
      // TODO: BIG UTF-8
    else ("".text, 0)
  val (cstr, ccnt) = s.list.map(escape).unzip
  (dquotes(cstr.hcat), ccnt.sum)

fun genLitInt32(i: int)
  if i == minSmallInt32 then parens("INT32_MIN".text)
  else parens("KK_I32".text |.| parens(i.pretty))

fun genLitInt64(i: int)
  if i == minSmallInt64 then parens("INT64_MIN".text)
  else parens("KK_I64".text |.| parens(i.pretty))

fun genLitUint8(i: int)
  parens("(uint8_t)".text |.| parens(i.pretty))

fun genLitSSizeT(i: int)
  parens("KK_IZ".text |.| parens(i.pretty))

fun genLitIntPtrT(i: int)
  parens("KK_IP".text |.| parens(i.pretty))

fun isSmallLitInt(e)
  match e
    ELit(LitInt(i)) -> is-small-int(i)
    _ -> False

fun is-small-int(i)
  i >= minSmallInt && i < maxSmallInt
val maxSmallInt = 8191 // 2^13 -1 (conservative 14 bits on 32-bits platform)
val minSmallInt = -8192

fun is-small-int32(i)
  i >= minSmallInt32 && i < maxSmallInt32
val minSmallInt32 = -2147483648
val maxSmallInt32 = 2147483647

fun is-small-int64(i)
  i >= minSmallInt64 && i < maxSmallInt64
val minSmallInt64 = -9223372036854775808
val maxSmallInt64 = 9223372036854775807

fun is-small-uint8(i)
  i >= 0 && i < 255

fun is-small-ssizet(i)
  match targetPlatform.ptrSize
    4 -> i > minSmallInt32 && i < maxSmallInt32
    8 -> i > minSmallInt64 && i < maxSmallInt64
    _ -> fail("backend/c/from-core: is-small-ssizet: unknown platform ssize_t: " ++ targetPlatform.show)

fun is-small-int-ptr(i)
  match targetPlatform.ptrSize
    4 -> i > minSmallInt32 && i < maxSmallInt32
    8 -> i > minSmallInt64 && i < maxSmallInt64
    _ -> fail("backend/c/from-core: is-small-int-ptr: unknown platform intptr_t: " ++ targetPlatform.show)

fun cpp-name(n: name): doc
  if n.is-qualified then pp-mod-name(n.qualifier) |.| "_".text |.| n.unqualify.show.ascii-encode(False).text
  else n.encode(False)

fun pp-qname(modName: name, name: name): doc
  if modName == name.qualifier then cpp-name(name.unqualify)
  else cpp-name(name)

fun pp-mod-name(n: name): doc
  "kk_".text |.| n.encode(True)

fun encode(n: name, isModule: bool)
  val s = n.show.ascii-encode(isModule)
  if s.is-reserved || s == "" || s.head-char.map(is-digit).default(False) then ("kkloc_" ++ s).text
  else s.text

fun is-reserved(s: string): bool
  if s.starts-with("kk_").is-just then True
  else reserved.any(_ == s)

val reserved = [ 
  // C pseudo-keywords
  "bool", "toString", "arguments", "eval",
  // C types
  "char", "int", "intptr_t", "long", "short", "signed", "size_t",
  "ssize_t", "intptr_t", "uintptr_t", "unsigned", "uint8_t",
  // C keywords
  "async", "await", "break", "case", "catch", "continue", "const", "debugger",
  "default", "delete", "do", "else", "finally", "for", "function", "if", "in",
  "instanceof", "new", "return", "register", "switch", "this", "throw", "try", "typeof",
  "var", "void", "while", "with", "yield",
  // reserved for future use
  "class", "enum", "export", "extends", "import", "super",
  // special macros
  "errno", "exception_info"
]

fun pp-con-field(n: name, t: ktype): doc
  t.cpp-type |+| n.unqualify.cpp-name |.| semi

fun con-test-name(c: conInfo): doc
  cpp-name(make-hidden-name("is", c.name))

fun con-test-nameX(nm: name): doc
  cpp-name(make-hidden-name("is", nm))

fun con-tag-name(c: conInfo): doc
  cpp-name(make-hidden-name("tag", c.name))

fun prim-name(prim: string, d: doc)
  if prim == "" then d else
    d |.| "_".text |.| prim.text

fun prim-name-type(prim: string, s: string)
  val start = if s.starts-with("kk_").is-just then "" else "kk_"
  val end = match s.ends-with("_t") { Just(x) -> x.string; _ -> s}  
  prim-name(prim, (start ++ end).text)

fun con-base-case-name(c: conInfo): doc
  cpp-name(make-hidden-name("base", c.name))

fun con-base-case-nameX(c: name): doc
  cpp-name(make-hidden-name("base", c))

fun con-create-name(c: conInfo): doc
  make-hidden-name("new", c.name).cpp-name

fun con-create-nameX(c: name): doc
  make-hidden-name("new", c).cpp-name

fun con-singleton-name(c: conInfo): doc
  make-hidden-name("singleton", c.name).cpp-name

fun con-as-name(c: conInfo): doc
  cpp-name(make-hidden-name("as", c.name))

fun con-as-nameX(c: name): doc
  cpp-name(make-hidden-name("as", c))

fun open-tag-name(n: name): doc
  cpp-name(make-hidden-name("tag", n))

fun nt-parameters(pars: list<(name, ktype)>): doc
  parameters(pars.map(fn((n, t)) t.cpp-type |+| n.unqualify.cpp-name))

fun clos-fn-parameters(pars: list<(name, ktype)>): doc
  parameters(Cons("void* fnPtr".text, pars.map(fn((n, t)) t.cpp-type |+| n.unqualify.cpp-name)))

fun vcat-break(l: list<doc>): doc
  linebreak |.| l.vcat

fun parens-if(d: doc) // avoid parens if already parenthesized
  if d.doc-starts-with("(") && d.doc-ends-with(")") || d.doc-starts-with("kk_likely") then d
  else parens(d)

fun inlineblock(d: doc)
  if d.doc-starts-with("{") then d
  else hang("{".text |+| d, 2) |--| "}".text

fun block(d: doc)
  if d.doc-starts-with("{") then d
  else "{".text |--| tab(d) |--| "}".text

fun block1(l: list<doc>)
  match l
    [d] -> "{".text |+| d |+| "}".text
    _ -> block(l.vcat)

fun tblock(tp: doc, d: doc)
  "{".text |+| tp |--| tab(d) |--| "}".text

fun tco-block(tp: doc, d: doc)
  tblock(tp, "kk__tailcall: ;".text |--| d)

val tailcall = "goto kk__tailcall;".text

fun object(xs: list<(doc, doc)>): doc
  "{".text |+| hcat(xs.map(fn((d1, d2)) d1 |.| colon |+| d2).punctuate(comma |.| space)) |+| "}".text

fun tab(d: doc)
  indent(d, 2)

val typeComment = comment

fun comment(d: doc)
  "/*".text |+| d |+| "*/".text

fun linecomment(d: doc)
  "//".text |+| d

fun is-whitespace(c: char)
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

fun trim-comment(comm: string)
  fun trim-rest(xs: list<char>)
    xs.drop-while(is-whitespace).reverse.string
  fun trim-line(s: string)
    match s.list.reverse
      Cons('\\', xs) -> xs.trim-rest
      xs -> xs.trim-rest
  comm.lines.map(trim-line).unlines

fun unit-semi(tp: ktype): doc
  if tp.is-type-unit then " = kk_Unit;".text else semi

fun debug-comment(s: string)
  if debug then comment(s.text)
  else pprint/Empty

fun debug-wrap(d: doc, s: string)
  if debug then debug-comment("<" ++ s ++ ">") |--| tab(d) |--| debug-comment("</" ++ s ++ ">")
  else d

val tagField = "_tag".text
val constdecl = "const".text

fun t-parameters(tns: list<tName>): doc
  nt-parameters(tns.map(fn(tn) (tn.get-name, tn.tNameType)))

fun result-type(tp: ktype): <pure,comp-flags> ktype
  match tp.split-fun-scheme
    Just((_, _, _, res)) -> res
    _ -> fail("backend/c/from-core result-type: not a function type: " ++ tp.show) // TODO: Pretty type