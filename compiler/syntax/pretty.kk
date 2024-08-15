import compiler/syntax/syntax
import compiler/lib/pprint
import compiler/common/name
import compiler/common/syntax
import compiler/common/range

fun program/pretty(Program(_, n, _, typeDefs, defs, imports, externals, fixDefs, _):program<t,k>, ?t/pretty: (t) -> <div|e> doc, ?k/pretty: (k) -> <div|e> doc): <div|e> doc
  vcat(Cons("module".text |+| n.pretty, imports.map(fn(i) i.pretty) ++ fixDefs.map(fn(fd) fd.pretty) ++ externals.map(fn(e) e.pretty) ++ typeDefs.map(fn(td) td.pretty) ++ defs.map(fn(d) d.pretty)))
fun external/pretty(e: external): div doc
  empty
fun externcall/pretty(e: externalCall): doc
  match e
    ExternalInline -> empty
    ExternalCall -> empty

fun fixity/pretty(f: fixity): doc
  match f
    FixInfix -> "infix".text
    FixPrefix -> "prefix".text
    FixPostfix -> "postfix".text

fun fixdef/pretty(f: fixDef): doc
  f.name.pretty |+| f.fixity.pretty |+| f.vis.pretty

fun kimport/pretty(i: kimport): doc
  i.name.pretty |+| i.fullName.pretty |+| i.vis.pretty

fun typedefgroup/pretty(t: typeDefGroup<t,k>, ?t/pretty: (t) -> <div|e> doc, ?k/pretty: (k) -> <div|e> doc): <div|e> doc
  match t
    TypeDefRec(defs) -> defs.map(fn(d) d.pretty).vcat
    TypeDefNonRec(d) -> d.pretty

fun typedef/pretty(td: typeDef<t,u,k>, ?t/pretty: (t) -> <div|e> doc, ?u/pretty: (u) -> <div|e> doc, ?k/pretty: (k) -> <div|e> doc): <div|e> doc
  match td
    Synonym(binder, params, synonym, _, vis, doc) -> 
     doc.pretty |--| vis.pretty |+| "alias ".text |.| binder.pretty |+| params.map(fn(p) p.pretty).vcat |+| synonym.t/pretty 
    DataType(binder, params, constrs, _, vis, _, _, _, doc) -> 
      doc.pretty |--| vis.pretty |+| "type ".text |.| binder.pretty |+| params.map(fn(p) p.pretty).vcat |+| constrs.map(fn(c) c.pretty).vcat

fun vis/pretty(v: visibility): doc
  match v
    Public -> "pub".text
    Private -> "private".text

fun tb/pretty(t: typeBinder<k>, ?pretty: (k) -> <div|e> doc): <div|e> doc
  t.name.pretty |+| t.kind.pretty

fun con/pretty(u: userCon<t,u,k>, ?t/pretty: (t) -> <div|e> doc, ?u/pretty: (u) -> <div|e> doc, ?k/pretty: (k) -> <div|e> doc): <div|e> doc
  u.name.pretty |+| u.existentials.map(fn(e) e.pretty).vcat |+| 
   u.params.map(fn((vis,bind)) tupled([vis.pretty, bind.pretty]) ).vcat |+| 
   u.result.pretty |+| u.vis.pretty |+| u.doc.pretty

fun dg/pretty(d: defGroup<t>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  match d
    DefRec(defs) -> "DefRec ".text |.| defs.map(fn(df) df.pretty).vcat
    DefNonRec(df) -> "DefNonRec ".text |.| df.pretty

fun vb/pretty<t,v,e>(v: valueBinder<t,v>, ?t/pretty: (t) -> <div|e> doc, ?e/pretty: (v) -> <div|e> doc): <div|e> doc
  v.name.pretty |+| v.binderType.t/pretty |+| v.expr.e/pretty

fun vb2/pretty<t,v,e>(v: valueBinder<maybe<t>,maybe<v>>, ?t/pretty: (t) -> <div|e> doc, ?e/pretty: (v) -> <div|e> doc): <div|e> doc
  val first = match v.binderType
    Just(t) -> v.name.pretty |.| ":".text |+| t.pretty
    Nothing -> v.name.pretty
  first |.| v.expr.map(fn(e) " = ".text |.| e.pretty).default(empty)

fun defsort/pretty(d: defSort): doc
  match d
    DefFun -> "fun".text
    DefVal -> "val".text
    DefVar -> "var".text

fun definline/pretty(d: defInline): doc
  match d
    InlineNever -> "noinline".text
    InlineAlways -> "inline".text
    InlineAuto -> empty

fun def/pretty(d: def<t>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  d.binder.pretty |+| d.visibilty.pretty |+| d.sort.pretty |+| d.defInline.pretty |+| d.doc.text

fun arg/pretty(a: (maybe<(name,range)>, expr<t>), ?pretty: (t) -> <div|e> doc): <div|e> doc
  match a
    (Just((n, _)), expr) -> n.pretty |+| "=".text |+| expr.pretty
    (Nothing, expr) -> expr.pretty

fun expr/pretty(expr: expr<t>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  match expr
    Lam(binder, e) -> "fn".text |.| binder.map(fn(b) b.pretty).tupled |+| e.pretty
    Let(d, e) -> d.dg/pretty |--| e.expr/pretty 
    Bind(d, e) ->  d.pretty |+| e.pretty
    App(e, args) -> e.pretty |.| args.map(fn(a) a.pretty).tupled 
    Var(n) -> n.pretty
    Literal(l) -> l.pretty
    Ann(e, t) -> e.pretty |+| t.pretty
    Case(e, cases) -> e.pretty |+| cases.map(fn(c) c.pretty).vcat
    Parens(e, n, d) -> d.pretty |.| e.pretty |+| n.pretty
    Inject(t, e, behind) -> 
      if behind then "mask behind<".text |.| t.pretty |.| ">".text |--| e.pretty.indent(2)
      else "mask<".text |.| t.pretty |.| ">".text |--| e.pretty.indent(2)
    Handler(sort, scope, hOverride, allowMask, hEffect, localPars, initially, hReturn, fin, branches) -> 
      "Handler ".text |.| sort.pretty |+| scope.pretty |+| hOverride.pretty |+| 
      allowMask.pretty |+| hEffect.pretty |+| localPars.map(fn(p) p.pretty).tupled |+| 
      initially.pretty |+| hReturn.pretty |+| fin.pretty |+|
      branches.map(fn(b) b.pretty).vcat

fun handbranch/pretty(b: handlerBranch<t>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  b.branchSort.pretty |+| b.branchName.pretty |.| b.branchPars.map(fn(p) p.pretty).tupled |--| b.branchExpr.pretty.indent(2)

fun branchsort/pretty(b: operationSort): doc
  match b
    OpVal -> "val".text
    OpFun -> "fun".text
    OpExcept -> "final ctl".text
    OpControlRaw -> "raw ctl".text
    OpControl -> "ctl".text
    OpControlErr -> "ctl".text

fun hsort/pretty(h: handlerSort): doc
  match h
    HandlerInstance -> "named".text
    HandlerNormal -> empty

fun hov/pretty(h: handlerOverride): doc
  match h
    HandlerOverride -> "override".text
    HandlerNoOverride -> empty

fun hs/pretty(h: handlerScope): doc
  match h
    HandlerScoped -> "scoped".text
    HandlerNoScope -> empty

fun branch/pretty(b: branch<t>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  b.branchPattern.pretty |+| b.branchGuard.map(fn(g) g.guardExpr.pretty).vcat

fun patarg/pretty(pa: (maybe<(name, range)>, pattern<t>), ?pretty: (t) -> <div|e> doc): <div|e> doc
  match pa
    (Just((n, _)), p) -> n.pretty |+| "as".text |+| p.pretty
    (Nothing, p) -> p.pretty

fun pat/pretty(p: pattern<t>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  match p
    PatWild -> "_".text
    PatVar(patvar) -> patvar.pretty
    PatAnn(p, t) -> p.pretty |+| ":".text |+| t.pretty
    PatCon(name, args) -> name.pretty |.| (if args.length == 0 then empty else args.map(fn(a) a.pretty).tupled)
    PatParens(p) -> tupled([p.pretty])
    PatLit(value) -> value.pretty

fun vbm/pretty<t,e>(ValueBinder(nm, tp, subpat): valueBinder<maybe<t>, pattern<t>>, ?pretty: (t) -> <div|e> doc): <div|e> doc
  if subpat.is-patWild then
    nm.pretty |.| tp.map(fn(t) " : ".text |.| t.pretty).default(empty)
  else
    nm.pretty |+| "as".text |+| subpat.pretty |.| tp.map(fn(t) " : ".text |.| t.pretty).default(empty)

fun lit/pretty(l: lit): doc
  match l
    LitInt(v) -> v.pretty
    LitFloat(v) -> v.pretty
    LitChar(v) -> "'".text |.| v.text |.| "'".text
    LitString(v) -> v.show.pretty

fun uquant/pretty(u: userQuantifier): doc
  match u
    QSome -> "some".text
    QForall -> "forall".text
    QExists -> "exists".text

fun ut/pretty(u: userType): div doc
  match u
    TpQuan(q, b, kind) -> q.pretty |+| b.pretty |+| kind.pretty 
    TpQual(l, kind) -> l.map(pretty).vcat |+| kind.pretty
    TpFun(a, b, c) -> a.map(fn((n, ut)) n.pretty |.| ":".text |.| ut.pretty).tupled |+| b.pretty |+| c.pretty 
    TpApp(a, b) -> a.pretty |.| tupled(b.map(pretty))
    TpVar(n) -> n.pretty 
    TpCon(n) -> n.pretty
    TpParens(t) -> tupled([t.pretty])
    TpAnn(t, k) -> t.pretty |+| "::".text |+| k.pretty

fun uk/pretty(u: userKind): doc
  match u
    KindCon(name) -> name.pretty
    KindArrow(from, to) -> from.pretty |+| "->".text |+| to.pretty
    KindParens(kind) -> kind.pretty
    KindNone -> empty
