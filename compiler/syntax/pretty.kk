import compiler/syntax/syntax
import compiler/lib/pprint
import compiler/common/name
import compiler/common/syntax
import compiler/common/range
// Updated 7/12/25, Commit: #752748d, TODO: Check that it actually matches now


fun program/pretty(Program(_, n, _, typeDefs, defs, imports, externals, fixDefs, _):userProgram): div doc
  vcat(Cons("module".text |+| n.pretty, imports.map(fn(i) i.pretty) ++ fixDefs.map(fn(fd) fd.pretty) ++ externals.map(fn(e) e.pretty) ++ typeDefs.map(fn(td) td.pretty) ++ defs.map(fn(d) d.pretty)))

fun external/pretty(e: external): doc
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
  i.vis.pretty |.| "import".text |+| i.fullName.pretty 

fun typedefgroup/pretty(t: typeDefGroup<userType,userKind>): div doc
  match t
    TypeDefRec(defs) -> defs.map(fn(d) d.pretty).vcat
    TypeDefNonRec(d) -> d.pretty

fun typedef/pretty(td: typeDef<userType,userType,userKind>): div doc
  match td
    Synonym(binder, params, synonym, _, vis, doc) -> 
     doc.pretty |--| vis.pretty |.| "alias ".text |.| binder.pretty |+| params.map(fn(p) p.pretty).vcat |+| synonym.pretty 
    DataType(binder, params, constrs, _, vis, _, _, _, doc) -> 
      doc.pretty |--| vis.pretty |.| "type ".text |.| binder.pretty |+| params.map(fn(p) p.pretty).vcat |+| constrs.map(fn(c) c.pretty).vcat

fun vis/pretty(v: visibility): doc
  match v
    Public -> "pub ".text
    Private -> empty

fun tb/pretty(t: typeBinder<userKind>): div doc
  t.name.pretty |+| t.kind.pretty

fun con/pretty(u: userCon<userType,userType,userKind>): div doc
  u.name.pretty |+| u.existentials.map(fn(e) e.pretty).vcat |+| 
   u.params.map(fn((vis,bind)) tupled([vis.pretty, bind.pretty]) ).vcat |+| 
   u.result.pretty |+| u.vis.pretty |.| u.doc.pretty

fun dg/pretty(d: defGroup<userType>): div doc
  match d
    DefRec(defs) -> defs.map(fn(df) df.pretty |+| "\n".text).vcat
    DefNonRec(df) -> df.pretty

fun tdefvb/pretty(v: valueBinder<userType,maybe<expr<userType>>>): div doc
  v.name.pretty |+| v.expr.pretty

fun lamvb/pretty(v: valueBinder<maybe<userType>,maybe<expr<userType>>>): div doc
  val tp = match v.binderType 
    Just -> ":".text |+| v.binderType.pretty
    Nothing -> empty
  val def = match v.expr 
    Just -> "=".text |+| v.expr.pretty
    Nothing -> empty
  v.name.pretty |.| tp |.| (if tp.is-empty then def else " ".text |.| def)

fun defsort/pretty(d: defSort): doc
  match d
    DefFun -> "fun".text
    DefVal -> "val".text
    DefVar -> "var".text

fun definline/pretty(d: defInline): doc
  match d
    InlineNever -> "noinline".text
    InlineAlways -> "inline".text
    InlineAuto -> pretty/pprint/empty

fun dbinder/pretty(vb: valueBinder<(), userExpr>, sort: defSort): div doc
  match sort
    DefFun -> 
      match vb.expr
        Ann(Lam(binders, e)) -> 
          vb.name.pretty |.| binders.map(fn(b) b.pretty).tupled |--| e.pretty.indent(2)
        Lam(binders, e) -> 
          vb.name.pretty |.| binders.map(fn(b) b.pretty).tupled |--| e.pretty.indent(2)
        _ -> vb.name.pretty |+| vb.expr.pretty
    DefVal -> vb.name.pretty |+| "=".text |+| vb.expr.pretty
    DefVar -> vb.name.pretty |+| ":=".text |+| vb.expr.pretty

fun def/pretty(d: def<userType>): div doc
  val prf = d.doc.text |-| d.visibility.pretty |.| d.defInline.pretty |.| d.sort.pretty
  prf |+| d.binder.pretty(d.sort)

fun arg/pretty(a: (maybe<(name,range)>, expr<userType>)): div doc
  match a
    (Just((n, _)), expr) -> n.pretty |+| "=".text |+| expr.pretty
    (Nothing, expr) -> expr.pretty

fun expr/pretty(expr: expr<userType>): div doc
  match expr
    Lam(binder, e) -> "fn".text |.| binder.map(pretty).tupled |--| e.pretty.indent(2)
    Let(d, e) -> d.dg/pretty |--| e.expr/pretty 
    Bind(d, e) ->  d.pretty |--| e.pretty
    App(Handler(_, _, _, _, _, _, _, hReturn, _, branches), [body]) -> 
      "with handler".text |--| Cons(hReturn.pretty, branches.map(pretty)).vcat.indent(2)
      |--| body.snd.expr/pretty
    App(Var(opname, True), [a1, a2]) -> a1.arg/pretty |+| opname.show-plain.pretty |+| a2.arg/pretty
    App(e, args) -> e.pretty |.| args.map(arg/pretty).tupled 
    Var(n) -> n.pretty
    Literal(l) -> l.pretty
    Ann(e, t) -> e.pretty |+| t.pretty
    Case(e, cases) -> "match".text |+| e.pretty |--| cases.map(fn(c) c.pretty).vcat.indent(2)
    Parens(e, n, d) -> d.pretty |.| e.pretty |+| n.pretty
    Inject(t, e, behind) -> 
      if behind then "mask behind<".text |.| t.pretty |.| ">".text |--| e.pretty.indent(2)
      else "mask<".text |.| t.pretty |.| ">".text |--| e.pretty.indent(2)
    Handler(_, _, _, _, _, _, _, hReturn, _, branches) -> 
      "handler".text |--| Cons(hReturn.pretty, branches.map(fn(b) b.pretty)).vcat.indent(2)

fun handbranch/pretty(b: handlerBranch<userType>): div doc
  b.branchSort.pretty |+| b.branchName.pretty |--| b.branchExpr.pretty.indent(2)

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

fun branch/pretty(b: branch<userType>): div doc
  b.branchPattern.pretty |+| b.branchGuard.map(fn(g) "->".text |--| g.guardExpr.pretty.indent(2)).vcat

fun patarg/pretty(pa: (maybe<(name, range)>, userPattern)): div doc
  match pa
    (Just((n, _)), p) -> n.pretty |+| "as".text |+| p.pretty
    (Nothing, p) -> p.pretty

fun pat/pretty(p: userPattern): div doc
  match p
    PatWild -> "_".text
    PatVar(patvar) -> patvar.pretty
    PatAnn(p, t) -> p.pretty |+| ":".text |+| t.pretty
    PatCon(name, Nil) -> name.unqualify.pretty
    PatCon(name, args) -> 
      val args' = args.map(patarg/pretty).tupled
      name.unqualify.pretty |.| args'
    PatParens(p) -> tupled([p.pretty])
    PatLit(value) -> value.pretty

fun vbm/pretty(ValueBinder(nm, tp, subpat): valueBinder<maybe<userType>, userPattern>): div doc
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

fun main()
  "pprint"