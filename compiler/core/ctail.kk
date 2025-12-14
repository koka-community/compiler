import compiler/core/core
import compiler/core/pretty
import compiler/type/assumption
import compiler/kind/newtypes
import compiler/type/type
import compiler/common/name
import compiler/type/pretty
import compiler/common/unique

/*
 * Reference count transformation
 */


pub fun ctail-optimize( newtypes : newtypes, gamma : gamma, use-context-path : bool ) : <newtypesEff, ppEnvEff, corePhase, div> ()
  val defs = get-core-defs()
  val start = unique()
  val result = error/try()
    start.run-unique
      uctail-optimize( newtypes, gamma, use-context-path, defs )
  match result
    Ok(_) -> ()
    Err(e) -> phaseError( e.show )


pub fun uctail-optimize( newtypes : newtypes, gamma : gamma, use-context-path : bool, defs : defGroups) : <newtypesEff, ppEnvEff, unique, exn, div> defGroups
  ctail-run( newtypes, gamma, use-context-path, ctail-def-groups(True, defs) )


/*
 * Definition Groups
 */

fun ctail-def-groups( top-level : bool, defs : defGroups ) : <newtypesEff, ctail, exn, div> defGroups
  val dss = def.map fn ( def )
    ctail-def-group( top-level, def )
  dss.flatten

fun ctail-def-group( top-level : bool, def-group : defGroup ) : <newtypesEff, ctail, exn, div> list<defGroup>
  match def-group
    DefRec(Cons(def, Nil)) -> 
      if def.tname.has-ctail-call( True, def.expr ) then
        top-level.ctail-def( def )
    _ -> [def-group]

/*
 * we generate
 * - if the runtime can copy contexts (set-context-path)
 * - otherwise, a single definition of the effect is affine for sure (always-affine)
 * - or two definitions for multiple resumptions (is-multi)
 */
fun ctail-def( top-level : bool, def : def ) : <newtypesEff, ctail, exn, div> list<defGroup>
  def.with-current-def
    val res-ref-type = def.ktype.has-result-ref-type
    match res-ref-type
      Nothing -> [DefRec([def])]
      Just((tforall, targs, teff, tres)) ->
        val ctail-slot-type = tres.type-cctx
        val ctail-name = "trmc".make-hidden-name(def.name)
        val ctail-slot = "acc".new-hidden-name
        val ctail-type = TForAll(tforall, TFun(targs ++ [(ctail-slot, ctail-slot-type)], teff, tres))
        val ctail-tname = TName(ctail-name, ctail-type)
        val ctail-tslot = TName(ctail-slot, ctail-slot-type)

        val always-affine = teff.effect-is-affine
        val cdef-expr = ctail-name.with-context( False, always-affine, Just( ctail-tslot ), ctailExpr( True, def.expr.make-cdef-expr( ctail-tslot )))

        val use-context-path = get-env().useContextPath
        val cdef = def ( name = ctail-name, ktype = ctail-type, expr = cdef-expr )
        val needs-multi = !( use-context-path || always-affine )
        val ctail-multi-slot-type = TFun( [(name/nil, tres)], typeTotal, tres )
        val ctail-multi-name = "trmcm".make-hidden-name(def.name)
        val ctail-multi-slot = "accm".new-hidden-name
        val ctail-multi-type = TForAll( tforall, TFun( targs ++ [(ctail-multi-slot, ctail-multi-slot-type)], teff, tres ) )
        val ctail-multi-tname = TName( ctail-multi-name, ctail-multi-type )
        val ctail-multi-tslot = TName( ctail-multi-slot, ctail-multi-slot-type )
        val ctail-multi-var = Var( ctail-multi-tname, InfoArity( tforall.length, targs.length + 1 ) )

        val wrap-expr = with-context( ctail-multi-name, False, always-affine, Nothing) 
          val param = if needs-multi then
            Just( ctail-multi-var )
          else
            Nothing
          ctail-wrapper( ctail-tslot, param, def.expr )

        // todo: check if rec is needed (only if there are non-tail calls left over)
        if !needs-multi then
          // for sure, each op resumes at most once
          [DefRec([cdef, def( expr = wrap-expr )])]
        else
          // some ops may resume more than once; specialize for those
          val cdef-multi-expr = with-context( ctail-multi-name, True /* isMulti */, always-affine, Just( ctail-multi-tslot ) )
            ctail-expr( True, ctail-multi-tslot.make-cdef-expr( def.expr ) )
          val cdef-multi = def( name = ctail-multi-name, ktype = ctail-multi-type, expr = cdef-multi-expr )
          [DefRec([cdef, cdef-multi, def( expr = wrap-expr )])]


        
fun make-cdef-expr( expr : expr, slot : tName ) : <exn, div> expr
  match expr
    TypeLam( targs, body ) -> TypeLam( targs, body.make-cdef-expr( slot ) )
    Lam( args, eff, body ) -> Lam( args ++ [slot], eff, body )
    body -> ("core/ctail: illegal ctail function shape: " ++ body.show).throw(ExnError)

fun has-result-ref-type( tp : ktype) : <newtypesEff, ctail, exn, div> maybe<(list<typeVar>, list<(name, ktype)>, keffect, ktype)>
  match tp.split-fun-scheme
    Just((foralls, targs, teff, tres)) ->
      val is-r-type = tres.has-ref-type
      if is-r-type then
        Just((foralls, targs, teff, tres))
      else
        Nothing
    _ -> Nothing

fun has-ref-type( tp : ktype ) : <newtypesEff, ctail, exn, div> bool
  match tp.expand-syn
    TApp( t, ts ) -> t.has-ref-type
    TCon( tcon ) -> !( tcon.name.is-value-type )
    _ -> False


/*
 * Primitives
 */

// Polymorphic hole
fun make-hole( tp : ktype ) : expr
  val a = TypeVar( 0, kindStar, Bound )
  val fun-type = TForAll( [a], TFun( [], typeTotal, TVar( a ) ) )
  App( TypeApp( Var( TName( name-cctx-hole-create(), fun-type ), InfoExternal( [] ) ), [tp] ), [] )

// Initial empty context (@ctx hole)
fun make-cctx-empty( tp : ktype ) : expr
  val a = TypeVar( 0, kindStar, Bound )
  val fun-type = TForAll( [a], TFun( [], typeTotal, TVar( a ).type-cctx ) )
  App( TypeApp( Var( TName( name-cctx-empty(), fun-type ),
    // InfoArity 1 0
    InfoExternal([(C(CDefault), "kk_cctx_create(#1,#2,kk_context())"), (JS(JsDefault), "$std_core_types._cctx_create(#1,#2)")]),
    [tp] ) ), [] )

// The address of a field in a constructor (for context holes)
fun make-field-addr-of( obj-name : tName, con-name : tName, field-name : name, tp : ktype ) : expr
  val a = TypeVar( 0, kindStar, Bound )
  val fun-type = TForAll( [a], TFun( [(name/nil, TVar( a )), (name/nil, typeString), (name/nil, typeString)], 
    typeTotal, TApp( typeFieldAddr, [ TVar( a )] ) ) )
  App( TypeApp( Var( TName( name-field-addr-of(), funType ), InfoExternal( [] ) ) ), [tp] )

// Extend a context with a non-empty context
fun make-cctx-extend( slot : tName, res-name : tName, object-name : tName, con-name : tName, field-name : name, tp : ktype, always-affine : bool ) : expr
  val field-of = make-field-addr-of( object-name, con-name, field-name, tp )
  val a = TypeVar( 0, kindStar, Bound )
  val fun-type = TForAll( [a], TFun( [(name/nil, TVar( a )),
                                      (name/nil, TVar( a )),
                                      (name/nil, TApp( typeFieldAddr, [TVar( a )] ) )], typeTotal, TVar( a ).type-cctx ) )
  App( TypeApp( Var( TName( name-cctx-extend(), funType ), 
    (InfoExternal [
      (C( CDefault), "kk_cctx_extend" ++ (if always-affine then "_linear" else "") ++ "(#1,#2,#3,kk_context())"),
      (JS( JsDefault), "$std_core_types._cctx_extend(#1,#2,#3)") 
    ]), [tp] ) ), [Var( slot, InfoNone ), Var( res-name, InfoNone, field-of )])

fun make-cctx-apply( is-multi : boole, is-always-affine : bool, slot : tName, expr : expr ) : expr
  match is-multi
    True ->
      App( Var( slot, InfoNone ), [expr] )
    False ->
      val a = TypeVar( 0, kindStar, Bound )
      val fun-type = TForAll( [a], TFun( [(name/nil, TVar( a )), (name/nil, TVar( a ))], typeTotal, TVar( a ) ) )
      val tp = match slot.type-of
        TApp( _, Cons( t, Nil ) ) -> t
        TSyn( _, Cons( t, Nil ), _) -> t
      App( TypeApp( Var( TName( name-cctx-apply(), funType ),
        InfoExternal [(C( CDefault ), "kk_cctx_apply" ++ (if is-always-affine then "_linear" else "") ++ "(#1,#2,kk_context())"),
          (JS( JsDefault ), "$std_core_types._cctx_apply(#1,#2)") 
        ]), [tp] ), [Var( slot, InfoNone ), expr] )

/*
 * CTail Monad
 */

struct ctail-env
  currentDef : list<def>
  gamma : gamma
  name : tName
  slot : maybe<tName>
  isMulti : bool
  useContextPath : bool
  alwaysAffine : bool

effect ctail
  fun get-env() : ctail-env
  fun get-current-def() : list<def>
  fun get-gamma() : gamma
  fun get-name() : tName
  fun get-slot() : maybe<tName>
  fun get-is-multi() : bool
  fun get-use-context-path() : bool
  fun get-always-affine() : bool



fun with-env<a>( action : () -> <ctail|e> a, transform: (ctail-env) -> <ctail|e> ctail-env ) : <ctail|e> a
  val env = get-env().transform
  with override
    fun get-env() env
    fun get-current-def() env.currentDef
    fun get-gamma() env.gamma
    fun get-name() env.name
    fun get-slot() env.slot
    fun get-is-multi() env.isMulti
    fun get-use-context-path() env.useContextPath
    fun get-always-affine() env.alwaysAffine
  action()

fun ctail-run<a>( newtypes : newtypes, gamma : gamma, use-context-path : bool, action : () -> <ctail|e> a ) : <ppEnvEff, ctail, unique|e> a
  val env = Ctail-env( [], gamma, use-context-path, TName( name/nil, typeUnit ), Nothing, True, use-context-path, False )
  with handler
    fun get-env() env
    fun get-current-def() env.currentDef
    fun get-gamma() env.gamma
    fun get-name() env.name
    fun get-slot() env.slot
    fun get-is-multi() env.isMulti
    fun get-use-context-path() env.useContextPath
    fun get-always-affine() env.alwaysAffine
  action()


fun with-context<a>( name: tName, is-multi : bool, always-affine : bool, mb-slot : maybe<tName>, action : () -> <ctail|e> a ) : <ctail|e> a
  action.with-env fn ( env ) 
    env( name = name, isMulti = is-multi, alwaysAffine = always-affine, slot = mb-slot )

/*
 * env accessors
 */

fun with-current-def<a>( def : def, action : () -> <ctail> a ) : <ctail> a
  action.with-env fn ( env ) 
    env( currentDef = Cons(def, env.currentDef) )
    

/*
 * state accessors
 */

fun is-value-type( name : name ) : <newtypesEff, ctail, exn> bool
  val env = get-env()
  match name.newtypes-lookup-any
    Just( data-info ) -> 
      data-info.data-repr(data/is-value).fst.dataRepr/is-value
    _ -> False

