import compiler/core/core
import compiler/core/pretty
import compiler/type/assumption
import compiler/kind/newtypes
import compiler/type/type
import compiler/common/name
import compiler/type/pretty

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


pub fun uctail-optimize( newtypes : newtypes, gamma : gamma, use-context-path : bool, defs : defGroups) : <newtypesEff, ppEnvEff, uniquePhase, exn, div> defGroups
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
fun ctail-def( top-level : bool, def : def ) : <newtypesEff, ctail, exn, div> list<def>
  def.with-current-def
    val res-ref-type = def.ktype.has-result-ref-type
    match res-ref-type
      Nothing -> [DefRec([def])]
      Just((tforall, targs, teff, tres)) ->
        val ctail-slot-type = tres.type-cc-tx
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
  fun get-state() : int
  fun set-state( unique : int ) : ()
  fun modify-state( transform : (int) -> int ) : ()

fun with-env<a>( action : () -> <local<h>, ctail|e> a, transform: (ctail-env) -> e ctail-env ) : <local<h>, ctail|e> a
  val env = get-env().transform
  var unique := get-state()
  with handler
    fun get-env() env
    fun get-state() unique
    fun set-state( new-unique : int ) unique := new-unique
    fun modify-state( transform : (int) -> int ) unique := transform(unique)
  action()

fun ctail-run<a>( newtypes : newtypes, gamma : gamma, use-context-path : bool, action : () -> <ctail|e> a ) : <ppEnvEff, ctail, uniquePhase|e> a
  val env = Ctail-env( [], gamma, use-context-path, TName( name/nil, typeUnit ), Nothing, True, use-context-path, False )
  var state := get-unique()
  with handler
    fun get-env() env
    fun get-state() state
    fun set-state( unique : int ) state := unique
    fun modify-state( transform : (int) -> int ) state := transform(state)
  set-unique(state)
  action()


fun with-context<a>( name: tName, is-multi : bool, always-affine : bool, mb-slot : maybe<tName>, action : () -> <ctail|e> a ) : a
  action.with-env fn ( env ) 
    env( name = name, isMulti = is-multi, alwaysAffine = alwaysAffine, slot = mb-slot )

/*
 * env accessors
 */

fun with-current-def<a>( def : def, action : () -> <ctail> a ) : <ctail> a
  action.with-env fn ( env ) 
    env( current-def = def )
    

/*
 * state accessors
 */

fun is-value-type( name : name ) : <newtypesEff, ctail, exn> bool
  val env = get-env()
  match name.newtypes-lookup-any
    Just( data-info ) -> 
      data-info.data-repr(data/is-value).fst.dataRepr/is-value
    _ -> False

