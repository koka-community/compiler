import compiler/common/id
import compiler/common/name

pub effect unique
  fun update-unique( f : (int) -> int ) : int

pub fun set-unique( i : int) : unique int
  update-unique fn (_) i

pub fun get-unique() : unique int
  update-unique fn (x) x + 1

pub fun get-uniques( n : int ) : unique list<int>
  list(1, n).map fn (_) get-unique()

pub fun unique-id( base-name: string ) : unique id
  val i = get-unique()
  base-name.gen-id( i )

pub fun unique-ids( base-name: string, n : int ) : unique list<id>
  val ids = get-uniques( n )
  ids.map fn (i) base-name.gen-id( i )

pub fun unique-name( pre : string ) : unique name
  val i = get-unique()
  pre.new-hidden-name-ex( i.show )

pub fun unique-name-from( base-name : string ) : unique name
  val i = get-unique()
  i.to-hidden-unique-name( "uniq", base-name )

pub fun with-unique<a>( f : (int) -> (a, int) ) : unique a
  val u = get-unique()
  val (x, u') = f( u )
  set-unique( u' )
  x
  
pub fun run-unique<a>( init : int, f : (int) -> <unique|e> a ) : e (a, state)
  var state := init
  with handler
    fun update-unique( g : (int) -> int ) : int
      val old = state
      state := g( state )
      old
  val result = f( state )
  (result, state)
