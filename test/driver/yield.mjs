// Koka generated module: yield, koka version: 3.2.7
"use strict";
 
// imports
import * as $std_core from './std_core.mjs';
import * as $std_core_types from './std_core_types.mjs';
import * as $std_core_undiv from './std_core_undiv.mjs';
import * as $std_core_unsafe from './std_core_unsafe.mjs';
import * as $std_core_hnd from './std_core_hnd.mjs';
import * as $std_core_exn from './std_core_exn.mjs';
import * as $std_core_bool from './std_core_bool.mjs';
import * as $std_core_order from './std_core_order.mjs';
import * as $std_core_int from './std_core_int.mjs';
import * as $std_core_char from './std_core_char.mjs';
import * as $std_core_vector from './std_core_vector.mjs';
import * as $std_core_bytes from './std_core_bytes.mjs';
import * as $std_core_show from './std_core_show.mjs';
import * as $std_core_string from './std_core_string.mjs';
import * as $std_core_sslice from './std_core_sslice.mjs';
import * as $std_core_list from './std_core_list.mjs';
import * as $std_core_bslice from './std_core_bslice.mjs';
import * as $std_core_debug from './std_core_debug.mjs';
import * as $std_core_console from './std_core_console.mjs';
import * as $std_core_maybe from './std_core_maybe.mjs';
import * as $std_core_maybe2 from './std_core_maybe2.mjs';
import * as $std_core_either from './std_core_either.mjs';
import * as $std_core_result from './std_core_result.mjs';
import * as $std_core_tuple from './std_core_tuple.mjs';
import * as $std_core_lazy from './std_core_lazy.mjs';
import * as $std_core_delayed from './std_core_delayed.mjs';
 
// externals
 
// type declarations
 
 
// // runtime tag for the effect `:yield`
export var yield_fs__at_tag;
var yield_fs__at_tag = $std_core_hnd._new_htag("yield@yield.kk");
// type yield 
export function _Hnd_yield(_cfc, _ctl_yield) /* forall<e1,a> (int, hnd/clause1<int,bool,yield/yield,e1,a>) -> yield/yield<e1,a> */  {
  return { _cfc: _cfc, _ctl_yield: _ctl_yield };
}
 
// declarations
 
 
// // Automatically generated. Retrieves the `@cfc` constructor field of the `:` type.
export function yield_fs__at_cfc(yield_0) /* forall<e1,a> (yield : yield/yield<e1,a>) -> int */  {
  return yield_0._cfc;
}
 
 
// // handler for the effect `:yield`
export function yield_fs__at_handle(hnd, ret, action) /* forall<a,e1,b> (hnd : yield/yield<e1,b>, ret : (res : a) -> e1 b, action : () -> <yield/yield|e1> a) -> e1 b */  {
  return $std_core_hnd._hhandle(yield_fs__at_tag, hnd, ret, action);
}
 
 
// // Automatically generated. Retrieves the `@ctl-yield` constructor field of the `:` type.
export function yield_fs__at_ctl_yield(yield_0) /* forall<e1,a> (yield : yield/yield<e1,a>) -> hnd/clause1<int,bool,yield/yield,e1,a> */  {
  return yield_0._ctl_yield;
}
 
 
// // select `yield` operation out of the effect `:yield`
//  handler
export function yield_fs__at_select(hnd) /* forall<e1,a> (hnd : yield/yield<e1,a>) -> hnd/clause1<int,bool,yield/yield,e1,a> */  {
  return hnd._ctl_yield;
}
 
export function $yield(i) /* (i : int) -> yield/yield bool */  {
  return $std_core_hnd._perform1($std_core_hnd._evv_at(($std_core_hnd._open_none1($std_core_types._make_ssize__t, 0))), yield_fs__at_select, i);
}
 
 
// // monadic lift
export function _mlift_traverse_52(xx, _y_dot_38) /* forall<_e1,_e2> (xx : list<int>, bool) -> <yield/yield|_e2> () */  {
  if (_y_dot_38) {
    return $std_core_hnd._open_at1($std_core_hnd._evv_index(yield_fs__at_tag), traverse, xx);
  }
  else {
    return $std_core_types.Unit;
  }
}
 
export function traverse(xs) /* (xs : list<int>) -> yield/yield () */  {
  if (xs !== null) {
    return $std_core_hnd.yield_bind2($std_core_hnd._open_at1($std_core_hnd._evv_index(yield_fs__at_tag), $yield, xs.head), function(_y_dot_38 /* bool */ ) {
        return _mlift_traverse_52(xs.tail, _y_dot_38);
      }, function(_y_dot_38_0 /* bool */ ) {
        if (_y_dot_38_0) {
          return $std_core_hnd._open_at1($std_core_hnd._evv_index(yield_fs__at_tag), traverse, xs.tail);
        }
        else {
          return $std_core_types.Unit;
        }
      });
  }
  else {
    return $std_core_types.Unit;
  }
}
 
export function main() /* () -> () */  {
  return yield_fs__at_handle(_Hnd_yield(3, $std_core_hnd.clause_control1(function(i /* int */ , resume /* (bool) -> <console/console|_"10353"> () */ ) {
         
        $std_core_console.string_fs_println($std_core_types._lp__plus__plus__rp_("yielded ", $std_core_int.show(i)));
        return resume($std_core_types._int_le(i,2));
      })), function(_res /* () */ ) {
      return _res;
    }, function() {
      return $std_core_hnd._open_at1($std_core_hnd._evv_index(yield_fs__at_tag), traverse, $std_core_types.Cons(1, $std_core_types.Cons(2, $std_core_types.Cons(3, $std_core_types.Cons(4, $std_core_types.Nil)))));
    });
}
 
// main entry:
main($std_core.id);