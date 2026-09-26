// Koka generated module: t_var, koka version: 3.2.7
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
 
// declarations
 
 
// // monadic lift
export function _mlift_main_10(x, _y_dot_1) /* forall<$h1,_e1,h2> (x : local-var<h2,int>, int) -> <local<h2>,console/console|_e1> () */  {
  return $std_core_hnd.yield_bind(((x).value = ($std_core_int._lp__plus__rp_(_y_dot_1, 5))), function(wild /* () */ ) {
      return _mlift_main_9(x, wild);
    });
}
 
 
// // monadic lift
export function _mlift_main_9(x, wild) /* forall<$h1,_e1,h2> (x : local-var<h2,int>, wild : ()) -> <local<h2>,console/console|_e1> () */  {
  return $std_core_hnd.yield_bind(((x).value), function(_y_dot_3 /* int */ ) {
      return _mlift_main_8(x, _y_dot_3);
    });
}
 
 
// // monadic lift
export function _mlift_main_8(x, _y_dot_3) /* forall<$h1,_e1,h2> (x : local-var<h2,int>, int) -> <local<h2>,console/console|_e1> () */  {
  return $std_core_hnd.yield_bind(((x).value = ($std_core_int._lp__plus__rp_(_y_dot_3, 10))), function(wild_0 /* () */ ) {
      return _mlift_main_7(x, wild_0);
    });
}
 
 
// // monadic lift
export function _mlift_main_7(x, wild_0) /* forall<$h1,_e1,h2> (x : local-var<h2,int>, wild@0 : ()) -> <local<h2>,console/console|_e1> () */  {
  return $std_core_hnd.yield_bind(((x).value), function(_y_dot_5 /* int */ ) {
      return _mlift_main_6(_y_dot_5);
    });
}
 
 
// // monadic lift
export function _mlift_main_6(_y_dot_5) /* forall<_e1,h1> (int) -> <local<h1>,console/console|_e1> () */  {
  return $std_core_console.string_fs_println($std_core_int.show(_y_dot_5));
}
 
export function main() /* () -> () */  {
  return $std_core_types.local_scope(function() {
    return $std_core_hnd.local_var(0, function(x /* local-var<"10209",int> */ ) {
        return $std_core_hnd.yield_bind(((x).value), function(_y_dot_1 /* int */ ) {
            return _mlift_main_10(x, _y_dot_1);
          });
      });
  });
}
 
// main entry:
main($std_core.id);