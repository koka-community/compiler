// Koka generated module: t_maybe, koka version: 3.2.7
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
 
export function lookup_it(x) /* (x : int) -> maybe<int> */  {
  if ($std_core_types._int_gt(x,0)) {
    return $std_core_types.Just($std_core_types._int_mul(x,2));
  }
  else {
    return $std_core_types.Nothing;
  }
}
 
 
// // monadic lift
export function _mlift_main_6(v_0_0, _c_dot_4) /* (v@0@0 : int, ()) -> () */  {
  var _x2 = lookup_it(-1);
  if (_x2 !== null) {
    var _x1 = $std_core_types._lp__plus__plus__rp_("got ", $std_core_int.show(_x2.value));
  }
  else {
    var _x1 = "nothing";
  }
  return $std_core_console.string_fs_println(_x1);
}
 
export function main() /* () -> console/console () */  {
  var _x4 = lookup_it(5);
  if (_x4 !== null) {
    var _x3 = $std_core_types._lp__plus__plus__rp_("got ", $std_core_int.show(_x4.value));
  }
  else {
    var _x3 = "nothing";
  }
  return $std_core_hnd.yield_bind2($std_core_console.string_fs_println(_x3), function(_c_dot_4 /* () */ ) {
      return _mlift_main_6(v_0_0, _c_dot_4);
    }, function(_c_dot_4_0 /* () */ ) {
      var _x6 = lookup_it(-1);
      if (_x6 !== null) {
        var _x5 = $std_core_types._lp__plus__plus__rp_("got ", $std_core_int.show(_x6.value));
      }
      else {
        var _x5 = "nothing";
      }
      return $std_core_console.string_fs_println(_x5);
    });
}
 
// main entry:
main($std_core.id);