// Koka generated module: lists, koka version: 3.2.7
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
 
export function main() /* () -> console/console () */  {
  return $std_core_console.string_fs_println($std_core_list.show($std_core_list.map($std_core_types.Cons(1, $std_core_types.Cons(2, $std_core_types.Cons(3, $std_core_types.Nil))), function(x /* int */ ) {
        return $std_core_types._int_mul(x,2);
      }), $std_core_int.show));
}
 
// main entry:
main($std_core.id);