// Koka generated module: h2, koka version: 3.2.7
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
 
 
// // runtime tag for the effect `:ask`
export var ask_fs__at_tag;
var ask_fs__at_tag = $std_core_hnd._new_htag("ask@h2.kk");
// type ask 
export function _Hnd_ask(_cfc, _fun_ask) /* forall<e1,a> (int, hnd/clause0<int,h2/ask,e1,a>) -> h2/ask<e1,a> */  {
  return { _cfc: _cfc, _fun_ask: _fun_ask };
}
 
// declarations
 
 
// // Automatically generated. Retrieves the `@cfc` constructor field of the `:` type.
export function ask_fs__at_cfc(ask_0) /* forall<e1,a> (ask : h2/ask<e1,a>) -> int */  {
  return ask_0._cfc;
}
 
 
// // handler for the effect `:ask`
export function ask_fs__at_handle(hnd, ret, action) /* forall<a,e1,b> (hnd : h2/ask<e1,b>, ret : (res : a) -> e1 b, action : () -> <h2/ask|e1> a) -> e1 b */  {
  return $std_core_hnd._hhandle(ask_fs__at_tag, hnd, ret, action);
}
 
 
// // Automatically generated. Retrieves the `@fun-ask` constructor field of the `:` type.
export function ask_fs__at_fun_ask(ask_0) /* forall<e1,a> (ask : h2/ask<e1,a>) -> hnd/clause0<int,h2/ask,e1,a> */  {
  return ask_0._fun_ask;
}
 
 
// // select `ask` operation out of the effect `:ask`
//  handler
export function ask_fs__at_select(hnd) /* forall<e1,a> (hnd : h2/ask<e1,a>) -> hnd/clause0<int,h2/ask,e1,a> */  {
  return hnd._fun_ask;
}
 
export function ask() /* () -> h2/ask int */  {
  return $std_core_hnd._perform0($std_core_hnd._evv_at(($std_core_hnd._open_none1($std_core_types._make_ssize__t, 0))), ask_fs__at_select);
}
 
 
// // monadic lift
export function _mlift_main_42(_y_dot_34) /* forall<_e1> (int) -> <h2/ask,console/console|_e1> () */  {
   
  var _x1_40 = $std_core_hnd._open_none1($std_core_int.show, _y_dot_34);
  return $std_core_hnd._open_none1($std_core_console.string_fs_println, _x1_40);
}
 
export function main() /* () -> () */  {
  return ask_fs__at_handle(_Hnd_ask(1, $std_core_hnd.clause_tail0(function() {
         
        $std_core_console.string_fs_println("asked");
        return 21;
      })), function(_res /* () */ ) {
      return _res;
    }, function() {
      return $std_core_hnd.yield_bind($std_core_hnd._open_at0($std_core_hnd._evv_index(ask_fs__at_tag), ask), function(_y_dot_34 /* int */ ) {
          return _mlift_main_42(_y_dot_34);
        });
    });
}
 
// main entry:
main($std_core.id);