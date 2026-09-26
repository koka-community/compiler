// Koka generated module: smoke, koka version: 3.2.7
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
 
export var one;
var one = 1;
 
export function ident(x) /* forall<a> (x : a) -> a */  {
  return x;
}
 
export function twice(f, x) /* forall<a,e1> (f : (a) -> e1 a, x : a) -> e1 a */  {
  return $std_core_hnd.yield_bind(f(x), f);
}
 
export function compose(f, g) /* forall<a,b,c,e1> (f : (a) -> e1 b, g : (c) -> e1 a) -> (x : c) -> e1 b */  {
  return function(x /* "10050" */ ) {
    return $std_core_hnd.yield_bind(g(x), f);
  };
}
 
export var hello;
var hello = "hello driver";
 
export function apply_ident() /* () -> int */  {
  return ident(one);
}