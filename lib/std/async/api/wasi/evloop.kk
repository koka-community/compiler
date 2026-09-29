/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Event loop for a standalone WASI host (`host=wasm`): a single thread and no
// I/O readiness to poll, so the loop is a queue of timers run in due order.
module wasi/evloop

import std/num/int64

extern import
  c file "evloop.c"

pub extern event-loop-init() : any
  c "kk_wasi_loop_init"

pub extern event-loop-run(evloop : any) : ()
  c "kk_wasi_loop_run"

pub extern timer-setup( evloop : any, millisecs : int64, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_wasi_timer_setup"

pub extern immediate-setup( evloop : any, cb : () -> ioc () ) : ioc error<() -> ioc ()>
  c "kk_wasi_immediate_setup"
