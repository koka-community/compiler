/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// Cooperative fallback threading backend for `std/async/thread`.
//
// Web and wasi hosts have no OS threads, so `compute` degrades to a cooperative
// strand: yield to the loop once (giving other strands a chance to run), then
// run `work` inline on the single thread. Same API as the native backend, so
// applications stay portable.
module async/api/coop/thread

import async/async
import async/channel

// Run `work` cooperatively: yield to other strands, then compute inline.
pub fun await-compute( work : () -> ioc a ) : <async,ioc> a
  yield()
  work()

// ----------------------------------------------------------------
// thread-safe channel + spawn-thread: on a single-threaded cooperative host
// there ARE no other threads, so an `xchannel` is just a plain channel and
// `native-threads()` is False (callers gate real threading on it). The API
// matches the native backend so `std/async/thread` stays host-consistent.

pub value struct xchannel<a>( chan : channel<a> )
pub value struct xsender<a>( chan : channel<a> )

// Accepted for API parity with the native backend; there are no OS threads to schedule.
pub type thread-priority
  Background
  Normal
  Interactive

pub fun native-threads() : bool
  False

pub fun xchannel() : async xchannel<a>
  Xchannel(channel())

pub fun xchannel/sender( x : xchannel<a> ) : xsender<a>
  Xsender(x.chan)

pub fun xsender/xemit( s : xsender<a>, value : a ) : ioc ()
  s.chan.emit-io(value)

pub fun xchannel/xemit( x : xchannel<a>, value : a ) : ioc ()
  x.chan.emit-io(value)

pub fun xchannel/xreceive( x : xchannel<a> ) : <async,ndet> a
  x.chan.receive

pub fun xchannel/try-xreceive( x : xchannel<a> ) : <async,ndet> maybe<a>
  x.chan.try-receive

// No native handle to close on a cooperative host; a no-op for API parity.
// (Unlike native, emits after `close` still deliver here -- but on a correctly
// gated single-threaded host nothing emits after close anyway.)
pub fun xchannel/close( x : xchannel<a> ) : ioc ()
  ()

// No OS threads here: gated out by `native-threads()`. On js/wasm hosts this is
// a TRUE no-op: the body is NOT run (not even inline -- running it inline would
// silently change concurrency semantics and can deadlock, e.g. a body that
// `xreceive`s values the caller only emits after `spawn-thread` returns).
// Deliberately inert rather than throwing, since it is never reached on a
// correctly-gated path: check `native-threads()` before relying on a worker.
pub fun spawn-thread( body : () -> <async,ioc> (), priority : thread-priority = Normal ) : ioc ()
  ()
