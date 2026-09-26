// Request/reply over thread-safe channels: the boundary discipline for the
// parallel build.
//
// WHY THIS EXISTS
// ---------------
// Effects must not cross a thread boundary -- a handled operation performed on a
// worker would look up evidence belonging to the spawning thread. Handlers at the
// BOUNDARY are the answer: a worker keeps writing direct-style effectful code, and
// a handler translates each operation into a message. Only data crosses.
//
// THE SHAPE
// ---------
//   worker --Rpc(arg, its own reply sender)--> server (owner loop)
//   worker <--------------reply--------------- server
//
// A `spawn-thread` worker runs its OWN async loop (its body is `<async,ioc>`), so
// it can both `xemit` a request and `xreceive` the reply on an inbox it owns.
// `compute` cannot: its body is `ioc`, with no `async` to await on.
//
// Each request carries its own reply address, so the server needs no routing
// table and no correlation ids.
//
// RULES (std/async/api/uv/thread.kk)
//   * `xsender` is the ONLY half that may cross a thread. Give a worker
//     `chan.sender`, never the `xchannel` (which holds an owner-side Koka
//     channel with non-atomic mutable state).
//   * `xemit` is callable from any thread; `xreceive`/`close` are owner-only --
//     "owner" meaning the loop that CREATED that channel, so a worker may freely
//     receive on the inbox it made for itself.
//   * `spawn-thread` is DETACHED: process exit does not wait for workers. Always
//     await an explicit completion message.
//
// Use ONE CHANNEL PER CONCERN (work, results, requests, diagnostics) rather than
// a single channel carrying a union of every message type.
//
// Worked example: scratchpad/rpc/rpcdemo.kk (4 workers x 5 round-trips).
// Keep worker bodies inline or unannotated -- annotating a worker function tends
// to duplicate `ndet` in the row (`ioc` has one, `xreceive` adds another) and the
// boundary then fails to unify.
module compiler/compile/rpc

import std/async
import std/async/thread

// A request paired with the address its reply should go to.
pub struct rpc<a, b>
  arg   : a
  reply : xsender<b>

// ---------------------------------------------------------------------------
// Client side (runs ON a worker thread)
// ---------------------------------------------------------------------------

// A client endpoint: where to send requests, plus this worker's own inbox.
pub struct rpc-client<a, b>
  requests : xsender<rpc<a, b>>
  inbox    : xchannel<b>

// Create a client on the CURRENT loop. Call this inside the worker, never on the
// owner: the inbox must belong to the loop that will receive on it.
pub fun rpc-client(requests: xsender<rpc<a, b>>): async rpc-client<a, b>
  Rpc-client(requests, xchannel())

// One round-trip: send `arg` with our reply address, then wait for the answer.
// NOTE the row is `<async,ioc>`, NOT `<async,ndet,ioc>`: `ioc` already contains
// `ndet`, and naming it again yields a row with a duplicate label that will not
// unify at a `spawn-thread` boundary (whose body must be exactly `<async,ioc>`).
pub fun call(c: rpc-client<a, b>, arg: a): <async,ioc> b
  c.requests.xemit(Rpc(arg, c.inbox.sender))
  c.inbox.xreceive

// Release the inbox when the worker is done (owner-only op, and the worker owns it).
pub fun rpc-client/close(c: rpc-client<a, b>): ioc ()
  c.inbox.close

// ---------------------------------------------------------------------------
// Server side (runs on the OWNER loop)
// ---------------------------------------------------------------------------

// Serve exactly `n` requests with `serve-fn`, replying to each caller's address.
// `n` is known when the caller knows how many calls are outstanding; use
// `serve-while` when it is not.
pub fun serve(requests: xchannel<rpc<a, b>>, n: int, serve-fn: (a) -> <async,ioc|e> b): <async,ioc|e> ()
  if n <= 0 then () else
    val r = requests.xreceive
    r.reply.xemit(serve-fn(r.arg))
    serve(requests, n - 1, serve-fn)

// Serve until `more()` says stop, checking between requests. Use when the number
// of requests is dynamic (e.g. workers discovering dependencies as they parse).
pub fun serve-while(requests: xchannel<rpc<a, b>>, more: () -> <async,ioc|e> bool, serve-fn: (a) -> <async,ioc|e> b): <async,ioc|e> ()
  if !more() then () else
    val r = requests.xreceive
    r.reply.xemit(serve-fn(r.arg))
    serve-while(requests, more, serve-fn)

// Drain any requests already delivered to this loop without blocking. Lets an
// orchestrator interleave serving with its own bookkeeping.
pub fun serve-pending(requests: xchannel<rpc<a, b>>, serve-fn: (a) -> <async,ioc|e> b): <async,ioc|e> int
  match requests.try-xreceive
    Nothing -> 0
    Just(r) ->
      r.reply.xemit(serve-fn(r.arg))
      1 + serve-pending(requests, serve-fn)
