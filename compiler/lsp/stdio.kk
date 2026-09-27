// Nonblocking stdio transport.
//
// The language server protocol runs JSON-RPC over stdin/stdout. Reading stdin
// must not block the event loop -- a server has to stay responsive to
// cancellation and to progress reporting while a compile is running -- so
// stdin is a libuv stream read through `await`, one chunk at a time.
//
// This is the transport only: framing and JSON-RPC live in `jsonrpc.kk`, so a
// socket transport can be dropped in later without touching either.
module compiler/lsp/stdio

import std/async
import std/async/internal

// libuv as std/async's event loop links it (lib/std/async/api/uv/evloop.kk):
// from vcpkg, so a machine without a system libuv still builds this module
extern import
  c { vcpkg="libuv"; library="uv" }

extern import
  c file "stdio-inline.c"

// Read the next chunk of stdin. An EMPTY result means end-of-input.
//
// Bytes, not a string: a chunk boundary can fall in the middle of a UTF-8
// codepoint, and decoding half a codepoint would corrupt it. The framing layer
// accumulates bytes and decodes only whole messages.
pub fun read-chunk(): <async,ioc> bytes
  val r = await-error("lsp/stdin") fn(evloop, resume)
    match prim-stdin-read(evloop, resume)
      Ok(_) -> Ok(fn() prim-stdin-stop())
      Error(e) -> Error(e)
  match r
    Ok(b) -> b
    Error(_) -> bytes/empty       // treat a transport error as end-of-input

pub fun write-bytes(b: bytes): ioc ()
  prim-stdout-write(b)

// Take fd 1 for the protocol and send everything else to stderr. Call ONCE,
// before any frame is written. See the C side for why this is not optional.
pub fun claim-stdout(): ioc ()
  prim-stdout-claim()

extern prim-stdin-read(evloop: event-loop, resume: (bytes) -> ioc ()): ioc error<()>
  c "kk_lsp_stdin_read"

extern prim-stdin-stop(): ioc ()
  c "kk_lsp_stdin_stop"

extern prim-stdout-write(b: bytes): ioc ()
  c "kk_lsp_stdout_write"

extern prim-stdout-claim(): ioc ()
  c "kk_lsp_stdout_claim"
