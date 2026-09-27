// JSON-RPC 2.0 with LSP's `Content-Length` framing.
//
// Transport-independent: it pulls bytes from a `read` function and pushes them
// to a `write` function, so stdio (compiler/lsp/stdio.kk) and a future socket
// transport share this layer unchanged.
//
// Framing (LSP base protocol):
//     Content-Length: <n>\r\n
//     [Content-Type: ...\r\n]
//     \r\n
//     <n bytes of UTF-8 JSON>
//
// `n` counts BYTES, not characters, which is why the transport hands over
// `bytes` and decoding happens only once a whole message has arrived.
module compiler/lsp/jsonrpc

import std/num/int32
import std/num/float64
import compiler/lib/json

pub type message
  // a call expecting a response (`id` is a string or a number; kept as the raw
  // json so it round-trips into the response exactly as the client sent it)
  Request(id: json, method: string, params: json)
  // fire-and-forget
  Notification(method: string, params: json)
  // the client's ANSWER to a request the SERVER made (it carries an `id` but no
  // `method`). We make such requests -- `window/workDoneProgress/create` -- and
  // without this case the reply parsed as a method-less Request and drew an
  // "unsupported method: " error back at the client.
  Response(id: json)

// JSON-RPC error codes from the spec, plus LSP's own
pub val parse-error-code = -32700
pub val invalid-request-code = -32600
pub val method-not-found-code = -32601
pub val invalid-params-code = -32602
pub val internal-error-code = -32603

//----------------------------------------------------------------------
// framing
//----------------------------------------------------------------------

// Split a buffer into the first complete message and the remainder.
// `Nothing` means "need more bytes" -- the caller reads another chunk and
// retries with the longer buffer.
pub fun take-message(buf: bytes): <exn,div> maybe<(string, bytes)>
  match buf.find-header-end
    Nothing -> Nothing
    Just(hdr-end) ->
      val header = buf.subbytes(0, hdr-end).substring
      match header.content-length
        Nothing -> throw("jsonrpc: message header without a Content-Length: " ++ header.show)
        Just(n) ->
          val rest = buf.subbytes(hdr-end)
          if rest.length < n then Nothing      // body not fully arrived yet
          else Just((rest.subbytes(0, n).substring, rest.subbytes(n)))

// Index just past the blank line that ends the header block. Tolerates bare
// `\n` as well as `\r\n`: some clients (and every hand-written test) use it.
fun find-header-end(b: bytes): _ maybe<int>
  fun go(i: int): _ maybe<int>
    if i + 1 >= b.length then Nothing
    elif b[i] == 13 && b[i+1] == 10 then
      if i + 3 < b.length && b[i+2] == 13 && b[i+3] == 10 then Just(i + 4)
      elif i + 2 < b.length && b[i+2] == 10 then Just(i + 3)
      else go(i + 1)
    elif b[i] == 10 && b[i+1] == 10 then Just(i + 2)
    else go(i + 1)
  go(0)

fun content-length(header: string): maybe<int>
  header.lines.foldl(Nothing) fn(acc, line)
    match acc
      Just -> acc
      Nothing ->
        val l = line.trim
        if !l.to-lower.starts-with("content-length:").bool then Nothing
        else l.list.drop("content-length:".count).string.trim.parse-int

// Frame a payload for sending. The length is in BYTES.
pub fun frame(payload: string): bytes
  val body = payload.string/bytes
  ("Content-Length: " ++ body.length.show ++ "\r\n\r\n").bytes ++ body

//----------------------------------------------------------------------
// messages
//----------------------------------------------------------------------

pub fun parse-message(payload: string): <exn,div> message
  val j = payload.parse-json
  val method = j.field("method").as-string.default("")
  val params = j.field("params").default(JSObj([]))
  match j.field("id")
    Just(id) -> if method == "" then Response(id) else Request(id, method, params)
    Nothing -> Notification(method, params)

pub fun response(id: json, result: json): string
  JSObj([("jsonrpc", JSString("2.0")), ("id", id), ("result", result)]).show

pub fun error-response(id: json, code: int, msg: string): string
  JSObj([("jsonrpc", JSString("2.0")), ("id", id),
         ("error", JSObj([("code", JSInt(code)), ("message", JSString(msg))]))]).show

pub fun notification(method: string, params: json): string
  JSObj([("jsonrpc", JSString("2.0")), ("method", JSString(method)), ("params", params)]).show

//----------------------------------------------------------------------
// json helpers (std/data/json has encoders/decoders but no lookup)
//----------------------------------------------------------------------

pub fun field(j: json, key: string): maybe<json>
  match j
    JSObj(kvs) -> kvs.lookup(fn(k) k == key)
    _ -> Nothing

pub fun as-string(mj: maybe<json>): maybe<string>
  match mj
    Just(JSString(s)) -> Just(s)
    _ -> Nothing

pub fun as-bool(mj: maybe<json>): maybe<bool>
  match mj
    Just(JSBool(b)) -> Just(b)
    _ -> Nothing

pub fun as-int(mj: maybe<json>): maybe<int>
  match mj
    Just(JSInt(i)) -> Just(i)
    Just(JSNum(d)) -> Just(d.int)
    _ -> Nothing

//----------------------------------------------------------------------
// serve loop
//----------------------------------------------------------------------

// Pump messages from `read` to `on-message`, writing whatever it emits.
//
// `on-message` returns updated state plus ZERO OR MORE outgoing payloads: a
// request usually yields one response, a document-change notification yields no
// response but one `publishDiagnostics`, and `exit` yields none. `Nothing` for
// the state ends the loop (that is how `exit` stops the server).
//
// `read` returns an EMPTY chunk at end of input. Transport-agnostic on purpose:
// stdio passes `stdio/read-chunk`/`stdio/write-bytes`, a socket transport would
// pass its own.
pub alias reader<e> = () -> <exn,div|e> bytes
pub alias writer<e> = (bytes) -> <exn,div|e> ()
pub alias msg-handler<s,e> = (s, message) -> <exn,div|e> (maybe<s>, list<string>)
// Run when no more messages are buffered, just before blocking on input. This
// is where expensive deferred work belongs: a burst of edits arrives as many
// messages, and reacting to each one in turn does the same work repeatedly for
// results that are immediately superseded.
pub alias idle-handler<s,e> = (s) -> <exn,div|e> (s, list<string>)

pub fun serve(read: reader<e>, write: writer<e>, init: s, on-message: msg-handler<s,e>,
              on-idle: idle-handler<s,e> = fn(st) (st, [])): <exn,div|e> s
  fun go(st, buf: bytes, idle-done: bool)
    match buf.take-message
      Just((payload, rest)) ->
        val (mbst, outs) = match try({ payload.parse-message })
          Ok(m) -> on-message(st, m)
          Error(err) -> (Just(st), [error-response(JSNull, parse-error-code, err.message)])
        outs.foreach(fn(out) write(out.frame))
        match mbst
          // more may already be buffered; deferred work waits until it is not
          Just(st2) -> go(st2, rest, False)
          Nothing -> st
      Nothing | !idle-done ->
        // buffer drained: do the deferred work, then look again -- handling it
        // may itself have produced output, and more input may have arrived
        val (st2, outs) = on-idle(st)
        outs.foreach(fn(out) write(out.frame))
        go(st2, buf, True)
      Nothing ->
        val chunk = read()
        if chunk.is-empty then st        // end of input
        else go(st, buf ++ chunk, False)
  go(init, bytes/empty, True)

// Split framed input into whole payloads and push them onto `sink`, until end
// of input. Runs as its OWN strand so that reading never waits on whatever is
// processing the messages -- which is what lets a long compile be superseded by
// a newer edit instead of blocking it.
pub fun read-loop(read: reader<e>, sink: (maybe<string>) -> <exn,div|e> ()): <exn,div|e> ()
  fun go(buf: bytes)
    match buf.take-message
      Just((payload, rest)) ->
        sink(Just(payload))
        go(rest)
      Nothing ->
        val chunk = read()
        if chunk.is-empty then sink(Nothing)   // end of input
        else go(buf ++ chunk)
  go(bytes/empty)

// LSP work-done progress. The server must ask the client to create the token
// first (`window/workDoneProgress/create`); the reply is a `Response` we ignore.
pub fun progress-create(token: string): string
  JSObj([("jsonrpc", JSString("2.0")), ("id", JSString("wd-" ++ token)),
         ("method", JSString("window/workDoneProgress/create")),
         ("params", JSObj([("token", JSString(token))]))]).show

pub fun progress-begin(token: string, title: string): string
  notification("$/progress", JSObj([("token", JSString(token)),
    ("value", JSObj([("kind", JSString("begin")), ("title", JSString(title)),
                     ("cancellable", JSBool(False)), ("percentage", JSInt(0))]))]))

// A report with no percentage: the phase feed knows WHAT it is doing but not
// how far along it is (upstream sends a percentage because its build tracks a
// work total; ours reports per module via `on-progress` instead).
pub fun progress-message(token: string, msg: string): string
  notification("$/progress", JSObj([("token", JSString(token)),
    ("value", JSObj([("kind", JSString("report")), ("message", JSString(msg))]))]))

pub fun progress-report(token: string, msg: string, pct: int): string
  notification("$/progress", JSObj([("token", JSString(token)),
    ("value", JSObj([("kind", JSString("report")), ("message", JSString(msg)),
                     ("percentage", JSInt(pct))]))]))

pub fun progress-end(token: string, msg: string): string
  notification("$/progress", JSObj([("token", JSString(token)),
    ("value", JSObj([("kind", JSString("end")), ("message", JSString(msg))]))]))
