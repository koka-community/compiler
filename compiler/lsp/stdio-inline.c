/* Nonblocking stdin over libuv, for the JSON-RPC transport (see stdio.kk).

   Prototypes from std/async/api/uv/evloop.h are repeated here rather than
   included: `extern import c file` INLINES this file into the generated C,
   where a local `#include` cannot resolve. The definitions link from
   std/async's own object. */
#include <uv.h>
#ifdef _WIN32
#include <io.h>
#define kk_lsp_write _write
#else
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <poll.h>
#define kk_lsp_write write
#endif

typedef kk_box_t kk_uv_loop_t;
uv_loop_t* kk_uv_loop(kk_uv_loop_t loop_borrowed, kk_context_t* ctx);
kk_std_core_exn__error kk_result_ok(kk_box_t val, kk_context_t* ctx);
kk_std_core_exn__error kk_error_from_uv_errno(int uv_err, kk_context_t* ctx);

/* stdin is read one chunk at a time (an `await`-shaped API wants exactly one
   outstanding read), through whichever libuv mechanism fd 0 actually supports:

     pipe/socket  uv_pipe_open + uv_read_start   -- how an LSP client connects
     tty          uv_tty_init  + uv_read_start
     regular file uv_fs_read                     -- `prog < file`

   The last case is why `uv_guess_handle` is consulted: uv STREAMS do not
   support regular files, and `uv_pipe_open` on a redirected file silently
   never delivers EOF, so the process hangs forever instead of exiting. */
static uv_stream_t*  kk_lsp_stdin   = NULL;   /* stream modes only */
static kk_function_t kk_lsp_cb;
static bool          kk_lsp_pending = false;
static int           kk_lsp_kind    = -1;     /* uv_handle_type, -1 = not probed */
static int64_t       kk_lsp_offset  = 0;      /* file mode read offset */

#define KK_LSP_BUFSZ (64*1024)

static void kk_lsp_alloc(uv_handle_t* h, size_t suggested, uv_buf_t* buf) {
  kk_unused(h);
  buf->base = (char*)kk_malloc((kk_ssize_t)suggested, kk_get_context());
  buf->len  = (buf->base == NULL ? 0 : suggested);
}

/* An empty chunk means end-of-input; the Koka side treats it as EOF. */
static void kk_lsp_deliver(kk_ssize_t len, const uint8_t* p, kk_context_t* ctx) {
  if (!kk_lsp_pending) return;
  kk_lsp_pending = false;
  kk_function_t cb = kk_lsp_cb;
  uint8_t* buf;
  kk_bytes_t b = kk_bytes_alloc_len(len, len, p, &buf, ctx);
  kk_function_call(kk_unit_t, (kk_function_t, kk_bytes_t, kk_context_t*), cb, (cb, b, ctx), ctx);
}

static void kk_lsp_close_cb(uv_handle_t* h) {
  kk_free(h, kk_get_context());
}

static void kk_lsp_read_cb(uv_stream_t* s, ssize_t nread, const uv_buf_t* buf) {
  kk_context_t* ctx = kk_get_context();
  /* nread == 0 is libuv's EAGAIN: no data yet, not end of input. Keep reading.
     Taking it for EOF closed stdin, and the server exited cleanly (status 0) in
     the middle of a session, whenever a long check left the client's messages
     arriving while the stream had nothing to hand over. */
  if (nread == 0) {
    if (buf->base != NULL) kk_free(buf->base, ctx);
    return;
  }
  uv_read_stop(s);
  if (nread > 0) {
    kk_lsp_deliver((kk_ssize_t)nread, (const uint8_t*)buf->base, ctx);
  }
  else {
    /* UV_EOF or a read error. CLOSE the handle: an open (even if stopped)
       stdin handle keeps uv_run alive, so the process would otherwise linger
       after the client disconnects. */
    kk_lsp_stdin = NULL;
    uv_close((uv_handle_t*)s, &kk_lsp_close_cb);
    kk_lsp_deliver(0, NULL, ctx);
  }
  if (buf->base != NULL) kk_free(buf->base, ctx);
}

/* The request and its buffer are per-read, not static: `kk_lsp_deliver` re-enters
   Koka, which immediately starts the NEXT read -- reusing one `uv_fs_t` from
   inside its own callback silently drops that read, and the process then waits
   forever for an EOF that never arrives. Both are freed BEFORE delivering. */
static void kk_lsp_fs_cb(uv_fs_t* req) {
  kk_context_t* ctx = kk_get_context();
  ssize_t n = (ssize_t)req->result;
  char* buf = (char*)req->data;
  uv_fs_req_cleanup(req);
  kk_free(req, ctx);
  if (n > 0) {
    kk_lsp_offset += n;
    kk_lsp_deliver((kk_ssize_t)n, (const uint8_t*)buf, ctx);
  }
  else {
    kk_lsp_deliver(0, NULL, ctx);   /* 0 = EOF, <0 = error */
  }
  if (buf != NULL) kk_free(buf, ctx);
}

kk_std_core_exn__error kk_lsp_stdin_read(kk_box_t loop, kk_function_t cb, kk_context_t* ctx) {
  uv_loop_t* l = kk_uv_loop(loop, ctx);
  if (kk_lsp_pending) { kk_function_drop(cb, ctx); return kk_error_from_uv_errno(UV_EALREADY, ctx); }
  if (kk_lsp_kind < 0) kk_lsp_kind = (int)uv_guess_handle(0);

  if (kk_lsp_kind == UV_FILE) {
    char* fsbuf = (char*)kk_malloc(KK_LSP_BUFSZ, ctx);
    uv_fs_t* req = (uv_fs_t*)kk_zalloc(sizeof(uv_fs_t), ctx);
    if (fsbuf == NULL || req == NULL) {
      if (fsbuf) kk_free(fsbuf, ctx);
      if (req) kk_free(req, ctx);
      kk_function_drop(cb, ctx); return kk_error_from_uv_errno(UV_ENOMEM, ctx);
    }
    req->data = fsbuf;
    kk_lsp_cb = cb; kk_lsp_pending = true;
    uv_buf_t b = uv_buf_init(fsbuf, KK_LSP_BUFSZ);
      int e = uv_fs_read(l, req, 0, &b, 1, kk_lsp_offset, &kk_lsp_fs_cb);
    if (e != 0) {
      kk_lsp_pending = false; kk_free(fsbuf, ctx); kk_free(req, ctx);
      kk_function_drop(cb, ctx); return kk_error_from_uv_errno(e, ctx);
    }
    return kk_result_ok(kk_unit_box(kk_Unit), ctx);
  }

  if (kk_lsp_stdin == NULL) {
    int e = 0;
    if (kk_lsp_kind == UV_TTY) {
      uv_tty_t* t = (uv_tty_t*)kk_zalloc(sizeof(uv_tty_t), ctx);
      e = uv_tty_init(l, t, 0, 1);
      if (e != 0) { kk_free(t, ctx); kk_function_drop(cb, ctx); return kk_error_from_uv_errno(e, ctx); }
      kk_lsp_stdin = (uv_stream_t*)t;
    }
    else {
      uv_pipe_t* p = (uv_pipe_t*)kk_zalloc(sizeof(uv_pipe_t), ctx);
      e = uv_pipe_init(l, p, 0);
      if (e == 0) e = uv_pipe_open(p, 0);
      if (e != 0) { kk_free(p, ctx); kk_function_drop(cb, ctx); return kk_error_from_uv_errno(e, ctx); }
      kk_lsp_stdin = (uv_stream_t*)p;
    }
  }
  kk_lsp_cb = cb;
  kk_lsp_pending = true;
  int e = uv_read_start(kk_lsp_stdin, &kk_lsp_alloc, &kk_lsp_read_cb);
  if (e != 0) { kk_lsp_pending = false; kk_function_drop(cb, ctx); return kk_error_from_uv_errno(e, ctx); }
  return kk_result_ok(kk_unit_box(kk_Unit), ctx);
}

kk_unit_t kk_lsp_stdin_stop(kk_context_t* ctx) {
  if (kk_lsp_stdin != NULL) uv_read_stop(kk_lsp_stdin);
  if (kk_lsp_pending) { kk_lsp_pending = false; kk_function_drop(kk_lsp_cb, ctx); }
  return kk_Unit;
}

/* stdout: a plain blocking write is correct here. Responses are small and the
   loop has nothing else to do while one is in flight; going through uv would
   add an ordering hazard for no benefit. */
/* The JSON-RPC stream is fd 1 -- and so is every `println` in the compiler.
   A single stray print corrupts the protocol, and there ARE unconditional ones
   on the failure paths ("link failed for ...", "error: parallel compile of ...
   failed"), which is exactly when a client is least able to cope.

   So claim fd 1 once at startup: `dup` it to a private descriptor that only
   this file writes frames to, then point fd 1 at stderr. Stray output then
   lands on stderr -- which the VS Code extension already surfaces as the
   server's trace channel -- instead of derailing the connection. This is
   structural: it covers prints that do not exist yet. */
static int kk_lsp_out_fd = 1;

kk_unit_t kk_lsp_stdout_claim(kk_context_t* ctx) {
  kk_unused(ctx);
  if (kk_lsp_out_fd == 1) {
#ifdef _WIN32
    int priv = _dup(1);
    if (priv >= 0) { kk_lsp_out_fd = priv; _dup2(2, 1); }
#else
    int priv = dup(1);
    if (priv >= 0) { kk_lsp_out_fd = priv; dup2(2, 1); }
#endif
    /* Line-buffer the redirected stream. C makes stdout FULLY buffered when it
       is not a tty, so phase logging would sit in the FILE* buffer until ~4KB
       had accumulated -- i.e. arrive late, in bursts, or not at all for a short
       build. The client shows this as its trace channel, where the whole point
       is watching a slow compile progress. */
    setvbuf(stdout, NULL, _IOLBF, 0);
  }
  return kk_Unit;
}

kk_unit_t kk_lsp_stdout_write(kk_bytes_t b, kk_context_t* ctx) {
  kk_ssize_t len;
  const uint8_t* p = kk_bytes_buf_borrow(b, &len, ctx);
  kk_ssize_t off = 0;
  while (off < len) {
    ssize_t n = kk_lsp_write(kk_lsp_out_fd, p + off, (size_t)(len - off));
    if (n > 0) { off += (kk_ssize_t)n; continue; }
#ifndef _WIN32
    /* A SHORT WRITE MUST NOT TRUNCATE THE FRAME. fd 1 can be non-blocking --
       O_NONBLOCK lives on the open file description, so a client that opens the
       pipe non-blocking passes that on to us -- and once the pipe fills, write
       returns EAGAIN. Treating that as "done" left a partial body on the wire
       and the client then read the next frame's bytes where a Content-Length
       header should be ("Header must provide a Content-Length property").
       Wait for the pipe to drain and finish the frame instead. */
    if (n < 0 && errno == EINTR) continue;
    if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      struct pollfd pfd;
      pfd.fd = kk_lsp_out_fd; pfd.events = POLLOUT; pfd.revents = 0;
      poll(&pfd, 1, -1);
      continue;
    }
#endif
    break;   /* a real error: the peer is gone, so there is nothing to finish */
  }
  kk_bytes_drop(b, ctx);
  return kk_Unit;
}
