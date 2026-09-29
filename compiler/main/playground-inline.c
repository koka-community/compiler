// The playground's two primitives that the standard library lacks: reading all of
// stdin, and writing to stderr (stdout carries only the JSON result).

#include <stdio.h>

kk_string_t kk_playground_read_stdin(kk_context_t* ctx) {
  size_t cap = 4096, len = 0;
  char* buf = (char*)kk_malloc((kk_ssize_t)cap, ctx);
  size_t n;
  while ((n = fread(buf + len, 1, cap - len, stdin)) > 0) {
    len += n;
    if (len == cap) {
      cap *= 2;
      buf = (char*)kk_realloc(buf, (kk_ssize_t)cap, ctx);
    }
  }
  kk_string_t s = kk_string_alloc_from_qutf8n((kk_ssize_t)len, buf, ctx);
  kk_free(buf, ctx);
  return s;
}

kk_unit_t kk_playground_eprintln(kk_string_t s, kk_context_t* ctx) {
  kk_ssize_t len;
  const char* cs = kk_string_cbuf_borrow(s, &len, ctx);
  fwrite(cs, 1, (size_t)len, stderr);
  fputc('\n', stderr);
  fflush(stderr);
  kk_string_drop(s, ctx);
  return kk_Unit;
}
