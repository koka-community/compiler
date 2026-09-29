/* Koka <-> POSIX filesystem glue, in the shape of compiler/lib/isocline-inline.c.

   Both entry points here replace shell-outs that cost a fork+exec per call.
   `file-mtime` was `sh -c "stat -f %m ... || stat -c %Y ..."` and the atomic
   write was `mktemp` + `mv -f` -- MEASURED at ~8ms per spawn against ~2.4us
   for the syscall. mtimes are queried per module AND per dependency by the
   staleness check; the atomic write runs three times per compiled module
   (.kki, .c, .h), so that was six spawns per module. */
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <time.h>

/* Nanoseconds, not whole seconds: a dependency rewritten in the same second
   as its dependent's interface must still compare as newer. */
static int64_t kk_compiler_stat_mtime_ns(const struct stat* st) {
#if defined(__APPLE__)
  return (int64_t)st->st_mtimespec.tv_sec * 1000000000 + st->st_mtimespec.tv_nsec;
#elif defined(__linux__)
  return (int64_t)st->st_mtim.tv_sec * 1000000000 + st->st_mtim.tv_nsec;
#else
  return (int64_t)st->st_mtime * 1000000000;
#endif
}

kk_integer_t kk_compiler_file_mtime(kk_string_t p, kk_context_t* ctx) {
  struct stat st;
  const char* cpath = kk_string_cbuf_borrow(p, NULL, ctx);
  /* 0 for a missing or unreadable file: callers treat that as infinitely
     stale, which is the same answer the shell version gave. So an existing
     file is never 0, even where the file system records no times at all (the
     playground's in-memory WASI file system reports 0 for every file). */
  int64_t r = 0;
  if (cpath != NULL && stat(cpath, &st) == 0) {
    r = kk_compiler_stat_mtime_ns(&st);
    if (r <= 0) r = 1;
  }
  kk_string_drop(p, ctx);
  return kk_integer_from_int64(r, ctx);
}

/* Wall-clock time on the scale of `kk_compiler_file_mtime`. */
kk_integer_t kk_compiler_epoch_nanos(kk_context_t* ctx) {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  return kk_integer_from_int64((int64_t)ts.tv_sec * 1000000000 + ts.tv_nsec, ctx);
}

/* Write `content` to a unique temp file in the DESTINATION's own directory,
   then rename it over the destination. `rename(2)` within one filesystem is
   atomic, so a concurrent reader sees either the old file or the complete new
   one -- never a half-written interface or C file. Several koka processes
   share one build cache (8 sweep workers do exactly this), which is why the
   write cannot simply truncate-and-write in place.

   Returns false on any failure; the Koka side then falls back to a plain
   (non-atomic) write, as the shell version did when `mktemp` was missing. */
bool kk_compiler_write_atomic(kk_string_t path, kk_string_t content, kk_context_t* ctx) {
  kk_ssize_t clen = 0;
  const char* cpath = kk_string_cbuf_borrow(path, NULL, ctx);
  const char* cbuf  = kk_string_cbuf_borrow(content, &clen, ctx);
  bool ok = false;
#if !defined(__wasi__)   /* wasi-libc has no mkstemp; a WASI build has one writer anyway */
  if (cpath != NULL && cbuf != NULL) {
    /* temp file must live in the same directory as the destination, or the
       rename would cross filesystems and lose atomicity */
    const char* slash = strrchr(cpath, '/');
    size_t dlen = (slash == NULL) ? 1 : (size_t)(slash - cpath);
    char* tmp = (char*)malloc(dlen + 16);
    if (tmp != NULL) {
      if (slash == NULL) tmp[0] = '.'; else memcpy(tmp, cpath, dlen);
      memcpy(tmp + dlen, "/.kkw-XXXXXX", 13);  /* includes the NUL */
      int fd = mkstemp(tmp);
      if (fd >= 0) {
        ok = true;
        /* mkstemp creates 0600; generated artifacts are ordinary build output */
        (void)fchmod(fd, 0644);
        kk_ssize_t off = 0;
        while (off < clen) {
          ssize_t w = write(fd, cbuf + off, (size_t)(clen - off));
          if (w <= 0) { ok = false; break; }
          off += (kk_ssize_t)w;
        }
        if (close(fd) != 0) ok = false;
        if (ok && rename(tmp, cpath) != 0) ok = false;
        if (!ok) (void)unlink(tmp);
      }
      free(tmp);
    }
  }
#endif
  kk_string_drop(path, ctx);
  kk_string_drop(content, ctx);
  return ok;
}

/* Read at most `max_bytes` from the head of a file.

   An interface's import block is the first thing in the file, but interfaces
   are far larger than their sources -- compiler/compile/build is 83KB of
   source against a 5.77MB .kki -- so slurping the whole thing to read 25 lines
   is 69x more I/O than just parsing the source would have been. */
kk_string_t kk_compiler_read_head(kk_string_t p, kk_integer_t max_bytes, kk_context_t* ctx) {
  const char* cpath = kk_string_cbuf_borrow(p, NULL, ctx);
  kk_ssize_t cap = (kk_ssize_t)kk_integer_clamp_ssize_t(max_bytes, ctx);
  kk_string_t out = kk_string_empty();
  if (cpath != NULL && cap > 0) {
    FILE* f = fopen(cpath, "rb");
    if (f != NULL) {
      char* buf = (char*)malloc((size_t)cap + 1);
      if (buf != NULL) {
        size_t n = fread(buf, 1, (size_t)cap, f);
        buf[n] = 0;
        /* a truncated multi-byte sequence at the cut is possible; the caller
           only scans ASCII `import` lines well before the cut, and
           `alloc_from_qutf8` sanitises anything invalid */
        out = kk_string_alloc_from_qutf8(buf, ctx);
        free(buf);
      }
      fclose(f);
    }
  }
  kk_string_drop(p, ctx);
  return out;
}
