/* Koka <-> isocline glue, in the shape of std/text/regex.kk's regex-inline.c:
   the library itself is linked (see `library="isocline"` in isocline.kk and
   scripts/install-isocline.sh), and only this thin marshalling layer is
   inlined into the generated C. */
#include <isocline.h>

kk_std_core_types__maybe kk_ic_readline(kk_string_t prompt, kk_context_t* ctx) {
  char* line = ic_readline(kk_string_cbuf_borrow(prompt, NULL, ctx));
  kk_string_drop(prompt, ctx);
  /* NULL on EOF (ctrl-D) or when another thread called ic_async_stop() */
  if (line == NULL) return kk_std_core_types__new_Nothing(ctx);
  kk_string_t s = kk_string_alloc_from_qutf8(line, ctx);
  ic_free(line);
  return kk_std_core_types__new_Just(kk_string_box(s), ctx);
}

bool kk_ic_async_stop(kk_context_t* ctx) {
  kk_unused(ctx);
  return ic_async_stop();
}

kk_unit_t kk_ic_set_history(kk_string_t fname, int32_t max_entries, kk_context_t* ctx) {
  const char* f = kk_string_cbuf_borrow(fname, NULL, ctx);
  ic_set_history(f[0] == 0 ? NULL : f, (long)max_entries);
  kk_string_drop(fname, ctx);
  return kk_Unit;
}

kk_unit_t kk_ic_history_add(kk_string_t entry, kk_context_t* ctx) {
  ic_history_add(kk_string_cbuf_borrow(entry, NULL, ctx));
  kk_string_drop(entry, ctx);
  return kk_Unit;
}

kk_unit_t kk_ic_history_remove_last(kk_context_t* ctx) {
  kk_unused(ctx); ic_history_remove_last(); return kk_Unit;
}

kk_unit_t kk_ic_enable_auto_tab(bool enable, kk_context_t* ctx) {
  kk_unused(ctx); ic_enable_auto_tab(enable); return kk_Unit;
}

kk_unit_t kk_ic_enable_color(bool enable, kk_context_t* ctx) {
  kk_unused(ctx); ic_enable_color(enable); return kk_Unit;
}

kk_unit_t kk_ic_style_def(kk_string_t name, kk_string_t fmt, kk_context_t* ctx) {
  ic_style_def(kk_string_cbuf_borrow(name, NULL, ctx), kk_string_cbuf_borrow(fmt, NULL, ctx));
  kk_string_drop(name, ctx); kk_string_drop(fmt, ctx);
  return kk_Unit;
}

kk_unit_t kk_ic_set_prompt_marker(kk_string_t marker, kk_string_t cont_marker, kk_context_t* ctx) {
  ic_set_prompt_marker(kk_string_cbuf_borrow(marker, NULL, ctx),
                       kk_string_cbuf_borrow(cont_marker, NULL, ctx));
  kk_string_drop(marker, ctx); kk_string_drop(cont_marker, ctx);
  return kk_Unit;
}
