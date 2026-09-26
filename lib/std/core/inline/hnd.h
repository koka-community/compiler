





/*---------------------------------------------------------------------------
  Copyright 2020-2021, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/
typedef kk_datatype_ptr_t kk_std_core_hnd__ev_t;
static inline kk_std_core_hnd__ev_t kk_std_core_hnd__ev_dup(kk_std_core_hnd__ev_t _x, kk_context_t* ctx);

typedef struct kk_evv_vector_s {
  struct kk_block_s     _block;
  kk_std_core_hnd__ev_t vec[1];
} *kk_evv_vector_t;


typedef kk_datatype_ptr_t kk_evv_t;   // either a kk_evv_vector_t, or a single evidence

static inline kk_evv_t kk_evv_dup(kk_evv_t evv, kk_context_t* ctx) {
  return kk_datatype_ptr_dup(evv,ctx);
}

static inline void kk_evv_drop(kk_evv_t evv, kk_context_t* ctx) {
  kk_datatype_ptr_drop(evv,ctx);
}

static inline kk_evv_t kk_evv_empty(kk_context_t* ctx) {
  // the address of a link-time constant; no call, and no dup because the
  // block's refcount is stuck (see kk_evv_empty_static_block in kklib.h)
  return kk_datatype_from_ptr(&kk_evv_empty_static_block, ctx);
}

static inline bool kk_evv_is_empty(kk_evv_t evv, kk_context_t* ctx) {  // todo: optimize
  kk_evv_t empty = kk_evv_empty(ctx);
  bool eq = kk_datatype_eq(evv,empty);
  kk_datatype_ptr_drop(empty,ctx);
  return eq;
}

static inline bool kk_evv_is_vector(kk_evv_t evv, kk_context_t* ctx) {
  return kk_datatype_ptr_has_tag(evv,KK_TAG_EVV_VECTOR,ctx);
}

static inline kk_std_core_hnd__ev_t kk_evv_as_ev( kk_evv_t evv, kk_context_t* ctx ) {
  kk_unused_internal(ctx);
  kk_assert_internal(!kk_evv_is_vector(evv,ctx));
  return evv;
}

static inline kk_evv_t kk_ev_as_evv( kk_std_core_hnd__ev_t ev, kk_context_t* ctx ) {
  kk_unused(ctx);
  return ev;
}

static inline kk_evv_vector_t kk_evv_as_vector( kk_evv_t evv, kk_context_t* ctx ) {
  kk_assert_internal(kk_evv_is_vector(evv,ctx));
  return kk_datatype_as_assert(kk_evv_vector_t,evv,KK_TAG_EVV_VECTOR,ctx);
}

// Evidence-vector integrity checks.
//
// COMPILED IN only for debug builds (`KK_DEBUG_FULL`, i.e. `--buildtype=debug`
// and below) or explicitly with `-DKK_EVV_CHECK=1`; release builds contain none
// of this and pay nothing. Even when compiled in they stay off until
// `KOKA_EVV_CHECK` is set in the environment (1 = report, 2 = abort at the first
// violation). See `hnd.c` for the checks themselves.
//
// The invariant: a statically computed evidence index is derived from the
// handled labels of a KNOWN effect row, and row polymorphism can only make the
// runtime vector LONGER than that static prefix -- never shorter. So an index at
// or past the end always means the vector is smaller than the type at this point
// promised, and the fault is upstream of here.
#if !defined(KK_EVV_CHECK)
#if defined(KK_DEBUG_FULL)
#define KK_EVV_CHECK 1
#else
#define KK_EVV_CHECK 0
#endif
#endif

#if KK_EVV_CHECK
kk_decl_export int       kk_evv_check_level(void);
kk_decl_export void      kk_evv_note(const char* op, kk_evv_t evv, int arg, kk_context_t* ctx);
kk_decl_export void      kk_evv_oob(const char* where, kk_ssize_t i, kk_ssize_t len, kk_context_t* ctx);
#else
#define kk_evv_check_level()          (0)
#define kk_evv_note(op,evv,arg,ctx)   ((void)0)
#define kk_evv_oob(w,i,n,ctx)         ((void)0)
#endif

static inline kk_std_core_hnd__ev_t kk_evv_at( kk_ssize_t i, kk_context_t* ctx ) {
  kk_evv_t evv = ctx->evv;
  if (!kk_evv_is_vector(evv,ctx)) {  // evv is a single evidence
    kk_assert_internal(i==0);
    if kk_unlikely(kk_evv_check_level() > 0 && i != 0) { kk_evv_oob("kk_evv_at", i, 1, ctx); }
    return kk_evv_as_ev(kk_evv_dup(evv,ctx),ctx);
  }
  else {  // evv as a vector
    kk_assert_internal(i >= 0 && i < (kk_block_scan_fsize(kk_datatype_as_ptr(evv,ctx))));
    if kk_unlikely(kk_evv_check_level() > 0) {
      kk_ssize_t n = kk_block_scan_fsize(kk_datatype_as_ptr(evv,ctx));
      if (i < 0 || i >= n) { kk_evv_oob("kk_evv_at", i, n, ctx); return kk_evv_as_ev(kk_evv_dup(evv,ctx),ctx); }
    }
    kk_evv_vector_t vec = kk_evv_as_vector(evv,ctx);
    return kk_std_core_hnd__ev_dup(vec->vec[i],ctx);
  }
}

static inline kk_evv_t kk_evv_get(kk_context_t* ctx) {
  return kk_evv_dup(ctx->evv,ctx);
}

static inline kk_unit_t kk_evv_set(kk_evv_t evv, kk_context_t* ctx) {
  kk_evv_drop(ctx->evv, ctx);
  ctx->evv = evv;
  if kk_unlikely(kk_evv_check_level() > 0) { kk_evv_note("evv_set", evv, 0, ctx); }
  return kk_Unit;
}

static inline kk_evv_t kk_evv_swap(kk_evv_t evv, kk_context_t* ctx) {
  kk_evv_t evv0 = ctx->evv;
  ctx->evv = evv;
  if kk_unlikely(kk_evv_check_level() > 0) { kk_evv_note("evv_swap", evv, 0, ctx); }
  return evv0;
}

static inline bool kk_evv_eq(kk_evv_t evv1, kk_evv_t evv2, kk_context_t* ctx) {  // TODO:make borrowing
  bool eq = kk_datatype_eq(evv1,evv2);
  kk_evv_drop(evv1,ctx);
  kk_evv_drop(evv2,ctx);
  return eq;
}

static inline kk_evv_t kk_evv_swap_create0(kk_context_t* ctx) {
  return kk_evv_swap(kk_evv_empty(ctx),ctx);
}

static inline kk_evv_t kk_evv_swap_create1(kk_ssize_t i, kk_context_t* ctx) {
  kk_evv_t evv0 = ctx->evv;
  if (kk_evv_is_vector(evv0,ctx)) {
    if kk_unlikely(kk_evv_check_level() > 0) { kk_evv_note("evv_swap_create1", evv0, (int)i, ctx); }
    ctx->evv = kk_evv_at(i, ctx);   // bounds-checked there
    return evv0;
  }
  else {
    kk_assert_internal(i==0);
    return kk_evv_dup(evv0,ctx);  // already a single evidence
  }
}

struct kk_std_core_hnd_Htag;
kk_ssize_t      kk_evv_index( struct kk_std_core_hnd_Htag htag, kk_context_t* ctx );
kk_evv_t        kk_evv_create(kk_evv_t evv, kk_vector_t indices, kk_context_t* ctx);
kk_evv_t        kk_evv_insert(kk_evv_t evv, kk_std_core_hnd__ev_t ev, kk_context_t* ctx);
kk_evv_t        kk_evv_delete(kk_evv_t evv, kk_ssize_t index, bool behind, kk_context_t* ctx);
kk_string_t     kk_evv_show(kk_evv_t evv, kk_context_t* ctx);
kk_unit_t       kk_evv_guard(kk_evv_t evv, kk_context_t* ctx);
kk_evv_t        kk_evv_swap_create( kk_vector_t indices, kk_context_t* ctx );
bool            kk_evv_is_affine(kk_context_t* ctx);

static inline kk_evv_t kk_evv_swap_delete(kk_ssize_t i, bool behind, kk_context_t* ctx) {
  kk_evv_t evv0 = ctx->evv;
  ctx->evv = kk_evv_delete(kk_evv_dup(evv0,ctx), i, behind, ctx);
  return evv0;
}

struct kk_std_core_hnd_yld_s;
typedef int32_t kk_marker_t;

kk_box_t        kk_fatal_resume_final(kk_context_t* ctx);
kk_box_t        kk_yield_cont( kk_function_t next, kk_context_t* ctx );
kk_box_t        kk_yield_extend( kk_function_t next, kk_context_t* ctx );
kk_box_t        kk_yield_final( kk_marker_t m, kk_function_t clause, kk_context_t* ctx );
kk_function_t   kk_yield_to( kk_marker_t m, kk_function_t clause, kk_context_t* ctx );
struct kk_std_core_hnd_yld_s  kk_yield_prompt( kk_marker_t m, kk_context_t* ctx );

kk_box_t        kk_yield_capture(kk_context_t* ctx);
kk_box_t        kk_yield_reyield(kk_box_t yld, kk_context_t* ctx);


