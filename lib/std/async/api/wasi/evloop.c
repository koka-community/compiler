/*---------------------------------------------------------------------------
  Copyright 2026, Tim Whiting, Microsoft Research, Daan Leijen.

  This is free software; you can redistribute it and/or modify it under the
  terms of the Apache License, Version 2.0. A copy of the License can be
  found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

// #include <kklib.h>
#include <time.h>

// Timers are kept in a list sorted by (due time, creation order), so timers due
// at the same time fire in the order they were set up. The loop runs until the
// list is empty: with one thread and no I/O handles, a pending timer is the only
// thing that can still produce work.

typedef struct kk_wasi_timer_s {
  struct kk_wasi_timer_s* next;
  int64_t        due_ns;
  int64_t        id;
  kk_function_t  cb;
} kk_wasi_timer_t;

typedef struct kk_wasi_loop_s {
  kk_wasi_timer_t* timers;
  int64_t          next_id;
} kk_wasi_loop_t;

static int64_t kk_wasi_now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}

static kk_wasi_loop_t* kk_wasi_loop(kk_box_t evloop_borrowed, kk_context_t* ctx) {
  return (kk_wasi_loop_t*)kk_cptr_raw_unbox_borrowed(evloop_borrowed, ctx);
}

kk_box_t kk_wasi_loop_init(kk_context_t* ctx) {
  kk_wasi_loop_t* loop = (kk_wasi_loop_t*)kk_zalloc(sizeof(kk_wasi_loop_t), ctx);
  return kk_cptr_raw_box(&kk_free_fun, loop, ctx);
}

static inline void kk_wasi_call0(kk_function_t f, kk_context_t* ctx) {
  kk_function_call(kk_unit_t, (kk_function_t, kk_context_t*), f, (f, ctx), ctx);  // drops f
}

void kk_wasi_loop_run(kk_box_t evloop, kk_context_t* ctx) {
  kk_wasi_loop_t* loop = kk_wasi_loop(evloop, ctx);
  while (loop != NULL && loop->timers != NULL) {
    kk_wasi_timer_t* t = loop->timers;
    const int64_t wait_ns = t->due_ns - kk_wasi_now_ns();
    if (wait_ns > 0) {
      struct timespec ts = { (time_t)(wait_ns / 1000000000), (long)(wait_ns % 1000000000) };
      nanosleep(&ts, NULL);
    }
    // unlink before the call: the callback may set up or dispose other timers
    loop->timers = t->next;
    kk_function_t cb = t->cb;
    kk_free(t, ctx);
    kk_wasi_call0(cb, ctx);
  }
  kk_box_drop(evloop, ctx);
}

// The dispose function finds its timer by id rather than holding a pointer, so
// disposing a timer that already fired is a no-op instead of a use-after-free.
struct kk_wasi_dispose_s {
  struct kk_function_s _base;
  kk_box_t evloop;
  int64_t  id;
};

static kk_box_t kk_wasi_timer_dispose(kk_function_t fself, kk_context_t* ctx) {
  struct kk_wasi_dispose_s* self = kk_function_as(struct kk_wasi_dispose_s*, fself, ctx);
  kk_wasi_loop_t* loop = kk_wasi_loop(self->evloop, ctx);
  const int64_t id = self->id;
  kk_wasi_timer_t** p = (loop == NULL ? NULL : &loop->timers);
  while (p != NULL && *p != NULL) {
    if ((*p)->id == id) {
      kk_wasi_timer_t* t = *p;
      *p = t->next;
      kk_function_drop(t->cb, ctx);
      kk_free(t, ctx);
      break;
    }
    p = &(*p)->next;
  }
  kk_function_drop(fself, ctx);
  return kk_unit_box(kk_Unit);
}

kk_std_core_exn__error kk_wasi_timer_setup(kk_box_t evloop, int64_t millisecs, kk_function_t cb, kk_context_t* ctx) {
  kk_wasi_loop_t* loop = kk_wasi_loop(evloop, ctx);
  if (millisecs < 0) millisecs = 0;
  kk_wasi_timer_t* t = (kk_wasi_timer_t*)kk_zalloc(sizeof(kk_wasi_timer_t), ctx);
  t->due_ns = kk_wasi_now_ns() + millisecs * 1000000;
  t->id = loop->next_id++;
  t->cb = cb;
  kk_wasi_timer_t** p = &loop->timers;
  while (*p != NULL && (*p)->due_ns <= t->due_ns) { p = &(*p)->next; }
  t->next = *p;
  *p = t;
  struct kk_wasi_dispose_s* d = kk_function_alloc_as(struct kk_wasi_dispose_s, 1, ctx);
  d->_base.fun = kk_kkfun_ptr_box(&kk_wasi_timer_dispose, ctx);
  d->evloop = evloop;   // owned by the dispose function
  d->id = t->id;
  kk_function_t dispose = kk_datatype_from_base(&d->_base, ctx);
  return kk_std_core_types__new_Ok(kk_function_box(dispose, ctx), ctx);
}

kk_std_core_exn__error kk_wasi_immediate_setup(kk_box_t evloop, kk_function_t cb, kk_context_t* ctx) {
  return kk_wasi_timer_setup(evloop, 0, cb, ctx);
}
