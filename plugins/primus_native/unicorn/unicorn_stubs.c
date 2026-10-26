/* The bindings to the C API of Unicorn, see bap_unicorn.mli.

   The hooks call back into OCaml from the emulation, on the thread that
   started it, which holds the runtime lock all the time. An exception
   raised by a hook can not unwind the frames of Unicorn, so it stops
   the emulation and is reraised when uc_emu_start returns. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/signals.h>

#include <unicorn/unicorn.h>

#include "unicorn_regs.h"
#include "bap_native_trace.h"

struct hook {
    uc_hook handle;
    value closure;
    struct engine *engine;
    int write;
    /* the trace, that the native hook of the code records, see
       [fixup], or NULL */
    struct bap_native_trace *trace;
    /* the trace, that the native hook of the accesses records, or NULL */
    struct bap_native_trace *mem;
    /* the sorted addresses, whose instructions the hook of the sites
       sees, see [on_sites], or NULL */
    uint64_t *sites;
    size_t nsites;
    struct hook *next;
};

/* the numbers of the pages of 4KiB, in an open hash, e.g., of the code,
   whose writes the traces keep the bytes of, that they overwrite */
struct pages {
    uint64_t *slots;
    size_t size; /* a power of two */
    size_t used; /* with the removed ones */
};

#define FREE UINT64_MAX
#define GONE (UINT64_MAX - 1)

static size_t pages_find(struct pages *p, uint64_t page) {
    size_t i = (page * 0x9E3779B97F4A7C15ULL >> 32) & (p->size - 1);
    while (p->slots[i] != FREE && p->slots[i] != page) {
        i = (i + 1) & (p->size - 1);
    }
    return i;
}

static int pages_mem(struct pages *p, uint64_t page) {
    return p->size > 0 && p->slots[pages_find(p, page)] == page;
}

static void pages_add(struct pages *p, uint64_t page);

static void pages_grow(struct pages *p) {
    struct pages old = *p;
    size_t size = old.size == 0 ? 64 : 2 * old.size;
    uint64_t *slots = malloc(size * sizeof(uint64_t));
    if (slots == NULL) {
        caml_raise_out_of_memory();
    }
    for (size_t i = 0; i < size; i++) {
        slots[i] = FREE;
    }
    p->slots = slots;
    p->size = size;
    p->used = 0;
    for (size_t i = 0; i < old.size; i++) {
        if (old.slots[i] != FREE && old.slots[i] != GONE) {
            pages_add(p, old.slots[i]);
        }
    }
    free(old.slots);
}

static void pages_add(struct pages *p, uint64_t page) {
    if (pages_mem(p, page)) {
        return;
    }
    if (2 * (p->used + 1) > p->size) {
        pages_grow(p);
    }
    p->slots[pages_find(p, page)] = page;
    p->used++;
}

static void pages_remove(struct pages *p, uint64_t page) {
    if (pages_mem(p, page)) {
        p->slots[pages_find(p, page)] = GONE;
    }
}

/* adds or removes the pages of the region */
static void pages_set(struct pages *p, uint64_t addr, uint64_t size, int in) {
    if (size == 0) {
        return;
    }
    for (uint64_t page = addr >> 12; page <= (addr + size - 1) >> 12; page++) {
        if (in) {
            pages_add(p, page);
        } else {
            pages_remove(p, page);
        }
    }
}

/* the regions, that are mapped, while the emulation is stopped, whose
   writes fill them, so they aren't the changes, that the traces mark */
struct fresh {
    uint64_t addr;
    uint64_t size;
    struct fresh *next;
};

#define PENDING 65536

struct engine {
    uc_engine *uc;
    uc_arch arch;
    struct hook *hooks;
    uc_hook attempt_hook;
    int write_hooks;
    uint64_t attempt;
    /* the writes, since the emulation stopped, see [mark] */
    int running;
    int wrote_regs;
    int wrote_mem;
    struct bap_native_trace_range *wrote; /* the bytes, unless too many, see [PENDING] */
    size_t nwrote;
    int wrote_all;
    struct fresh *fresh;
    struct pages code; /* the executable pages */
    /* the exception that a hook raised, or Val_unit */
    value exn;
};

#define Engine_val(v) (*((struct engine **)Data_custom_val(v)))
/* the context, and the engine, whose context it is, as Unicorn restores
   the bytes of the context into the engine, of whatever size it is */
struct saved_context {
    uc_context *ctx;
    uc_arch arch;
    size_t size;
};

#define Saved_val(v) ((struct saved_context *)Data_custom_val(v))
#define Context_val(v) (Saved_val(v)->ctx)

static void fail(uc_err err) {
    CAMLparam0();
    CAMLlocal1(msg);
    const value *exn = caml_named_value("Bap_unicorn.Error");
    if (exn == NULL) {
        caml_failwith(uc_strerror(err));
    }
    msg = caml_copy_string(uc_strerror(err));
    value args[2] = {Val_int(err), msg};
    caml_raise_with_args(*exn, 2, args);
    CAMLnoreturn;
}

static void check(uc_err err) {
    if (err != UC_ERR_OK) {
        fail(err);
    }
}

static uc_engine *engine_uc(value v) {
    struct engine *e = Engine_val(v);
    if (e->uc == NULL) {
        caml_invalid_argument("Unicorn: the engine is closed");
    }
    return e->uc;
}

static void free_hooks(struct engine *e) {
    struct hook *h = e->hooks;
    while (h != NULL) {
        struct hook *next = h->next;
        caml_remove_generational_global_root(&h->closure);
        free(h->sites);
        free(h);
        h = next;
    }
    e->hooks = NULL;
}

static void free_fresh(struct engine *e) {
    while (e->fresh != NULL) {
        struct fresh *next = e->fresh->next;
        free(e->fresh);
        e->fresh = next;
    }
}

static void close_engine(struct engine *e) {
    if (e->uc != NULL) {
        uc_close(e->uc);
        e->uc = NULL;
    }
    free_hooks(e);
    free_fresh(e);
    free(e->wrote);
    e->wrote = NULL;
    free(e->code.slots);
    e->code.slots = NULL;
    e->code.size = 0;
    e->code.used = 0;
}

static void finalize_engine(value v) {
    struct engine *e = Engine_val(v);
    close_engine(e);
    caml_remove_generational_global_root(&e->exn);
    free(e);
}

static struct custom_operations engine_ops = {
    "bap.unicorn.engine.1",     finalize_engine,
    custom_compare_default,     custom_hash_default,
    custom_serialize_default,   custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

static void finalize_context(value v) {
    uc_context *ctx = Context_val(v);
    if (ctx != NULL) {
        uc_context_free(ctx);
    }
}

static struct custom_operations context_ops = {
    "bap.unicorn.context.1",    finalize_context,
    custom_compare_default,     custom_hash_default,
    custom_serialize_default,   custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

value bap_uc_version(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(r);
    unsigned int major, minor;
    uc_version(&major, &minor);
    r = caml_alloc_tuple(2);
    Store_field(r, 0, Val_int(major));
    Store_field(r, 1, Val_int(minor));
    CAMLreturn(r);
}

value bap_uc_arch_supported(value arch) {
    return Val_bool(uc_arch_supported(Int_val(arch)));
}

value bap_uc_open(value arch, value mode) {
    CAMLparam2(arch, mode);
    CAMLlocal1(r);
    uc_engine *uc;
    check(uc_open(Int_val(arch), Int_val(mode), &uc));
    struct engine *e = malloc(sizeof(struct engine));
    if (e == NULL) {
        uc_close(uc);
        caml_raise_out_of_memory();
    }
    e->uc = uc;
    e->arch = Int_val(arch);
    e->hooks = NULL;
    e->attempt_hook = 0;
    e->write_hooks = 0;
    e->attempt = 0;
    e->running = 0;
    e->wrote_regs = 0;
    e->wrote_mem = 0;
    e->wrote = NULL;
    e->nwrote = 0;
    e->wrote_all = 0;
    e->fresh = NULL;
    e->code.slots = NULL;
    e->code.size = 0;
    e->code.used = 0;
    e->exn = Val_unit;
    caml_register_generational_global_root(&e->exn);
    r = caml_alloc_custom(&engine_ops, sizeof(struct engine *), 0, 1);
    Engine_val(r) = e;
    CAMLreturn(r);
}

value bap_uc_close(value v) {
    /* the engine, that runs, e.g., whose hook closes it, is in use */
    if (Engine_val(v) != NULL && Engine_val(v)->running)
        caml_invalid_argument("Bap_unicorn.close: the engine runs");
    close_engine(Engine_val(v));
    return Val_unit;
}

value bap_uc_set_cpu_model(value v, value model) {
    check(uc_ctl_set_cpu_model(engine_uc(v), Int_val(model)));
    return Val_unit;
}

/* the virtual TLB maps the addresses to themselves, with all accesses,
   as the TLB of a CPU without its MMU does, so that the regions of the
   memory keep their protections; without the hook, the entry allows
   only the access, that filled it, so that the code, that loads from
   a page and stores to it, e.g., to the stack, refills it each time */
static bool fill_tlb(uc_engine *uc, uint64_t addr, uc_mem_type type,
                     uc_tlb_entry *entry, void *data) {
    entry->paddr = addr;
    entry->perms = UC_PROT_ALL;
    return true;
}

value bap_uc_set_tlb_virtual(value v) {
    uc_engine *uc = engine_uc(v);
    uc_hook hook;
    check(uc_ctl_tlb_mode(uc, UC_TLB_VIRTUAL));
    check(uc_hook_add(uc, &hook, UC_HOOK_TLB_FILL, (void *)fill_tlb, NULL, 1,
                      0));
    return Val_unit;
}

value bap_uc_flush_tb(value v) {
    check(uc_ctl_flush_tb(engine_uc(v)));
    return Val_unit;
}

value bap_uc_mem_map(value v, value addr, value size, value perms) {
    struct engine *e = Engine_val(v);
    check(uc_mem_map(engine_uc(v), Int64_val(addr), Int64_val(size),
                     Int_val(perms)));
    pages_set(&e->code, Int64_val(addr), Int64_val(size),
              Int_val(perms) & UC_PROT_EXEC);
    struct fresh *f = malloc(sizeof(struct fresh));
    if (f != NULL) {
        f->addr = Int64_val(addr);
        f->size = Int64_val(size);
        f->next = e->fresh;
        e->fresh = f;
    }
    return Val_unit;
}

value bap_uc_mem_unmap(value v, value addr, value size) {
    check(uc_mem_unmap(engine_uc(v), Int64_val(addr), Int64_val(size)));
    pages_set(&Engine_val(v)->code, Int64_val(addr), Int64_val(size), 0);
    return Val_unit;
}

value bap_uc_mem_protect(value v, value addr, value size, value perms) {
    check(uc_mem_protect(engine_uc(v), Int64_val(addr), Int64_val(size),
                         Int_val(perms)));
    pages_set(&Engine_val(v)->code, Int64_val(addr), Int64_val(size),
              Int_val(perms) & UC_PROT_EXEC);
    return Val_unit;
}

/* neither reading nor writing the memory runs hooks, so the strings
   stay in place */

static void mark_running(struct engine *e, int regs, int mem, uint64_t addr,
                         uint64_t size);

/* the bytes, that are written, while the emulation is stopped, which
   are coalesced, as Primus stores them byte by byte */
static void wrote(struct engine *e, uint64_t addr, uint64_t size) {
    e->wrote_mem = 1;
    if (e->wrote_all) {
        return;
    }
    if (e->nwrote > 0) {
        struct bap_native_trace_range *r = &e->wrote[e->nwrote - 1];
        if (r->addr + r->size == addr) {
            r->size += size;
            return;
        }
    }
    if (e->wrote == NULL) {
        e->wrote = malloc(PENDING * sizeof(struct bap_native_trace_range));
    }
    if (e->wrote == NULL || e->nwrote == PENDING) {
        e->wrote_all = 1;
        return;
    }
    e->wrote[e->nwrote].addr = addr;
    e->wrote[e->nwrote].size = size;
    e->nwrote++;
}

static int is_fresh(struct engine *e, uint64_t addr, uint64_t size) {
    for (struct fresh *f = e->fresh; f != NULL; f = f->next) {
        if (addr >= f->addr && addr + size <= f->addr + f->size) {
            return 1;
        }
    }
    return 0;
}

value bap_uc_mem_write(value v, value addr, value data) {
    struct engine *e = Engine_val(v);
    check(uc_mem_write(engine_uc(v), Int64_val(addr), String_val(data),
                       caml_string_length(data)));
    if (!is_fresh(e, Int64_val(addr), caml_string_length(data))) {
        if (e->running) {
            mark_running(e, 0, 1, Int64_val(addr), caml_string_length(data));
        } else {
            wrote(e, Int64_val(addr), caml_string_length(data));
        }
    }
    return Val_unit;
}

value bap_uc_mem_read(value v, value addr, value len) {
    CAMLparam3(v, addr, len);
    CAMLlocal1(r);
    uc_engine *uc = engine_uc(v);
    if (Long_val(len) < 0)
        caml_invalid_argument("Bap_unicorn.mem_read: a negative size");
    r = caml_alloc_string(Long_val(len));
    check(uc_mem_read(uc, Int64_val(addr), Bytes_val(r), Long_val(len)));
    CAMLreturn(r);
}

value bap_uc_mem_regions(value v) {
    CAMLparam1(v);
    CAMLlocal3(r, cell, region);
    uc_mem_region *regions;
    uint32_t count;
    check(uc_mem_regions(engine_uc(v), &regions, &count));
    r = Val_emptylist;
    for (uint32_t i = count; i > 0; i--) {
        uc_mem_region *x = &regions[i - 1];
        region = caml_alloc_tuple(3);
        Store_field(region, 0, caml_copy_int64(x->begin));
        Store_field(region, 1, caml_copy_int64(x->end));
        Store_field(region, 2, Val_int(x->perms));
        cell = caml_alloc_small(2, Tag_cons);
        Field(cell, 0) = region;
        Field(cell, 1) = r;
        r = cell;
    }
    uc_free(regions);
    CAMLreturn(r);
}

/* The registers are read and written with their own sizes, which
   uc_reg_read2 reports, so that the values do not depend on the byte
   order of the host. The larger registers are read as strings. */

#define REG_BUF 64

static size_t reg_read(uc_engine *uc, int reg, uint8_t *buf) {
    size_t size = REG_BUF;
    memset(buf, 0, REG_BUF);
    check(uc_reg_read2(uc, reg, buf, &size));
    return size;
}

static uint64_t reg_value(const uint8_t *buf, size_t size) {
    switch (size) {
    case 1: return *buf;
    case 2: {
        uint16_t x;
        memcpy(&x, buf, 2);
        return x;
    }
    case 4: {
        uint32_t x;
        memcpy(&x, buf, 4);
        return x;
    }
    case 8: {
        uint64_t x;
        memcpy(&x, buf, 8);
        return x;
    }
    default: caml_invalid_argument("Unicorn.reg_read: a wide register");
    }
}

value bap_uc_reg_read(value v, value reg) {
    uint8_t buf[REG_BUF];
    size_t size = reg_read(engine_uc(v), Int_val(reg), buf);
    return caml_copy_int64(reg_value(buf, size));
}

value bap_uc_reg_write(value v, value reg, value x) {
    uc_engine *uc = engine_uc(v);
    struct engine *e = Engine_val(v);
    if (e->running) {
        mark_running(e, 1, 0, 0, 0);
    } else {
        e->wrote_regs = 1;
    }
    uint8_t buf[REG_BUF];
    size_t size = reg_read(uc, Int_val(reg), buf);
    uint64_t x64 = Int64_val(x);
    switch (size) {
    case 1: buf[0] = x64; break;
    case 2: {
        uint16_t y = x64;
        memcpy(buf, &y, 2);
        break;
    }
    case 4: {
        uint32_t y = x64;
        memcpy(buf, &y, 4);
        break;
    }
    case 8: memcpy(buf, &x64, 8); break;
    default: caml_invalid_argument("Unicorn.reg_write: a wide register");
    }
    check(uc_reg_write2(uc, Int_val(reg), buf, &size));
    return Val_unit;
}

value bap_uc_reg_read_bytes(value v, value reg) {
    uint8_t buf[REG_BUF];
    size_t size = reg_read(engine_uc(v), Int_val(reg), buf);
    return caml_alloc_initialized_string(size, (const char *)buf);
}

value bap_uc_reg_write_bytes(value v, value reg, value data) {
    uc_engine *uc = engine_uc(v);
    struct engine *e = Engine_val(v);
    if (e->running) {
        mark_running(e, 1, 0, 0, 0);
    } else {
        e->wrote_regs = 1;
    }
    uint8_t buf[REG_BUF];
    size_t size = reg_read(uc, Int_val(reg), buf);
    if (caml_string_length(data) != size) {
        caml_invalid_argument("Unicorn.reg_write_bytes: a wrong size");
    }
    memcpy(buf, String_val(data), size);
    check(uc_reg_write2(uc, Int_val(reg), buf, &size));
    return Val_unit;
}

value bap_uc_registers_restored(value v) {
    Engine_val(v)->wrote_regs = 0;
    return Val_unit;
}

value bap_uc_reg_size(value v, value reg) {
    uint8_t buf[REG_BUF];
    return Val_long(reg_read(engine_uc(v), Int_val(reg), buf));
}

value bap_uc_regs(value arch) {
    CAMLparam1(arch);
    CAMLlocal3(r, cell, reg);
    const struct bap_uc_reg *regs = bap_uc_reg_table(Int_val(arch));
    r = Val_emptylist;
    if (regs == NULL) {
        CAMLreturn(r);
    }
    size_t n = 0;
    while (regs[n].name != NULL) {
        n++;
    }
    for (size_t i = n; i > 0; i--) {
        reg = caml_alloc_tuple(2);
        Store_field(reg, 0, caml_copy_string(regs[i - 1].name));
        Store_field(reg, 1, Val_int(regs[i - 1].id));
        cell = caml_alloc_small(2, Tag_cons);
        Field(cell, 0) = reg;
        Field(cell, 1) = r;
        r = cell;
    }
    CAMLreturn(r);
}

static void fixup(struct engine *e);
static void mark(struct engine *e);
static int read_pc(uc_engine *uc, uc_arch arch, uint64_t *pc);
static void invalidate_read_values(struct engine *e, uint64_t pc, int known);

/* The signals, whose OCaml handlers are pending, stop the engine, that
   runs, as OCaml runs its handlers only, when its code runs, e.g., in
   the hooks, and Unicorn may run the code of the program for long
   without them, e.g., a loop. The watcher looks at the signals a few
   times a second, while an engine runs, and stops it, after which the
   handlers run, see [bap_uc_process_signals], e.g., the one of a
   script, which pauses the program to save it. It also stops the
   engine at the deadline of its run, e.g., at the end of the time slice
   of a thread, instead of the timeout of Unicorn, which creates a
   thread for each run. The engine stops at the start of a block, see
   build.cmake of libunicorn. The engine, that runs, is guarded, as it is
   closed, after it stops. On Windows, the signals are not watched, and
   the timeouts are of Unicorn. */
#ifndef _WIN32
#include <pthread.h>
#include <signal.h>
#include <time.h>

/* of the runtime, which declares it only for itself, and which only
   reads the atomic bits of the signals, so the watcher calls it */
CAMLextern int caml_check_pending_signals(void);

static pthread_mutex_t watched_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t watched_changed = PTHREAD_COND_INITIALIZER;
static uc_engine *watched = NULL;
static int interrupted = 0;
static int has_deadline = 0;
static struct timespec deadline;

static int before(const struct timespec *x, const struct timespec *y) {
    return x->tv_sec < y->tv_sec ||
           (x->tv_sec == y->tv_sec && x->tv_nsec < y->tv_nsec);
}

static struct timespec after(long usec) {
    struct timespec t;
    clock_gettime(CLOCK_REALTIME, &t);
    t.tv_sec += usec / 1000000;
    t.tv_nsec += (usec % 1000000) * 1000;
    if (t.tv_nsec >= 1000000000) {
        t.tv_sec += 1;
        t.tv_nsec -= 1000000000;
    }
    return t;
}

static void *watch_signals(void *data) {
    pthread_mutex_lock(&watched_lock);
    for (;;) {
        struct timespec until = after(20 * 1000);
        if (watched != NULL && has_deadline && before(&deadline, &until)) {
            until = deadline;
        }
        pthread_cond_timedwait(&watched_changed, &watched_lock, &until);
        if (watched == NULL) {
            continue;
        }
        struct timespec now = after(0);
        if (caml_check_pending_signals()) {
            interrupted = 1;
            uc_emu_stop(watched);
        } else if (has_deadline && !before(&now, &deadline)) {
            has_deadline = 0;
            uc_emu_stop(watched);
        }
    }
    return NULL;
}

/* the signals go to the threads of OCaml, and not to the watcher */
static void start_watcher(void) {
    sigset_t all, old;
    pthread_t thread;
    sigfillset(&all);
    pthread_sigmask(SIG_SETMASK, &all, &old);
    if (pthread_create(&thread, NULL, watch_signals, NULL) == 0) {
        pthread_detach(thread);
    }
    pthread_sigmask(SIG_SETMASK, &old, NULL);
}

/* the engine runs, at most [usec] microseconds, if it is not 0, and
   the timeout of Unicorn is 0 */
static uint64_t watch(uc_engine *uc, uint64_t usec) {
    static pthread_once_t once = PTHREAD_ONCE_INIT;
    pthread_once(&once, start_watcher);
    pthread_mutex_lock(&watched_lock);
    watched = uc;
    has_deadline = usec > 0;
    if (has_deadline) {
        deadline = after((long)usec);
    }
    pthread_cond_signal(&watched_changed);
    pthread_mutex_unlock(&watched_lock);
    return 0;
}

static int unwatch(void) {
    pthread_mutex_lock(&watched_lock);
    watched = NULL;
    has_deadline = 0;
    int was = interrupted;
    interrupted = 0;
    pthread_mutex_unlock(&watched_lock);
    return was;
}
#else
static uint64_t watch(uc_engine *uc, uint64_t usec) { return usec; }
static int unwatch(void) { return 0; }
#endif

/* if a signal stopped the engine, which ran last, see [watch] */
static int last_interrupted = 0;

value bap_uc_interrupted(value unit) { return Val_bool(last_interrupted); }

value bap_uc_process_signals(value unit) {
    caml_process_pending_actions();
    return Val_unit;
}

value bap_uc_emu_start(value v, value start, value until, value timeout,
                       value count, value tid) {
    CAMLparam5(v, start, until, timeout, count);
    CAMLxparam1(tid);
    CAMLlocal1(exn);
    struct engine *e = Engine_val(v);
    for (struct hook *h = e->hooks; h != NULL; h = h->next) {
        if (h->trace != NULL) h->trace->tid = (uint64_t)Long_val(tid);
        if (h->mem != NULL) h->mem->tid = (uint64_t)Long_val(tid);
    }
    mark(e);
    e->running = 1;
    uint64_t usec = watch(engine_uc(v), Int64_val(timeout));
    uc_err err = uc_emu_start(engine_uc(v), Int64_val(start),
                              Int64_val(until), usec, Long_val(count));
    last_interrupted = unwatch();
    e->running = 0;
    if (err != UC_ERR_OK) {
        uint64_t pc = 0;
        int known = read_pc(e->uc, e->arch, &pc);
        invalidate_read_values(e, pc, known);
    }
    fixup(e);
    if (e->exn != Val_unit) {
        exn = e->exn;
        caml_modify_generational_global_root(&e->exn, Val_unit);
        caml_raise(exn);
    }
    check(err);
    CAMLreturn(Val_unit);
}

value bap_uc_emu_start_bytecode(value *argv, int argn) {
    (void)argn;
    return bap_uc_emu_start(argv[0], argv[1], argv[2], argv[3], argv[4],
                            argv[5]);
}

value bap_uc_emu_stop(value v) {
    check(uc_emu_stop(engine_uc(v)));
    return Val_unit;
}

/* calls the hook, unless an earlier one raised an exception, which
   stops the emulation */
static value call(struct hook *h, int n, value *args) {
    struct engine *e = h->engine;
    if (e->exn != Val_unit) {
        return Val_unit;
    }
    value r = caml_callbackN_exn(h->closure, n, args);
    if (Is_exception_result(r)) {
        caml_modify_generational_global_root(&e->exn,
                                             Extract_exception(r));
        uc_emu_stop(e->uc);
        return Val_unit;
    }
    return r;
}

static void on_attempt(uc_engine *uc, uint64_t addr, uint32_t size,
                       void *data) {
    struct engine *e = data;
    e->attempt++;
}

static void on_code(uc_engine *uc, uint64_t addr, uint32_t size,
                    void *data) {
    CAMLparam0();
    CAMLlocalN(args, 2);
    args[0] = caml_copy_int64(addr);
    args[1] = Val_int(size);
    call(data, 2, args);
    CAMLreturn0;
}

static void on_intr(uc_engine *uc, uint32_t intno, void *data) {
    CAMLparam0();
    CAMLlocalN(args, 1);
    args[0] = Val_int(intno);
    call(data, 1, args);
    CAMLreturn0;
}

static bool on_insn_invalid(uc_engine *uc, void *data) {
    CAMLparam0();
    CAMLlocalN(args, 1);
    CAMLlocal1(r);
    args[0] = Val_unit;
    r = call(data, 1, args);
    CAMLreturnT(bool, r != Val_unit && Bool_val(r));
}

static value mem_args(value *args, uc_mem_type type, uint64_t addr,
                      int size, int64_t x) {
    args[0] = Val_int(type - UC_MEM_READ);
    args[1] = caml_copy_int64(addr);
    args[2] = Val_int(size);
    args[3] = caml_copy_int64(x);
    return Val_unit;
}

static void on_mem(uc_engine *uc, uc_mem_type type, uint64_t addr, int size,
                   int64_t x, void *data) {
    CAMLparam0();
    CAMLlocalN(args, 4);
    mem_args(args, type, addr, size, x);
    call(data, 4, args);
    CAMLreturn0;
}

static int read_pc(uc_engine *uc, uc_arch arch, uint64_t *pc);

static void invalidate_read_values(struct engine *e, uint64_t pc, int known) {
    for (struct hook *h = e->hooks; h != NULL; h = h->next) {
        struct bap_native_trace *t = h->trace;
        if (t == NULL || t->count == 0) continue;
        uint64_t last = t->count - 1;
        for (uint64_t i = t->accesses; i > 0; i--) {
            struct bap_native_trace_access *a = &t->mem[(i - 1) & t->amask];
            if (a->insn != last) break;
            if (known && t->sizes != NULL && a->pc != pc) continue;
            if (!(a->write & 1)) {
                a->write = 0;
                a->value = 0;
            }
        }
    }
}

static bool on_mem_event(uc_engine *uc, uc_mem_type type, uint64_t addr,
                         int size, int64_t x, void *data) {
    CAMLparam0();
    CAMLlocalN(args, 4);
    CAMLlocal1(r);
    struct hook *h = data;
    uint64_t pc = 0;
    int known = read_pc(uc, h->engine->arch, &pc);
    invalidate_read_values(h->engine, pc, known);
    mem_args(args, type, addr, size, x);
    r = call(data, 4, args);
    CAMLreturnT(bool, r != Val_unit && Bool_val(r));
}

static void on_insn(uc_engine *uc, void *data) {
    CAMLparam0();
    CAMLlocalN(args, 1);
    args[0] = Val_unit;
    call(data, 1, args);
    CAMLreturn0;
}

enum hook_kind { HOOK_CODE, HOOK_BLOCK, HOOK_INTR, HOOK_INSN_INVALID,
                 HOOK_MEM, HOOK_MEM_EVENT, HOOK_INSN };

/* the kind of the hook, the type mask of Unicorn, and the closure */
value bap_uc_hook_add(value v, value kind, value types, value start,
                      value stop, value closure) {
    CAMLparam5(v, kind, types, start, stop);
    CAMLxparam1(closure);
    struct engine *e = Engine_val(v);
    uc_engine *uc = engine_uc(v);
    void *callback;
    int type = Int_val(types);
    switch (Int_val(kind)) {
    case HOOK_CODE: callback = on_code; type = UC_HOOK_CODE; break;
    case HOOK_BLOCK: callback = on_code; type = UC_HOOK_BLOCK; break;
    case HOOK_INTR: callback = on_intr; type = UC_HOOK_INTR; break;
    case HOOK_INSN_INVALID:
        callback = on_insn_invalid;
        type = UC_HOOK_INSN_INVALID;
        break;
    case HOOK_MEM: callback = on_mem; break;
    case HOOK_MEM_EVENT: callback = on_mem_event; break;
    /* the types are the instruction of x86, e.g., UC_X86_INS_SYSCALL */
    case HOOK_INSN: callback = on_insn; type = UC_HOOK_INSN; break;
    default: caml_invalid_argument("Unicorn.hook_add");
    }
    struct hook *h = malloc(sizeof(struct hook));
    if (h == NULL) {
        caml_raise_out_of_memory();
    }
    h->closure = closure;
    h->engine = e;
    h->write = Int_val(kind) == HOOK_MEM && (type & UC_HOOK_MEM_WRITE);
    h->trace = NULL;
    h->mem = NULL;
    h->sites = NULL;
    h->nsites = 0;
    caml_register_generational_global_root(&h->closure);
    uc_err err = UC_ERR_OK;
    if (h->write && e->write_hooks++ == 0) {
        err = uc_hook_add(uc, &e->attempt_hook, UC_HOOK_CODE, on_attempt, e, 1,
                          0);
        if (err != UC_ERR_OK) {
            e->write_hooks--;
        }
    }
    if (err == UC_ERR_OK) {
        err = Int_val(kind) == HOOK_INSN
                  ? uc_hook_add(uc, &h->handle, type, callback, h,
                                Int64_val(start), Int64_val(stop),
                                Int_val(types))
                  : uc_hook_add(uc, &h->handle, type, callback, h,
                                Int64_val(start), Int64_val(stop));
    }
    if (err != UC_ERR_OK) {
        if (h->write && e->write_hooks > 0 && --e->write_hooks == 0) {
            uc_hook_del(uc, e->attempt_hook);
            e->attempt_hook = 0;
        }
        caml_remove_generational_global_root(&h->closure);
        free(h);
        fail(err);
    }
    h->next = e->hooks;
    e->hooks = h;
    CAMLreturn(caml_copy_int64((int64_t)h->handle));
}

value bap_uc_hook_add_bytecode(value *argv, int argn) {
    return bap_uc_hook_add(argv[0], argv[1], argv[2], argv[3], argv[4],
                           argv[5]);
}

/* calls the hook of the sites at the instructions of its addresses
   only, which it finds by the binary search, so that the instructions
   of its range, that aren't sites, don't call OCaml */
static void on_sites(uc_engine *uc, uint64_t addr, uint32_t size,
                     void *data) {
    struct hook *h = data;
    size_t lo = 0, hi = h->nsites;
    while (lo < hi) {
        size_t mid = lo + (hi - lo) / 2;
        if (h->sites[mid] < addr) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if (lo < h->nsites && h->sites[lo] == addr) {
        on_code(uc, addr, size, data);
    }
}

/* the hook of the code at the [sites], the sorted array of the
   addresses, from the first to the last one */
value bap_uc_hook_sites(value v, value sites, value closure) {
    CAMLparam3(v, sites, closure);
    struct engine *e = Engine_val(v);
    size_t n = Wosize_val(sites);
    if (n == 0) {
        caml_invalid_argument("Unicorn.on_sites: no sites");
    }
    uint64_t *addrs = malloc(n * sizeof(uint64_t));
    struct hook *h = malloc(sizeof(struct hook));
    if (addrs == NULL || h == NULL) {
        free(addrs);
        free(h);
        caml_raise_out_of_memory();
    }
    for (size_t i = 0; i < n; i++) {
        addrs[i] = (uint64_t)Int64_val(Field(sites, i));
    }
    h->closure = closure;
    h->engine = e;
    h->trace = NULL;
    h->mem = NULL;
    h->sites = addrs;
    h->nsites = n;
    caml_register_generational_global_root(&h->closure);
    uc_err err = uc_hook_add(engine_uc(v), &h->handle, UC_HOOK_CODE, on_sites,
                             h, addrs[0], addrs[n - 1]);
    if (err != UC_ERR_OK) {
        caml_remove_generational_global_root(&h->closure);
        free(addrs);
        free(h);
        fail(err);
    }
    h->next = e->hooks;
    e->hooks = h;
    CAMLreturn(caml_copy_int64((int64_t)h->handle));
}

value bap_uc_x86_syscalls(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(r);
    r = caml_alloc_tuple(2);
    Store_field(r, 0, Val_int(UC_X86_INS_SYSCALL));
    Store_field(r, 1, Val_int(UC_X86_INS_SYSENTER));
    CAMLreturn(r);
}

value bap_uc_hook_del(value v, value handle) {
    struct engine *e = Engine_val(v);
    uc_hook hh = (uc_hook)Int64_val(handle);
    struct hook **p = &e->hooks;
    while (*p != NULL && (*p)->handle != hh) {
        p = &(*p)->next;
    }
    if (*p == NULL) {
        caml_invalid_argument("Unicorn.hook_del: an unknown hook");
    }
    struct hook *h = *p;
    check(uc_hook_del(engine_uc(v), hh));
    if (h->write && --e->write_hooks == 0) {
        check(uc_hook_del(engine_uc(v), e->attempt_hook));
        e->attempt_hook = 0;
    }
    *p = h->next;
    caml_remove_generational_global_root(&h->closure);
    free(h->sites);
    free(h);
    return Val_unit;
}

value bap_uc_attempt(value v) {
    return caml_copy_int64(Engine_val(v)->attempt);
}

value bap_uc_context_save(value v) {
    CAMLparam1(v);
    CAMLlocal1(r);
    uc_engine *uc = engine_uc(v);
    uc_context *ctx;
    check(uc_context_alloc(uc, &ctx));
    uc_err err = uc_context_save(uc, ctx);
    if (err != UC_ERR_OK) {
        uc_context_free(ctx);
        fail(err);
    }
    r = caml_alloc_custom(&context_ops, sizeof(struct saved_context), 0, 1);
    Saved_val(r)->ctx = ctx;
    Saved_val(r)->arch = Engine_val(v)->arch;
    Saved_val(r)->size = uc_context_size(uc);
    CAMLreturn(r);
}

value bap_uc_context_restore(value v, value ctx) {
    uc_engine *uc = engine_uc(v);
    if (Saved_val(ctx)->arch != Engine_val(v)->arch ||
        Saved_val(ctx)->size != uc_context_size(uc))
        caml_invalid_argument("Bap_unicorn.restore: the context of another "
                              "engine");
    check(uc_context_restore(uc, Context_val(ctx)));
    return Val_unit;
}

/* Unicorn's native hooks record into the shared trace rings. */

#define UNKNOWN BAP_NATIVE_TRACE_UNKNOWN
#define MID BAP_NATIVE_TRACE_MID
#define BOUNDS BAP_NATIVE_TRACE_BOUNDS
#define Trace_val(v) Bap_native_trace_val(v)

/* the mode of ARM, that the instruction runs in, which the slices
   decode it in, as the program counters of Thumb have no lower bit, and
   the blocks are in one mode */
static uint8_t thumb(uc_engine *uc) {
    uint32_t cpsr = 0;
    uc_reg_read(uc, UC_ARM_REG_CPSR, &cpsr);
    return (cpsr >> 5) & 1;
}

static int capture_reg(uc_engine *uc, int id, uint32_t offset, uint32_t size,
                       uint64_t *value) {
    uint8_t buf[REG_BUF];
    size_t reg_size = REG_BUF;
    memset(buf, 0, REG_BUF);
    if (uc_reg_read2(uc, id, buf, &reg_size) != UC_ERR_OK ||
        offset > reg_size || size > reg_size - offset) {
        return 0;
    }
    *value = 0;
    for (uint32_t i = 0; i < size; i++) {
        *value |= (uint64_t)buf[offset + i] << (8 * i);
    }
    return 1;
}

static int capture_readable(uc_engine *uc, uint64_t addr, uint32_t size) {
    uc_mem_region *regions;
    uint32_t count;
    if (addr + size - 1 < addr ||
        uc_mem_regions(uc, &regions, &count) != UC_ERR_OK) {
        return 0;
    }
    uint64_t current = addr;
    uint32_t left = size;
    while (left > 0) {
        uint32_t i;
        for (i = 0; i < count; i++) {
            if (regions[i].begin <= current && current <= regions[i].end) {
                break;
            }
        }
        if (i == count || !(regions[i].perms & UC_PROT_READ)) {
            uc_free(regions);
            return 0;
        }
        uint64_t available = regions[i].end - current;
        if (available >= left - 1) {
            left = 0;
        } else {
            uint32_t step = (uint32_t)available + 1;
            current += step;
            left -= step;
        }
    }
    uc_free(regions);
    return 1;
}

static void capture_state(uc_engine *uc, struct bap_native_trace *t,
                          uint64_t site) {
    if (!bap_native_trace_captures(t, site)) {
        return;
    }
    for (size_t i = 0; i < t->nregs; i++) {
        struct bap_native_capture_reg *r = &t->capture_regs[i];
        if (!capture_reg(uc, r->id, r->offset, r->size,
                         &t->capture_reg_scratch[i])) {
            t->capture_reg_scratch[i] = 0;
        }
    }
    for (size_t i = 0; i < t->nfields; i++) {
        struct bap_native_capture_field *f = &t->capture_fields[i];
        uint64_t base;
        uint8_t bytes[8];
        t->capture_present_scratch[i] = 0;
        t->capture_field_scratch[i] = 0;
        if (capture_reg(uc, f->id, f->offset, f->size, &base) &&
            capture_readable(uc, base + f->at, f->field_size) &&
            uc_mem_read(uc, base + f->at, bytes, f->field_size) == UC_ERR_OK) {
            uint64_t value = 0;
            for (uint32_t k = 0; k < f->field_size; k++) {
                value |= (uint64_t)bytes[k] << (8 * k);
            }
            t->capture_field_scratch[i] = value;
            t->capture_present_scratch[i] = 1;
        }
    }
    bap_native_trace_capture(t, site, t->capture_reg_scratch,
                             t->capture_field_scratch,
                             t->capture_present_scratch);
}

static void trace_code(uc_engine *uc, uint64_t addr, uint32_t size,
                       void *data) {
    struct hook *h = data;
    struct bap_native_trace *t = h->trace;
    if (--t->skip) {
        return;
    }
    t->skip = t->every;
    t->pcs[t->count & t->mask] = addr;
    t->tids[t->count & t->mask] = t->tid;
    if (t->modes != NULL) {
        t->modes[t->count & t->mask] = t->thumb;
    }
    t->count++;
    capture_state(uc, t, addr);
}

/* the mode of the block, whose instructions the trace of the code
   records, as the blocks of QEMU are in one mode, and the hooks of the
   blocks run before the ones of their instructions */
static void trace_mode(uc_engine *uc, uint64_t addr, uint32_t size,
                       void *data) {
    struct bap_native_trace *t = data;
    t->thumb = thumb(uc);
}

static void trace_block(uc_engine *uc, uint64_t addr, uint32_t size,
                        void *data) {
    struct bap_native_trace *t = data;
    t->pcs[t->count & t->mask] = addr;
    t->tids[t->count & t->mask] = t->tid;
    t->sizes[t->count & t->mask] = size;
    if (t->modes != NULL) {
        t->modes[t->count & t->mask] = thumb(uc);
    }
    t->count++;
}

static int read_pc(uc_engine *uc, uc_arch arch, uint64_t *pc);

/* the program counter of the instruction, that makes the access, is
   read only in a trace of blocks, where it is in the block, and a write
   of at most eight bytes to the code keeps the bytes, that it overwrites,
   as the memory has them, the first one in the lowest byte, e.g., of the
   code, that the program patches, which the slices lift, as it was */
static void trace_mem(uc_engine *uc, uc_mem_type type, uint64_t addr,
                      int size, int64_t x, void *data) {
    struct hook *h = data;
    struct bap_native_trace *t = h->mem;
    if (t->count == 0) {
        return;
    }
    struct bap_native_trace_access *a = &t->mem[t->accesses & t->amask];
    a->insn = t->count - 1;
    a->pc = 0;
    if (t->sizes != NULL && !read_pc(uc, h->engine->arch, &a->pc)) {
        a->pc = 0;
    }
    a->addr = addr;
    a->size = size;
    int write = type == UC_MEM_WRITE;
    int read_value = !write && t->read_values && size <= 8;
    uint64_t value = (uint64_t)x;
    if (read_value) {
        uint8_t bytes[8];
        if (uc_mem_read(uc, addr, bytes, size) == UC_ERR_OK) {
            value = 0;
            for (int i = 0; i < size; i++) {
                value |= (uint64_t)bytes[i] << (8 * i);
            }
        } else {
            read_value = 0;
        }
    }
    a->write = write | (read_value ? 2 : 0);
    a->value = write || read_value ? value : 0;
    a->old = 0;
    a->tid = t->tid;
    if (type == UC_MEM_WRITE && size <= 8 && h->engine->code.size > 0 &&
        (pages_mem(&h->engine->code, addr >> 12) ||
         pages_mem(&h->engine->code, (addr + size - 1) >> 12))) {
        uint8_t bytes[8] = {0};
        if (uc_mem_read(uc, addr, bytes, size) == UC_ERR_OK) {
            for (int i = 0; i < size; i++) {
                a->old |= (uint64_t)bytes[i] << (8 * i);
            }
        }
    }
    t->accesses++;
}

/* the program counter, from which Unicorn continues */
static int read_pc(uc_engine *uc, uc_arch arch, uint64_t *pc) {
    int reg;
    switch (arch) {
    case UC_ARCH_X86: {
        size_t mode = 0;
        if (uc_query(uc, UC_QUERY_MODE, &mode) != UC_ERR_OK) {
            return 0;
        }
        reg = mode & UC_MODE_64   ? UC_X86_REG_RIP
              : mode & UC_MODE_32 ? UC_X86_REG_EIP
                                  : UC_X86_REG_IP;
        break;
    }
    case UC_ARCH_ARM: reg = UC_ARM_REG_PC; break;
    case UC_ARCH_ARM64: reg = UC_ARM64_REG_PC; break;
    case UC_ARCH_MIPS: reg = UC_MIPS_REG_PC; break;
    case UC_ARCH_PPC: reg = UC_PPC_REG_PC; break;
    case UC_ARCH_RISCV: reg = UC_RISCV_REG_PC; break;
    default: return 0;
    }
    uint8_t buf[REG_BUF];
    memset(buf, 0, REG_BUF);
    size_t size = REG_BUF;
    if (uc_reg_read2(uc, reg, buf, &size) != UC_ERR_OK || size > 8) {
        return 0;
    }
    *pc = reg_value(buf, size);
    if (arch == UC_ARCH_ARM) {
        *pc &= ~(uint64_t)1;
    }
    return 1;
}

/* The instruction, that Unicorn stopped at, e.g., at a stop of Primus,
   or at a fault, which it repeats, after the executor mapped the page,
   was recorded, but didn't run, so its record and its accesses are
   dropped, as it is recorded again, when it runs. The pc of Thumb has
   no lower bit, as the hooks of the code see it. */
static void fixup(struct engine *e) {
    uint64_t pc;
    int known = 0;
    for (struct hook *h = e->hooks; h != NULL; h = h->next) {
        struct bap_native_trace *t = h->trace;
        if (t == NULL || t->every != 1 || t->count == 0) {
            continue;
        }
        if (!known) {
            if (!read_pc(e->uc, e->arch, &pc)) {
                return;
            }
            known = 1;
        }
        uint64_t last = t->count - 1;
        uint64_t start = t->pcs[last & t->mask];
        if (t->sizes != NULL) {
            /* the block, that Unicorn left at [pc], ran only before it,
               and the accesses of the instructions after it are none */
            uint32_t size = t->sizes[last & t->mask];
            if (pc < start || pc >= start + size) {
                continue;
            }
            if (pc > start) {
                t->sizes[last & t->mask] = pc - start;
                bap_native_trace_forget_captures(t, last, pc);
                /* the hooks of the instructions, that didn't run, made
                   their boundaries before the next block */
                for (uint64_t i = t->marks; i > 0 && t->marks - i < BOUNDS;
                     i--) {
                    uint64_t *b = &t->bounds[(i - 1) & (BOUNDS - 1)];
                    uint64_t record = *b & ~(7ULL << 61);
                    if (record < last) {
                        break;
                    }
                    if (record == last && (*b & MID) &&
                        t->at[(i - 1) & (BOUNDS - 1)] >= pc) {
                        *b = (*b & (7ULL << 61)) | t->count;
                    }
                }
                while (t->accesses > 0) {
                    struct bap_native_trace_access *a = &t->mem[(t->accesses - 1) & t->amask];
                    if (a->insn != last || a->pc < pc) {
                        break;
                    }
                    t->accesses--;
                }
                continue;
            }
        } else if (start != pc) {
            continue;
        }
        bap_native_trace_forget_captures(t, last, pc);
        t->count--;
        while (t->accesses > 0 &&
               t->mem[(t->accesses - 1) & t->amask].insn == last) {
            t->accesses--;
        }
    }
}

/* The registers or the memory, that the emulation has, which were
   written, while it was stopped, e.g., by the code, that Primus runs,
   or by the script, but not the pages, that were filled, as they were
   mapped, make a boundary of the traces, the index of the record, that
   follows it, with the written registers in the bit 62, and the memory
   in the bit 63, so that the slices see, that the values of the
   locations may come from outside of the trace. */
static void bound(struct bap_native_trace *t, uint64_t bound, uint64_t pc,
                  struct bap_native_trace_range *ranges, uint64_t n) {
    bap_native_trace_add_bound(t, bound, pc, ranges, n);
}

static void mark(struct engine *e) {
    if (e->wrote_regs || e->wrote_mem) {
        for (struct hook *h = e->hooks; h != NULL; h = h->next) {
            struct bap_native_trace *t = h->trace;
            if (t == NULL) {
                continue;
            }
            bound(t,
                  t->count | ((uint64_t)e->wrote_regs << 62) |
                      ((uint64_t)e->wrote_mem << 63),
                  0, e->wrote, e->wrote_all ? UNKNOWN : e->nwrote);
        }
    }
    e->wrote_regs = 0;
    e->wrote_mem = 0;
    e->nwrote = 0;
    e->wrote_all = 0;
    free_fresh(e);
}

/* The registers or the memory, that a hook writes, while the emulation
   runs, make a boundary before the instruction at the pc, with the bit
   61, in its record, which is the last one, if the trace has it, as the
   hook of the blocks runs before the hooks of their instructions, and
   the hooks of the code before the ones of the accesses, or else the
   next one, as the hook of the trace runs after the one, that writes.
   An instruction, that repeats, e.g., of a string, has the last record,
   if the hook of the trace is after the one, that writes, too. */
static void mark_running(struct engine *e, int regs, int mem, uint64_t addr,
                         uint64_t size) {
    uint64_t pc;
    if (!read_pc(e->uc, e->arch, &pc)) {
        e->wrote_regs |= regs;
        if (mem) {
            wrote(e, addr, size);
        }
        return;
    }
    struct bap_native_trace_range range = {addr, size};
    for (struct hook *h = e->hooks; h != NULL; h = h->next) {
        struct bap_native_trace *t = h->trace;
        if (t == NULL) {
            continue;
        }
        uint64_t record = t->count;
        if (t->count > 0) {
            uint64_t last = (t->count - 1) & t->mask;
            uint64_t start = t->pcs[last];
            if (t->sizes != NULL ? pc >= start && pc < start + t->sizes[last]
                                 : pc == start) {
                record = t->count - 1;
            }
        }
        bound(t, record | MID | ((uint64_t)regs << 62) | ((uint64_t)mem << 63),
              pc, &range, mem ? 1 : 0);
    }
}

enum trace_kind { TRACE_CODE, TRACE_BLOCK, TRACE_MEM, TRACE_MODE };

/* the native hook, which records the trace, which it keeps alive */
value bap_uc_trace_add(value v, value tv, value kind, value start,
                       value stop) {
    CAMLparam5(v, tv, kind, start, stop);
    struct engine *e = Engine_val(v);
    uc_engine *uc = engine_uc(v);
    struct bap_native_trace *t = Trace_val(tv);
    void *callback;
    int type;
    switch (Int_val(kind)) {
    case TRACE_CODE: callback = trace_code; type = UC_HOOK_CODE; break;
    case TRACE_BLOCK:
        if (t->sizes == NULL) {
            caml_invalid_argument("Unicorn.trace: not a trace of blocks");
        }
        callback = trace_block;
        type = UC_HOOK_BLOCK;
        break;
    case TRACE_MEM:
        if (t->mem == NULL) {
            caml_invalid_argument("Unicorn.trace: no accesses are recorded");
        }
        callback = trace_mem;
        type = t->read_values ? UC_HOOK_MEM_READ_AFTER | UC_HOOK_MEM_WRITE
                              : UC_HOOK_MEM_READ | UC_HOOK_MEM_WRITE;
        break;
    case TRACE_MODE:
        /* only ARM has the modes, and its trace of the code, as the one
           of the blocks reads the mode itself */
        if (e->arch != UC_ARCH_ARM || t->sizes != NULL) {
            CAMLreturn(caml_copy_int64(-1));
        }
        callback = trace_mode;
        type = UC_HOOK_BLOCK;
        t->thumb = thumb(uc);
        break;
    default: caml_invalid_argument("Unicorn.trace");
    }
    struct hook *h = malloc(sizeof(struct hook));
    if (h == NULL) {
        caml_raise_out_of_memory();
    }
    h->closure = tv;
    h->engine = e;
    h->sites = NULL;
    h->nsites = 0;
    h->trace = Int_val(kind) == TRACE_CODE || Int_val(kind) == TRACE_BLOCK
                   ? t
                   : NULL;
    h->mem = Int_val(kind) == TRACE_MEM ? t : NULL;
    if (e->arch == UC_ARCH_ARM && t->modes == NULL) {
        t->modes = calloc(t->mask + 1, 1);
        if (t->modes == NULL) {
            free(h);
            caml_raise_out_of_memory();
        }
    }
    caml_register_generational_global_root(&h->closure);
    int with_engine = Int_val(kind) == TRACE_CODE || Int_val(kind) == TRACE_MEM;
    uc_err err =
        uc_hook_add(uc, &h->handle, type, callback,
                    with_engine ? (void *)h : (void *)t, Int64_val(start),
                    Int64_val(stop));
    if (err != UC_ERR_OK) {
        caml_remove_generational_global_root(&h->closure);
        free(h);
        fail(err);
    }
    h->next = e->hooks;
    e->hooks = h;
    CAMLreturn(caml_copy_int64((int64_t)h->handle));
}
