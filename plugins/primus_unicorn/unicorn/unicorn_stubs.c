/* The bindings to the C API of Unicorn, see bap_unicorn.mli.

   The hooks call back into OCaml from the emulation, on the thread that
   started it, which holds the runtime lock all the time. An exception
   raised by a hook can not unwind the frames of Unicorn, so it stops
   the emulation and is reraised when uc_emu_start returns. */

#include <stdlib.h>
#include <string.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include <unicorn/unicorn.h>

#include "unicorn_regs.h"

struct hook {
    uc_hook handle;
    value closure;
    struct engine *engine;
    struct hook *next;
};

struct engine {
    uc_engine *uc;
    uc_arch arch;
    struct hook *hooks;
    /* the exception that a hook raised, or Val_unit */
    value exn;
};

#define Engine_val(v) (*((struct engine **)Data_custom_val(v)))
#define Context_val(v) (*((uc_context **)Data_custom_val(v)))

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
        free(h);
        h = next;
    }
    e->hooks = NULL;
}

static void close_engine(struct engine *e) {
    if (e->uc != NULL) {
        uc_close(e->uc);
        e->uc = NULL;
    }
    free_hooks(e);
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
    e->exn = Val_unit;
    caml_register_generational_global_root(&e->exn);
    r = caml_alloc_custom(&engine_ops, sizeof(struct engine *), 0, 1);
    Engine_val(r) = e;
    CAMLreturn(r);
}

value bap_uc_close(value v) {
    close_engine(Engine_val(v));
    return Val_unit;
}

value bap_uc_set_cpu_model(value v, value model) {
    check(uc_ctl_set_cpu_model(engine_uc(v), Int_val(model)));
    return Val_unit;
}

value bap_uc_set_tlb_virtual(value v) {
    check(uc_ctl_tlb_mode(engine_uc(v), UC_TLB_VIRTUAL));
    return Val_unit;
}

value bap_uc_flush_tb(value v) {
    check(uc_ctl_flush_tb(engine_uc(v)));
    return Val_unit;
}

value bap_uc_mem_map(value v, value addr, value size, value perms) {
    check(uc_mem_map(engine_uc(v), Int64_val(addr), Int64_val(size),
                     Int_val(perms)));
    return Val_unit;
}

value bap_uc_mem_unmap(value v, value addr, value size) {
    check(uc_mem_unmap(engine_uc(v), Int64_val(addr), Int64_val(size)));
    return Val_unit;
}

value bap_uc_mem_protect(value v, value addr, value size, value perms) {
    check(uc_mem_protect(engine_uc(v), Int64_val(addr), Int64_val(size),
                         Int_val(perms)));
    return Val_unit;
}

/* neither reading nor writing the memory runs hooks, so the strings
   stay in place */

value bap_uc_mem_write(value v, value addr, value data) {
    check(uc_mem_write(engine_uc(v), Int64_val(addr), String_val(data),
                       caml_string_length(data)));
    return Val_unit;
}

value bap_uc_mem_read(value v, value addr, value len) {
    CAMLparam3(v, addr, len);
    CAMLlocal1(r);
    uc_engine *uc = engine_uc(v);
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
    uint8_t buf[REG_BUF];
    size_t size = reg_read(uc, Int_val(reg), buf);
    if (caml_string_length(data) != size) {
        caml_invalid_argument("Unicorn.reg_write_bytes: a wrong size");
    }
    memcpy(buf, String_val(data), size);
    check(uc_reg_write2(uc, Int_val(reg), buf, &size));
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

value bap_uc_emu_start(value v, value start, value until, value timeout,
                       value count) {
    CAMLparam5(v, start, until, timeout, count);
    CAMLlocal1(exn);
    struct engine *e = Engine_val(v);
    uc_err err = uc_emu_start(engine_uc(v), Int64_val(start),
                              Int64_val(until), Int64_val(timeout),
                              Long_val(count));
    if (e->exn != Val_unit) {
        exn = e->exn;
        caml_modify_generational_global_root(&e->exn, Val_unit);
        caml_raise(exn);
    }
    check(err);
    CAMLreturn(Val_unit);
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

static bool on_mem_event(uc_engine *uc, uc_mem_type type, uint64_t addr,
                         int size, int64_t x, void *data) {
    CAMLparam0();
    CAMLlocalN(args, 4);
    CAMLlocal1(r);
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
    caml_register_generational_global_root(&h->closure);
    uc_err err =
        Int_val(kind) == HOOK_INSN
            ? uc_hook_add(uc, &h->handle, type, callback, h, Int64_val(start),
                          Int64_val(stop), Int_val(types))
            : uc_hook_add(uc, &h->handle, type, callback, h, Int64_val(start),
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

value bap_uc_hook_add_bytecode(value *argv, int argn) {
    return bap_uc_hook_add(argv[0], argv[1], argv[2], argv[3], argv[4],
                           argv[5]);
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
    *p = h->next;
    caml_remove_generational_global_root(&h->closure);
    free(h);
    return Val_unit;
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
    r = caml_alloc_custom(&context_ops, sizeof(uc_context *), 0, 1);
    Context_val(r) = ctx;
    CAMLreturn(r);
}

value bap_uc_context_restore(value v, value ctx) {
    check(uc_context_restore(engine_uc(v), Context_val(ctx)));
    return Val_unit;
}
