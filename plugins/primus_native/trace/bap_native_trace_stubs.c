/* Native trace rings shared by the execution engines. */

#include <stdio.h>
#include <stdlib.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "bap_native_trace.h"

#define RANGES BAP_NATIVE_TRACE_RANGES
#define BOUNDS BAP_NATIVE_TRACE_BOUNDS
#define UNKNOWN BAP_NATIVE_TRACE_UNKNOWN
#define MID BAP_NATIVE_TRACE_MID

static void finalize_trace(value v) {
    struct bap_native_trace *t = Bap_native_trace_val(v);
    free(t->bounds);
    free(t->at);
    free(t->first);
    free(t->nranges);
    free(t->ranges);
    free(t->pcs);
    free(t->sizes);
    free(t->modes);
    free(t->mem);
    free(t);
}

static struct custom_operations trace_ops = {
    "bap.unicorn.trace.1",      finalize_trace,
    custom_compare_default,     custom_hash_default,
    custom_serialize_default,   custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

static uint64_t ring_size(intnat n) {
    uint64_t size = 1;
    while (size < (uint64_t)n) {
        size <<= 1;
    }
    return size;
}

#define MAX_RING ((intnat)1 << 36)

value bap_native_trace_create(value size, value every, value blocks,
                              value accesses) {
    CAMLparam4(size, every, blocks, accesses);
    CAMLlocal1(r);
    struct bap_native_trace *t = calloc(1, sizeof(struct bap_native_trace));
    if (t == NULL) {
        caml_raise_out_of_memory();
    }
    if (Long_val(size) > MAX_RING || Long_val(accesses) > MAX_RING) {
        free(t);
        caml_invalid_argument("Bap_unicorn.Trace.create: too large");
    }
    uint64_t n = ring_size(Long_val(size) < 1 ? 2 : Long_val(size) + 1);
    t->mask = n - 1;
    t->pcs = malloc(n * sizeof(uint64_t));
    t->sizes = Bool_val(blocks) ? malloc(n * sizeof(uint32_t)) : NULL;
    t->every = Long_val(every) < 1 ? 1 : Long_val(every);
    t->bounds = malloc(BOUNDS * sizeof(uint64_t));
    t->at = malloc(BOUNDS * sizeof(uint64_t));
    t->first = malloc(BOUNDS * sizeof(uint64_t));
    t->nranges = malloc(BOUNDS * sizeof(uint64_t));
    t->ranges = malloc(RANGES * sizeof(struct bap_native_trace_range));
    t->skip = t->every;
    if (Long_val(accesses) > 0) {
        uint64_t m = ring_size(Long_val(accesses) + 1);
        t->amask = m - 1;
        t->mem = malloc(m * sizeof(struct bap_native_trace_access));
    }
    if (t->pcs == NULL || t->bounds == NULL || t->at == NULL ||
        t->first == NULL || t->nranges == NULL || t->ranges == NULL ||
        (Bool_val(blocks) && t->sizes == NULL) ||
        (Long_val(accesses) > 0 && t->mem == NULL)) {
        free(t->bounds);
        free(t->at);
        free(t->first);
        free(t->nranges);
        free(t->ranges);
        free(t->pcs);
        free(t->sizes);
        free(t->mem);
        free(t);
        caml_raise_out_of_memory();
    }
    r = caml_alloc_custom_mem(&trace_ops, sizeof(struct bap_native_trace *),
                              n * sizeof(uint64_t));
    Bap_native_trace_val(r) = t;
    CAMLreturn(r);
}

value bap_native_trace_prepare(value tv, value arm) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    if (Bool_val(arm) && t->modes == NULL) {
        t->modes = calloc(t->mask + 1, 1);
        if (t->modes == NULL) {
            caml_raise_out_of_memory();
        }
    }
    return Val_unit;
}

value bap_native_trace_record(value tv, value pc, value size, value thumb) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t addr = Int64_val(pc);
    if (t->sizes == NULL) {
        if (--t->skip) {
            return Val_unit;
        }
        t->skip = t->every;
    } else {
        t->sizes[t->count & t->mask] = Long_val(size);
    }
    t->pcs[t->count & t->mask] = addr;
    if (t->modes != NULL) {
        t->modes[t->count & t->mask] = Bool_val(thumb);
    }
    t->count++;
    return Val_unit;
}

value bap_native_trace_extend(value tv, value size) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    if (t->sizes != NULL && t->count > 0) {
        t->sizes[(t->count - 1) & t->mask] += Long_val(size);
    }
    return Val_unit;
}

void *bap_native_trace_of(value tv) { return Bap_native_trace_val(tv); }

void bap_native_trace_block(void *tp, uint64_t pc, uint32_t size, int thumb,
                            int starts) {
    struct bap_native_trace *t = tp;
    if (t->sizes == NULL) {
        return;
    }
    if (!starts) {
        if (t->count > 0) {
            t->sizes[(t->count - 1) & t->mask] += size;
        }
        return;
    }
    t->sizes[t->count & t->mask] = size;
    t->pcs[t->count & t->mask] = pc;
    if (t->modes != NULL) {
        t->modes[t->count & t->mask] = thumb;
    }
    t->count++;
}

value bap_native_trace_access(value tv, value write, value addr, value size,
                              value x, value old, value pc) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    if (t->mem == NULL || t->count == 0) {
        return Val_unit;
    }
    struct bap_native_trace_access *a = &t->mem[t->accesses & t->amask];
    a->insn = t->count - 1;
    a->pc = t->sizes != NULL ? Int64_val(pc) : 0;
    a->addr = Int64_val(addr);
    a->size = Long_val(size);
    a->write = Bool_val(write);
    a->value = Bool_val(write) ? (uint64_t)Int64_val(x) : 0;
    a->old = Bool_val(write) ? (uint64_t)Int64_val(old) : 0;
    t->accesses++;
    return Val_unit;
}

value bap_native_trace_unrun(value tv, value pcv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t pc = Int64_val(pcv);
    if (t->every != 1 || t->count == 0) {
        return Val_unit;
    }
    uint64_t last = t->count - 1;
    uint64_t start = t->pcs[last & t->mask];
    if (t->sizes != NULL) {
        uint32_t size = t->sizes[last & t->mask];
        if (pc < start || pc >= start + size) {
            return Val_unit;
        }
        if (pc > start) {
            t->sizes[last & t->mask] = pc - start;
            while (t->accesses > 0) {
                struct bap_native_trace_access *a =
                    &t->mem[(t->accesses - 1) & t->amask];
                if (a->insn != last || a->pc < pc) {
                    break;
                }
                t->accesses--;
            }
            return Val_unit;
        }
    } else if (start != pc) {
        return Val_unit;
    }
    t->count--;
    while (t->accesses > 0 &&
           t->mem[(t->accesses - 1) & t->amask].insn == last) {
        t->accesses--;
    }
    return Val_unit;
}

void bap_native_trace_add_bound(struct bap_native_trace *t, uint64_t bound,
                                uint64_t pc,
                                struct bap_native_trace_range *ranges,
                                uint64_t n) {
    uint64_t i = (t->marks - 1) & (BOUNDS - 1);
    uint64_t last = t->bounds[i];
    if (t->marks > 0 && (last & ~(3ULL << 62)) == (bound & ~(3ULL << 62)) &&
        (!(bound & MID) || t->at[i] == pc) &&
        (t->nranges[i] == UNKNOWN ||
         t->first[i] + t->nranges[i] == t->ranges_count)) {
        t->bounds[i] = last | bound;
    } else {
        i = t->marks & (BOUNDS - 1);
        t->bounds[i] = bound;
        t->at[i] = pc;
        t->first[i] = t->ranges_count;
        t->nranges[i] = 0;
        t->marks++;
    }
    if (n == UNKNOWN || t->nranges[i] == UNKNOWN) {
        t->nranges[i] = UNKNOWN;
        return;
    }
    for (uint64_t k = 0; k < n; k++) {
        t->ranges[t->ranges_count & (RANGES - 1)] = ranges[k];
        t->ranges_count++;
    }
    t->nranges[i] += n;
}

value bap_native_trace_bound(value tv, value regs, value mem, value running,
                             value pcv, value ranges, value unknown) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t pc = Int64_val(pcv);
    uint64_t n = Wosize_val(ranges) / 2;
    struct bap_native_trace_range *rs =
        n > 0 ? malloc(n * sizeof(struct bap_native_trace_range)) : NULL;
    if (n > 0 && rs == NULL) {
        caml_raise_out_of_memory();
    }
    for (uint64_t i = 0; i < n; i++) {
        rs[i].addr = Int64_val(Field(ranges, 2 * i));
        rs[i].size = Int64_val(Field(ranges, 2 * i + 1));
    }
    uint64_t record = t->count;
    uint64_t flags =
        ((uint64_t)Bool_val(regs) << 62) | ((uint64_t)Bool_val(mem) << 63);
    if (Bool_val(running)) {
        if (t->count > 0) {
            uint64_t last = (t->count - 1) & t->mask;
            uint64_t start = t->pcs[last];
            if (t->sizes != NULL ? pc >= start && pc < start + t->sizes[last]
                                 : pc == start) {
                record = t->count - 1;
            }
        }
        flags |= MID;
    }
    bap_native_trace_add_bound(t, record | flags, Bool_val(running) ? pc : 0, rs,
                               Bool_val(unknown) ? UNKNOWN : n);
    free(rs);
    return Val_unit;
}

value bap_native_trace_access_bytecode(value *argv, int argn) {
    return bap_native_trace_access(argv[0], argv[1], argv[2], argv[3], argv[4],
                                   argv[5], argv[6]);
}

value bap_native_trace_bound_bytecode(value *argv, int argn) {
    return bap_native_trace_bound(argv[0], argv[1], argv[2], argv[3], argv[4],
                                  argv[5], argv[6]);
}

value bap_native_trace_count(value tv) {
    return caml_copy_int64(Bap_native_trace_val(tv)->count);
}

value bap_native_trace_accesses_count(value tv) {
    return caml_copy_int64(Bap_native_trace_val(tv)->accesses);
}

value bap_native_trace_blocks(value tv) {
    return Val_bool(Bap_native_trace_val(tv)->sizes != NULL);
}

value bap_native_trace_clear(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    t->count = 0;
    t->accesses = 0;
    t->marks = 0;
    t->ranges_count = 0;
    t->skip = t->every;
    return Val_unit;
}

static uint64_t kept(uint64_t count, uint64_t mask, intnat n) {
    uint64_t k = count < mask ? count : mask;
    return n >= 0 && (uint64_t)n < k ? (uint64_t)n : k;
}

value bap_native_trace_retained(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    return Val_long(kept(t->count, t->mask, -1));
}

value bap_native_trace_pcs(value tv, value n) {
    CAMLparam2(tv, n);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = kept(t->count, t->mask, Long_val(n));
    r = caml_ba_alloc_dims(CAML_BA_INT64 | CAML_BA_C_LAYOUT, 1, NULL, k);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t first = t->count - k;
    for (uint64_t i = 0; i < k; i++) {
        data[i] = t->pcs[(first + i) & t->mask];
    }
    CAMLreturn(r);
}

value bap_native_trace_sizes(value tv, value n) {
    CAMLparam2(tv, n);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = t->sizes == NULL ? 0 : kept(t->count, t->mask, Long_val(n));
    r = caml_ba_alloc_dims(CAML_BA_INT32 | CAML_BA_C_LAYOUT, 1, NULL, k);
    int32_t *data = Caml_ba_data_val(r);
    uint64_t first = t->count - k;
    for (uint64_t i = 0; i < k; i++) {
        data[i] = t->sizes[(first + i) & t->mask];
    }
    CAMLreturn(r);
}

value bap_native_trace_modes(value tv, value n) {
    CAMLparam2(tv, n);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = kept(t->count, t->mask, Long_val(n));
    r = caml_ba_alloc_dims(CAML_BA_UINT8 | CAML_BA_C_LAYOUT, 1, NULL, k);
    uint8_t *data = Caml_ba_data_val(r);
    uint64_t first = t->count - k;
    for (uint64_t i = 0; i < k; i++) {
        data[i] = t->modes == NULL ? 0 : t->modes[(first + i) & t->mask];
    }
    CAMLreturn(r);
}

value bap_native_trace_mem(value tv, value n) {
    CAMLparam2(tv, n);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = t->mem == NULL ? 0 : kept(t->accesses, t->amask, Long_val(n));
    r = caml_ba_alloc_dims(CAML_BA_INT64 | CAML_BA_C_LAYOUT, 2, NULL, k,
                           (intnat)6);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t first = t->accesses - k;
    for (uint64_t i = 0; i < k; i++) {
        struct bap_native_trace_access *a = &t->mem[(first + i) & t->amask];
        data[6 * i] = a->insn;
        data[6 * i + 1] = a->addr;
        data[6 * i + 2] = a->value;
        data[6 * i + 3] = (int64_t)a->size | ((int64_t)a->write << 32);
        data[6 * i + 4] = a->pc;
        data[6 * i + 5] = a->old;
    }
    CAMLreturn(r);
}

value bap_native_trace_save(value tv, value n, value path) {
    CAMLparam3(tv, n, path);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    FILE *f = fopen(String_val(path), "w");
    if (f == NULL) {
        caml_failwith("Unicorn.Trace.save: can't open the file");
    }
    uint64_t k = kept(t->count, t->mask, Long_val(n));
    uint64_t first = t->count - k;
    for (uint64_t i = 0; i < k; i++) {
        fprintf(f, "%llx\n", (unsigned long long)t->pcs[(first + i) & t->mask]);
    }
    if (fclose(f) != 0) {
        caml_failwith("Unicorn.Trace.save: can't write the file");
    }
    CAMLreturn(caml_copy_int64(k));
}

static uint64_t written(struct bap_native_trace *t, uint64_t i) {
    uint64_t n = t->nranges[i];
    return n != UNKNOWN && t->ranges_count - t->first[i] <= RANGES ? n
                                                                  : UNKNOWN;
}

value bap_native_trace_bounds(value tv) {
    CAMLparam1(tv);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = t->marks < BOUNDS ? t->marks : BOUNDS;
    r = caml_ba_alloc_dims(CAML_BA_INT64 | CAML_BA_C_LAYOUT, 1, NULL, 3 * k);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t first = t->marks - k;
    for (uint64_t i = 0; i < k; i++) {
        uint64_t j = (first + i) & (BOUNDS - 1);
        data[3 * i] = t->bounds[j];
        data[3 * i + 1] = t->at[j];
        data[3 * i + 2] = written(t, j);
    }
    CAMLreturn(r);
}

value bap_native_trace_ranges(value tv) {
    CAMLparam1(tv);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = t->marks < BOUNDS ? t->marks : BOUNDS;
    uint64_t first = t->marks - k, total = 0;
    for (uint64_t i = 0; i < k; i++) {
        uint64_t n = written(t, (first + i) & (BOUNDS - 1));
        total += n == UNKNOWN ? 0 : n;
    }
    r = caml_ba_alloc_dims(CAML_BA_INT64 | CAML_BA_C_LAYOUT, 1, NULL,
                           2 * total);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t pos = 0;
    for (uint64_t i = 0; i < k; i++) {
        uint64_t j = (first + i) & (BOUNDS - 1);
        uint64_t n = written(t, j);
        for (uint64_t m = 0; n != UNKNOWN && m < n; m++) {
            struct bap_native_trace_range *x =
                &t->ranges[(t->first[j] + m) & (RANGES - 1)];
            data[pos++] = x->addr;
            data[pos++] = x->size;
        }
    }
    CAMLreturn(r);
}

/* Compatibility with the former Unicorn-owned trace implementation. */
value bap_uc_trace_create(value size, value every, value blocks,
                          value accesses) {
    return bap_native_trace_create(size, every, blocks, accesses);
}

value bap_uc_trace_count(value tv) { return bap_native_trace_count(tv); }
value bap_uc_trace_retained(value tv) { return bap_native_trace_retained(tv); }

value bap_uc_trace_accesses_count(value tv) {
    return bap_native_trace_accesses_count(tv);
}

value bap_uc_trace_clear(value tv) { return bap_native_trace_clear(tv); }
value bap_uc_trace_prepare(value tv, value arm) {
    return bap_native_trace_prepare(tv, arm);
}

value bap_uc_trace_record(value tv, value pc, value size, value thumb) {
    return bap_native_trace_record(tv, pc, size, thumb);
}

value bap_uc_trace_extend(value tv, value size) {
    return bap_native_trace_extend(tv, size);
}

value bap_uc_trace_access(value tv, value write, value addr, value size,
                          value x, value old, value pc) {
    return bap_native_trace_access(tv, write, addr, size, x, old, pc);
}

value bap_uc_trace_unrun(value tv, value pc) {
    return bap_native_trace_unrun(tv, pc);
}

value bap_uc_trace_bound(value tv, value regs, value mem, value running,
                         value pc, value ranges, value unknown) {
    return bap_native_trace_bound(tv, regs, mem, running, pc, ranges, unknown);
}

value bap_uc_trace_access_bytecode(value *argv, int argn) {
    return bap_native_trace_access_bytecode(argv, argn);
}

value bap_uc_trace_bound_bytecode(value *argv, int argn) {
    return bap_native_trace_bound_bytecode(argv, argn);
}

value bap_uc_trace_blocks(value tv) { return bap_native_trace_blocks(tv); }
value bap_uc_trace_pcs(value tv, value n) {
    return bap_native_trace_pcs(tv, n);
}

value bap_uc_trace_sizes(value tv, value n) {
    return bap_native_trace_sizes(tv, n);
}

value bap_uc_trace_modes(value tv, value n) {
    return bap_native_trace_modes(tv, n);
}

value bap_uc_trace_mem(value tv, value n) {
    return bap_native_trace_mem(tv, n);
}

value bap_uc_trace_save(value tv, value n, value path) {
    return bap_native_trace_save(tv, n, path);
}

value bap_uc_trace_bounds(value tv) { return bap_native_trace_bounds(tv); }
value bap_uc_trace_ranges(value tv) { return bap_native_trace_ranges(tv); }
void *bap_uc_trace_of(value tv) { return bap_native_trace_of(tv); }

void bap_uc_trace_block(void *tp, uint64_t pc, uint32_t size, int thumb,
                        int starts) {
    bap_native_trace_block(tp, pc, size, thumb, starts);
}
