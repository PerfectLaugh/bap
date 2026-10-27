/* Native trace rings shared by the execution engines. */

#include <limits.h>
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

static void free_capture(struct bap_native_trace *t) {
    free(t->capture_sites);
    free(t->capture_regs);
    free(t->capture_fields);
    free(t->capture);
    free(t->capture_values);
    free(t->capture_field_values);
    free(t->capture_present);
    free(t->capture_reg_scratch);
    free(t->capture_field_scratch);
    free(t->capture_present_scratch);
    t->capture_sites = NULL;
    t->capture_regs = NULL;
    t->capture_fields = NULL;
    t->capture = NULL;
    t->capture_values = NULL;
    t->capture_field_values = NULL;
    t->capture_present = NULL;
    t->capture_reg_scratch = NULL;
    t->capture_field_scratch = NULL;
    t->capture_present_scratch = NULL;
}

static void finalize_trace(value v) {
    struct bap_native_trace *t = Bap_native_trace_val(v);
    if (t->capture_rooted) {
        caml_remove_generational_global_root(&t->capture_reg_desc);
        caml_remove_generational_global_root(&t->capture_field_desc);
    }
    free_capture(t);
    free(t->bounds);
    free(t->bound_tids);
    free(t->at);
    free(t->first);
    free(t->nranges);
    free(t->ranges);
    free(t->pcs);
    free(t->tids);
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

static value create_trace(value size, value every, value blocks, value accesses,
                          value read_values, int exact) {
    CAMLparam5(size, every, blocks, accesses, read_values);
    CAMLlocal1(r);
    struct bap_native_trace *t = calloc(1, sizeof(struct bap_native_trace));
    if (t == NULL) {
        caml_raise_out_of_memory();
    }
    t->read_values = Bool_val(read_values);
    if ((!exact && (Long_val(size) > MAX_RING || Long_val(accesses) > MAX_RING)) ||
        (exact && (Long_val(size) > 2 * (intnat)MAX_RING ||
                   Long_val(accesses) > 2 * (intnat)MAX_RING))) {
        free(t);
        caml_invalid_argument("Bap_unicorn.Trace.create: too large");
    }
    uint64_t n = exact ? (uint64_t)Long_val(size)
                       : ring_size(Long_val(size) < 1 ? 2 : Long_val(size) + 1);
    t->mask = n - 1;
    t->pcs = malloc(n * sizeof(uint64_t));
    t->tids = malloc(n * sizeof(uint64_t));
    t->sizes = Bool_val(blocks) ? malloc(n * sizeof(uint32_t)) : NULL;
    t->every = Long_val(every) < 1 ? 1 : Long_val(every);
    t->bounds = malloc(BOUNDS * sizeof(uint64_t));
    t->bound_tids = malloc(BOUNDS * sizeof(uint64_t));
    t->at = malloc(BOUNDS * sizeof(uint64_t));
    t->first = malloc(BOUNDS * sizeof(uint64_t));
    t->nranges = malloc(BOUNDS * sizeof(uint64_t));
    t->ranges = malloc(RANGES * sizeof(struct bap_native_trace_range));
    t->skip = t->every;
    if (Long_val(accesses) > 0) {
        uint64_t m = exact ? (uint64_t)Long_val(accesses)
                           : ring_size(Long_val(accesses) + 1);
        t->amask = m - 1;
        t->mem = malloc(m * sizeof(struct bap_native_trace_access));
    }
    if (t->pcs == NULL || t->tids == NULL || t->bounds == NULL ||
        t->bound_tids == NULL || t->at == NULL || t->first == NULL ||
        t->nranges == NULL || t->ranges == NULL ||
        (Bool_val(blocks) && t->sizes == NULL) ||
        (Long_val(accesses) > 0 && t->mem == NULL)) {
        free(t->bounds);
        free(t->bound_tids);
        free(t->at);
        free(t->first);
        free(t->nranges);
        free(t->ranges);
        free(t->pcs);
        free(t->tids);
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

value bap_native_trace_create(value size, value every, value blocks,
                              value accesses, value read_values) {
    return create_trace(size, every, blocks, accesses, read_values, 0);
}

value bap_native_trace_snapshot_create(value size, value every, value blocks,
                                       value accesses, value read_values) {
    return create_trace(size, every, blocks, accesses, read_values, 1);
}

static int compare_sites(const void *xp, const void *yp) {
    uint64_t x = *(const uint64_t *)xp;
    uint64_t y = *(const uint64_t *)yp;
    return x < y ? -1 : x > y ? 1 : 0;
}

int bap_native_trace_captures(struct bap_native_trace *t, uint64_t site) {
    size_t lo = 0, hi = t->nsites;
    while (lo < hi) {
        size_t i = lo + (hi - lo) / 2;
        if (t->capture_sites[i] < site) {
            lo = i + 1;
        } else {
            hi = i;
        }
    }
    return lo < t->nsites && t->capture_sites[lo] == site;
}

static size_t capture_size(uint64_t ring, size_t n, size_t size) {
    if (ring == 0 || n == 0) {
        return 0;
    }
    if (n > SIZE_MAX / size || ring > SIZE_MAX / (n * size)) {
        caml_invalid_argument("Bap_native_trace.State.configure: too large");
    }
    return (size_t)ring * n * size;
}

static void capture_slice(value tuple, int *id, uint32_t *offset,
                          uint32_t *size) {
    intnat r = Long_val(Field(tuple, 0));
    intnat o = Long_val(Field(tuple, 1));
    intnat n = Long_val(Field(tuple, 2));
    if (r < 0 || r > INT_MAX || o < 0 || n < 1 || n > 8 ||
        (uintnat)o > UINT32_MAX - (uintnat)n) {
        caml_invalid_argument("Bap_native_trace.State.configure: bad slice");
    }
    *id = (int)r;
    *offset = (uint32_t)o;
    *size = (uint32_t)n;
}

value bap_native_trace_state_configure(value tv, value sites, value regs,
                                       value fields) {
    CAMLparam4(tv, sites, regs, fields);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    size_t nsites = Wosize_val(sites), nregs = Wosize_val(regs);
    size_t nfields = Wosize_val(fields);
    for (size_t i = 0; i < nregs; i++) {
        int id;
        uint32_t offset, size;
        capture_slice(Field(regs, i), &id, &offset, &size);
    }
    for (size_t i = 0; i < nfields; i++) {
        value f = Field(fields, i);
        int id;
        uint32_t offset, size;
        capture_slice(f, &id, &offset, &size);
        intnat n = Long_val(Field(f, 4));
        if (n < 1 || n > 8) {
            caml_invalid_argument(
                "Bap_native_trace.State.configure: bad field size");
        }
    }
    uint64_t ring = t->mask + 1;
    size_t sites_size = capture_size(1, nsites, sizeof(uint64_t));
    size_t regs_size =
        capture_size(1, nregs, sizeof(struct bap_native_capture_reg));
    size_t fields_size =
        capture_size(1, nfields, sizeof(struct bap_native_capture_field));
    size_t records_size =
        capture_size(ring, 1, sizeof(struct bap_native_capture));
    size_t values_size = capture_size(ring, nregs, sizeof(uint64_t));
    size_t field_values_size = capture_size(ring, nfields, sizeof(uint64_t));
    size_t present_size = capture_size(ring, nfields, sizeof(uint8_t));
    uint64_t *new_sites = malloc(sites_size ? sites_size : 1);
    struct bap_native_capture_reg *new_regs = malloc(regs_size ? regs_size : 1);
    struct bap_native_capture_field *new_fields =
        malloc(fields_size ? fields_size : 1);
    struct bap_native_capture *capture = malloc(records_size);
    uint64_t *values = malloc(values_size ? values_size : 1);
    uint64_t *field_values = malloc(field_values_size ? field_values_size : 1);
    uint8_t *present = malloc(present_size ? present_size : 1);
    uint64_t *reg_scratch = malloc(values_size ? nregs * sizeof(uint64_t) : 1);
    uint64_t *field_scratch =
        malloc(field_values_size ? nfields * sizeof(uint64_t) : 1);
    uint8_t *present_scratch =
        malloc(present_size ? nfields * sizeof(uint8_t) : 1);
    if (new_sites == NULL || new_regs == NULL || new_fields == NULL ||
        capture == NULL || values == NULL || field_values == NULL ||
        present == NULL || reg_scratch == NULL || field_scratch == NULL ||
        present_scratch == NULL) {
        free(new_sites);
        free(new_regs);
        free(new_fields);
        free(capture);
        free(values);
        free(field_values);
        free(present);
        free(reg_scratch);
        free(field_scratch);
        free(present_scratch);
        caml_raise_out_of_memory();
    }
    for (size_t i = 0; i < nsites; i++) {
        new_sites[i] = (uint64_t)Int64_val(Field(sites, i));
    }
    qsort(new_sites, nsites, sizeof(uint64_t), compare_sites);
    for (size_t i = 0; i < nregs; i++) {
        capture_slice(Field(regs, i), &new_regs[i].id, &new_regs[i].offset,
                      &new_regs[i].size);
    }
    for (size_t i = 0; i < nfields; i++) {
        value f = Field(fields, i);
        capture_slice(f, &new_fields[i].id, &new_fields[i].offset,
                      &new_fields[i].size);
        new_fields[i].at = (uint64_t)Int64_val(Field(f, 3));
        new_fields[i].field_size = (uint32_t)Long_val(Field(f, 4));
    }
    free_capture(t);
    t->capture_sites = new_sites;
    t->nsites = nsites;
    t->capture_regs = new_regs;
    t->nregs = nregs;
    t->capture_fields = new_fields;
    t->nfields = nfields;
    t->capture = capture;
    t->capture_values = values;
    t->capture_field_values = field_values;
    t->capture_present = present;
    t->capture_reg_scratch = reg_scratch;
    t->capture_field_scratch = field_scratch;
    t->capture_present_scratch = present_scratch;
    t->captures = 0;
    if (t->capture_rooted) {
        caml_modify_generational_global_root(&t->capture_reg_desc, regs);
        caml_modify_generational_global_root(&t->capture_field_desc, fields);
    } else {
        t->capture_reg_desc = regs;
        t->capture_field_desc = fields;
        caml_register_generational_global_root(&t->capture_reg_desc);
        caml_register_generational_global_root(&t->capture_field_desc);
        t->capture_rooted = 1;
    }
    CAMLreturn(Val_unit);
}

value bap_native_trace_state_captures(value tv, value site) {
    return Val_bool(bap_native_trace_captures(Bap_native_trace_val(tv),
                                              (uint64_t)Int64_val(site)));
}

value bap_native_trace_state_enabled(value tv) {
    return Val_bool(Bap_native_trace_val(tv)->nsites > 0);
}

value bap_native_trace_state_registers(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    return t->capture_rooted ? t->capture_reg_desc : caml_alloc(0, 0);
}

value bap_native_trace_state_fields(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    return t->capture_rooted ? t->capture_field_desc : caml_alloc(0, 0);
}

void bap_native_trace_capture(struct bap_native_trace *t, uint64_t site,
                              const uint64_t *regs, const uint64_t *fields,
                              const uint8_t *present) {
    if (t->count == 0 || t->capture == NULL) {
        return;
    }
    uint64_t i = t->captures & t->mask;
    t->capture[i].site = site;
    t->capture[i].index = t->count - 1;
    t->capture[i].tid = t->tid;
    for (size_t k = 0; k < t->nregs; k++) {
        t->capture_values[i * t->nregs + k] = regs[k];
    }
    for (size_t k = 0; k < t->nfields; k++) {
        t->capture_field_values[i * t->nfields + k] = fields[k];
        t->capture_present[i * t->nfields + k] = present[k];
    }
    t->captures++;
}

value bap_native_trace_state_capture(value tv, value sitev, value regs,
                                     value fields) {
    CAMLparam4(tv, sitev, regs, fields);
    CAMLlocal1(ignored);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t site = (uint64_t)Int64_val(sitev);
    if (!bap_native_trace_captures(t, site) || Wosize_val(regs) != t->nregs ||
        Wosize_val(fields) != t->nfields) {
        caml_invalid_argument("Bap_native_trace.Record.capture: bad values");
    }
    if (t->count == 0) {
        caml_invalid_argument("Bap_native_trace.Record.capture: no instruction");
    }
    uint64_t *rv = malloc(capture_size(1, t->nregs, sizeof(uint64_t)));
    uint64_t *fv = malloc(capture_size(1, t->nfields, sizeof(uint64_t)));
    uint8_t *present = malloc(capture_size(1, t->nfields, sizeof(uint8_t)));
    if ((t->nregs > 0 && rv == NULL) ||
        (t->nfields > 0 && (fv == NULL || present == NULL))) {
        free(rv);
        free(fv);
        free(present);
        caml_raise_out_of_memory();
    }
    for (size_t i = 0; i < t->nregs; i++) {
        rv[i] = (uint64_t)Int64_val(Field(regs, i));
    }
    for (size_t i = 0; i < t->nfields; i++) {
        value x = Field(fields, i);
        present[i] = !Is_long(x);
        fv[i] = present[i] ? (uint64_t)Int64_val(Field(x, 0)) : 0;
    }
    bap_native_trace_capture(t, site, rv, fv, present);
    free(rv);
    free(fv);
    free(present);
    ignored = Val_unit;
    CAMLreturn(ignored);
}

void bap_native_trace_forget_captures(struct bap_native_trace *t,
                                      uint64_t index, uint64_t pc) {
    while (t->captures > 0) {
        struct bap_native_capture *c =
            &t->capture[(t->captures - 1) & t->mask];
        if (c->index != index || c->site < pc) {
            break;
        }
        t->captures--;
    }
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
    t->tids[t->count & t->mask] = t->tid;
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
    t->tids[t->count & t->mask] = t->tid;
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
    a->write = Bool_val(write) |
               (!Bool_val(write) && t->read_values && Long_val(size) <= 8 ? 2 : 0);
    a->value = Bool_val(write) || (t->read_values && Long_val(size) <= 8)
                   ? (uint64_t)Int64_val(x)
                   : 0;
    a->old = Bool_val(write) ? (uint64_t)Int64_val(old) : 0;
    a->tid = t->tid;
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
            bap_native_trace_forget_captures(t, last, pc);
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
    bap_native_trace_forget_captures(t, last, pc);
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
    if (t->marks > 0 && t->bound_tids[i] == t->tid &&
        (last & ~(3ULL << 62)) == (bound & ~(3ULL << 62)) &&
        (!(bound & MID) || t->at[i] == pc) &&
        (t->nranges[i] == UNKNOWN ||
         t->first[i] + t->nranges[i] == t->ranges_count)) {
        t->bounds[i] = last | bound;
    } else {
        i = t->marks & (BOUNDS - 1);
        t->bounds[i] = bound;
        t->bound_tids[i] = t->tid;
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

value bap_native_trace_read_values(value tv) {
    return Val_bool(Bap_native_trace_val(tv)->read_values);
}

value bap_native_trace_clear(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    t->count = 0;
    t->accesses = 0;
    t->marks = 0;
    t->ranges_count = 0;
    t->captures = 0;
    t->skip = t->every;
    return Val_unit;
}

static uint64_t kept(uint64_t count, uint64_t mask, intnat n) {
    uint64_t k = count < mask ? count : mask;
    return n >= 0 && (uint64_t)n < k ? (uint64_t)n : k;
}

value bap_native_trace_state_records(value tv, value nv) {
    CAMLparam2(tv, nv);
    CAMLlocal5(result, cell, record, regs, fields);
    CAMLlocal1(x);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = t->capture == NULL
                     ? 0
                     : kept(t->captures, t->mask, Long_val(nv));
    uint64_t first = t->captures - k;
    result = Val_emptylist;
    for (uint64_t i = k; i > 0; i--) {
        uint64_t at = (first + i - 1) & t->mask;
        struct bap_native_capture *c = &t->capture[at];
        regs = caml_alloc_tuple(t->nregs);
        for (size_t j = 0; j < t->nregs; j++) {
            x = caml_copy_int64(t->capture_values[at * t->nregs + j]);
            Store_field(regs, j, x);
        }
        fields = caml_alloc_tuple(t->nfields);
        for (size_t j = 0; j < t->nfields; j++) {
            size_t pos = at * t->nfields + j;
            if (t->capture_present[pos]) {
                x = caml_copy_int64(t->capture_field_values[pos]);
                cell = caml_alloc_small(1, 0);
                Store_field(cell, 0, x);
                Store_field(fields, j, cell);
            } else {
                Store_field(fields, j, Val_int(0));
            }
        }
        record = caml_alloc_tuple(5);
        x = caml_copy_int64(c->site);
        Store_field(record, 0, x);
        x = caml_copy_int64(c->index);
        Store_field(record, 1, x);
        Store_field(record, 2, Val_long(c->tid));
        Store_field(record, 3, regs);
        Store_field(record, 4, fields);
        cell = caml_alloc_small(2, Tag_cons);
        Store_field(cell, 0, record);
        Store_field(cell, 1, result);
        result = cell;
    }
    CAMLreturn(result);
}

value bap_native_trace_retained(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    return Val_long(kept(t->count, t->mask, -1));
}

value bap_native_trace_retained_accesses(value tv) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    return Val_long(kept(t->accesses, t->amask, -1));
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

value bap_native_trace_tids(value tv, value n) {
    CAMLparam2(tv, n);
    CAMLlocal1(r);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t k = kept(t->count, t->mask, Long_val(n));
    r = caml_ba_alloc_dims(CAML_BA_INT64 | CAML_BA_C_LAYOUT, 1, NULL, k);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t first = t->count - k;
    for (uint64_t i = 0; i < k; i++) {
        data[i] = t->tids[(first + i) & t->mask];
    }
    CAMLreturn(r);
}

value bap_native_trace_set_thread(value tv, value tid) {
    Bap_native_trace_val(tv)->tid = (uint64_t)Long_val(tid);
    return Val_unit;
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
                           (intnat)7);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t first = t->accesses - k;
    for (uint64_t i = 0; i < k; i++) {
        struct bap_native_trace_access *a = &t->mem[(first + i) & t->amask];
        data[7 * i] = a->insn;
        data[7 * i + 1] = a->addr;
        data[7 * i + 2] = a->value;
        data[7 * i + 3] = (int64_t)a->size | ((int64_t)a->write << 32);
        data[7 * i + 4] = a->pc;
        data[7 * i + 5] = a->old;
        data[7 * i + 6] = a->tid;
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
    r = caml_ba_alloc_dims(CAML_BA_INT64 | CAML_BA_C_LAYOUT, 1, NULL, 4 * k);
    int64_t *data = Caml_ba_data_val(r);
    uint64_t first = t->marks - k;
    for (uint64_t i = 0; i < k; i++) {
        uint64_t j = (first + i) & (BOUNDS - 1);
        data[4 * i] = t->bounds[j];
        data[4 * i + 1] = t->at[j];
        data[4 * i + 2] = written(t, j);
        data[4 * i + 3] = t->bound_tids[j];
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

static int live_slot(uint64_t slot, uint64_t total, uint64_t mask,
                     int keep_all) {
    uint64_t capacity = keep_all ? mask + 1 : mask;
    uint64_t k = total < capacity ? total : capacity;
    return slot < total && total - slot <= k;
}

static value snapshot_u64_slots(const uint64_t *slots, uint64_t n,
                                uint64_t total, uint64_t mask, int keep_all) {
    CAMLparam0();
    CAMLlocal2(result, x);
    result = caml_alloc_tuple(n);
    for (uint64_t i = 0; i < n; i++) {
        x = caml_copy_int64(live_slot(i, total, mask, keep_all) ? slots[i] : 0);
        Store_field(result, i, x);
    }
    CAMLreturn(result);
}

static value snapshot_u32_slots(const uint32_t *slots, uint64_t n,
                                uint64_t total, uint64_t mask) {
    CAMLparam0();
    CAMLlocal2(result, x);
    result = caml_alloc_tuple(n);
    for (uint64_t i = 0; i < n; i++) {
        x = caml_copy_int32(live_slot(i, total, mask, 0) ? slots[i] : 0);
        Store_field(result, i, x);
    }
    CAMLreturn(result);
}

static value snapshot_modes_slots(const uint8_t *slots, uint64_t n,
                                  uint64_t total, uint64_t mask) {
    CAMLparam0();
    CAMLlocal1(result);
    result = caml_alloc_tuple(n);
    for (uint64_t i = 0; i < n; i++) {
        Store_field(result, i,
                    Val_long(live_slot(i, total, mask, 0) ? slots[i] : 0));
    }
    CAMLreturn(result);
}

static value snapshot_accesses(struct bap_native_trace *t) {
    CAMLparam0();
    CAMLlocal2(result, x);
    uint64_t n = t->mem == NULL ? 0 : t->amask + 1;
    result = caml_alloc_tuple(7 * n);
    for (uint64_t i = 0; i < n; i++) {
        struct bap_native_trace_access empty = {0};
        struct bap_native_trace_access *a =
            live_slot(i, t->accesses, t->amask, 0) ? &t->mem[i] : &empty;
        uint64_t values[7] = {
            a->insn, a->addr, a->value,
            (uint64_t)a->size | ((uint64_t)a->write << 32),
            a->pc, a->old, a->tid};
        for (int j = 0; j < 7; j++) {
            x = caml_copy_int64(values[j]);
            Store_field(result, 7 * i + j, x);
        }
    }
    CAMLreturn(result);
}

static value snapshot_bounds(struct bap_native_trace *t) {
    CAMLparam0();
    CAMLlocal2(result, x);
    result = caml_alloc_tuple(4 * BOUNDS);
    for (uint64_t i = 0; i < BOUNDS; i++) {
        int live = live_slot(i, t->marks, BOUNDS - 1, 1);
        uint64_t values[4] = {live ? t->bounds[i] : 0, live ? t->at[i] : 0,
                              live ? t->nranges[i] : 0,
                              live ? t->bound_tids[i] : 0};
        for (int j = 0; j < 4; j++) {
            x = caml_copy_int64(values[j]);
            Store_field(result, 4 * i + j, x);
        }
    }
    CAMLreturn(result);
}

static value snapshot_ranges(struct bap_native_trace *t) {
    CAMLparam0();
    CAMLlocal2(result, x);
    result = caml_alloc_tuple(2 * RANGES);
    for (uint64_t i = 0; i < RANGES; i++) {
        int live = live_slot(i, t->ranges_count, RANGES - 1, 1);
        x = caml_copy_int64(live ? t->ranges[i].addr : 0);
        Store_field(result, 2 * i, x);
        x = caml_copy_int64(live ? t->ranges[i].size : 0);
        Store_field(result, 2 * i + 1, x);
    }
    CAMLreturn(result);
}

static value snapshot_captures(struct bap_native_trace *t) {
    CAMLparam0();
    CAMLlocal5(result, record, regs, fields, x);
    CAMLlocal1(cell);
    uint64_t k = t->capture == NULL
                     ? 0
                     : (t->captures < t->mask ? t->captures : t->mask);
    uint64_t first = t->captures - k;
    result = caml_alloc_tuple(k);
    for (uint64_t i = 0; i < k; i++) {
        uint64_t at = (first + i) & t->mask;
        struct bap_native_capture *c = &t->capture[at];
        regs = caml_alloc_tuple(t->nregs);
        for (size_t j = 0; j < t->nregs; j++) {
            x = caml_copy_int64(t->capture_values[at * t->nregs + j]);
            Store_field(regs, j, x);
        }
        fields = caml_alloc_tuple(t->nfields);
        for (size_t j = 0; j < t->nfields; j++) {
            size_t pos = at * t->nfields + j;
            if (t->capture_present[pos]) {
                x = caml_copy_int64(t->capture_field_values[pos]);
                cell = caml_alloc_small(1, 0);
                Store_field(cell, 0, x);
                Store_field(fields, j, cell);
            } else {
                Store_field(fields, j, Val_int(0));
            }
        }
        record = caml_alloc_tuple(5);
        x = caml_copy_int64(c->site);
        Store_field(record, 0, x);
        x = caml_copy_int64(c->index);
        Store_field(record, 1, x);
        Store_field(record, 2, Val_long(c->tid));
        Store_field(record, 3, regs);
        Store_field(record, 4, fields);
        Store_field(result, i, record);
    }
    CAMLreturn(result);
}

value bap_native_trace_snapshot_export(value tv) {
    CAMLparam1(tv);
    CAMLlocal2(result, x);
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t n = t->mask + 1;
    result = caml_alloc_tuple(23);
    Store_field(result, 0, Val_long(n));
    Store_field(result, 1, Val_long(t->every));
    Store_field(result, 2, Val_bool(t->sizes != NULL));
    Store_field(result, 3, Val_long(t->mem == NULL ? 0 : t->amask + 1));
    Store_field(result, 4, Val_bool(t->read_values));
    x = caml_copy_int64(t->count);
    Store_field(result, 5, x);
    x = caml_copy_int64(t->skip);
    Store_field(result, 6, x);
    x = caml_copy_int64(t->tid);
    Store_field(result, 7, x);
    x = snapshot_u64_slots(t->pcs, n, t->count, t->mask, 0);
    Store_field(result, 8, x);
    x = snapshot_u64_slots(t->tids, n, t->count, t->mask, 0);
    Store_field(result, 9, x);
    x = t->sizes == NULL
            ? caml_alloc_tuple(0)
            : snapshot_u32_slots(t->sizes, n, t->count, t->mask);
    Store_field(result, 10, x);
    x = t->modes == NULL
            ? caml_alloc_tuple(0)
            : snapshot_modes_slots(t->modes, n, t->count, t->mask);
    Store_field(result, 11, x);
    x = caml_copy_int64(t->accesses);
    Store_field(result, 12, x);
    x = snapshot_accesses(t);
    Store_field(result, 13, x);
    x = caml_copy_int64(t->marks);
    Store_field(result, 14, x);
    x = caml_copy_int64(t->ranges_count);
    Store_field(result, 15, x);
    x = snapshot_bounds(t);
    Store_field(result, 16, x);
    x = snapshot_ranges(t);
    Store_field(result, 17, x);
    x = caml_alloc_tuple(t->nsites);
    for (size_t i = 0; i < t->nsites; i++) {
        value site = caml_copy_int64(t->capture_sites[i]);
        Store_field(x, i, site);
    }
    Store_field(result, 18, x);
    Store_field(result, 19,
                t->capture_rooted ? t->capture_reg_desc : caml_alloc_tuple(0));
    Store_field(result, 20,
                t->capture_rooted ? t->capture_field_desc : caml_alloc_tuple(0));
    x = caml_copy_int64(t->captures);
    Store_field(result, 21, x);
    x = snapshot_captures(t);
    Store_field(result, 22, x);
    CAMLreturn(result);
}

value bap_native_trace_snapshot_import(value tv, value state) {
    struct bap_native_trace *t = Bap_native_trace_val(tv);
    uint64_t n = t->mask + 1;
    t->count = Int64_val(Field(state, 5));
    t->skip = Int64_val(Field(state, 6));
    t->tid = Int64_val(Field(state, 7));
    for (uint64_t i = 0; i < n; i++) {
        t->pcs[i] = Int64_val(Field(Field(state, 8), i));
        t->tids[i] = Int64_val(Field(Field(state, 9), i));
        if (t->sizes != NULL) {
            t->sizes[i] = Int32_val(Field(Field(state, 10), i));
        }
        if (t->modes != NULL) {
            t->modes[i] = Long_val(Field(Field(state, 11), i));
        }
    }
    t->accesses = Int64_val(Field(state, 12));
    for (uint64_t i = 0; t->mem != NULL && i <= t->amask; i++) {
        value row = Field(state, 13);
        struct bap_native_trace_access *a = &t->mem[i];
        uint64_t size = Int64_val(Field(row, 7 * i + 3));
        a->insn = Int64_val(Field(row, 7 * i));
        a->addr = Int64_val(Field(row, 7 * i + 1));
        a->value = Int64_val(Field(row, 7 * i + 2));
        a->size = size;
        a->write = size >> 32;
        a->pc = Int64_val(Field(row, 7 * i + 4));
        a->old = Int64_val(Field(row, 7 * i + 5));
        a->tid = Int64_val(Field(row, 7 * i + 6));
    }
    t->marks = Int64_val(Field(state, 14));
    t->ranges_count = Int64_val(Field(state, 15));
    for (uint64_t i = 0; i < BOUNDS; i++) {
        value bounds = Field(state, 16);
        t->bounds[i] = Int64_val(Field(bounds, 4 * i));
        t->at[i] = Int64_val(Field(bounds, 4 * i + 1));
        t->nranges[i] = Int64_val(Field(bounds, 4 * i + 2));
        t->bound_tids[i] = Int64_val(Field(bounds, 4 * i + 3));
    }
    for (uint64_t i = 0; i < RANGES; i++) {
        value ranges = Field(state, 17);
        t->ranges[i].addr = Int64_val(Field(ranges, 2 * i));
        t->ranges[i].size = Int64_val(Field(ranges, 2 * i + 1));
    }
    t->captures = Int64_val(Field(state, 21));
    value captures = Field(state, 22);
    uint64_t k = Wosize_val(captures), first = t->captures - k;
    for (uint64_t i = 0; i < k; i++) {
        uint64_t at = (first + i) & t->mask;
        value record = Field(captures, i);
        t->capture[at].site = Int64_val(Field(record, 0));
        t->capture[at].index = Int64_val(Field(record, 1));
        t->capture[at].tid = Long_val(Field(record, 2));
        value regs = Field(record, 3), fields = Field(record, 4);
        for (size_t j = 0; j < t->nregs; j++) {
            t->capture_values[at * t->nregs + j] =
                Int64_val(Field(regs, j));
        }
        for (size_t j = 0; j < t->nfields; j++) {
            size_t pos = at * t->nfields + j;
            value field = Field(fields, j);
            t->capture_present[pos] = !Is_long(field);
            t->capture_field_values[pos] =
                Is_long(field) ? 0 : Int64_val(Field(field, 0));
        }
    }
    return Val_unit;
}

/* Compatibility with the former Unicorn-owned trace implementation. */
value bap_uc_trace_create(value size, value every, value blocks,
                          value accesses) {
    return bap_native_trace_create(size, every, blocks, accesses, Val_false);
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
