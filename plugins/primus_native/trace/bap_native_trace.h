#ifndef BAP_NATIVE_TRACE_H
#define BAP_NATIVE_TRACE_H

#include <stdint.h>

#include <caml/custom.h>
#include <caml/mlvalues.h>

#define BAP_NATIVE_TRACE_RANGES 65536
#define BAP_NATIVE_TRACE_BOUNDS 65536
#define BAP_NATIVE_TRACE_UNKNOWN UINT64_MAX
#define BAP_NATIVE_TRACE_MID (1ULL << 61)

struct bap_native_trace_range {
    uint64_t addr;
    uint64_t size;
};

struct bap_native_trace_access {
    uint64_t insn;
    uint64_t pc;
    uint64_t addr;
    uint64_t value;
    uint64_t old;
    uint64_t tid;
    uint32_t size;
    uint32_t write;
};

struct bap_native_trace {
    uint64_t count;
    uint64_t mask;
    uint64_t *pcs;
    uint64_t *tids;
    uint64_t tid;
    uint32_t *sizes;
    uint8_t *modes;
    uint8_t thumb;
    uint64_t every;
    uint64_t skip;
    uint64_t accesses;
    uint64_t amask;
    int read_values;
    struct bap_native_trace_access *mem;
    uint64_t marks;
    uint64_t *bounds;
    uint64_t *bound_tids;
    uint64_t *at;
    uint64_t *first;
    uint64_t *nranges;
    uint64_t ranges_count;
    struct bap_native_trace_range *ranges;
};

#define Bap_native_trace_val(v) \
    (*((struct bap_native_trace **)Data_custom_val(v)))

void *bap_native_trace_of(value tv);
void bap_native_trace_block(void *tp, uint64_t pc, uint32_t size, int thumb,
                            int starts);
void bap_native_trace_add_bound(struct bap_native_trace *t, uint64_t bound,
                                uint64_t pc,
                                struct bap_native_trace_range *ranges,
                                uint64_t n);

#endif
