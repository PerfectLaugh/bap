/* The runtime of the blocks of the lifted engine, that the JIT of LLVM
   compiled, see bap_lifted_jit.ml: the memory, whose pages are the
   bigarrays of the engine, and the accesses of the blocks, which check
   the permissions, and log the bytes, that the stores overwrite, so that
   the instruction, whose access faults, is undone, as the lifted engine
   undoes it.

   The code calls no OCaml, and allocates nothing, so that the bytes of
   the registers, which are in the heap of OCaml, stay, while it runs. */

#include <stddef.h>
#include <stdint.h>
#include <time.h>
#include <stdlib.h>
#include <string.h>

#include <caml/alloc.h>
#include <caml/bigarray.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "bap_native_trace.h"

#define PAGE_BITS 12
#define PAGE_SIZE ((uint64_t)1 << PAGE_BITS)
#define PAGE_OF(addr) ((addr) & ~(PAGE_SIZE - 1))
#define TLB_SIZE 256
#define UNDO_SIZE 4096
#define MAX_REGS 256

/* the permissions of Unicorn, see Uc.Perm */
#define PERM_READ 1
#define PERM_WRITE 2
#define PERM_EXEC 4

typedef struct jit_mem jit_mem;

/* the frame, whose fields the code reads and writes, see the type %frame
   of bap_lifted_jit.ml */
typedef struct {
    jit_mem *mem;
    uint64_t next;  /* the target of the jump of the block */
    uint32_t undo;  /* the bytes of the stores of the instruction */
    uint64_t chained; /* the instructions of the blocks before the last */
    uint64_t last; /* the address of the last block, that ran */
    uint64_t budget; /* the instructions, that the linked blocks may run */
    uint64_t until; /* the address, at which the run stops */
    int32_t chain; /* if the blocks continue with the linked ones */
    void *tlb; /* the pages, that the code accesses itself, see [entry] */
    void *log; /* the undo log, see [undo_entry] */
} frame;

/* the bytes, that a store of at most 8 bytes overwrote, which are
   restored, if the instruction stops, in the reverse order */
typedef struct {
    uint8_t *at;
    uint64_t old;
    uint32_t size;
} undo_entry;

/* the offsets, that the code of the blocks reads, see [exit_to] of
   bap_lifted_jit.ml */
_Static_assert(offsetof(frame, chained) == 24, "chained");
_Static_assert(offsetof(frame, last) == 32, "last");
_Static_assert(offsetof(frame, budget) == 40, "budget");
_Static_assert(offsetof(frame, until) == 48, "until");
_Static_assert(offsetof(frame, chain) == 56, "chain");
_Static_assert(offsetof(frame, tlb) == 64, "tlb");
_Static_assert(offsetof(frame, log) == 72, "log");
_Static_assert(sizeof(undo_entry) == 24, "undo_entry");

/* the entries of the next blocks of a block, @block_slots of its module,
   keyed by the targets of its exits, which the code calls, and the
   runtime fills, see [run] */
typedef struct {
    uint64_t key;
    void *fn;
    uint64_t pc, end, length;
} slot;

typedef struct {
    uint64_t page;
    uint8_t *data;
    int perm;
} entry;

/* the layout, that the code reads, see [fast_access] of bap_lifted_jit.ml,
   whose undo log has UNDO_SIZE entries too */
_Static_assert(sizeof(entry) == 24 && offsetof(entry, data) == 8 &&
                   offsetof(entry, perm) == 16,
               "entry");

/* the flags of a block of ARM, its mode, Thumb, and the modes, after
   the jump of its last instruction to an even and to an odd address, see
   [jump] of bap_lifted.ml */
#define LINK_ARM 8
#define LINK_THUMB 1
#define LINK_EVEN 2
#define LINK_ODD 4
/* the last instruction of the block jumps, so the next one starts a
   block of the traces, see [record] */
#define LINK_JUMPS 16

/* the traces of the blocks, that the runs record, see [record] */
#define MAX_TRACES 4
/* they are in the shared trace library, which Windows may load further than
   2 GB away, where the relative calls, that flexdll relocates, don't reach, so
   they are called by their addresses, which the compiler doesn't fold into the
   calls */
static void *(*volatile trace_of)(value) = bap_native_trace_of;
static void (*volatile trace_block)(void *, uint64_t, uint32_t, int, int) =
    bap_native_trace_block;

/* the block, that the run of another one continues with, see [run] */
typedef struct {
    uint64_t pc; /* EMPTY, if the slot is free */
    intnat fn;
    uint64_t end; /* the address after its instructions */
    uint32_t length; /* its instructions */
    int flags; /* see LINK_ARM */
    uint8_t *code; /* the copy of its bytes */
    size_t size;
    slot *slots; /* its next blocks */
} jit_link;

struct jit_mem {
    frame frame;
    jit_link *links; /* the blocks, by their addresses, with open addressing */
    size_t lcapacity, lcount;

    entry *table; /* the pages, with the open addressing */
    size_t capacity, count;
    uint64_t seed; /* of the hash, which the program can't predict */
    entry tlb[TLB_SIZE];
    undo_entry undo[UNDO_SIZE];
    /* the traces of the blocks, which the hooks keep alive, and if the
       last block, that ran, starts a block of them */
    void *traces[MAX_TRACES];
    int ntraces;
    int starts;
};

#define EMPTY UINT64_MAX

#define Mem_val(v) (*(jit_mem **)Data_custom_val(v))

static void free_links(jit_mem *m) {
    for (size_t i = 0; i < m->lcapacity; i++)
        if (m->links[i].pc != EMPTY) free(m->links[i].code);
}

static void finalize(value v) {
    jit_mem *m = Mem_val(v);
    free_links(m);
    free(m->links);
    free(m->table);
    free(m);
}

static struct custom_operations mem_ops = {
    "bap.engine.jit.mem",       finalize,
    custom_compare_default,     custom_hash_default,
    custom_serialize_default,   custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

/* the hash of the page, whose seed is random, so that the program can't
   map the pages, whose hashes collide, which would make the accesses
   slow */
static size_t hash(uint64_t seed, uint64_t page, size_t capacity) {
    uint64_t x = ((page >> PAGE_BITS) ^ seed) * 0x9E3779B97F4A7C15ULL;
    x ^= x >> 29;
    x *= 0xBF58476D1CE4E5B9ULL;
    return (size_t)(x >> 32) & (capacity - 1);
}

static void flush_tlb(jit_mem *m) {
    for (int i = 0; i < TLB_SIZE; i++) m->tlb[i].page = EMPTY;
}

static void insert(uint64_t seed, entry *table, size_t capacity, entry e) {
    size_t i = hash(seed, e.page, capacity);
    while (table[i].page != EMPTY && table[i].page != e.page)
        i = (i + 1) & (capacity - 1);
    table[i] = e;
}

static void rehash(jit_mem *m, size_t capacity) {
    entry *table = malloc(capacity * sizeof(entry));
    if (!table) caml_raise_out_of_memory();
    for (size_t i = 0; i < capacity; i++) table[i].page = EMPTY;
    for (size_t i = 0; i < m->capacity; i++)
        if (m->table[i].page != EMPTY)
            insert(m->seed, table, capacity, m->table[i]);
    free(m->table);
    m->table = table;
    m->capacity = capacity;
}

/* the index of the page in the table, or of the empty entry, where it
   would be */
static size_t slot_of(jit_mem *m, uint64_t page) {
    size_t i = hash(m->seed, page, m->capacity);
    while (m->table[i].page != EMPTY && m->table[i].page != page)
        i = (i + 1) & (m->capacity - 1);
    return i;
}

static entry *find(jit_mem *m, uint64_t page) {
    entry *t = &m->tlb[(page >> PAGE_BITS) & (TLB_SIZE - 1)];
    if (t->page == page) return t;
    size_t i = slot_of(m, page);
    if (m->table[i].page != page) return NULL;
    *t = m->table[i];
    return t;
}

/* the slot of the block at [pc], or the free one, where it would be */
static size_t link_slot(jit_mem *m, jit_link *links, size_t capacity,
                        uint64_t pc) {
    size_t i = hash(m->seed, pc << PAGE_BITS, capacity);
    while (links[i].pc != EMPTY && links[i].pc != pc)
        i = (i + 1) & (capacity - 1);
    return i;
}

static void relink(jit_mem *m, size_t capacity) {
    jit_link *links = malloc(capacity * sizeof(jit_link));
    if (!links) caml_raise_out_of_memory();
    for (size_t i = 0; i < capacity; i++) links[i].pc = EMPTY;
    for (size_t i = 0; i < m->lcapacity; i++)
        if (m->links[i].pc != EMPTY)
            links[link_slot(m, links, capacity, m->links[i].pc)] =
                m->links[i];
    free(m->links);
    m->links = links;
    m->lcapacity = capacity;
}

static jit_link *find_link(jit_mem *m, uint64_t pc) {
    jit_link *l = &m->links[link_slot(m, m->links, m->lcapacity, pc)];
    return l->pc == pc ? l : NULL;
}

value bap_jit_mem_create(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(v);
    jit_mem *m = calloc(1, sizeof(jit_mem));
    if (!m) caml_raise_out_of_memory();
    m->frame.mem = m;
    m->frame.tlb = m->tlb;
    m->frame.log = m->undo;
    m->frame.until = EMPTY;
    m->seed = ((uint64_t)(uintptr_t)m << 16) ^ (uint64_t)time(NULL) ^
              ((uint64_t)clock() << 32);
    v = caml_alloc_custom(&mem_ops, sizeof(jit_mem *), 0, 1);
    Mem_val(v) = m;
    rehash(m, 64);
    relink(m, 64);
    flush_tlb(m);
    CAMLreturn(v);
}

/* [map mem page data perm] the page, whose bytes are [data], which the
   engine keeps, while it is mapped */
value bap_jit_mem_map(value mem, value page, value data, value perm) {
    jit_mem *m = Mem_val(mem);
    uint64_t p = (uint64_t)Int64_val(page);
    if (p != PAGE_OF(p) || Caml_ba_array_val(data)->dim[0] != PAGE_SIZE)
        caml_invalid_argument("Bap_lifted_jit.Runtime.map");
    flush_tlb(m);
    if (find(m, p)) caml_invalid_argument("Bap_lifted_jit.Runtime.map: mapped");
    if (2 * (m->count + 1) > m->capacity) rehash(m, 2 * m->capacity);
    entry e = {p, Caml_ba_data_val(data), Int_val(perm)};
    insert(m->seed, m->table, m->capacity, e);
    m->count++;
    flush_tlb(m);
    return Val_unit;
}

value bap_jit_mem_unmap(value mem, value page) {
    jit_mem *m = Mem_val(mem);
    uint64_t p = (uint64_t)Int64_val(page);
    size_t mask = m->capacity - 1;
    size_t i = slot_of(m, p);
    if (m->table[i].page == p) {
        /* the entries of the cluster after it, which the hole would cut
           off from their homes, move into it, as the deletions of the
           linear probing do, rather than the table is made anew */
        m->table[i].page = EMPTY;
        m->count--;
        size_t hole = i;
        for (size_t j = (i + 1) & mask; m->table[j].page != EMPTY;
             j = (j + 1) & mask) {
            size_t home = hash(m->seed, m->table[j].page, m->capacity);
            /* the entry stays, if its home is cyclically in (hole, j] */
            int stays = hole <= j ? (hole < home && home <= j)
                                  : (hole < home || home <= j);
            if (!stays) {
                m->table[hole] = m->table[j];
                m->table[j].page = EMPTY;
                hole = j;
            }
        }
    }
    flush_tlb(m);
    return Val_unit;
}

value bap_jit_mem_protect(value mem, value page, value perm) {
    jit_mem *m = Mem_val(mem);
    uint64_t p = (uint64_t)Int64_val(page);
    size_t i = slot_of(m, p);
    if (m->table[i].page == p) m->table[i].perm = Int_val(perm);
    flush_tlb(m);
    return Val_unit;
}

/* the accesses of the code, which return 0, if the access faults, so
   that the instruction is run again by the lifted engine, which calls
   the hooks of the invalid accesses */

int32_t bap_jit_load(frame *f, uint64_t addr, uint32_t n, uint8_t *out) {
    jit_mem *m = f->mem;
    while (n > 0) {
        entry *e = find(m, PAGE_OF(addr));
        if (!e || !(e->perm & PERM_READ)) return 0;
        uint64_t off = addr - e->page;
        uint32_t k = PAGE_SIZE - off < n ? (uint32_t)(PAGE_SIZE - off) : n;
        memcpy(out, e->data + off, k);
        out += k;
        addr += k;
        n -= k;
    }
    return 1;
}

/* the pages of the bytes, that a store of [n] bytes at [addr] writes,
   which wrap around the end of the address space, as the accesses of the
   closures do, are writable */
static int writable(jit_mem *m, uint64_t addr, uint32_t n) {
    while (n > 0) {
        entry *e = find(m, PAGE_OF(addr));
        /* the store to the code, which may be of the block, that runs,
           whose code is checked only, when it starts, stops it, so that
           the closures run the instruction, and the next block checks
           the code */
        if (!e || !(e->perm & PERM_WRITE) || (e->perm & PERM_EXEC)) return 0;
        uint64_t off = addr - e->page;
        uint32_t k = PAGE_SIZE - off < n ? (uint32_t)(PAGE_SIZE - off) : n;
        addr += k;
        n -= k;
    }
    return 1;
}

int32_t bap_jit_store(frame *f, uint64_t addr, uint32_t n,
                      const uint8_t *in) {
    jit_mem *m = f->mem;
    /* the store is checked as a whole, so that it writes all of its
       bytes, or none */
    if (n / 8 + 2 > UNDO_SIZE - f->undo || !writable(m, addr, n)) return 0;
    while (n > 0) {
        entry *e = find(m, PAGE_OF(addr));
        uint64_t off = addr - e->page;
        uint32_t k = PAGE_SIZE - off < n ? (uint32_t)(PAGE_SIZE - off) : n;
        for (uint32_t i = 0; i < k; i += 8) {
            undo_entry *u = &m->undo[f->undo++];
            u->at = e->data + off + i;
            u->size = k - i < 8 ? k - i : 8;
            u->old = 0;
            memcpy(&u->old, u->at, u->size);
        }
        memcpy(e->data + off, in, k);
        in += k;
        addr += k;
        n -= k;
    }
    return 1;
}

value bap_jit_helpers(value unit) {
    CAMLparam1(unit);
    CAMLlocal3(r, load, store);
    load = caml_copy_nativeint((intnat)&bap_jit_load);
    store = caml_copy_nativeint((intnat)&bap_jit_store);
    r = caml_alloc_tuple(2);
    Store_field(r, 0, load);
    Store_field(r, 1, store);
    CAMLreturn(r);
}

typedef int32_t (*block)(frame *, uint8_t **);

/* [link mem pc fn code length end] the block [fn] at [pc], whose bytes
   are [code], and whose [length] instructions end at [end], which the
   runs of the blocks continue with, see [run] */
static void clear_slots(slot *s) {
    for (int i = 0; i < 2; i++) {
        s[i].key = EMPTY;
        s[i].fn = NULL;
    }
}

value bap_jit_link(value mem, value pc, value fn, value code, value length,
                   value end, value flags, value slots) {
    jit_mem *m = Mem_val(mem);
    uint64_t p = (uint64_t)Int64_val(pc);
    if (find_link(m, p)) return Val_unit;
    if (2 * (m->lcount + 1) > m->lcapacity) relink(m, 2 * m->lcapacity);
    size_t n = caml_string_length(code);
    uint8_t *copy = malloc(n);
    if (!copy) caml_raise_out_of_memory();
    memcpy(copy, String_val(code), n);
    jit_link l = {p,    Nativeint_val(fn), (uint64_t)Int64_val(end),
              (uint32_t)Long_val(length), Int_val(flags), copy, n,
              (slot *)Nativeint_val(slots)};
    clear_slots(l.slots);
    m->links[link_slot(m, m->links, m->lcapacity, p)] = l;
    m->lcount++;
    return Val_unit;
}

value bap_jit_link_byte(value *argv, int argc) {
    (void)argc;
    return bap_jit_link(argv[0], argv[1], argv[2], argv[3], argv[4],
                        argv[5], argv[6], argv[7]);
}

/* the block at [pc] isn't linked, e.g., as its code is released */
value bap_jit_unlink(value mem, value pc) {
    jit_mem *m = Mem_val(mem);
    uint64_t p = (uint64_t)Int64_val(pc);
    jit_link *l = find_link(m, p);
    if (l) {
        /* the blocks don't continue with it anymore */
        for (size_t i = 0; i < m->lcapacity; i++)
            if (m->links[i].pc != EMPTY)
                for (int k = 0; k < 2; k++)
                    if (m->links[i].slots[k].fn &&
                        m->links[i].slots[k].pc == p) {
                        m->links[i].slots[k].key = EMPTY;
                        m->links[i].slots[k].fn = NULL;
                    }
        free(l->code);
        l->pc = EMPTY;
        m->lcount--;
        /* the links after it are inserted again */
        relink(m, m->lcapacity);
    }
    return Val_unit;
}

value bap_jit_unlink_all(value mem) {
    jit_mem *m = Mem_val(mem);
    for (size_t i = 0; i < m->lcapacity; i++)
        if (m->links[i].pc != EMPTY) clear_slots(m->links[i].slots);
    free_links(m);
    for (size_t i = 0; i < m->lcapacity; i++) m->links[i].pc = EMPTY;
    m->lcount = 0;
    return Val_unit;
}

/* [traces mem traces] the blocks, that the runs chain, are recorded in
   the [traces] of the blocks, see [Bap_native_trace], and they return to the
   runtime, rather than call the next ones themselves */
value bap_jit_traces(value mem, value traces) {
    jit_mem *m = Mem_val(mem);
    size_t n = Wosize_val(traces);
    if (n > MAX_TRACES) caml_invalid_argument("Bap_lifted_jit: too many traces");
    for (size_t i = 0; i < n; i++) m->traces[i] = trace_of(Field(traces, i));
    m->ntraces = (int)n;
    return Val_unit;
}

/* the block, that ran whole, before the next one, in the traces */
static void record(jit_mem *m, jit_link *l) {
    for (int i = 0; i < m->ntraces; i++)
        trace_block(m->traces[i], l->pc, (uint32_t)(l->end - l->pc),
                    l->flags & LINK_THUMB, m->starts);
    m->starts = (l->flags & LINK_JUMPS) != 0;
}

value bap_jit_starts(value mem) { return Val_bool(Mem_val(mem)->starts); }

/* [limits mem chain budget until] the runs continue with the linked
   blocks, if [chain], at most for [budget] instructions, until [until] */
value bap_jit_limits(value mem, value chain, value budget, value until) {
    jit_mem *m = Mem_val(mem);
    m->frame.chain = Bool_val(chain);
    m->frame.budget = (uint64_t)Long_val(budget);
    m->frame.until = (uint64_t)Int64_val(until);
    return Val_unit;
}

/* [run fn mem regs code addr] runs the block [fn], whose instructions
   are the bytes [code] at [addr], which the engine drops, when they are
   written, rather than they are checked here, whose registers are
   [regs], and then
   the linked blocks, that the blocks continue with, see [limits], and
   returns the result of the last one, see bap_lifted_jit.ml, or -1, if
   its code changed, whose address is [last], after the [chained]
   instructions of the blocks before it */
intnat bap_jit_run(intnat fn, value mem, value regs, value code,
                   int64_t addr) {
    jit_mem *m = Mem_val(mem);
    frame *f = &m->frame;
    size_t nregs = Wosize_val(regs);
    uint8_t *ptrs[MAX_REGS];
    (void)code;
    f->chained = 0;
    f->last = (uint64_t)addr;
    /* the engine runs the blocks at the starts of the blocks */
    m->starts = 1;
    if (nregs > MAX_REGS) return -1;
    for (size_t i = 0; i < nregs; i++) ptrs[i] = Bytes_val(Field(regs, i));
    uint64_t pc = (uint64_t)addr;
    /* the code of the blocks doesn't continue with the next ones itself,
       e.g., with itself, while the traces record them here */
    int chain = f->chain;
    if (m->ntraces) f->chain = 0;
    jit_link *current = chain ? find_link(m, pc) : NULL;
    for (;;) {
        f->undo = 0;
        int32_t r = ((block)fn)(f, ptrs);
        if ((r & 3) == 0 || (r & 3) == 3) {
            /* the instruction, that stopped, didn't run, e.g., the delay
               slot of the branch, that is taken */
            for (uint32_t i = f->undo; i-- > 0;)
                memcpy(m->undo[i].at, &m->undo[i].old, m->undo[i].size);
            return r;
        }
        /* the block may have continued with the next ones, by the tail
           calls, see [exit_to] */
        if (f->last != pc) {
            pc = f->last;
            current = chain ? find_link(m, pc) : NULL;
        }
        if (!current) return r;
        uint64_t ran = (uint64_t)(r >> 2) + 1;
        uint64_t key = (r & 3) == 1 ? f->next : current->end;
        uint64_t next = key;
        int thumb = current->flags & LINK_THUMB;
        if ((current->flags & LINK_ARM) && (r & 3) == 1) {
            /* the jump, that changes the mode, returns to the engine */
            uint64_t dst = next & ~(uint64_t)1;
            int mode = dst == current->end ? thumb
                       : (next & 1)       ? current->flags & LINK_ODD
                                          : current->flags & LINK_EVEN;
            if (!mode != !thumb) return r;
            next = dst;
        }
        jit_link *l = find_link(m, next);
        if (!l || (l->flags & LINK_THUMB) != thumb) return r;
        /* the block continues with the next one by itself, next time,
           unless the blocks are recorded here */
        if (m->ntraces == 0) {
            slot *s = current->slots;
            int i = s[0].fn == NULL || s[0].key == key ? 0 : 1;
            s[i].key = key;
            s[i].fn = (void *)l->fn;
            s[i].pc = l->pc;
            s[i].end = l->end;
            s[i].length = l->length;
        }
        if (next == f->until || (f->until > l->pc && f->until < l->end) ||
            f->chained + ran + l->length > f->budget)
            return r;
        record(m, current);
        f->chained += ran;
        f->last = next;
        current = l;
        fn = l->fn;
        pc = next;
    }
}

value bap_jit_run_byte(value fn, value mem, value regs, value code,
                       value addr) {
    return Val_long(bap_jit_run(Nativeint_val(fn), mem, regs, code,
                                Int64_val(addr)));
}

int64_t bap_jit_next(value mem) { return (int64_t)Mem_val(mem)->frame.next; }

int64_t bap_jit_last(value mem) { return (int64_t)Mem_val(mem)->frame.last; }

value bap_jit_last_byte(value mem) {
    return caml_copy_int64(bap_jit_last(mem));
}

intnat bap_jit_chained(value mem) {
    return (intnat)Mem_val(mem)->frame.chained;
}

value bap_jit_chained_byte(value mem) {
    return Val_long(bap_jit_chained(mem));
}

value bap_jit_next_byte(value mem) {
    return caml_copy_int64(bap_jit_next(mem));
}
