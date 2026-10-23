/* The runtime of the blocks of the lifted engine, that the JIT of LLVM
   compiled, see bap_engine_jit.ml: the memory, whose pages are the
   bigarrays of the engine, and the accesses of the blocks, which check
   the permissions, and log the bytes, that the stores overwrite, so that
   the instruction, whose access faults, is undone, as the lifted engine
   undoes it.

   The code calls no OCaml, and allocates nothing, so that the bytes of
   the registers, which are in the heap of OCaml, stay, while it runs. */

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
   of bap_engine_jit.ml */
typedef struct {
    jit_mem *mem;
    uint64_t next;  /* the target of the jump of the block */
    uint32_t undo;  /* the bytes of the stores of the instruction */
} frame;

typedef struct {
    uint64_t page;
    uint8_t *data;
    int perm;
} entry;

struct jit_mem {
    frame frame;
    entry *table; /* the pages, with the open addressing */
    size_t capacity, count;
    uint64_t seed; /* of the hash, which the program can't predict */
    entry tlb[TLB_SIZE];
    uint8_t *undo_at[UNDO_SIZE];
    uint8_t undo_old[UNDO_SIZE];
};

#define EMPTY UINT64_MAX

#define Mem_val(v) (*(jit_mem **)Data_custom_val(v))

static void finalize(value v) {
    jit_mem *m = Mem_val(v);
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

value bap_jit_mem_create(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(v);
    jit_mem *m = calloc(1, sizeof(jit_mem));
    if (!m) caml_raise_out_of_memory();
    m->frame.mem = m;
    m->seed = ((uint64_t)(uintptr_t)m << 16) ^ (uint64_t)time(NULL) ^
              ((uint64_t)clock() << 32);
    v = caml_alloc_custom(&mem_ops, sizeof(jit_mem *), 0, 1);
    Mem_val(v) = m;
    rehash(m, 64);
    flush_tlb(m);
    CAMLreturn(v);
}

/* [map mem page data perm] the page, whose bytes are [data], which the
   engine keeps, while it is mapped */
value bap_jit_mem_map(value mem, value page, value data, value perm) {
    jit_mem *m = Mem_val(mem);
    uint64_t p = (uint64_t)Int64_val(page);
    if (p != PAGE_OF(p) || Caml_ba_array_val(data)->dim[0] != PAGE_SIZE)
        caml_invalid_argument("Bap_engine_jit.Runtime.map");
    flush_tlb(m);
    if (find(m, p)) caml_invalid_argument("Bap_engine_jit.Runtime.map: mapped");
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
    if (n > UNDO_SIZE - f->undo || !writable(m, addr, n)) return 0;
    while (n > 0) {
        entry *e = find(m, PAGE_OF(addr));
        uint64_t off = addr - e->page;
        uint32_t k = PAGE_SIZE - off < n ? (uint32_t)(PAGE_SIZE - off) : n;
        for (uint32_t i = 0; i < k; i++) {
            m->undo_at[f->undo] = e->data + off + i;
            m->undo_old[f->undo] = e->data[off + i];
            f->undo++;
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

/* if the bytes at [addr] are [code], which are executable */
static int same_code(jit_mem *m, uint64_t addr, const uint8_t *code,
                     size_t n) {
    while (n > 0) {
        entry *e = find(m, PAGE_OF(addr));
        if (!e || !(e->perm & PERM_EXEC)) return 0;
        uint64_t off = addr - e->page;
        size_t k = PAGE_SIZE - off < n ? (size_t)(PAGE_SIZE - off) : n;
        if (memcmp(e->data + off, code, k)) return 0;
        code += k;
        addr += k;
        n -= k;
    }
    return 1;
}

typedef int32_t (*block)(frame *, uint8_t **);

/* [run fn mem regs code addr] runs the block [fn], whose instructions
   are the bytes [code] at [addr], and whose registers are [regs], see
   bap_engine_jit.ml for the result, or returns -1, if the code changed */
intnat bap_jit_run(intnat fn, value mem, value regs, value code,
                   int64_t addr) {
    jit_mem *m = Mem_val(mem);
    size_t nregs = Wosize_val(regs);
    uint8_t *ptrs[MAX_REGS];
    if (nregs > MAX_REGS) return -1;
    if (!same_code(m, (uint64_t)addr, (const uint8_t *)String_val(code),
                   caml_string_length(code)))
        return -1;
    for (size_t i = 0; i < nregs; i++) ptrs[i] = Bytes_val(Field(regs, i));
    m->frame.undo = 0;
    int32_t r = ((block)fn)(&m->frame, ptrs);
    /* the instruction, that stopped, didn't run */
    if ((r & 3) == 0)
        for (uint32_t i = m->frame.undo; i-- > 0;)
            *m->undo_at[i] = m->undo_old[i];
    return r;
}

value bap_jit_run_byte(value fn, value mem, value regs, value code,
                       value addr) {
    return Val_long(bap_jit_run(Nativeint_val(fn), mem, regs, code,
                                Int64_val(addr)));
}

int64_t bap_jit_next(value mem) { return (int64_t)Mem_val(mem)->frame.next; }

value bap_jit_next_byte(value mem) {
    return caml_copy_int64(bap_jit_next(mem));
}
