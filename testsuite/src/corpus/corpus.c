/* The code, whose instructions the compilers emit commonly, for the
   coverage of the lifters, see corpus.sh: the integers of every width,
   the bits, the floats, the conversions, the vectors of the loops, the
   atomics, the copies, and the calls. */

#include <stdint.h>
#include <stddef.h>

#define N 64

typedef int8_t i8;
typedef int16_t i16;
typedef int32_t i32;
typedef int64_t i64;
typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

#if defined(PART_INT) || defined(ALL)
/* integers */

#define ARITH(T)                                                             \
    T add_##T(T a, T b) { return a + b; }                                    \
    T sub_##T(T a, T b) { return a - b; }                                    \
    T mul_##T(T a, T b) { return a * b; }                                    \
    T div_##T(T a, T b) { return b ? a / b : 0; }                            \
    T mod_##T(T a, T b) { return b ? a % b : 0; }                            \
    T and_##T(T a, T b) { return a & b; }                                    \
    T or_##T(T a, T b) { return a | b; }                                     \
    T xor_##T(T a, T b) { return a ^ b; }                                    \
    T not_##T(T a) { return ~a; }                                            \
    T neg_##T(T a) { return -a; }                                            \
    T shl_##T(T a, int s) { return a << (s & (sizeof(T) * 8 - 1)); }         \
    T shr_##T(T a, int s) { return a >> (s & (sizeof(T) * 8 - 1)); }         \
    T shl3_##T(T a) { return a << 3; }                                       \
    T shr3_##T(T a) { return a >> 3; }                                       \
    T rotl_##T(T a, int s) {                                                 \
        unsigned w = sizeof(T) * 8;                                          \
        s &= w - 1;                                                          \
        return (T)((a << s) | (a >> ((w - s) & (w - 1))));                   \
    }                                                                        \
    int lt_##T(T a, T b) { return a < b; }                                   \
    int le_##T(T a, T b) { return a <= b; }                                  \
    int eq_##T(T a, T b) { return a == b; }                                  \
    T min_##T(T a, T b) { return a < b ? a : b; }                            \
    T max_##T(T a, T b) { return a > b ? a : b; }                            \
    T abs_##T(T a) { return a < 0 ? -a : a; }                                \
    T sel_##T(int c, T a, T b) { return c ? a : b; }                         \
    T madd_##T(T a, T b, T c) { return a * b + c; }                          \
    T divc_##T(T a) { return a / 7; }                                        \
    T modc_##T(T a) { return a % 10; }                                       \
    T mulc_##T(T a) { return a * 1000003; }

ARITH(i8)
ARITH(i16)
ARITH(i32)
ARITH(i64)
ARITH(u8)
ARITH(u16)
ARITH(u32)
ARITH(u64)

#ifdef __SIZEOF_INT128__
typedef __int128 i128;
typedef unsigned __int128 u128;
ARITH(i128)
ARITH(u128)
u64 mulhi(u64 a, u64 b) { return (u64)(((u128)a * b) >> 64); }
i64 smulhi(i64 a, i64 b) { return (i64)(((i128)a * b) >> 64); }
#endif

i64 widen_mul(i32 a, i32 b) { return (i64)a * b; }
u64 uwiden_mul(u32 a, u32 b) { return (u64)a * b; }
i32 sext8(i8 x) { return x; }
i32 sext16(i16 x) { return x; }
i64 sext32(i32 x) { return x; }
u64 zext32(u32 x) { return x; }
u32 trunc64(u64 x) { return (u32)x; }

/* overflow and saturation */

int add_overflow(i32 a, i32 b, i32 *r) { return __builtin_add_overflow(a, b, r); }
int sub_overflow(i64 a, i64 b, i64 *r) { return __builtin_sub_overflow(a, b, r); }
int mul_overflow(i32 a, i32 b, i32 *r) { return __builtin_mul_overflow(a, b, r); }
int uadd_overflow(u64 a, u64 b, u64 *r) { return __builtin_add_overflow(a, b, r); }
u8 sat_add_u8(u8 a, u8 b) { unsigned s = a + b; return s > 255 ? 255 : s; }
i16 sat_add_i16(i16 a, i16 b) {
    i32 s = a + b;
    return s > 32767 ? 32767 : s < -32768 ? -32768 : s;
}

#endif

#if defined(PART_BITS) || defined(ALL)
/* bits */

int popcount32(u32 x) { return __builtin_popcount(x); }
int popcount64(u64 x) { return __builtin_popcountll(x); }
int clz32(u32 x) { return x ? __builtin_clz(x) : 32; }
int clz64(u64 x) { return x ? __builtin_clzll(x) : 64; }
int ctz32(u32 x) { return x ? __builtin_ctz(x) : 32; }
int ctz64(u64 x) { return x ? __builtin_ctzll(x) : 64; }
int ffs32(i32 x) { return __builtin_ffs(x); }
int parity32(u32 x) { return __builtin_parity(x); }
u16 bswap16(u16 x) { return __builtin_bswap16(x); }
u32 bswap32(u32 x) { return __builtin_bswap32(x); }
u64 bswap64(u64 x) { return __builtin_bswap64(x); }
u32 bitrev32(u32 x) {
    x = ((x >> 1) & 0x55555555) | ((x & 0x55555555) << 1);
    x = ((x >> 2) & 0x33333333) | ((x & 0x33333333) << 2);
    x = ((x >> 4) & 0x0F0F0F0F) | ((x & 0x0F0F0F0F) << 4);
    return __builtin_bswap32(x);
}
u32 extract_bits(u32 x) { return (x >> 5) & 0x3FF; }
u32 insert_bits(u32 x, u32 y) { return (x & ~0xFF00u) | ((y & 0xFF) << 8); }
u64 andn(u64 a, u64 b) { return a & ~b; }
u64 orn(u64 a, u64 b) { return a | ~b; }
u64 blsr(u64 x) { return x & (x - 1); }
u64 blsi(u64 x) { return x & -x; }
u64 blsmsk(u64 x) { return x ^ (x - 1); }
u32 bzhi(u32 x, int n) { return n >= 32 ? x : x & ((1u << n) - 1); }
i32 sign_extract(i32 x) { return (x << 12) >> 20; }

struct bitfields {
    unsigned a : 3;
    signed b : 5;
    unsigned c : 13;
    unsigned d : 11;
};

int bitfield_get(struct bitfields *f) { return f->a + f->b + f->c + f->d; }
void bitfield_set(struct bitfields *f, int x) {
    f->a = x;
    f->b = x >> 3;
    f->c = x >> 8;
}

#endif

#if defined(PART_FLOAT) || defined(ALL)
/* floats */

#define FLOATS(T)                                                            \
    T fadd_##T(T a, T b) { return a + b; }                                   \
    T fsub_##T(T a, T b) { return a - b; }                                   \
    T fmul_##T(T a, T b) { return a * b; }                                   \
    T fdiv_##T(T a, T b) { return a / b; }                                   \
    T fneg_##T(T a) { return -a; }                                           \
    T fabs_##T(T a) { return __builtin_fabs(a); }                            \
    T fsqrt_##T(T a) { return __builtin_sqrt(a); }                           \
    T fma_##T(T a, T b, T c) { return __builtin_fma(a, b, c); }              \
    T fmadd_##T(T a, T b, T c) { return a * b + c; }                         \
    T fmin_##T(T a, T b) { return a < b ? a : b; }                           \
    T fmax_##T(T a, T b) { return __builtin_fmax(a, b); }                    \
    int flt_##T(T a, T b) { return a < b; }                                  \
    int fle_##T(T a, T b) { return a <= b; }                                 \
    int feq_##T(T a, T b) { return a == b; }                                 \
    int funord_##T(T a, T b) { return __builtin_isunordered(a, b); }         \
    i32 ftoi_##T(T a) { return (i32)a; }                                     \
    i64 ftol_##T(T a) { return (i64)a; }                                     \
    u32 ftou_##T(T a) { return (u32)a; }                                     \
    u64 ftoul_##T(T a) { return (u64)a; }                                    \
    T itof_##T(i32 a) { return (T)a; }                                       \
    T ltof_##T(i64 a) { return (T)a; }                                       \
    T utof_##T(u32 a) { return (T)a; }                                       \
    T ultof_##T(u64 a) { return (T)a; }                                      \
    T fround_##T(T a) { return __builtin_round(a); }                         \
    T ffloor_##T(T a) { return __builtin_floor(a); }                         \
    T fceil_##T(T a) { return __builtin_ceil(a); }                           \
    T ftrunc_##T(T a) { return __builtin_trunc(a); }                         \
    T fcopysign_##T(T a, T b) { return __builtin_copysign(a, b); }           \
    T fconst_##T(T a) { return a * (T)1.5 + (T)0.25; }                       \
    T fsel_##T(T a, T b, T c) { return a > b ? c : b; }

FLOATS(float)
FLOATS(double)

double ftod(float x) { return x; }
float dtof(double x) { return (float)x; }

#endif

#if defined(PART_VECTOR) || defined(ALL)
/* vectors of the loops */

#define VECTOR(T)                                                            \
    void vadd_##T(T *restrict r, const T *restrict a, const T *restrict b) { \
        for (int i = 0; i < N; i++) r[i] = a[i] + b[i];                      \
    }                                                                        \
    void vmul_##T(T *restrict r, const T *restrict a, const T *restrict b) { \
        for (int i = 0; i < N; i++) r[i] = a[i] * b[i];                      \
    }                                                                        \
    void vsub_##T(T *restrict r, const T *restrict a, const T *restrict b) { \
        for (int i = 0; i < N; i++) r[i] = a[i] - b[i];                      \
    }                                                                        \
    void vmin_##T(T *restrict r, const T *restrict a, const T *restrict b) { \
        for (int i = 0; i < N; i++) r[i] = a[i] < b[i] ? a[i] : b[i];        \
    }                                                                        \
    void vmax_##T(T *restrict r, const T *restrict a, const T *restrict b) { \
        for (int i = 0; i < N; i++) r[i] = a[i] > b[i] ? a[i] : b[i];        \
    }                                                                        \
    void vsel_##T(T *restrict r, const T *restrict a, const T *restrict b) { \
        for (int i = 0; i < N; i++) r[i] = a[i] == b[i] ? a[i] : 0;          \
    }                                                                        \
    T vsum_##T(const T *a) {                                                 \
        T s = 0;                                                             \
        for (int i = 0; i < N; i++) s += a[i];                               \
        return s;                                                            \
    }                                                                        \
    T vdot_##T(const T *a, const T *b) {                                     \
        T s = 0;                                                             \
        for (int i = 0; i < N; i++) s += a[i] * b[i];                        \
        return s;                                                            \
    }                                                                        \
    void vshift_##T(T *restrict r, const T *restrict a) {                    \
        for (int i = 0; i < N; i++) r[i] = (T)(a[i] >> 2) ^ (T)(a[i] << 1);  \
    }                                                                        \
    void vabs_##T(T *restrict r, const T *restrict a) {                      \
        for (int i = 0; i < N; i++) r[i] = a[i] < 0 ? -a[i] : a[i];          \
    }                                                                        \
    void vneg_##T(T *restrict r, const T *restrict a) {                      \
        for (int i = 0; i < N; i++) r[i] = ~a[i] & (a[i] | 3);               \
    }

VECTOR(i8)
VECTOR(i16)
VECTOR(i32)
VECTOR(i64)
VECTOR(u8)
VECTOR(u16)
VECTOR(u32)
VECTOR(u64)

#define FVECTOR(T)                                                           \
    void fvadd_##T(T *restrict r, const T *restrict a, const T *restrict b) {\
        for (int i = 0; i < N; i++) r[i] = a[i] + b[i] * a[i];               \
    }                                                                        \
    void fvdiv_##T(T *restrict r, const T *restrict a, const T *restrict b) {\
        for (int i = 0; i < N; i++) r[i] = a[i] / b[i];                      \
    }                                                                        \
    void fvsqrt_##T(T *restrict r, const T *restrict a) {                    \
        for (int i = 0; i < N; i++) r[i] = __builtin_sqrt(a[i]);             \
    }                                                                        \
    void fvminmax_##T(T *restrict r, const T *restrict a,                    \
                      const T *restrict b) {                                 \
        for (int i = 0; i < N; i++)                                          \
            r[i] = a[i] < b[i] ? __builtin_fmax(a[i], 0) : b[i];             \
    }                                                                        \
    T fvsum_##T(const T *a) {                                                \
        T s = 0;                                                             \
        for (int i = 0; i < N; i++) s += a[i];                               \
        return s;                                                            \
    }                                                                        \
    void fvcvt_##T(i32 *restrict r, const T *restrict a) {                   \
        for (int i = 0; i < N; i++) r[i] = (i32)a[i];                        \
    }                                                                        \
    void ivcvt_##T(T *restrict r, const i32 *restrict a) {                   \
        for (int i = 0; i < N; i++) r[i] = (T)a[i];                          \
    }

FVECTOR(float)
FVECTOR(double)

void widen(i32 *restrict r, const i16 *restrict a, const u8 *restrict b) {
    for (int i = 0; i < N; i++) r[i] = a[i] * b[i];
}

void narrow(u8 *restrict r, const i32 *restrict a) {
    for (int i = 0; i < N; i++) r[i] = a[i] > 255 ? 255 : a[i] < 0 ? 0 : a[i];
}

void interleave(i32 *restrict r, const i32 *restrict a) {
    for (int i = 0; i < N / 2; i++) {
        r[2 * i] = a[i];
        r[2 * i + 1] = a[i + N / 2];
    }
}

void gather(i32 *restrict r, const i32 *restrict a, const i32 *restrict idx) {
    for (int i = 0; i < N; i++) r[i] = a[idx[i] & (N - 1)];
}

u8 avg(const u8 *a, const u8 *b, u8 *restrict r) {
    for (int i = 0; i < N; i++) r[i] = (a[i] + b[i] + 1) >> 1;
    return r[0];
}

#endif

#if defined(PART_ATOMIC) || defined(ALL)
/* atomics */

#define ATOMICS(T)                                                           \
    T atomic_add_##T(T *p, T x) {                                            \
        return __atomic_fetch_add(p, x, __ATOMIC_SEQ_CST);                   \
    }                                                                        \
    T atomic_sub_##T(T *p, T x) {                                            \
        return __atomic_sub_fetch(p, x, __ATOMIC_ACQ_REL);                   \
    }                                                                        \
    T atomic_and_##T(T *p, T x) {                                            \
        return __atomic_fetch_and(p, x, __ATOMIC_RELAXED);                   \
    }                                                                        \
    T atomic_or_##T(T *p, T x) {                                             \
        return __atomic_fetch_or(p, x, __ATOMIC_RELEASE);                    \
    }                                                                        \
    T atomic_xor_##T(T *p, T x) {                                            \
        return __atomic_fetch_xor(p, x, __ATOMIC_ACQUIRE);                   \
    }                                                                        \
    T atomic_xchg_##T(T *p, T x) {                                           \
        return __atomic_exchange_n(p, x, __ATOMIC_SEQ_CST);                  \
    }                                                                        \
    int atomic_cas_##T(T *p, T *e, T x) {                                    \
        return __atomic_compare_exchange_n(p, e, x, 0, __ATOMIC_SEQ_CST,      \
                                           __ATOMIC_SEQ_CST);                \
    }                                                                        \
    T atomic_load_##T(T *p) { return __atomic_load_n(p, __ATOMIC_SEQ_CST); }  \
    void atomic_store_##T(T *p, T x) {                                       \
        __atomic_store_n(p, x, __ATOMIC_SEQ_CST);                            \
    }                                                                        \
    T atomic_max_##T(T *p, T x) {                                            \
        T old = __atomic_load_n(p, __ATOMIC_RELAXED);                        \
        while (old < x && !__atomic_compare_exchange_n(                      \
                              p, &old, x, 1, __ATOMIC_SEQ_CST,               \
                              __ATOMIC_RELAXED))                             \
            ;                                                                \
        return old;                                                          \
    }

ATOMICS(u8)
ATOMICS(u16)
ATOMICS(u32)
ATOMICS(u64)

void fence(void) { __atomic_thread_fence(__ATOMIC_SEQ_CST); }
void fence_acq(void) { __atomic_thread_fence(__ATOMIC_ACQUIRE); }

#endif

#if defined(PART_MEMORY) || defined(ALL)
/* memory */

struct big {
    i64 x[9];
    i32 y;
    i8 z[13];
};

void copy_big(struct big *d, const struct big *s) { *d = *s; }
void zero_big(struct big *d) { *d = (struct big){0}; }
void fill(u8 *p, u8 v, size_t n) { __builtin_memset(p, v, n); }
void copy(void *d, const void *s, size_t n) { __builtin_memcpy(d, s, n); }
void move(void *d, const void *s, size_t n) { __builtin_memmove(d, s, n); }
size_t length(const char *s) {
    size_t n = 0;
    while (s[n]) n++;
    return n;
}
u32 unaligned32(const u8 *p) {
    u32 x;
    __builtin_memcpy(&x, p + 1, 4);
    return x;
}
u64 unaligned64(const u8 *p) {
    u64 x;
    __builtin_memcpy(&x, p + 3, 8);
    return x;
}
i64 indexed(const i64 *a, i32 i, i32 j) { return a[i] + a[j * 2 + 1]; }
i32 stack_array(int n) {
    volatile i32 a[37];
    for (int i = 0; i < 37; i++) a[i] = i * n;
    return a[n % 37];
}

/* control */

int jump_table(int x) {
    switch (x) {
    case 0: return 11;
    case 1: return 23;
    case 2: return 37;
    case 3: return 41;
    case 4: return 59;
    case 5: return 61;
    case 6: return 73;
    case 7: return 89;
    default: return -1;
    }
}

typedef int (*callback)(int);
int indirect(callback f, int x) { return f(x) + f(x + 1); }
int recursive(int n) { return n <= 1 ? 1 : n * recursive(n - 1); }
int tail(int n, int acc) { return n == 0 ? acc : tail(n - 1, acc + n); }
int many_args(int a, int b, int c, int d, int e, int f, int g, int h, int i,
              int j, double k, double l, float m) {
    return a + b + c + d + e + f + g + h + i + j + (int)(k * l) + (int)m;
}
int call_many(void) {
    return many_args(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1.5, 2.5, 3.5f);
}
struct pair {
    i64 a;
    double b;
};
struct pair make_pair(i64 a, double b) { return (struct pair){a, b}; }
struct big make_big(int x) {
    struct big b = {{0}};
    b.y = x;
    return b;
}
int loops(const i32 *a, int n) {
    int s = 0;
    for (int i = 0; i < n; i++)
        if (a[i] & 1) s += a[i];
        else s -= a[i] >> 1;
    return s;
}
int select_chain(int a, int b, int c) {
    return (a > b) ? (b > c ? b : c) : (a > c ? a : c);
}
long double ldadd(long double a, long double b) { return a + b * a; }
#endif
