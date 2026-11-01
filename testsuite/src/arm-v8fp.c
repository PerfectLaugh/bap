/* The floating point of ARMv8 that isn't VRINT, on what its edges are, printed so that a run can be compared with qemu. */
#include <stdio.h>
#include <string.h>

static const unsigned long long doubles[] = {
  0x4004000000000000ull, 0xc004000000000000ull, 0x3ff8000000000000ull, 0xbff8000000000000ull, 0x4000000000000000ull,
  0, 0x8000000000000000ull, 0x7ff0000000000000ull, 0xfff0000000000000ull, 0x7ff8000000000001ull, 0x7ff0000000000001ull,
  0x41f0000000000000ull, 0xc1f0000000000000ull, 0x41e0000000000000ull, 0x0000000000000001ull, 0x3fe0000000000000ull };
static const unsigned singles[] = {
  0x40200000, 0xc0200000, 0x3fc00000, 0xbfc00000, 0x40000000, 0, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00001, 0x7f800001,
  0x4f800000, 0xcf800000, 0x4f000000, 0x00000001, 0x3f000000 };
enum { COUNT = 16 };

static double d_of(unsigned long long bits) { double value; memcpy(&value, &bits, 8); return value; }
static float s_of(unsigned bits) { float value; memcpy(&value, &bits, 4); return value; }
static unsigned long long bits_d(double value) { unsigned long long bits; memcpy(&bits, &value, 8); return bits; }
static unsigned bits_s(float value) { unsigned bits; memcpy(&bits, &value, 4); return bits; }
static unsigned long hash;
static void add(unsigned long long value) { hash = hash * 31 + (unsigned)value + (unsigned)(value >> 32) * 7; }

#define BIN_D(op) do { for (int i = 0; i < COUNT; i++) for (int j = 0; j < COUNT; j++) { double a = d_of(doubles[i]), b = d_of(doubles[j]), r; \
    __asm__ volatile(op ".f64 %P0, %P1, %P2" : "=w"(r) : "w"(a), "w"(b)); add(bits_d(r)); } printf(op " d %lx\n", hash); } while (0)
#define BIN_S(op) do { for (int i = 0; i < COUNT; i++) for (int j = 0; j < COUNT; j++) { float a = s_of(singles[i]), b = s_of(singles[j]), r; \
    __asm__ volatile(op ".f32 %0, %1, %2" : "=t"(r) : "t"(a), "t"(b)); add(bits_s(r)); } printf(op " s %lx\n", hash); } while (0)
#define SEL_D(op) do { for (unsigned f = 0; f < 16; f++) { double a = 1.5, b = 2.5, r; \
    __asm__ volatile("msr APSR_nzcvq, %3\n" op ".f64 %P0, %P1, %P2" : "=w"(r) : "w"(a), "w"(b), "r"(f << 28) : "cc"); add(bits_d(r)); } printf(op " d %lx\n", hash); } while (0)
#define SEL_S(op) do { for (unsigned f = 0; f < 16; f++) { float a = 1.5f, b = 2.5f, r; \
    __asm__ volatile("msr APSR_nzcvq, %3\n" op ".f32 %0, %1, %2" : "=t"(r) : "t"(a), "t"(b), "r"(f << 28) : "cc"); add(bits_s(r)); } printf(op " s %lx\n", hash); } while (0)
#define CVT_D(op) do { for (int i = 0; i < COUNT; i++) { double a = d_of(doubles[i]); float r; \
    __asm__ volatile(op ".f64 %0, %P1" : "=t"(r) : "w"(a)); add(bits_s(r)); } printf(op " d %lx\n", hash); } while (0)
#define CVT_S(op) do { for (int i = 0; i < COUNT; i++) { float a = s_of(singles[i]); float r; \
    __asm__ volatile(op ".f32 %0, %1" : "=t"(r) : "t"(a)); add(bits_s(r)); } printf(op " s %lx\n", hash); } while (0)
#define ALL_CVT(mode) do { CVT_D("vcvt" mode ".s32"); CVT_D("vcvt" mode ".u32"); CVT_S("vcvt" mode ".s32"); CVT_S("vcvt" mode ".u32"); } while (0)

int main(void) {
  BIN_D("vmaxnm"); BIN_S("vmaxnm"); BIN_D("vminnm"); BIN_S("vminnm");
  SEL_D("vseleq"); SEL_S("vseleq"); SEL_D("vselge"); SEL_S("vselge"); SEL_D("vselgt"); SEL_S("vselgt"); SEL_D("vselvs"); SEL_S("vselvs");
  ALL_CVT("a"); ALL_CVT("n"); ALL_CVT("p"); ALL_CVT("m");
  for (int i = 0; i < COUNT; i++) {
    double a = d_of(doubles[i]); float keep = s_of(0x12345678), low = keep, high = keep;
    __asm__ volatile("vcvtb.f16.f64 %0, %P1" : "+t"(low) : "w"(a));
    __asm__ volatile("vcvtt.f16.f64 %0, %P1" : "+t"(high) : "w"(a));
    add(bits_s(low)); add(bits_s(high));
    float half = s_of(0x3c00c000 + i * 0x01000100); double back, top;
    __asm__ volatile("vcvtb.f64.f16 %P0, %1" : "=w"(back) : "t"(half));
    __asm__ volatile("vcvtt.f64.f16 %P0, %1" : "=w"(top) : "t"(half));
    add(bits_d(back)); add(bits_d(top));
  }
  printf("half %lx\n", hash);
  return 0;
}
