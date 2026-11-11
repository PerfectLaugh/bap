// What NEON gives, and the cumulative flags of FPSCR that it raises, of its standard FPSCR, whatever FPSCR says (testLinuxRaises):
// arithmetic, minimum and maximum, conversions, the steps of Newton-Raphson, comparisons and a fused multiply-add, each from all clear.
#include <stdio.h>
#define T(name, ins, A, B) { unsigned r, f; __asm__ volatile("vmsr fpscr,%3\n vmov s0,%2\n vmov s1,%4\n vdup.32 d2,d0[0]\n vdup.32 d3,d0[1]\n " ins "\n vmov %0,s8\n vmrs %1,fpscr" : "=&r"(r), "=&r"(f) : "r"(A), "r"(0u), "r"(B) : "d0","d1","d2","d3","d4"); printf("%-28s r=%08x fpscr=%08x\n", name, r, f); }
int main(){
  T("vadd snan,1", "vadd.f32 d4,d2,d3", 0x7f800001u, 0x3f800000u)
  T("vadd qnan(payload),1", "vadd.f32 d4,d2,d3", 0xffc12345u, 0x3f800000u)
  T("vmul den result", "vmul.f32 d4,d2,d3", 0x00800000u, 0x3f000000u)
  T("vsub min-normal", "vsub.f32 d4,d2,d3", 0x00c00000u, 0x00800000u)
  T("vmax nan,1", "vmax.f32 d4,d2,d3", 0x7fc00001u, 0x3f800000u)
  T("vmin -0,+0", "vmin.f32 d4,d2,d3", 0x80000000u, 0x00000000u)
  T("vmax -0,+0", "vmax.f32 d4,d2,d3", 0x80000000u, 0x00000000u)
  T("vmax +0,-0", "vmax.f32 d4,d2,d3", 0x00000000u, 0x80000000u)
  T("vcvt.s32 2.7", "vcvt.s32.f32 d4,d2", 0x402ccccdu, 0)
  T("vcvt.s32 nan", "vcvt.s32.f32 d4,d2", 0x7fc00000u, 0)
  T("vcvt.u32 -1", "vcvt.u32.f32 d4,d2", 0xbf800000u, 0)
  T("vrecps 2,3", "vrecps.f32 d4,d2,d3", 0x40000000u, 0x40400000u)
  T("vrsqrts 2,3", "vrsqrts.f32 d4,d2,d3", 0x40000000u, 0x40400000u)
  T("vrecps inf,0", "vrecps.f32 d4,d2,d3", 0x7f800000u, 0)
  T("vcge nan", "vcge.f32 d4,d2,d3", 0x7fc00000u, 0)
  T("vcgt snan", "vcgt.f32 d4,d2,d3", 0x7f800001u, 0)
  T("vceq snan", "vceq.f32 d4,d2,d3", 0x7f800001u, 0)
  T("vacge -3,2", "vacge.f32 d4,d2,d3", 0xc0400000u, 0x40000000u)
  T("vfma 0*inf+?", "vfma.f32 d4,d2,d3", 0x7f800000u, 0)
  T("vmla", "vmla.f32 d4,d2,d3", 0x3f800000u, 0x3f800000u)
  T("vcvt.f32.s32", "vcvt.f32.s32 d4,d2", 0x01000001u, 0)
  T("vcvt fixed", "vcvt.s32.f32 d4,d2,#4", 0x3f800000u, 0)
  T("vpadd", "vpadd.f32 d4,d2,d3", 0x3f800000u, 0x33800001u)
  return 0;}
