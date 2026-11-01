/* Each condition and shape of an IT block under each of the flags, and the jump tables of Thumb, printed so that
   a run can be compared with qemu. Generated: one function per condition and shape. */
#include <stdio.h>
#ifndef __thumb2__
#error "for Thumb 2"
#endif
typedef unsigned (*shape)(unsigned flags);
static unsigned it_eq_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit eq\n\taddeq r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee eq\n\taddeq r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_eq_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee eq\n\taddeq r0, r0, #1\n\taddne.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit ne\n\taddne r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee ne\n\taddne r0, r0, #1\n\taddne.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddsne.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddne r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ne_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee ne\n\taddne r0, r0, #1\n\taddeq.w r0, r0, #2\n\taddseq.w r1, r1, #0\n\taddeq r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit cs\n\taddcs r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee cs\n\taddcs r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cs_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee cs\n\taddcs r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit cc\n\taddcc r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee cc\n\taddcc r0, r0, #1\n\taddcc.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscc.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_cc_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee cc\n\taddcc r0, r0, #1\n\taddcs.w r0, r0, #2\n\taddscs.w r1, r1, #0\n\taddcs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit mi\n\taddmi r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee mi\n\taddmi r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_mi_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee mi\n\taddmi r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit pl\n\taddpl r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee pl\n\taddpl r0, r0, #1\n\taddpl.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddspl.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddpl r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_pl_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee pl\n\taddpl r0, r0, #1\n\taddmi.w r0, r0, #2\n\taddsmi.w r1, r1, #0\n\taddmi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit vs\n\taddvs r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee vs\n\taddvs r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vs_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee vs\n\taddvs r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit vc\n\taddvc r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee vc\n\taddvc r0, r0, #1\n\taddvc.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvc.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvc r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_vc_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee vc\n\taddvc r0, r0, #1\n\taddvs.w r0, r0, #2\n\taddsvs.w r1, r1, #0\n\taddvs r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit hi\n\taddhi r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee hi\n\taddhi r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_hi_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee hi\n\taddhi r0, r0, #1\n\taddls.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit ls\n\taddls r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee ls\n\taddls r0, r0, #1\n\taddls.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddsls.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddls r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ls_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee ls\n\taddls r0, r0, #1\n\taddhi.w r0, r0, #2\n\taddshi.w r1, r1, #0\n\taddhi r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit ge\n\taddge r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee ge\n\taddge r0, r0, #1\n\taddge.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_ge_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee ge\n\taddge r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit lt\n\taddlt r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee lt\n\taddlt r0, r0, #1\n\taddlt.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\taddslt.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddlt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_lt_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee lt\n\taddlt r0, r0, #1\n\taddge.w r0, r0, #2\n\taddsge.w r1, r1, #0\n\taddge r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit gt\n\taddgt r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee gt\n\taddgt r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_gt_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee gt\n\taddgt r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_x(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit le\n\taddle r0, r0, #1\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_t(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titt le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_e(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tite le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_tt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittt le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_te(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titte le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_et(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titet le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_ee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titee le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_ttt(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titttt le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_tte(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittte le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_tet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittet le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_tee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tittee le\n\taddle r0, r0, #1\n\taddle.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_ett(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titett le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_ete(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titete le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsle.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_eet(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeet le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddle r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static unsigned it_le_eee(unsigned flags) {
  register unsigned r0 __asm__("r0") = 0;
  register unsigned r1 __asm__("r1") = 0;
  unsigned out;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\titeee le\n\taddle r0, r0, #1\n\taddgt.w r0, r0, #2\n\taddsgt.w r1, r1, #0\n\taddgt r0, r0, #8\n\tmrs %[o], APSR" : [o] "=&r"(out), "+l"(r0), "+l"(r1) : [f] "r"(flags) : "cc");
  return r0 | (out & 0xf0000000u);
}
static const shape shapes[] = {it_eq_x, it_eq_t, it_eq_e, it_eq_tt, it_eq_te, it_eq_et, it_eq_ee, it_eq_ttt, it_eq_tte, it_eq_tet, it_eq_tee, it_eq_ett, it_eq_ete, it_eq_eet, it_eq_eee, it_ne_x, it_ne_t, it_ne_e, it_ne_tt, it_ne_te, it_ne_et, it_ne_ee, it_ne_ttt, it_ne_tte, it_ne_tet, it_ne_tee, it_ne_ett, it_ne_ete, it_ne_eet, it_ne_eee, it_cs_x, it_cs_t, it_cs_e, it_cs_tt, it_cs_te, it_cs_et, it_cs_ee, it_cs_ttt, it_cs_tte, it_cs_tet, it_cs_tee, it_cs_ett, it_cs_ete, it_cs_eet, it_cs_eee, it_cc_x, it_cc_t, it_cc_e, it_cc_tt, it_cc_te, it_cc_et, it_cc_ee, it_cc_ttt, it_cc_tte, it_cc_tet, it_cc_tee, it_cc_ett, it_cc_ete, it_cc_eet, it_cc_eee, it_mi_x, it_mi_t, it_mi_e, it_mi_tt, it_mi_te, it_mi_et, it_mi_ee, it_mi_ttt, it_mi_tte, it_mi_tet, it_mi_tee, it_mi_ett, it_mi_ete, it_mi_eet, it_mi_eee, it_pl_x, it_pl_t, it_pl_e, it_pl_tt, it_pl_te, it_pl_et, it_pl_ee, it_pl_ttt, it_pl_tte, it_pl_tet, it_pl_tee, it_pl_ett, it_pl_ete, it_pl_eet, it_pl_eee, it_vs_x, it_vs_t, it_vs_e, it_vs_tt, it_vs_te, it_vs_et, it_vs_ee, it_vs_ttt, it_vs_tte, it_vs_tet, it_vs_tee, it_vs_ett, it_vs_ete, it_vs_eet, it_vs_eee, it_vc_x, it_vc_t, it_vc_e, it_vc_tt, it_vc_te, it_vc_et, it_vc_ee, it_vc_ttt, it_vc_tte, it_vc_tet, it_vc_tee, it_vc_ett, it_vc_ete, it_vc_eet, it_vc_eee, it_hi_x, it_hi_t, it_hi_e, it_hi_tt, it_hi_te, it_hi_et, it_hi_ee, it_hi_ttt, it_hi_tte, it_hi_tet, it_hi_tee, it_hi_ett, it_hi_ete, it_hi_eet, it_hi_eee, it_ls_x, it_ls_t, it_ls_e, it_ls_tt, it_ls_te, it_ls_et, it_ls_ee, it_ls_ttt, it_ls_tte, it_ls_tet, it_ls_tee, it_ls_ett, it_ls_ete, it_ls_eet, it_ls_eee, it_ge_x, it_ge_t, it_ge_e, it_ge_tt, it_ge_te, it_ge_et, it_ge_ee, it_ge_ttt, it_ge_tte, it_ge_tet, it_ge_tee, it_ge_ett, it_ge_ete, it_ge_eet, it_ge_eee, it_lt_x, it_lt_t, it_lt_e, it_lt_tt, it_lt_te, it_lt_et, it_lt_ee, it_lt_ttt, it_lt_tte, it_lt_tet, it_lt_tee, it_lt_ett, it_lt_ete, it_lt_eet, it_lt_eee, it_gt_x, it_gt_t, it_gt_e, it_gt_tt, it_gt_te, it_gt_et, it_gt_ee, it_gt_ttt, it_gt_tte, it_gt_tet, it_gt_tee, it_gt_ett, it_gt_ete, it_gt_eet, it_gt_eee, it_le_x, it_le_t, it_le_e, it_le_tt, it_le_te, it_le_et, it_le_ee, it_le_ttt, it_le_tte, it_le_tet, it_le_tee, it_le_ett, it_le_ete, it_le_eet, it_le_eee};

/* A branch and a load in the last slot. */
static unsigned last_branch(unsigned flags) {
  unsigned out = 0;
  __asm__ volatile("msr APSR_nzcvq, %[f]\n\tit ne\n\tbne 1f\n\tmovs %[o], #1\n\tb 2f\n1:\tmovs %[o], #2\n2:" : [o] "+l"(out) : [f] "r"(flags) : "cc");
  return out;
}
static unsigned table_byte(unsigned index) {
  unsigned out;
  __asm__ volatile("tbb [pc, %[i]]\n"
                   "1:\t.byte (2f-1b)/2, (3f-1b)/2, (4f-1b)/2, (5f-1b)/2\n"
                   "2:\tmovs %[o], #10\n\tb 6f\n3:\tmovs %[o], #11\n\tb 6f\n4:\tmovs %[o], #12\n\tb 6f\n5:\tmovs %[o], #13\n6:"
                   : [o] "=&l"(out) : [i] "r"(index) : "cc");
  return out;
}
static unsigned table_half(unsigned index) {
  unsigned out;
  __asm__ volatile("tbh [pc, %[i], lsl #1]\n"
                   "1:\t.short (2f-1b)/2, (3f-1b)/2, (4f-1b)/2, (5f-1b)/2\n"
                   "2:\tmovs %[o], #20\n\tb 6f\n3:\tmovs %[o], #21\n\tb 6f\n4:\tmovs %[o], #22\n\tb 6f\n5:\tmovs %[o], #23\n6:"
                   : [o] "=&l"(out) : [i] "r"(index) : "cc");
  return out;
}
int main(void) {
  unsigned total = 0;
  for (unsigned s = 0; s < sizeof shapes / sizeof shapes[0]; s++) {
    unsigned hash = 0;
    for (unsigned f = 0; f < 16; f++) hash = hash * 31 + shapes[s](f << 28);
    printf("%u %08x\n", s, hash);
    total += hash;
  }
  for (unsigned f = 0; f < 16; f++) printf("%u", last_branch(f << 28));
  printf("\n");
  for (unsigned i = 0; i < 4; i++) printf("%u %u\n", table_byte(i), table_half(i));
  printf("total %08x\n", total);
  return 0;
}
