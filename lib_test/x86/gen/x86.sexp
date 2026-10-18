; the common fields of x86_64.sexp and i686.sexp, the instructions are
; assembled with GNU as and executed natively by runner.c, see
; lib_test/cross/lifter_gen.ml
(toolchain native)
(helpers X86_tests_helpers)
; the XMM registers are the low halves of the YMM registers of BAP
(rename_xmm true)
(sets
 (count (0 1 7 8 15 16 31 32 33 63 64 0xff))
 (bool (0 1))
 (xmm (0 0x3ff0000000000000 0x40000000000000003ff8000000000000 0xc0040000000000007ff0000000000000 0x7ff8000000000000fff0000000000000 0x80000000000000000000000000000001 0x3f800000c02000007f8000003fc00000 0x0123456789abcdeffedcba9876543210 0x7fc00000ff800000000000004f000000 0x4004000000000000bff8000000000000 0xbfe0000000000000c004000000000000 0x40200000c02000003f000000bfc00000))
 (byte (0 1 0x7f 0x80 0xff))
 (nz (1 0x80 0x7fffffff 0x80000000 0xffffffff 0x8000000000000000 0xffffffffffffffff 0x123456789abcdef0 0x10))
 (nz32 (1 0x80 0x7fff 0x8000 0x80000000 0xffffffff 0x12345678 0x10))
 (vec (0 0xffffffffffffffffffffffffffffffff 0x0123456789abcdeffedcba9876543210 0x80007fff00010000ffff800000ff7f01 0x7f80017fff00fe81807f7f8001ff0080))
 (mxcsr (0x1f80 0x3f80 0x5f80 0x7f80))
 (ymm (0 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 0x0123456789abcdeffedcba98765432100f1e2d3c4b5a69788796a5b4c3d2e1f0 0x80007fff00010000ffff800000ff7f017f80017fff00fe81807f7f8001ff0080))
 (mm (0 0xffffffffffffffff 0x0123456789abcdef 0x80007fff0001ff80 0x7f80017fff00fe81))
 (nzhigh (0 1))
 (count16 (0 1 7 8 15))
 (small (0 1 3))
 (pair (0x41 0x81))
 (bitoff (0 5 31 32 63 64 0xffffffffffffffff 0xffffffffffffffc0 100))
 (ah (0 0xd500 0xff00))
 (flagword (0x202 0xad7))
 (str (0 0x6463626100000000000000000000 0x00000000000000006867666564636261 0x2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a2a 0x7a610000000000000000000000000000 0x0000000000000000000000000000617a 0x00000000000000000064000063626100))
 (len (0 3 8 16 0xfffffffb 100)))
(kinds
 ((CF PF AF ZF SF IF DF OF) bool)
 ((XMM*) xmm)
 ((YMM*) ymm)
 ((MM*) mm))
