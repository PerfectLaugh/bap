; i686, executed natively with the 32-bit C library (gcc -m32), see
; lib_test/cross/lifter_gen.ml
(include x86.sexp)
(bits 32)
(sp ESP)
(mode i686)
(gpr (0 1 0x7f 0x80 0x7fff 0x8000 0x7fffffff 0x80000000 0xffffffff 0x12345678 0xfedcba98))
(gpr2 (0 1 0x80 0x7fff 0x80000000 0xffffffff 0x7fffffff 0x12345678))
