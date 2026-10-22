#!/usr/bin/env python3
"""generates ieee754-intrinsics.lisp, the intrinsics of IEEE 754, that
the lifters call, e.g., intrinsic:fadd_rtz_ieee754_binary_32, which
Primus runs with ieee754-op, see primus_lisp_ieee754.ml:

  ./ieee754-intrinsics.py > ieee754-intrinsics.lisp
"""

rmodes = ["rne", "rtz", "rtp", "rtn", "rna"]
floats = [16, 32, 64, 80, 128]
ints = [8, 16, 32, 64, 128]
ops = {"fadd": 1, "fsub": 2, "fmul": 3, "fdiv": 4, "fsqrt": 5, "fround": 6,
       "fconvert": 7, "cast_float": 8, "cast_sfloat": 9, "cast_int": 10,
       "cast_sint": 11, "forder": 12, "is_nan": 13, "is_inf": 14,
       "fmad": 15}

print(""";; the intrinsics of IEEE 754, that the lifters call, which run in
;; Primus with ieee754-op, exactly, see primus_lisp_ieee754.ml, generated
;; by ieee754-intrinsics.py: <op>_<rmode>_ieee754_binary_<size>, e.g.,
;; fmad, x0 * x1 + x2, rounded once, and, for
;; the conversions, <op>_<rmode>_ieee754_binary_<from>_<to>, whose
;; operands and results are of their sizes

(require ieee754)

(in-package intrinsic)

(declare (global x0 x1 x2 y0))

(defun ieee754-policy ()
  "the NaNs, and the invalid integers, of the target, see ieee754-op:
   the NaNs are propagated, and the integers saturate, and are 0 for the
   NaNs, as on ARM"
  0)

(defun ieee754-policy ()
  "the default NaN is negative, the first NaN operand is the result, and
   the invalid integers are indefinite"
  (declare (context (target x86)))
  0x15)

(defun ieee754-policy ()
  "the NaNs are canonical, and the integers of the NaNs are the maximum"
  (declare (context (target riscv)))
  0x22)

(defun ieee754-policy ()
  "the integers of the NaNs are the minimum"
  (declare (context (target powerpc-family)))
  0x30)

(defun ieee754-policy ()
  "the invalid integers are the maximum"
  (declare (context (target mips-family)))
  0x20)
""")

def defun(name, op, rm, src, dst, args):
    print(f'(defun {name} ()\n'
          f'  (declare (external "intrinsic:{name}"))\n'
          f'  (set y0 (ieee754-op {ops[op]} {rm} {src} {dst} (ieee754-policy) {args})))\n')

for k in floats:
    for i, rm in enumerate(rmodes):
        for op in ["fadd", "fsub", "fmul", "fdiv"]:
            defun(f"{op}_{rm}_ieee754_binary_{k}", op, i, k, k, "x0 x1")
        defun(f"fmad_{rm}_ieee754_binary_{k}", "fmad", i, k, k, "x0 x1 x2")
        for op in ["fsqrt", "fround"]:
            defun(f"{op}_{rm}_ieee754_binary_{k}", op, i, k, k, "x0")
        for k2 in floats:
            if k2 != k:
                defun(f"fconvert_{rm}_ieee754_binary_{k}_{k2}", "fconvert", i, k, k2, "x0")
        for n in ints:
            defun(f"cast_float_{rm}_ieee754_binary_{n}_{k}", "cast_float", i, n, k, "x0")
            defun(f"cast_sfloat_{rm}_ieee754_binary_{n}_{k}", "cast_sfloat", i, n, k, "x0")
            defun(f"cast_int_{rm}_ieee754_binary_{k}_{n}", "cast_int", i, k, n, "x0")
            defun(f"cast_sint_{rm}_ieee754_binary_{k}_{n}", "cast_sint", i, k, n, "x0")
    defun(f"forder_ieee754_binary_{k}", "forder", 0, k, 1, "x0 x1")
    defun(f"is_nan_ieee754_binary_{k}", "is_nan", 0, k, 1, "x0")
    defun(f"is_inf_ieee754_binary_{k}", "is_inf", 0, k, 1, "x0")
