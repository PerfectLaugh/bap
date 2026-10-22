;; the intrinsics of IEEE 754, that the lifters call, which run in
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

(defun fadd_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fadd_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 1 0 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fsub_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fsub_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 2 0 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmul_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fmul_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 3 0 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fdiv_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fdiv_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 4 0 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmad_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fmad_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 15 0 16 16 (ieee754-policy) x0:16 x1:16 x2:16)))

(defun fsqrt_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fsqrt_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 5 0 16 16 (ieee754-policy) x0:16)))

(defun fround_rne_ieee754_binary_16 ()
  (declare (external "intrinsic:fround_rne_ieee754_binary_16"))
  (set y0:16 (ieee754-op 6 0 16 16 (ieee754-policy) x0:16)))

(defun fconvert_rne_ieee754_binary_16_32 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 7 0 16 32 (ieee754-policy) x0:16)))

(defun fconvert_rne_ieee754_binary_16_64 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 7 0 16 64 (ieee754-policy) x0:16)))

(defun fconvert_rne_ieee754_binary_16_80 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 7 0 16 80 (ieee754-policy) x0:16)))

(defun fconvert_rne_ieee754_binary_16_128 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 7 0 16 128 (ieee754-policy) x0:16)))

(defun cast_float_rne_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 8 0 8 16 (ieee754-policy) x0:8)))

(defun cast_sfloat_rne_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 9 0 8 16 (ieee754-policy) x0:8)))

(defun cast_int_rne_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 10 0 16 8 (ieee754-policy) x0:16)))

(defun cast_sint_rne_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 11 0 16 8 (ieee754-policy) x0:16)))

(defun cast_float_rne_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 8 0 16 16 (ieee754-policy) x0:16)))

(defun cast_sfloat_rne_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 9 0 16 16 (ieee754-policy) x0:16)))

(defun cast_int_rne_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 10 0 16 16 (ieee754-policy) x0:16)))

(defun cast_sint_rne_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 11 0 16 16 (ieee754-policy) x0:16)))

(defun cast_float_rne_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 8 0 32 16 (ieee754-policy) x0:32)))

(defun cast_sfloat_rne_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 9 0 32 16 (ieee754-policy) x0:32)))

(defun cast_int_rne_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 10 0 16 32 (ieee754-policy) x0:16)))

(defun cast_sint_rne_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 11 0 16 32 (ieee754-policy) x0:16)))

(defun cast_float_rne_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 8 0 64 16 (ieee754-policy) x0:64)))

(defun cast_sfloat_rne_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 9 0 64 16 (ieee754-policy) x0:64)))

(defun cast_int_rne_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 10 0 16 64 (ieee754-policy) x0:16)))

(defun cast_sint_rne_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 11 0 16 64 (ieee754-policy) x0:16)))

(defun cast_float_rne_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 8 0 128 16 (ieee754-policy) x0:128)))

(defun cast_sfloat_rne_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 9 0 128 16 (ieee754-policy) x0:128)))

(defun cast_int_rne_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 10 0 16 128 (ieee754-policy) x0:16)))

(defun cast_sint_rne_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 11 0 16 128 (ieee754-policy) x0:16)))

(defun fadd_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fadd_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 1 1 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fsub_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fsub_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 2 1 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmul_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fmul_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 3 1 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fdiv_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fdiv_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 4 1 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmad_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fmad_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 15 1 16 16 (ieee754-policy) x0:16 x1:16 x2:16)))

(defun fsqrt_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fsqrt_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 5 1 16 16 (ieee754-policy) x0:16)))

(defun fround_rtz_ieee754_binary_16 ()
  (declare (external "intrinsic:fround_rtz_ieee754_binary_16"))
  (set y0:16 (ieee754-op 6 1 16 16 (ieee754-policy) x0:16)))

(defun fconvert_rtz_ieee754_binary_16_32 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 7 1 16 32 (ieee754-policy) x0:16)))

(defun fconvert_rtz_ieee754_binary_16_64 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 7 1 16 64 (ieee754-policy) x0:16)))

(defun fconvert_rtz_ieee754_binary_16_80 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 7 1 16 80 (ieee754-policy) x0:16)))

(defun fconvert_rtz_ieee754_binary_16_128 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 7 1 16 128 (ieee754-policy) x0:16)))

(defun cast_float_rtz_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 8 1 8 16 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtz_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 9 1 8 16 (ieee754-policy) x0:8)))

(defun cast_int_rtz_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 10 1 16 8 (ieee754-policy) x0:16)))

(defun cast_sint_rtz_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 11 1 16 8 (ieee754-policy) x0:16)))

(defun cast_float_rtz_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 8 1 16 16 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtz_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 9 1 16 16 (ieee754-policy) x0:16)))

(defun cast_int_rtz_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 10 1 16 16 (ieee754-policy) x0:16)))

(defun cast_sint_rtz_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 11 1 16 16 (ieee754-policy) x0:16)))

(defun cast_float_rtz_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 8 1 32 16 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtz_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 9 1 32 16 (ieee754-policy) x0:32)))

(defun cast_int_rtz_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 10 1 16 32 (ieee754-policy) x0:16)))

(defun cast_sint_rtz_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 11 1 16 32 (ieee754-policy) x0:16)))

(defun cast_float_rtz_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 8 1 64 16 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtz_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 9 1 64 16 (ieee754-policy) x0:64)))

(defun cast_int_rtz_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 10 1 16 64 (ieee754-policy) x0:16)))

(defun cast_sint_rtz_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 11 1 16 64 (ieee754-policy) x0:16)))

(defun cast_float_rtz_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 8 1 128 16 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtz_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 9 1 128 16 (ieee754-policy) x0:128)))

(defun cast_int_rtz_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 10 1 16 128 (ieee754-policy) x0:16)))

(defun cast_sint_rtz_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 11 1 16 128 (ieee754-policy) x0:16)))

(defun fadd_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fadd_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 1 2 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fsub_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fsub_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 2 2 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmul_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fmul_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 3 2 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fdiv_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fdiv_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 4 2 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmad_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fmad_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 15 2 16 16 (ieee754-policy) x0:16 x1:16 x2:16)))

(defun fsqrt_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fsqrt_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 5 2 16 16 (ieee754-policy) x0:16)))

(defun fround_rtp_ieee754_binary_16 ()
  (declare (external "intrinsic:fround_rtp_ieee754_binary_16"))
  (set y0:16 (ieee754-op 6 2 16 16 (ieee754-policy) x0:16)))

(defun fconvert_rtp_ieee754_binary_16_32 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 7 2 16 32 (ieee754-policy) x0:16)))

(defun fconvert_rtp_ieee754_binary_16_64 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 7 2 16 64 (ieee754-policy) x0:16)))

(defun fconvert_rtp_ieee754_binary_16_80 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 7 2 16 80 (ieee754-policy) x0:16)))

(defun fconvert_rtp_ieee754_binary_16_128 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 7 2 16 128 (ieee754-policy) x0:16)))

(defun cast_float_rtp_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 8 2 8 16 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtp_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 9 2 8 16 (ieee754-policy) x0:8)))

(defun cast_int_rtp_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 10 2 16 8 (ieee754-policy) x0:16)))

(defun cast_sint_rtp_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 11 2 16 8 (ieee754-policy) x0:16)))

(defun cast_float_rtp_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 8 2 16 16 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtp_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 9 2 16 16 (ieee754-policy) x0:16)))

(defun cast_int_rtp_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 10 2 16 16 (ieee754-policy) x0:16)))

(defun cast_sint_rtp_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 11 2 16 16 (ieee754-policy) x0:16)))

(defun cast_float_rtp_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 8 2 32 16 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtp_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 9 2 32 16 (ieee754-policy) x0:32)))

(defun cast_int_rtp_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 10 2 16 32 (ieee754-policy) x0:16)))

(defun cast_sint_rtp_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 11 2 16 32 (ieee754-policy) x0:16)))

(defun cast_float_rtp_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 8 2 64 16 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtp_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 9 2 64 16 (ieee754-policy) x0:64)))

(defun cast_int_rtp_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 10 2 16 64 (ieee754-policy) x0:16)))

(defun cast_sint_rtp_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 11 2 16 64 (ieee754-policy) x0:16)))

(defun cast_float_rtp_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 8 2 128 16 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtp_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 9 2 128 16 (ieee754-policy) x0:128)))

(defun cast_int_rtp_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 10 2 16 128 (ieee754-policy) x0:16)))

(defun cast_sint_rtp_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 11 2 16 128 (ieee754-policy) x0:16)))

(defun fadd_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fadd_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 1 3 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fsub_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fsub_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 2 3 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmul_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fmul_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 3 3 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fdiv_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fdiv_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 4 3 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmad_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fmad_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 15 3 16 16 (ieee754-policy) x0:16 x1:16 x2:16)))

(defun fsqrt_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fsqrt_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 5 3 16 16 (ieee754-policy) x0:16)))

(defun fround_rtn_ieee754_binary_16 ()
  (declare (external "intrinsic:fround_rtn_ieee754_binary_16"))
  (set y0:16 (ieee754-op 6 3 16 16 (ieee754-policy) x0:16)))

(defun fconvert_rtn_ieee754_binary_16_32 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 7 3 16 32 (ieee754-policy) x0:16)))

(defun fconvert_rtn_ieee754_binary_16_64 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 7 3 16 64 (ieee754-policy) x0:16)))

(defun fconvert_rtn_ieee754_binary_16_80 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 7 3 16 80 (ieee754-policy) x0:16)))

(defun fconvert_rtn_ieee754_binary_16_128 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 7 3 16 128 (ieee754-policy) x0:16)))

(defun cast_float_rtn_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 8 3 8 16 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtn_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 9 3 8 16 (ieee754-policy) x0:8)))

(defun cast_int_rtn_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 10 3 16 8 (ieee754-policy) x0:16)))

(defun cast_sint_rtn_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 11 3 16 8 (ieee754-policy) x0:16)))

(defun cast_float_rtn_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 8 3 16 16 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtn_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 9 3 16 16 (ieee754-policy) x0:16)))

(defun cast_int_rtn_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 10 3 16 16 (ieee754-policy) x0:16)))

(defun cast_sint_rtn_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 11 3 16 16 (ieee754-policy) x0:16)))

(defun cast_float_rtn_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 8 3 32 16 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtn_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 9 3 32 16 (ieee754-policy) x0:32)))

(defun cast_int_rtn_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 10 3 16 32 (ieee754-policy) x0:16)))

(defun cast_sint_rtn_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 11 3 16 32 (ieee754-policy) x0:16)))

(defun cast_float_rtn_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 8 3 64 16 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtn_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 9 3 64 16 (ieee754-policy) x0:64)))

(defun cast_int_rtn_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 10 3 16 64 (ieee754-policy) x0:16)))

(defun cast_sint_rtn_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 11 3 16 64 (ieee754-policy) x0:16)))

(defun cast_float_rtn_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 8 3 128 16 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtn_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 9 3 128 16 (ieee754-policy) x0:128)))

(defun cast_int_rtn_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 10 3 16 128 (ieee754-policy) x0:16)))

(defun cast_sint_rtn_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 11 3 16 128 (ieee754-policy) x0:16)))

(defun fadd_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fadd_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 1 4 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fsub_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fsub_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 2 4 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmul_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fmul_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 3 4 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fdiv_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fdiv_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 4 4 16 16 (ieee754-policy) x0:16 x1:16)))

(defun fmad_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fmad_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 15 4 16 16 (ieee754-policy) x0:16 x1:16 x2:16)))

(defun fsqrt_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fsqrt_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 5 4 16 16 (ieee754-policy) x0:16)))

(defun fround_rna_ieee754_binary_16 ()
  (declare (external "intrinsic:fround_rna_ieee754_binary_16"))
  (set y0:16 (ieee754-op 6 4 16 16 (ieee754-policy) x0:16)))

(defun fconvert_rna_ieee754_binary_16_32 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 7 4 16 32 (ieee754-policy) x0:16)))

(defun fconvert_rna_ieee754_binary_16_64 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 7 4 16 64 (ieee754-policy) x0:16)))

(defun fconvert_rna_ieee754_binary_16_80 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 7 4 16 80 (ieee754-policy) x0:16)))

(defun fconvert_rna_ieee754_binary_16_128 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 7 4 16 128 (ieee754-policy) x0:16)))

(defun cast_float_rna_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 8 4 8 16 (ieee754-policy) x0:8)))

(defun cast_sfloat_rna_ieee754_binary_8_16 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_8_16"))
  (set y0:16 (ieee754-op 9 4 8 16 (ieee754-policy) x0:8)))

(defun cast_int_rna_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 10 4 16 8 (ieee754-policy) x0:16)))

(defun cast_sint_rna_ieee754_binary_16_8 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_16_8"))
  (set y0:8 (ieee754-op 11 4 16 8 (ieee754-policy) x0:16)))

(defun cast_float_rna_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 8 4 16 16 (ieee754-policy) x0:16)))

(defun cast_sfloat_rna_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 9 4 16 16 (ieee754-policy) x0:16)))

(defun cast_int_rna_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 10 4 16 16 (ieee754-policy) x0:16)))

(defun cast_sint_rna_ieee754_binary_16_16 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_16_16"))
  (set y0:16 (ieee754-op 11 4 16 16 (ieee754-policy) x0:16)))

(defun cast_float_rna_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 8 4 32 16 (ieee754-policy) x0:32)))

(defun cast_sfloat_rna_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 9 4 32 16 (ieee754-policy) x0:32)))

(defun cast_int_rna_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 10 4 16 32 (ieee754-policy) x0:16)))

(defun cast_sint_rna_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 11 4 16 32 (ieee754-policy) x0:16)))

(defun cast_float_rna_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 8 4 64 16 (ieee754-policy) x0:64)))

(defun cast_sfloat_rna_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 9 4 64 16 (ieee754-policy) x0:64)))

(defun cast_int_rna_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 10 4 16 64 (ieee754-policy) x0:16)))

(defun cast_sint_rna_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 11 4 16 64 (ieee754-policy) x0:16)))

(defun cast_float_rna_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 8 4 128 16 (ieee754-policy) x0:128)))

(defun cast_sfloat_rna_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 9 4 128 16 (ieee754-policy) x0:128)))

(defun cast_int_rna_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 10 4 16 128 (ieee754-policy) x0:16)))

(defun cast_sint_rna_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 11 4 16 128 (ieee754-policy) x0:16)))

(defun forder_ieee754_binary_16 ()
  (declare (external "intrinsic:forder_ieee754_binary_16"))
  (set y0:1 (ieee754-op 12 0 16 1 (ieee754-policy) x0:16 x1:16)))

(defun is_nan_ieee754_binary_16 ()
  (declare (external "intrinsic:is_nan_ieee754_binary_16"))
  (set y0:1 (ieee754-op 13 0 16 1 (ieee754-policy) x0:16)))

(defun is_inf_ieee754_binary_16 ()
  (declare (external "intrinsic:is_inf_ieee754_binary_16"))
  (set y0:1 (ieee754-op 14 0 16 1 (ieee754-policy) x0:16)))

(defun fadd_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fadd_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 1 0 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fsub_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fsub_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 2 0 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmul_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fmul_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 3 0 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fdiv_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fdiv_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 4 0 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmad_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fmad_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 15 0 32 32 (ieee754-policy) x0:32 x1:32 x2:32)))

(defun fsqrt_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fsqrt_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 5 0 32 32 (ieee754-policy) x0:32)))

(defun fround_rne_ieee754_binary_32 ()
  (declare (external "intrinsic:fround_rne_ieee754_binary_32"))
  (set y0:32 (ieee754-op 6 0 32 32 (ieee754-policy) x0:32)))

(defun fconvert_rne_ieee754_binary_32_16 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 7 0 32 16 (ieee754-policy) x0:32)))

(defun fconvert_rne_ieee754_binary_32_64 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 7 0 32 64 (ieee754-policy) x0:32)))

(defun fconvert_rne_ieee754_binary_32_80 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 7 0 32 80 (ieee754-policy) x0:32)))

(defun fconvert_rne_ieee754_binary_32_128 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 7 0 32 128 (ieee754-policy) x0:32)))

(defun cast_float_rne_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 8 0 8 32 (ieee754-policy) x0:8)))

(defun cast_sfloat_rne_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 9 0 8 32 (ieee754-policy) x0:8)))

(defun cast_int_rne_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 10 0 32 8 (ieee754-policy) x0:32)))

(defun cast_sint_rne_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 11 0 32 8 (ieee754-policy) x0:32)))

(defun cast_float_rne_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 8 0 16 32 (ieee754-policy) x0:16)))

(defun cast_sfloat_rne_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 9 0 16 32 (ieee754-policy) x0:16)))

(defun cast_int_rne_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 10 0 32 16 (ieee754-policy) x0:32)))

(defun cast_sint_rne_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 11 0 32 16 (ieee754-policy) x0:32)))

(defun cast_float_rne_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 8 0 32 32 (ieee754-policy) x0:32)))

(defun cast_sfloat_rne_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 9 0 32 32 (ieee754-policy) x0:32)))

(defun cast_int_rne_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 10 0 32 32 (ieee754-policy) x0:32)))

(defun cast_sint_rne_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 11 0 32 32 (ieee754-policy) x0:32)))

(defun cast_float_rne_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 8 0 64 32 (ieee754-policy) x0:64)))

(defun cast_sfloat_rne_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 9 0 64 32 (ieee754-policy) x0:64)))

(defun cast_int_rne_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 10 0 32 64 (ieee754-policy) x0:32)))

(defun cast_sint_rne_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 11 0 32 64 (ieee754-policy) x0:32)))

(defun cast_float_rne_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 8 0 128 32 (ieee754-policy) x0:128)))

(defun cast_sfloat_rne_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 9 0 128 32 (ieee754-policy) x0:128)))

(defun cast_int_rne_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 10 0 32 128 (ieee754-policy) x0:32)))

(defun cast_sint_rne_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 11 0 32 128 (ieee754-policy) x0:32)))

(defun fadd_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fadd_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 1 1 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fsub_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fsub_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 2 1 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmul_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fmul_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 3 1 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fdiv_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fdiv_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 4 1 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmad_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fmad_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 15 1 32 32 (ieee754-policy) x0:32 x1:32 x2:32)))

(defun fsqrt_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fsqrt_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 5 1 32 32 (ieee754-policy) x0:32)))

(defun fround_rtz_ieee754_binary_32 ()
  (declare (external "intrinsic:fround_rtz_ieee754_binary_32"))
  (set y0:32 (ieee754-op 6 1 32 32 (ieee754-policy) x0:32)))

(defun fconvert_rtz_ieee754_binary_32_16 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 7 1 32 16 (ieee754-policy) x0:32)))

(defun fconvert_rtz_ieee754_binary_32_64 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 7 1 32 64 (ieee754-policy) x0:32)))

(defun fconvert_rtz_ieee754_binary_32_80 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 7 1 32 80 (ieee754-policy) x0:32)))

(defun fconvert_rtz_ieee754_binary_32_128 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 7 1 32 128 (ieee754-policy) x0:32)))

(defun cast_float_rtz_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 8 1 8 32 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtz_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 9 1 8 32 (ieee754-policy) x0:8)))

(defun cast_int_rtz_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 10 1 32 8 (ieee754-policy) x0:32)))

(defun cast_sint_rtz_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 11 1 32 8 (ieee754-policy) x0:32)))

(defun cast_float_rtz_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 8 1 16 32 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtz_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 9 1 16 32 (ieee754-policy) x0:16)))

(defun cast_int_rtz_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 10 1 32 16 (ieee754-policy) x0:32)))

(defun cast_sint_rtz_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 11 1 32 16 (ieee754-policy) x0:32)))

(defun cast_float_rtz_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 8 1 32 32 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtz_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 9 1 32 32 (ieee754-policy) x0:32)))

(defun cast_int_rtz_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 10 1 32 32 (ieee754-policy) x0:32)))

(defun cast_sint_rtz_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 11 1 32 32 (ieee754-policy) x0:32)))

(defun cast_float_rtz_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 8 1 64 32 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtz_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 9 1 64 32 (ieee754-policy) x0:64)))

(defun cast_int_rtz_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 10 1 32 64 (ieee754-policy) x0:32)))

(defun cast_sint_rtz_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 11 1 32 64 (ieee754-policy) x0:32)))

(defun cast_float_rtz_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 8 1 128 32 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtz_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 9 1 128 32 (ieee754-policy) x0:128)))

(defun cast_int_rtz_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 10 1 32 128 (ieee754-policy) x0:32)))

(defun cast_sint_rtz_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 11 1 32 128 (ieee754-policy) x0:32)))

(defun fadd_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fadd_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 1 2 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fsub_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fsub_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 2 2 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmul_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fmul_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 3 2 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fdiv_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fdiv_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 4 2 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmad_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fmad_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 15 2 32 32 (ieee754-policy) x0:32 x1:32 x2:32)))

(defun fsqrt_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fsqrt_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 5 2 32 32 (ieee754-policy) x0:32)))

(defun fround_rtp_ieee754_binary_32 ()
  (declare (external "intrinsic:fround_rtp_ieee754_binary_32"))
  (set y0:32 (ieee754-op 6 2 32 32 (ieee754-policy) x0:32)))

(defun fconvert_rtp_ieee754_binary_32_16 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 7 2 32 16 (ieee754-policy) x0:32)))

(defun fconvert_rtp_ieee754_binary_32_64 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 7 2 32 64 (ieee754-policy) x0:32)))

(defun fconvert_rtp_ieee754_binary_32_80 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 7 2 32 80 (ieee754-policy) x0:32)))

(defun fconvert_rtp_ieee754_binary_32_128 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 7 2 32 128 (ieee754-policy) x0:32)))

(defun cast_float_rtp_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 8 2 8 32 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtp_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 9 2 8 32 (ieee754-policy) x0:8)))

(defun cast_int_rtp_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 10 2 32 8 (ieee754-policy) x0:32)))

(defun cast_sint_rtp_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 11 2 32 8 (ieee754-policy) x0:32)))

(defun cast_float_rtp_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 8 2 16 32 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtp_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 9 2 16 32 (ieee754-policy) x0:16)))

(defun cast_int_rtp_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 10 2 32 16 (ieee754-policy) x0:32)))

(defun cast_sint_rtp_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 11 2 32 16 (ieee754-policy) x0:32)))

(defun cast_float_rtp_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 8 2 32 32 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtp_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 9 2 32 32 (ieee754-policy) x0:32)))

(defun cast_int_rtp_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 10 2 32 32 (ieee754-policy) x0:32)))

(defun cast_sint_rtp_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 11 2 32 32 (ieee754-policy) x0:32)))

(defun cast_float_rtp_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 8 2 64 32 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtp_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 9 2 64 32 (ieee754-policy) x0:64)))

(defun cast_int_rtp_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 10 2 32 64 (ieee754-policy) x0:32)))

(defun cast_sint_rtp_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 11 2 32 64 (ieee754-policy) x0:32)))

(defun cast_float_rtp_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 8 2 128 32 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtp_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 9 2 128 32 (ieee754-policy) x0:128)))

(defun cast_int_rtp_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 10 2 32 128 (ieee754-policy) x0:32)))

(defun cast_sint_rtp_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 11 2 32 128 (ieee754-policy) x0:32)))

(defun fadd_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fadd_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 1 3 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fsub_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fsub_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 2 3 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmul_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fmul_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 3 3 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fdiv_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fdiv_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 4 3 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmad_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fmad_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 15 3 32 32 (ieee754-policy) x0:32 x1:32 x2:32)))

(defun fsqrt_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fsqrt_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 5 3 32 32 (ieee754-policy) x0:32)))

(defun fround_rtn_ieee754_binary_32 ()
  (declare (external "intrinsic:fround_rtn_ieee754_binary_32"))
  (set y0:32 (ieee754-op 6 3 32 32 (ieee754-policy) x0:32)))

(defun fconvert_rtn_ieee754_binary_32_16 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 7 3 32 16 (ieee754-policy) x0:32)))

(defun fconvert_rtn_ieee754_binary_32_64 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 7 3 32 64 (ieee754-policy) x0:32)))

(defun fconvert_rtn_ieee754_binary_32_80 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 7 3 32 80 (ieee754-policy) x0:32)))

(defun fconvert_rtn_ieee754_binary_32_128 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 7 3 32 128 (ieee754-policy) x0:32)))

(defun cast_float_rtn_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 8 3 8 32 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtn_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 9 3 8 32 (ieee754-policy) x0:8)))

(defun cast_int_rtn_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 10 3 32 8 (ieee754-policy) x0:32)))

(defun cast_sint_rtn_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 11 3 32 8 (ieee754-policy) x0:32)))

(defun cast_float_rtn_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 8 3 16 32 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtn_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 9 3 16 32 (ieee754-policy) x0:16)))

(defun cast_int_rtn_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 10 3 32 16 (ieee754-policy) x0:32)))

(defun cast_sint_rtn_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 11 3 32 16 (ieee754-policy) x0:32)))

(defun cast_float_rtn_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 8 3 32 32 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtn_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 9 3 32 32 (ieee754-policy) x0:32)))

(defun cast_int_rtn_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 10 3 32 32 (ieee754-policy) x0:32)))

(defun cast_sint_rtn_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 11 3 32 32 (ieee754-policy) x0:32)))

(defun cast_float_rtn_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 8 3 64 32 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtn_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 9 3 64 32 (ieee754-policy) x0:64)))

(defun cast_int_rtn_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 10 3 32 64 (ieee754-policy) x0:32)))

(defun cast_sint_rtn_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 11 3 32 64 (ieee754-policy) x0:32)))

(defun cast_float_rtn_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 8 3 128 32 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtn_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 9 3 128 32 (ieee754-policy) x0:128)))

(defun cast_int_rtn_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 10 3 32 128 (ieee754-policy) x0:32)))

(defun cast_sint_rtn_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 11 3 32 128 (ieee754-policy) x0:32)))

(defun fadd_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fadd_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 1 4 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fsub_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fsub_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 2 4 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmul_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fmul_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 3 4 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fdiv_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fdiv_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 4 4 32 32 (ieee754-policy) x0:32 x1:32)))

(defun fmad_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fmad_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 15 4 32 32 (ieee754-policy) x0:32 x1:32 x2:32)))

(defun fsqrt_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fsqrt_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 5 4 32 32 (ieee754-policy) x0:32)))

(defun fround_rna_ieee754_binary_32 ()
  (declare (external "intrinsic:fround_rna_ieee754_binary_32"))
  (set y0:32 (ieee754-op 6 4 32 32 (ieee754-policy) x0:32)))

(defun fconvert_rna_ieee754_binary_32_16 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 7 4 32 16 (ieee754-policy) x0:32)))

(defun fconvert_rna_ieee754_binary_32_64 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 7 4 32 64 (ieee754-policy) x0:32)))

(defun fconvert_rna_ieee754_binary_32_80 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 7 4 32 80 (ieee754-policy) x0:32)))

(defun fconvert_rna_ieee754_binary_32_128 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 7 4 32 128 (ieee754-policy) x0:32)))

(defun cast_float_rna_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 8 4 8 32 (ieee754-policy) x0:8)))

(defun cast_sfloat_rna_ieee754_binary_8_32 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_8_32"))
  (set y0:32 (ieee754-op 9 4 8 32 (ieee754-policy) x0:8)))

(defun cast_int_rna_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 10 4 32 8 (ieee754-policy) x0:32)))

(defun cast_sint_rna_ieee754_binary_32_8 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_32_8"))
  (set y0:8 (ieee754-op 11 4 32 8 (ieee754-policy) x0:32)))

(defun cast_float_rna_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 8 4 16 32 (ieee754-policy) x0:16)))

(defun cast_sfloat_rna_ieee754_binary_16_32 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_16_32"))
  (set y0:32 (ieee754-op 9 4 16 32 (ieee754-policy) x0:16)))

(defun cast_int_rna_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 10 4 32 16 (ieee754-policy) x0:32)))

(defun cast_sint_rna_ieee754_binary_32_16 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_32_16"))
  (set y0:16 (ieee754-op 11 4 32 16 (ieee754-policy) x0:32)))

(defun cast_float_rna_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 8 4 32 32 (ieee754-policy) x0:32)))

(defun cast_sfloat_rna_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 9 4 32 32 (ieee754-policy) x0:32)))

(defun cast_int_rna_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 10 4 32 32 (ieee754-policy) x0:32)))

(defun cast_sint_rna_ieee754_binary_32_32 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_32_32"))
  (set y0:32 (ieee754-op 11 4 32 32 (ieee754-policy) x0:32)))

(defun cast_float_rna_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 8 4 64 32 (ieee754-policy) x0:64)))

(defun cast_sfloat_rna_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 9 4 64 32 (ieee754-policy) x0:64)))

(defun cast_int_rna_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 10 4 32 64 (ieee754-policy) x0:32)))

(defun cast_sint_rna_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 11 4 32 64 (ieee754-policy) x0:32)))

(defun cast_float_rna_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 8 4 128 32 (ieee754-policy) x0:128)))

(defun cast_sfloat_rna_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 9 4 128 32 (ieee754-policy) x0:128)))

(defun cast_int_rna_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 10 4 32 128 (ieee754-policy) x0:32)))

(defun cast_sint_rna_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 11 4 32 128 (ieee754-policy) x0:32)))

(defun forder_ieee754_binary_32 ()
  (declare (external "intrinsic:forder_ieee754_binary_32"))
  (set y0:1 (ieee754-op 12 0 32 1 (ieee754-policy) x0:32 x1:32)))

(defun is_nan_ieee754_binary_32 ()
  (declare (external "intrinsic:is_nan_ieee754_binary_32"))
  (set y0:1 (ieee754-op 13 0 32 1 (ieee754-policy) x0:32)))

(defun is_inf_ieee754_binary_32 ()
  (declare (external "intrinsic:is_inf_ieee754_binary_32"))
  (set y0:1 (ieee754-op 14 0 32 1 (ieee754-policy) x0:32)))

(defun fadd_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fadd_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 1 0 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fsub_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fsub_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 2 0 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmul_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fmul_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 3 0 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fdiv_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fdiv_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 4 0 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmad_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fmad_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 15 0 64 64 (ieee754-policy) x0:64 x1:64 x2:64)))

(defun fsqrt_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fsqrt_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 5 0 64 64 (ieee754-policy) x0:64)))

(defun fround_rne_ieee754_binary_64 ()
  (declare (external "intrinsic:fround_rne_ieee754_binary_64"))
  (set y0:64 (ieee754-op 6 0 64 64 (ieee754-policy) x0:64)))

(defun fconvert_rne_ieee754_binary_64_16 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 7 0 64 16 (ieee754-policy) x0:64)))

(defun fconvert_rne_ieee754_binary_64_32 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 7 0 64 32 (ieee754-policy) x0:64)))

(defun fconvert_rne_ieee754_binary_64_80 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 7 0 64 80 (ieee754-policy) x0:64)))

(defun fconvert_rne_ieee754_binary_64_128 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 7 0 64 128 (ieee754-policy) x0:64)))

(defun cast_float_rne_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 8 0 8 64 (ieee754-policy) x0:8)))

(defun cast_sfloat_rne_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 9 0 8 64 (ieee754-policy) x0:8)))

(defun cast_int_rne_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 10 0 64 8 (ieee754-policy) x0:64)))

(defun cast_sint_rne_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 11 0 64 8 (ieee754-policy) x0:64)))

(defun cast_float_rne_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 8 0 16 64 (ieee754-policy) x0:16)))

(defun cast_sfloat_rne_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 9 0 16 64 (ieee754-policy) x0:16)))

(defun cast_int_rne_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 10 0 64 16 (ieee754-policy) x0:64)))

(defun cast_sint_rne_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 11 0 64 16 (ieee754-policy) x0:64)))

(defun cast_float_rne_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 8 0 32 64 (ieee754-policy) x0:32)))

(defun cast_sfloat_rne_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 9 0 32 64 (ieee754-policy) x0:32)))

(defun cast_int_rne_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 10 0 64 32 (ieee754-policy) x0:64)))

(defun cast_sint_rne_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 11 0 64 32 (ieee754-policy) x0:64)))

(defun cast_float_rne_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 8 0 64 64 (ieee754-policy) x0:64)))

(defun cast_sfloat_rne_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 9 0 64 64 (ieee754-policy) x0:64)))

(defun cast_int_rne_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 10 0 64 64 (ieee754-policy) x0:64)))

(defun cast_sint_rne_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 11 0 64 64 (ieee754-policy) x0:64)))

(defun cast_float_rne_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 8 0 128 64 (ieee754-policy) x0:128)))

(defun cast_sfloat_rne_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 9 0 128 64 (ieee754-policy) x0:128)))

(defun cast_int_rne_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 10 0 64 128 (ieee754-policy) x0:64)))

(defun cast_sint_rne_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 11 0 64 128 (ieee754-policy) x0:64)))

(defun fadd_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fadd_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 1 1 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fsub_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fsub_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 2 1 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmul_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fmul_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 3 1 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fdiv_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fdiv_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 4 1 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmad_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fmad_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 15 1 64 64 (ieee754-policy) x0:64 x1:64 x2:64)))

(defun fsqrt_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fsqrt_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 5 1 64 64 (ieee754-policy) x0:64)))

(defun fround_rtz_ieee754_binary_64 ()
  (declare (external "intrinsic:fround_rtz_ieee754_binary_64"))
  (set y0:64 (ieee754-op 6 1 64 64 (ieee754-policy) x0:64)))

(defun fconvert_rtz_ieee754_binary_64_16 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 7 1 64 16 (ieee754-policy) x0:64)))

(defun fconvert_rtz_ieee754_binary_64_32 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 7 1 64 32 (ieee754-policy) x0:64)))

(defun fconvert_rtz_ieee754_binary_64_80 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 7 1 64 80 (ieee754-policy) x0:64)))

(defun fconvert_rtz_ieee754_binary_64_128 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 7 1 64 128 (ieee754-policy) x0:64)))

(defun cast_float_rtz_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 8 1 8 64 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtz_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 9 1 8 64 (ieee754-policy) x0:8)))

(defun cast_int_rtz_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 10 1 64 8 (ieee754-policy) x0:64)))

(defun cast_sint_rtz_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 11 1 64 8 (ieee754-policy) x0:64)))

(defun cast_float_rtz_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 8 1 16 64 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtz_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 9 1 16 64 (ieee754-policy) x0:16)))

(defun cast_int_rtz_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 10 1 64 16 (ieee754-policy) x0:64)))

(defun cast_sint_rtz_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 11 1 64 16 (ieee754-policy) x0:64)))

(defun cast_float_rtz_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 8 1 32 64 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtz_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 9 1 32 64 (ieee754-policy) x0:32)))

(defun cast_int_rtz_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 10 1 64 32 (ieee754-policy) x0:64)))

(defun cast_sint_rtz_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 11 1 64 32 (ieee754-policy) x0:64)))

(defun cast_float_rtz_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 8 1 64 64 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtz_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 9 1 64 64 (ieee754-policy) x0:64)))

(defun cast_int_rtz_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 10 1 64 64 (ieee754-policy) x0:64)))

(defun cast_sint_rtz_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 11 1 64 64 (ieee754-policy) x0:64)))

(defun cast_float_rtz_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 8 1 128 64 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtz_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 9 1 128 64 (ieee754-policy) x0:128)))

(defun cast_int_rtz_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 10 1 64 128 (ieee754-policy) x0:64)))

(defun cast_sint_rtz_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 11 1 64 128 (ieee754-policy) x0:64)))

(defun fadd_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fadd_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 1 2 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fsub_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fsub_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 2 2 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmul_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fmul_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 3 2 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fdiv_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fdiv_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 4 2 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmad_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fmad_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 15 2 64 64 (ieee754-policy) x0:64 x1:64 x2:64)))

(defun fsqrt_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fsqrt_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 5 2 64 64 (ieee754-policy) x0:64)))

(defun fround_rtp_ieee754_binary_64 ()
  (declare (external "intrinsic:fround_rtp_ieee754_binary_64"))
  (set y0:64 (ieee754-op 6 2 64 64 (ieee754-policy) x0:64)))

(defun fconvert_rtp_ieee754_binary_64_16 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 7 2 64 16 (ieee754-policy) x0:64)))

(defun fconvert_rtp_ieee754_binary_64_32 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 7 2 64 32 (ieee754-policy) x0:64)))

(defun fconvert_rtp_ieee754_binary_64_80 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 7 2 64 80 (ieee754-policy) x0:64)))

(defun fconvert_rtp_ieee754_binary_64_128 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 7 2 64 128 (ieee754-policy) x0:64)))

(defun cast_float_rtp_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 8 2 8 64 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtp_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 9 2 8 64 (ieee754-policy) x0:8)))

(defun cast_int_rtp_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 10 2 64 8 (ieee754-policy) x0:64)))

(defun cast_sint_rtp_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 11 2 64 8 (ieee754-policy) x0:64)))

(defun cast_float_rtp_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 8 2 16 64 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtp_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 9 2 16 64 (ieee754-policy) x0:16)))

(defun cast_int_rtp_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 10 2 64 16 (ieee754-policy) x0:64)))

(defun cast_sint_rtp_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 11 2 64 16 (ieee754-policy) x0:64)))

(defun cast_float_rtp_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 8 2 32 64 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtp_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 9 2 32 64 (ieee754-policy) x0:32)))

(defun cast_int_rtp_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 10 2 64 32 (ieee754-policy) x0:64)))

(defun cast_sint_rtp_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 11 2 64 32 (ieee754-policy) x0:64)))

(defun cast_float_rtp_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 8 2 64 64 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtp_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 9 2 64 64 (ieee754-policy) x0:64)))

(defun cast_int_rtp_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 10 2 64 64 (ieee754-policy) x0:64)))

(defun cast_sint_rtp_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 11 2 64 64 (ieee754-policy) x0:64)))

(defun cast_float_rtp_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 8 2 128 64 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtp_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 9 2 128 64 (ieee754-policy) x0:128)))

(defun cast_int_rtp_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 10 2 64 128 (ieee754-policy) x0:64)))

(defun cast_sint_rtp_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 11 2 64 128 (ieee754-policy) x0:64)))

(defun fadd_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fadd_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 1 3 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fsub_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fsub_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 2 3 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmul_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fmul_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 3 3 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fdiv_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fdiv_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 4 3 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmad_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fmad_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 15 3 64 64 (ieee754-policy) x0:64 x1:64 x2:64)))

(defun fsqrt_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fsqrt_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 5 3 64 64 (ieee754-policy) x0:64)))

(defun fround_rtn_ieee754_binary_64 ()
  (declare (external "intrinsic:fround_rtn_ieee754_binary_64"))
  (set y0:64 (ieee754-op 6 3 64 64 (ieee754-policy) x0:64)))

(defun fconvert_rtn_ieee754_binary_64_16 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 7 3 64 16 (ieee754-policy) x0:64)))

(defun fconvert_rtn_ieee754_binary_64_32 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 7 3 64 32 (ieee754-policy) x0:64)))

(defun fconvert_rtn_ieee754_binary_64_80 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 7 3 64 80 (ieee754-policy) x0:64)))

(defun fconvert_rtn_ieee754_binary_64_128 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 7 3 64 128 (ieee754-policy) x0:64)))

(defun cast_float_rtn_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 8 3 8 64 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtn_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 9 3 8 64 (ieee754-policy) x0:8)))

(defun cast_int_rtn_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 10 3 64 8 (ieee754-policy) x0:64)))

(defun cast_sint_rtn_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 11 3 64 8 (ieee754-policy) x0:64)))

(defun cast_float_rtn_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 8 3 16 64 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtn_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 9 3 16 64 (ieee754-policy) x0:16)))

(defun cast_int_rtn_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 10 3 64 16 (ieee754-policy) x0:64)))

(defun cast_sint_rtn_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 11 3 64 16 (ieee754-policy) x0:64)))

(defun cast_float_rtn_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 8 3 32 64 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtn_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 9 3 32 64 (ieee754-policy) x0:32)))

(defun cast_int_rtn_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 10 3 64 32 (ieee754-policy) x0:64)))

(defun cast_sint_rtn_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 11 3 64 32 (ieee754-policy) x0:64)))

(defun cast_float_rtn_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 8 3 64 64 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtn_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 9 3 64 64 (ieee754-policy) x0:64)))

(defun cast_int_rtn_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 10 3 64 64 (ieee754-policy) x0:64)))

(defun cast_sint_rtn_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 11 3 64 64 (ieee754-policy) x0:64)))

(defun cast_float_rtn_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 8 3 128 64 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtn_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 9 3 128 64 (ieee754-policy) x0:128)))

(defun cast_int_rtn_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 10 3 64 128 (ieee754-policy) x0:64)))

(defun cast_sint_rtn_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 11 3 64 128 (ieee754-policy) x0:64)))

(defun fadd_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fadd_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 1 4 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fsub_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fsub_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 2 4 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmul_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fmul_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 3 4 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fdiv_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fdiv_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 4 4 64 64 (ieee754-policy) x0:64 x1:64)))

(defun fmad_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fmad_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 15 4 64 64 (ieee754-policy) x0:64 x1:64 x2:64)))

(defun fsqrt_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fsqrt_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 5 4 64 64 (ieee754-policy) x0:64)))

(defun fround_rna_ieee754_binary_64 ()
  (declare (external "intrinsic:fround_rna_ieee754_binary_64"))
  (set y0:64 (ieee754-op 6 4 64 64 (ieee754-policy) x0:64)))

(defun fconvert_rna_ieee754_binary_64_16 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 7 4 64 16 (ieee754-policy) x0:64)))

(defun fconvert_rna_ieee754_binary_64_32 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 7 4 64 32 (ieee754-policy) x0:64)))

(defun fconvert_rna_ieee754_binary_64_80 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 7 4 64 80 (ieee754-policy) x0:64)))

(defun fconvert_rna_ieee754_binary_64_128 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 7 4 64 128 (ieee754-policy) x0:64)))

(defun cast_float_rna_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 8 4 8 64 (ieee754-policy) x0:8)))

(defun cast_sfloat_rna_ieee754_binary_8_64 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_8_64"))
  (set y0:64 (ieee754-op 9 4 8 64 (ieee754-policy) x0:8)))

(defun cast_int_rna_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 10 4 64 8 (ieee754-policy) x0:64)))

(defun cast_sint_rna_ieee754_binary_64_8 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_64_8"))
  (set y0:8 (ieee754-op 11 4 64 8 (ieee754-policy) x0:64)))

(defun cast_float_rna_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 8 4 16 64 (ieee754-policy) x0:16)))

(defun cast_sfloat_rna_ieee754_binary_16_64 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_16_64"))
  (set y0:64 (ieee754-op 9 4 16 64 (ieee754-policy) x0:16)))

(defun cast_int_rna_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 10 4 64 16 (ieee754-policy) x0:64)))

(defun cast_sint_rna_ieee754_binary_64_16 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_64_16"))
  (set y0:16 (ieee754-op 11 4 64 16 (ieee754-policy) x0:64)))

(defun cast_float_rna_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 8 4 32 64 (ieee754-policy) x0:32)))

(defun cast_sfloat_rna_ieee754_binary_32_64 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_32_64"))
  (set y0:64 (ieee754-op 9 4 32 64 (ieee754-policy) x0:32)))

(defun cast_int_rna_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 10 4 64 32 (ieee754-policy) x0:64)))

(defun cast_sint_rna_ieee754_binary_64_32 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_64_32"))
  (set y0:32 (ieee754-op 11 4 64 32 (ieee754-policy) x0:64)))

(defun cast_float_rna_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 8 4 64 64 (ieee754-policy) x0:64)))

(defun cast_sfloat_rna_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 9 4 64 64 (ieee754-policy) x0:64)))

(defun cast_int_rna_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 10 4 64 64 (ieee754-policy) x0:64)))

(defun cast_sint_rna_ieee754_binary_64_64 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_64_64"))
  (set y0:64 (ieee754-op 11 4 64 64 (ieee754-policy) x0:64)))

(defun cast_float_rna_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 8 4 128 64 (ieee754-policy) x0:128)))

(defun cast_sfloat_rna_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 9 4 128 64 (ieee754-policy) x0:128)))

(defun cast_int_rna_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 10 4 64 128 (ieee754-policy) x0:64)))

(defun cast_sint_rna_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 11 4 64 128 (ieee754-policy) x0:64)))

(defun forder_ieee754_binary_64 ()
  (declare (external "intrinsic:forder_ieee754_binary_64"))
  (set y0:1 (ieee754-op 12 0 64 1 (ieee754-policy) x0:64 x1:64)))

(defun is_nan_ieee754_binary_64 ()
  (declare (external "intrinsic:is_nan_ieee754_binary_64"))
  (set y0:1 (ieee754-op 13 0 64 1 (ieee754-policy) x0:64)))

(defun is_inf_ieee754_binary_64 ()
  (declare (external "intrinsic:is_inf_ieee754_binary_64"))
  (set y0:1 (ieee754-op 14 0 64 1 (ieee754-policy) x0:64)))

(defun fadd_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fadd_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 1 0 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fsub_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fsub_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 2 0 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmul_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fmul_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 3 0 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fdiv_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fdiv_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 4 0 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmad_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fmad_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 15 0 80 80 (ieee754-policy) x0:80 x1:80 x2:80)))

(defun fsqrt_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fsqrt_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 5 0 80 80 (ieee754-policy) x0:80)))

(defun fround_rne_ieee754_binary_80 ()
  (declare (external "intrinsic:fround_rne_ieee754_binary_80"))
  (set y0:80 (ieee754-op 6 0 80 80 (ieee754-policy) x0:80)))

(defun fconvert_rne_ieee754_binary_80_16 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 7 0 80 16 (ieee754-policy) x0:80)))

(defun fconvert_rne_ieee754_binary_80_32 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 7 0 80 32 (ieee754-policy) x0:80)))

(defun fconvert_rne_ieee754_binary_80_64 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 7 0 80 64 (ieee754-policy) x0:80)))

(defun fconvert_rne_ieee754_binary_80_128 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 7 0 80 128 (ieee754-policy) x0:80)))

(defun cast_float_rne_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 8 0 8 80 (ieee754-policy) x0:8)))

(defun cast_sfloat_rne_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 9 0 8 80 (ieee754-policy) x0:8)))

(defun cast_int_rne_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 10 0 80 8 (ieee754-policy) x0:80)))

(defun cast_sint_rne_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 11 0 80 8 (ieee754-policy) x0:80)))

(defun cast_float_rne_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 8 0 16 80 (ieee754-policy) x0:16)))

(defun cast_sfloat_rne_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 9 0 16 80 (ieee754-policy) x0:16)))

(defun cast_int_rne_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 10 0 80 16 (ieee754-policy) x0:80)))

(defun cast_sint_rne_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 11 0 80 16 (ieee754-policy) x0:80)))

(defun cast_float_rne_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 8 0 32 80 (ieee754-policy) x0:32)))

(defun cast_sfloat_rne_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 9 0 32 80 (ieee754-policy) x0:32)))

(defun cast_int_rne_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 10 0 80 32 (ieee754-policy) x0:80)))

(defun cast_sint_rne_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 11 0 80 32 (ieee754-policy) x0:80)))

(defun cast_float_rne_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 8 0 64 80 (ieee754-policy) x0:64)))

(defun cast_sfloat_rne_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 9 0 64 80 (ieee754-policy) x0:64)))

(defun cast_int_rne_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 10 0 80 64 (ieee754-policy) x0:80)))

(defun cast_sint_rne_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 11 0 80 64 (ieee754-policy) x0:80)))

(defun cast_float_rne_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 8 0 128 80 (ieee754-policy) x0:128)))

(defun cast_sfloat_rne_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 9 0 128 80 (ieee754-policy) x0:128)))

(defun cast_int_rne_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 10 0 80 128 (ieee754-policy) x0:80)))

(defun cast_sint_rne_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 11 0 80 128 (ieee754-policy) x0:80)))

(defun fadd_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fadd_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 1 1 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fsub_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fsub_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 2 1 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmul_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fmul_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 3 1 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fdiv_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fdiv_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 4 1 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmad_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fmad_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 15 1 80 80 (ieee754-policy) x0:80 x1:80 x2:80)))

(defun fsqrt_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fsqrt_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 5 1 80 80 (ieee754-policy) x0:80)))

(defun fround_rtz_ieee754_binary_80 ()
  (declare (external "intrinsic:fround_rtz_ieee754_binary_80"))
  (set y0:80 (ieee754-op 6 1 80 80 (ieee754-policy) x0:80)))

(defun fconvert_rtz_ieee754_binary_80_16 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 7 1 80 16 (ieee754-policy) x0:80)))

(defun fconvert_rtz_ieee754_binary_80_32 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 7 1 80 32 (ieee754-policy) x0:80)))

(defun fconvert_rtz_ieee754_binary_80_64 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 7 1 80 64 (ieee754-policy) x0:80)))

(defun fconvert_rtz_ieee754_binary_80_128 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 7 1 80 128 (ieee754-policy) x0:80)))

(defun cast_float_rtz_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 8 1 8 80 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtz_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 9 1 8 80 (ieee754-policy) x0:8)))

(defun cast_int_rtz_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 10 1 80 8 (ieee754-policy) x0:80)))

(defun cast_sint_rtz_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 11 1 80 8 (ieee754-policy) x0:80)))

(defun cast_float_rtz_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 8 1 16 80 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtz_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 9 1 16 80 (ieee754-policy) x0:16)))

(defun cast_int_rtz_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 10 1 80 16 (ieee754-policy) x0:80)))

(defun cast_sint_rtz_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 11 1 80 16 (ieee754-policy) x0:80)))

(defun cast_float_rtz_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 8 1 32 80 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtz_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 9 1 32 80 (ieee754-policy) x0:32)))

(defun cast_int_rtz_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 10 1 80 32 (ieee754-policy) x0:80)))

(defun cast_sint_rtz_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 11 1 80 32 (ieee754-policy) x0:80)))

(defun cast_float_rtz_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 8 1 64 80 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtz_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 9 1 64 80 (ieee754-policy) x0:64)))

(defun cast_int_rtz_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 10 1 80 64 (ieee754-policy) x0:80)))

(defun cast_sint_rtz_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 11 1 80 64 (ieee754-policy) x0:80)))

(defun cast_float_rtz_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 8 1 128 80 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtz_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 9 1 128 80 (ieee754-policy) x0:128)))

(defun cast_int_rtz_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 10 1 80 128 (ieee754-policy) x0:80)))

(defun cast_sint_rtz_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 11 1 80 128 (ieee754-policy) x0:80)))

(defun fadd_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fadd_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 1 2 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fsub_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fsub_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 2 2 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmul_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fmul_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 3 2 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fdiv_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fdiv_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 4 2 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmad_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fmad_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 15 2 80 80 (ieee754-policy) x0:80 x1:80 x2:80)))

(defun fsqrt_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fsqrt_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 5 2 80 80 (ieee754-policy) x0:80)))

(defun fround_rtp_ieee754_binary_80 ()
  (declare (external "intrinsic:fround_rtp_ieee754_binary_80"))
  (set y0:80 (ieee754-op 6 2 80 80 (ieee754-policy) x0:80)))

(defun fconvert_rtp_ieee754_binary_80_16 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 7 2 80 16 (ieee754-policy) x0:80)))

(defun fconvert_rtp_ieee754_binary_80_32 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 7 2 80 32 (ieee754-policy) x0:80)))

(defun fconvert_rtp_ieee754_binary_80_64 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 7 2 80 64 (ieee754-policy) x0:80)))

(defun fconvert_rtp_ieee754_binary_80_128 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 7 2 80 128 (ieee754-policy) x0:80)))

(defun cast_float_rtp_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 8 2 8 80 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtp_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 9 2 8 80 (ieee754-policy) x0:8)))

(defun cast_int_rtp_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 10 2 80 8 (ieee754-policy) x0:80)))

(defun cast_sint_rtp_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 11 2 80 8 (ieee754-policy) x0:80)))

(defun cast_float_rtp_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 8 2 16 80 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtp_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 9 2 16 80 (ieee754-policy) x0:16)))

(defun cast_int_rtp_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 10 2 80 16 (ieee754-policy) x0:80)))

(defun cast_sint_rtp_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 11 2 80 16 (ieee754-policy) x0:80)))

(defun cast_float_rtp_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 8 2 32 80 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtp_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 9 2 32 80 (ieee754-policy) x0:32)))

(defun cast_int_rtp_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 10 2 80 32 (ieee754-policy) x0:80)))

(defun cast_sint_rtp_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 11 2 80 32 (ieee754-policy) x0:80)))

(defun cast_float_rtp_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 8 2 64 80 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtp_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 9 2 64 80 (ieee754-policy) x0:64)))

(defun cast_int_rtp_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 10 2 80 64 (ieee754-policy) x0:80)))

(defun cast_sint_rtp_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 11 2 80 64 (ieee754-policy) x0:80)))

(defun cast_float_rtp_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 8 2 128 80 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtp_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 9 2 128 80 (ieee754-policy) x0:128)))

(defun cast_int_rtp_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 10 2 80 128 (ieee754-policy) x0:80)))

(defun cast_sint_rtp_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 11 2 80 128 (ieee754-policy) x0:80)))

(defun fadd_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fadd_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 1 3 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fsub_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fsub_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 2 3 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmul_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fmul_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 3 3 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fdiv_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fdiv_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 4 3 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmad_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fmad_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 15 3 80 80 (ieee754-policy) x0:80 x1:80 x2:80)))

(defun fsqrt_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fsqrt_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 5 3 80 80 (ieee754-policy) x0:80)))

(defun fround_rtn_ieee754_binary_80 ()
  (declare (external "intrinsic:fround_rtn_ieee754_binary_80"))
  (set y0:80 (ieee754-op 6 3 80 80 (ieee754-policy) x0:80)))

(defun fconvert_rtn_ieee754_binary_80_16 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 7 3 80 16 (ieee754-policy) x0:80)))

(defun fconvert_rtn_ieee754_binary_80_32 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 7 3 80 32 (ieee754-policy) x0:80)))

(defun fconvert_rtn_ieee754_binary_80_64 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 7 3 80 64 (ieee754-policy) x0:80)))

(defun fconvert_rtn_ieee754_binary_80_128 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 7 3 80 128 (ieee754-policy) x0:80)))

(defun cast_float_rtn_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 8 3 8 80 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtn_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 9 3 8 80 (ieee754-policy) x0:8)))

(defun cast_int_rtn_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 10 3 80 8 (ieee754-policy) x0:80)))

(defun cast_sint_rtn_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 11 3 80 8 (ieee754-policy) x0:80)))

(defun cast_float_rtn_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 8 3 16 80 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtn_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 9 3 16 80 (ieee754-policy) x0:16)))

(defun cast_int_rtn_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 10 3 80 16 (ieee754-policy) x0:80)))

(defun cast_sint_rtn_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 11 3 80 16 (ieee754-policy) x0:80)))

(defun cast_float_rtn_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 8 3 32 80 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtn_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 9 3 32 80 (ieee754-policy) x0:32)))

(defun cast_int_rtn_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 10 3 80 32 (ieee754-policy) x0:80)))

(defun cast_sint_rtn_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 11 3 80 32 (ieee754-policy) x0:80)))

(defun cast_float_rtn_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 8 3 64 80 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtn_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 9 3 64 80 (ieee754-policy) x0:64)))

(defun cast_int_rtn_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 10 3 80 64 (ieee754-policy) x0:80)))

(defun cast_sint_rtn_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 11 3 80 64 (ieee754-policy) x0:80)))

(defun cast_float_rtn_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 8 3 128 80 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtn_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 9 3 128 80 (ieee754-policy) x0:128)))

(defun cast_int_rtn_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 10 3 80 128 (ieee754-policy) x0:80)))

(defun cast_sint_rtn_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 11 3 80 128 (ieee754-policy) x0:80)))

(defun fadd_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fadd_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 1 4 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fsub_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fsub_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 2 4 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmul_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fmul_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 3 4 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fdiv_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fdiv_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 4 4 80 80 (ieee754-policy) x0:80 x1:80)))

(defun fmad_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fmad_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 15 4 80 80 (ieee754-policy) x0:80 x1:80 x2:80)))

(defun fsqrt_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fsqrt_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 5 4 80 80 (ieee754-policy) x0:80)))

(defun fround_rna_ieee754_binary_80 ()
  (declare (external "intrinsic:fround_rna_ieee754_binary_80"))
  (set y0:80 (ieee754-op 6 4 80 80 (ieee754-policy) x0:80)))

(defun fconvert_rna_ieee754_binary_80_16 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 7 4 80 16 (ieee754-policy) x0:80)))

(defun fconvert_rna_ieee754_binary_80_32 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 7 4 80 32 (ieee754-policy) x0:80)))

(defun fconvert_rna_ieee754_binary_80_64 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 7 4 80 64 (ieee754-policy) x0:80)))

(defun fconvert_rna_ieee754_binary_80_128 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 7 4 80 128 (ieee754-policy) x0:80)))

(defun cast_float_rna_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 8 4 8 80 (ieee754-policy) x0:8)))

(defun cast_sfloat_rna_ieee754_binary_8_80 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_8_80"))
  (set y0:80 (ieee754-op 9 4 8 80 (ieee754-policy) x0:8)))

(defun cast_int_rna_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 10 4 80 8 (ieee754-policy) x0:80)))

(defun cast_sint_rna_ieee754_binary_80_8 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_80_8"))
  (set y0:8 (ieee754-op 11 4 80 8 (ieee754-policy) x0:80)))

(defun cast_float_rna_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 8 4 16 80 (ieee754-policy) x0:16)))

(defun cast_sfloat_rna_ieee754_binary_16_80 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_16_80"))
  (set y0:80 (ieee754-op 9 4 16 80 (ieee754-policy) x0:16)))

(defun cast_int_rna_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 10 4 80 16 (ieee754-policy) x0:80)))

(defun cast_sint_rna_ieee754_binary_80_16 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_80_16"))
  (set y0:16 (ieee754-op 11 4 80 16 (ieee754-policy) x0:80)))

(defun cast_float_rna_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 8 4 32 80 (ieee754-policy) x0:32)))

(defun cast_sfloat_rna_ieee754_binary_32_80 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_32_80"))
  (set y0:80 (ieee754-op 9 4 32 80 (ieee754-policy) x0:32)))

(defun cast_int_rna_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 10 4 80 32 (ieee754-policy) x0:80)))

(defun cast_sint_rna_ieee754_binary_80_32 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_80_32"))
  (set y0:32 (ieee754-op 11 4 80 32 (ieee754-policy) x0:80)))

(defun cast_float_rna_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 8 4 64 80 (ieee754-policy) x0:64)))

(defun cast_sfloat_rna_ieee754_binary_64_80 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_64_80"))
  (set y0:80 (ieee754-op 9 4 64 80 (ieee754-policy) x0:64)))

(defun cast_int_rna_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 10 4 80 64 (ieee754-policy) x0:80)))

(defun cast_sint_rna_ieee754_binary_80_64 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_80_64"))
  (set y0:64 (ieee754-op 11 4 80 64 (ieee754-policy) x0:80)))

(defun cast_float_rna_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 8 4 128 80 (ieee754-policy) x0:128)))

(defun cast_sfloat_rna_ieee754_binary_128_80 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 9 4 128 80 (ieee754-policy) x0:128)))

(defun cast_int_rna_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 10 4 80 128 (ieee754-policy) x0:80)))

(defun cast_sint_rna_ieee754_binary_80_128 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_80_128"))
  (set y0:128 (ieee754-op 11 4 80 128 (ieee754-policy) x0:80)))

(defun forder_ieee754_binary_80 ()
  (declare (external "intrinsic:forder_ieee754_binary_80"))
  (set y0:1 (ieee754-op 12 0 80 1 (ieee754-policy) x0:80 x1:80)))

(defun is_nan_ieee754_binary_80 ()
  (declare (external "intrinsic:is_nan_ieee754_binary_80"))
  (set y0:1 (ieee754-op 13 0 80 1 (ieee754-policy) x0:80)))

(defun is_inf_ieee754_binary_80 ()
  (declare (external "intrinsic:is_inf_ieee754_binary_80"))
  (set y0:1 (ieee754-op 14 0 80 1 (ieee754-policy) x0:80)))

(defun fadd_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fadd_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 1 0 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fsub_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fsub_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 2 0 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmul_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fmul_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 3 0 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fdiv_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fdiv_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 4 0 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmad_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fmad_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 15 0 128 128 (ieee754-policy) x0:128 x1:128 x2:128)))

(defun fsqrt_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fsqrt_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 5 0 128 128 (ieee754-policy) x0:128)))

(defun fround_rne_ieee754_binary_128 ()
  (declare (external "intrinsic:fround_rne_ieee754_binary_128"))
  (set y0:128 (ieee754-op 6 0 128 128 (ieee754-policy) x0:128)))

(defun fconvert_rne_ieee754_binary_128_16 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 7 0 128 16 (ieee754-policy) x0:128)))

(defun fconvert_rne_ieee754_binary_128_32 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 7 0 128 32 (ieee754-policy) x0:128)))

(defun fconvert_rne_ieee754_binary_128_64 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 7 0 128 64 (ieee754-policy) x0:128)))

(defun fconvert_rne_ieee754_binary_128_80 ()
  (declare (external "intrinsic:fconvert_rne_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 7 0 128 80 (ieee754-policy) x0:128)))

(defun cast_float_rne_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 8 0 8 128 (ieee754-policy) x0:8)))

(defun cast_sfloat_rne_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 9 0 8 128 (ieee754-policy) x0:8)))

(defun cast_int_rne_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 10 0 128 8 (ieee754-policy) x0:128)))

(defun cast_sint_rne_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 11 0 128 8 (ieee754-policy) x0:128)))

(defun cast_float_rne_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 8 0 16 128 (ieee754-policy) x0:16)))

(defun cast_sfloat_rne_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 9 0 16 128 (ieee754-policy) x0:16)))

(defun cast_int_rne_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 10 0 128 16 (ieee754-policy) x0:128)))

(defun cast_sint_rne_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 11 0 128 16 (ieee754-policy) x0:128)))

(defun cast_float_rne_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 8 0 32 128 (ieee754-policy) x0:32)))

(defun cast_sfloat_rne_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 9 0 32 128 (ieee754-policy) x0:32)))

(defun cast_int_rne_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 10 0 128 32 (ieee754-policy) x0:128)))

(defun cast_sint_rne_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 11 0 128 32 (ieee754-policy) x0:128)))

(defun cast_float_rne_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 8 0 64 128 (ieee754-policy) x0:64)))

(defun cast_sfloat_rne_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 9 0 64 128 (ieee754-policy) x0:64)))

(defun cast_int_rne_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 10 0 128 64 (ieee754-policy) x0:128)))

(defun cast_sint_rne_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 11 0 128 64 (ieee754-policy) x0:128)))

(defun cast_float_rne_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_float_rne_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 8 0 128 128 (ieee754-policy) x0:128)))

(defun cast_sfloat_rne_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sfloat_rne_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 9 0 128 128 (ieee754-policy) x0:128)))

(defun cast_int_rne_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_int_rne_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 10 0 128 128 (ieee754-policy) x0:128)))

(defun cast_sint_rne_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sint_rne_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 11 0 128 128 (ieee754-policy) x0:128)))

(defun fadd_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fadd_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 1 1 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fsub_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fsub_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 2 1 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmul_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fmul_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 3 1 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fdiv_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fdiv_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 4 1 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmad_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fmad_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 15 1 128 128 (ieee754-policy) x0:128 x1:128 x2:128)))

(defun fsqrt_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fsqrt_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 5 1 128 128 (ieee754-policy) x0:128)))

(defun fround_rtz_ieee754_binary_128 ()
  (declare (external "intrinsic:fround_rtz_ieee754_binary_128"))
  (set y0:128 (ieee754-op 6 1 128 128 (ieee754-policy) x0:128)))

(defun fconvert_rtz_ieee754_binary_128_16 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 7 1 128 16 (ieee754-policy) x0:128)))

(defun fconvert_rtz_ieee754_binary_128_32 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 7 1 128 32 (ieee754-policy) x0:128)))

(defun fconvert_rtz_ieee754_binary_128_64 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 7 1 128 64 (ieee754-policy) x0:128)))

(defun fconvert_rtz_ieee754_binary_128_80 ()
  (declare (external "intrinsic:fconvert_rtz_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 7 1 128 80 (ieee754-policy) x0:128)))

(defun cast_float_rtz_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 8 1 8 128 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtz_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 9 1 8 128 (ieee754-policy) x0:8)))

(defun cast_int_rtz_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 10 1 128 8 (ieee754-policy) x0:128)))

(defun cast_sint_rtz_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 11 1 128 8 (ieee754-policy) x0:128)))

(defun cast_float_rtz_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 8 1 16 128 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtz_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 9 1 16 128 (ieee754-policy) x0:16)))

(defun cast_int_rtz_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 10 1 128 16 (ieee754-policy) x0:128)))

(defun cast_sint_rtz_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 11 1 128 16 (ieee754-policy) x0:128)))

(defun cast_float_rtz_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 8 1 32 128 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtz_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 9 1 32 128 (ieee754-policy) x0:32)))

(defun cast_int_rtz_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 10 1 128 32 (ieee754-policy) x0:128)))

(defun cast_sint_rtz_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 11 1 128 32 (ieee754-policy) x0:128)))

(defun cast_float_rtz_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 8 1 64 128 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtz_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 9 1 64 128 (ieee754-policy) x0:64)))

(defun cast_int_rtz_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 10 1 128 64 (ieee754-policy) x0:128)))

(defun cast_sint_rtz_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 11 1 128 64 (ieee754-policy) x0:128)))

(defun cast_float_rtz_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_float_rtz_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 8 1 128 128 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtz_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sfloat_rtz_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 9 1 128 128 (ieee754-policy) x0:128)))

(defun cast_int_rtz_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_int_rtz_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 10 1 128 128 (ieee754-policy) x0:128)))

(defun cast_sint_rtz_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sint_rtz_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 11 1 128 128 (ieee754-policy) x0:128)))

(defun fadd_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fadd_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 1 2 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fsub_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fsub_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 2 2 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmul_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fmul_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 3 2 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fdiv_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fdiv_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 4 2 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmad_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fmad_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 15 2 128 128 (ieee754-policy) x0:128 x1:128 x2:128)))

(defun fsqrt_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fsqrt_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 5 2 128 128 (ieee754-policy) x0:128)))

(defun fround_rtp_ieee754_binary_128 ()
  (declare (external "intrinsic:fround_rtp_ieee754_binary_128"))
  (set y0:128 (ieee754-op 6 2 128 128 (ieee754-policy) x0:128)))

(defun fconvert_rtp_ieee754_binary_128_16 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 7 2 128 16 (ieee754-policy) x0:128)))

(defun fconvert_rtp_ieee754_binary_128_32 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 7 2 128 32 (ieee754-policy) x0:128)))

(defun fconvert_rtp_ieee754_binary_128_64 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 7 2 128 64 (ieee754-policy) x0:128)))

(defun fconvert_rtp_ieee754_binary_128_80 ()
  (declare (external "intrinsic:fconvert_rtp_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 7 2 128 80 (ieee754-policy) x0:128)))

(defun cast_float_rtp_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 8 2 8 128 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtp_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 9 2 8 128 (ieee754-policy) x0:8)))

(defun cast_int_rtp_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 10 2 128 8 (ieee754-policy) x0:128)))

(defun cast_sint_rtp_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 11 2 128 8 (ieee754-policy) x0:128)))

(defun cast_float_rtp_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 8 2 16 128 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtp_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 9 2 16 128 (ieee754-policy) x0:16)))

(defun cast_int_rtp_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 10 2 128 16 (ieee754-policy) x0:128)))

(defun cast_sint_rtp_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 11 2 128 16 (ieee754-policy) x0:128)))

(defun cast_float_rtp_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 8 2 32 128 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtp_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 9 2 32 128 (ieee754-policy) x0:32)))

(defun cast_int_rtp_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 10 2 128 32 (ieee754-policy) x0:128)))

(defun cast_sint_rtp_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 11 2 128 32 (ieee754-policy) x0:128)))

(defun cast_float_rtp_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 8 2 64 128 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtp_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 9 2 64 128 (ieee754-policy) x0:64)))

(defun cast_int_rtp_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 10 2 128 64 (ieee754-policy) x0:128)))

(defun cast_sint_rtp_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 11 2 128 64 (ieee754-policy) x0:128)))

(defun cast_float_rtp_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_float_rtp_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 8 2 128 128 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtp_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sfloat_rtp_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 9 2 128 128 (ieee754-policy) x0:128)))

(defun cast_int_rtp_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_int_rtp_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 10 2 128 128 (ieee754-policy) x0:128)))

(defun cast_sint_rtp_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sint_rtp_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 11 2 128 128 (ieee754-policy) x0:128)))

(defun fadd_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fadd_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 1 3 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fsub_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fsub_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 2 3 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmul_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fmul_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 3 3 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fdiv_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fdiv_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 4 3 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmad_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fmad_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 15 3 128 128 (ieee754-policy) x0:128 x1:128 x2:128)))

(defun fsqrt_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fsqrt_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 5 3 128 128 (ieee754-policy) x0:128)))

(defun fround_rtn_ieee754_binary_128 ()
  (declare (external "intrinsic:fround_rtn_ieee754_binary_128"))
  (set y0:128 (ieee754-op 6 3 128 128 (ieee754-policy) x0:128)))

(defun fconvert_rtn_ieee754_binary_128_16 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 7 3 128 16 (ieee754-policy) x0:128)))

(defun fconvert_rtn_ieee754_binary_128_32 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 7 3 128 32 (ieee754-policy) x0:128)))

(defun fconvert_rtn_ieee754_binary_128_64 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 7 3 128 64 (ieee754-policy) x0:128)))

(defun fconvert_rtn_ieee754_binary_128_80 ()
  (declare (external "intrinsic:fconvert_rtn_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 7 3 128 80 (ieee754-policy) x0:128)))

(defun cast_float_rtn_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 8 3 8 128 (ieee754-policy) x0:8)))

(defun cast_sfloat_rtn_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 9 3 8 128 (ieee754-policy) x0:8)))

(defun cast_int_rtn_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 10 3 128 8 (ieee754-policy) x0:128)))

(defun cast_sint_rtn_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 11 3 128 8 (ieee754-policy) x0:128)))

(defun cast_float_rtn_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 8 3 16 128 (ieee754-policy) x0:16)))

(defun cast_sfloat_rtn_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 9 3 16 128 (ieee754-policy) x0:16)))

(defun cast_int_rtn_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 10 3 128 16 (ieee754-policy) x0:128)))

(defun cast_sint_rtn_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 11 3 128 16 (ieee754-policy) x0:128)))

(defun cast_float_rtn_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 8 3 32 128 (ieee754-policy) x0:32)))

(defun cast_sfloat_rtn_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 9 3 32 128 (ieee754-policy) x0:32)))

(defun cast_int_rtn_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 10 3 128 32 (ieee754-policy) x0:128)))

(defun cast_sint_rtn_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 11 3 128 32 (ieee754-policy) x0:128)))

(defun cast_float_rtn_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 8 3 64 128 (ieee754-policy) x0:64)))

(defun cast_sfloat_rtn_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 9 3 64 128 (ieee754-policy) x0:64)))

(defun cast_int_rtn_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 10 3 128 64 (ieee754-policy) x0:128)))

(defun cast_sint_rtn_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 11 3 128 64 (ieee754-policy) x0:128)))

(defun cast_float_rtn_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_float_rtn_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 8 3 128 128 (ieee754-policy) x0:128)))

(defun cast_sfloat_rtn_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sfloat_rtn_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 9 3 128 128 (ieee754-policy) x0:128)))

(defun cast_int_rtn_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_int_rtn_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 10 3 128 128 (ieee754-policy) x0:128)))

(defun cast_sint_rtn_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sint_rtn_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 11 3 128 128 (ieee754-policy) x0:128)))

(defun fadd_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fadd_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 1 4 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fsub_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fsub_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 2 4 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmul_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fmul_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 3 4 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fdiv_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fdiv_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 4 4 128 128 (ieee754-policy) x0:128 x1:128)))

(defun fmad_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fmad_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 15 4 128 128 (ieee754-policy) x0:128 x1:128 x2:128)))

(defun fsqrt_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fsqrt_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 5 4 128 128 (ieee754-policy) x0:128)))

(defun fround_rna_ieee754_binary_128 ()
  (declare (external "intrinsic:fround_rna_ieee754_binary_128"))
  (set y0:128 (ieee754-op 6 4 128 128 (ieee754-policy) x0:128)))

(defun fconvert_rna_ieee754_binary_128_16 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 7 4 128 16 (ieee754-policy) x0:128)))

(defun fconvert_rna_ieee754_binary_128_32 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 7 4 128 32 (ieee754-policy) x0:128)))

(defun fconvert_rna_ieee754_binary_128_64 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 7 4 128 64 (ieee754-policy) x0:128)))

(defun fconvert_rna_ieee754_binary_128_80 ()
  (declare (external "intrinsic:fconvert_rna_ieee754_binary_128_80"))
  (set y0:80 (ieee754-op 7 4 128 80 (ieee754-policy) x0:128)))

(defun cast_float_rna_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 8 4 8 128 (ieee754-policy) x0:8)))

(defun cast_sfloat_rna_ieee754_binary_8_128 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_8_128"))
  (set y0:128 (ieee754-op 9 4 8 128 (ieee754-policy) x0:8)))

(defun cast_int_rna_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 10 4 128 8 (ieee754-policy) x0:128)))

(defun cast_sint_rna_ieee754_binary_128_8 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_128_8"))
  (set y0:8 (ieee754-op 11 4 128 8 (ieee754-policy) x0:128)))

(defun cast_float_rna_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 8 4 16 128 (ieee754-policy) x0:16)))

(defun cast_sfloat_rna_ieee754_binary_16_128 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_16_128"))
  (set y0:128 (ieee754-op 9 4 16 128 (ieee754-policy) x0:16)))

(defun cast_int_rna_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 10 4 128 16 (ieee754-policy) x0:128)))

(defun cast_sint_rna_ieee754_binary_128_16 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_128_16"))
  (set y0:16 (ieee754-op 11 4 128 16 (ieee754-policy) x0:128)))

(defun cast_float_rna_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 8 4 32 128 (ieee754-policy) x0:32)))

(defun cast_sfloat_rna_ieee754_binary_32_128 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_32_128"))
  (set y0:128 (ieee754-op 9 4 32 128 (ieee754-policy) x0:32)))

(defun cast_int_rna_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 10 4 128 32 (ieee754-policy) x0:128)))

(defun cast_sint_rna_ieee754_binary_128_32 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_128_32"))
  (set y0:32 (ieee754-op 11 4 128 32 (ieee754-policy) x0:128)))

(defun cast_float_rna_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 8 4 64 128 (ieee754-policy) x0:64)))

(defun cast_sfloat_rna_ieee754_binary_64_128 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_64_128"))
  (set y0:128 (ieee754-op 9 4 64 128 (ieee754-policy) x0:64)))

(defun cast_int_rna_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 10 4 128 64 (ieee754-policy) x0:128)))

(defun cast_sint_rna_ieee754_binary_128_64 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_128_64"))
  (set y0:64 (ieee754-op 11 4 128 64 (ieee754-policy) x0:128)))

(defun cast_float_rna_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_float_rna_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 8 4 128 128 (ieee754-policy) x0:128)))

(defun cast_sfloat_rna_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sfloat_rna_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 9 4 128 128 (ieee754-policy) x0:128)))

(defun cast_int_rna_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_int_rna_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 10 4 128 128 (ieee754-policy) x0:128)))

(defun cast_sint_rna_ieee754_binary_128_128 ()
  (declare (external "intrinsic:cast_sint_rna_ieee754_binary_128_128"))
  (set y0:128 (ieee754-op 11 4 128 128 (ieee754-policy) x0:128)))

(defun forder_ieee754_binary_128 ()
  (declare (external "intrinsic:forder_ieee754_binary_128"))
  (set y0:1 (ieee754-op 12 0 128 1 (ieee754-policy) x0:128 x1:128)))

(defun is_nan_ieee754_binary_128 ()
  (declare (external "intrinsic:is_nan_ieee754_binary_128"))
  (set y0:1 (ieee754-op 13 0 128 1 (ieee754-policy) x0:128)))

(defun is_inf_ieee754_binary_128 ()
  (declare (external "intrinsic:is_inf_ieee754_binary_128"))
  (set y0:1 (ieee754-op 14 0 128 1 (ieee754-policy) x0:128)))

