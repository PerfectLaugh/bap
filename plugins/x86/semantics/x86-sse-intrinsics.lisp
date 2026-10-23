(declare (context (target x86)
                  (x86-floating-points intrinsic-semantics)))
(require x86-common)

(in-package x86-common)

;;; SSE FLOATING-POINT INSTRUCTIONS
;;
;; The floating-point operations are calls to the intrinsic functions
;; <op>_<rmode>_ieee754_binary_<size> and, for the conversions,
;; <op>_<rmode>_ieee754_binary_<from>_<to>, with the operands and the
;; results of the sizes in their names. The rounding mode is the one
;; of MXCSR after reset, to nearest with ties to even, the other
;; controls of MXCSR and the exceptions are not modeled.

(defparameter *sse-rmode* 'rne)

(defparameter *sse-format* 'ieee754_binary)

(defun symbol-of-size (sz)
  (case sz
    16  '16
    32  '32
    64  '64
    80  '80
    128 '128
    256 '256
    'unknown))

(defun sse-load (size base scale index off)
  (load-bits size (operand-address base scale index off)))

(defmacro set-sse (rd x)
  "(set-sse RD X) sets the lower bits of RD to X keeping the others"
  (let ((wd (word-width rd))
        (wx (word-width x)))
    (set$ rd (concat (cast-high (- wd wx) rd)
                     (cast-low wx x)))))

;; scalar operations, the operands are the lowest bits of the arguments

(defun sse-binary (name rt x y)
  (intrinsic
   (symbol-concat name *sse-rmode* *sse-format* (symbol-of-size rt) :sep '_)
   (cast-low rt x)
   (cast-low rt y)
   :result rt))

(defun sse-unary (name rt x)
  (intrinsic
   (symbol-concat name *sse-rmode* *sse-format* (symbol-of-size rt) :sep '_)
   (cast-low rt x)
   :result rt))

(defun sse-convert (name rmode rs rt x)
  "(sse-convert NAME RMODE RS RT X) converts the RS lowest bits of X
   to RT bits"
  (intrinsic
   (symbol-concat name rmode *sse-format*
                  (symbol-of-size rs) (symbol-of-size rt) :sep '_)
   (cast-low rs x)
   :result rt))

(defun sse-is-nan (rt x)
  (intrinsic (symbol-concat 'is_nan *sse-format* (symbol-of-size rt) :sep '_)
             (cast-low rt x)
             :result 1))

(defun sse-forder (rt x y)
  (intrinsic (symbol-concat 'forder *sse-format* (symbol-of-size rt) :sep '_)
             (cast-low rt x)
             (cast-low rt y)
             :result 1))

;; MINSD and MAXSD return the second operand when the operands are
;; unordered or equal
(defun sse-min (rt x y)
  (let ((a (cast-low rt x))
        (b (cast-low rt y)))
    (if (sse-forder rt a b) a b)))

(defun sse-max (rt x y)
  (let ((a (cast-low rt x))
        (b (cast-low rt y)))
    (if (sse-forder rt b a) a b)))

(defun sse-exponent (rs x)
  (cast-unsigned 64 (if (= rs 64) (extract 62 52 x) (extract 30 23 x))))

(defun sse-bias (rs) (if (= rs 64) 1023 127))

(defun sse-to-int (rmode rs rt x)
  "(sse-to-int RMODE RS RT X) converts the floating-point number in the
   RS lowest bits of X to a RT-bit integer, a NaN or a number out of
   the range converts to the integer indefinite value, 1 << (RT - 1)"
  (let ((r (sse-convert 'cast_sint rmode rs rt x))
        (invalid (>= (sse-exponent rs x)
                     (cast-unsigned 64 (- (+ (sse-bias rs) rt) 1)))))
    (if invalid (lshift (cast-unsigned rt 1) (- rt 1)) r)))

;; packed operations, applied to each lane

(defun sse-packed (name rt x y)
  (if (= rt 64)
      (concat (sse-binary name 64 (extract 127 64 x) (extract 127 64 y))
              (sse-binary name 64 (extract 63 0 x) (extract 63 0 y)))
    (concat (sse-binary name 32 (extract 127 96 x) (extract 127 96 y))
            (sse-binary name 32 (extract 95 64 x) (extract 95 64 y))
            (sse-binary name 32 (extract 63 32 x) (extract 63 32 y))
            (sse-binary name 32 (extract 31 0 x) (extract 31 0 y)))))

(defmacro scalar-rr (name rt rd rn rm)
  (set-sse rd (sse-binary name rt rn rm)))
(defmacro scalar-rm (name rt rd rn base scale index off)
  (set-sse rd (sse-binary name rt rn (sse-load rt base scale index off))))
(defmacro packed-rr (name rt rd rn rm)
  (set-sse rd (sse-packed name rt rn rm)))
(defmacro packed-rm (name rt rd rn base scale index off)
  (set-sse rd (sse-packed name rt rn (sse-load 128 base scale index off))))

(defun ADDSDrr_Int (rd rn rm) (scalar-rr 'fadd 64 rd rn rm))
(defun SUBSDrr_Int (rd rn rm) (scalar-rr 'fsub 64 rd rn rm))
(defun MULSDrr_Int (rd rn rm) (scalar-rr 'fmul 64 rd rn rm))
(defun DIVSDrr_Int (rd rn rm) (scalar-rr 'fdiv 64 rd rn rm))
(defun ADDSSrr_Int (rd rn rm) (scalar-rr 'fadd 32 rd rn rm))
(defun SUBSSrr_Int (rd rn rm) (scalar-rr 'fsub 32 rd rn rm))
(defun MULSSrr_Int (rd rn rm) (scalar-rr 'fmul 32 rd rn rm))
(defun DIVSSrr_Int (rd rn rm) (scalar-rr 'fdiv 32 rd rn rm))
(defun ADDSDrm_Int (rd rn b s i off _) (scalar-rm 'fadd 64 rd rn b s i off))
(defun SUBSDrm_Int (rd rn b s i off _) (scalar-rm 'fsub 64 rd rn b s i off))
(defun MULSDrm_Int (rd rn b s i off _) (scalar-rm 'fmul 64 rd rn b s i off))
(defun DIVSDrm_Int (rd rn b s i off _) (scalar-rm 'fdiv 64 rd rn b s i off))
(defun ADDSSrm_Int (rd rn b s i off _) (scalar-rm 'fadd 32 rd rn b s i off))
(defun SUBSSrm_Int (rd rn b s i off _) (scalar-rm 'fsub 32 rd rn b s i off))
(defun MULSSrm_Int (rd rn b s i off _) (scalar-rm 'fmul 32 rd rn b s i off))
(defun DIVSSrm_Int (rd rn b s i off _) (scalar-rm 'fdiv 32 rd rn b s i off))

(defun ADDPDrr (rd rn rm) (packed-rr 'fadd 64 rd rn rm))
(defun SUBPDrr (rd rn rm) (packed-rr 'fsub 64 rd rn rm))
(defun MULPDrr (rd rn rm) (packed-rr 'fmul 64 rd rn rm))
(defun DIVPDrr (rd rn rm) (packed-rr 'fdiv 64 rd rn rm))
(defun ADDPSrr (rd rn rm) (packed-rr 'fadd 32 rd rn rm))
(defun SUBPSrr (rd rn rm) (packed-rr 'fsub 32 rd rn rm))
(defun MULPSrr (rd rn rm) (packed-rr 'fmul 32 rd rn rm))
(defun DIVPSrr (rd rn rm) (packed-rr 'fdiv 32 rd rn rm))
(defun ADDPDrm (rd rn b s i off _) (packed-rm 'fadd 64 rd rn b s i off))
(defun SUBPDrm (rd rn b s i off _) (packed-rm 'fsub 64 rd rn b s i off))
(defun MULPDrm (rd rn b s i off _) (packed-rm 'fmul 64 rd rn b s i off))
(defun DIVPDrm (rd rn b s i off _) (packed-rm 'fdiv 64 rd rn b s i off))
(defun ADDPSrm (rd rn b s i off _) (packed-rm 'fadd 32 rd rn b s i off))
(defun SUBPSrm (rd rn b s i off _) (packed-rm 'fsub 32 rd rn b s i off))
(defun MULPSrm (rd rn b s i off _) (packed-rm 'fmul 32 rd rn b s i off))
(defun DIVPSrm (rd rn b s i off _) (packed-rm 'fdiv 32 rd rn b s i off))

(defun SQRTSDr_Int (rd _ rm) (set-sse rd (sse-unary 'fsqrt 64 rm)))
(defun SQRTSSr_Int (rd _ rm) (set-sse rd (sse-unary 'fsqrt 32 rm)))
(defun SQRTSDm_Int (rd _ b s i off _)
  (set-sse rd (sse-unary 'fsqrt 64 (sse-load 64 b s i off))))
(defun SQRTSSm_Int (rd _ b s i off _)
  (set-sse rd (sse-unary 'fsqrt 32 (sse-load 32 b s i off))))
(defun SQRTPDr (rd rm)
  (set-sse rd (concat (sse-unary 'fsqrt 64 (extract 127 64 rm))
                      (sse-unary 'fsqrt 64 (extract 63 0 rm)))))

(defun MINSDrr_Int (rd rn rm) (set-sse rd (sse-min 64 rn rm)))
(defun MAXSDrr_Int (rd rn rm) (set-sse rd (sse-max 64 rn rm)))
(defun MINSSrr_Int (rd rn rm) (set-sse rd (sse-min 32 rn rm)))
(defun MAXSSrr_Int (rd rn rm) (set-sse rd (sse-max 32 rn rm)))
(defun MINSDrm_Int (rd rn b s i off _) (set-sse rd (sse-min 64 rn (sse-load 64 b s i off))))
(defun MAXSDrm_Int (rd rn b s i off _) (set-sse rd (sse-max 64 rn (sse-load 64 b s i off))))
(defun MINSSrm_Int (rd rn b s i off _) (set-sse rd (sse-min 32 rn (sse-load 32 b s i off))))
(defun MAXSSrm_Int (rd rn b s i off _) (set-sse rd (sse-max 32 rn (sse-load 32 b s i off))))

;; conversions

(defun CVTSI2SDrr_Int (rd _ rm) (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 32 64 rm)))
(defun CVTSI642SDrr_Int (rd _ rm) (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 64 64 rm)))
(defun CVTSI2SSrr_Int (rd _ rm) (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 32 32 rm)))
(defun CVTSI642SSrr_Int (rd _ rm) (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 64 32 rm)))
(defun CVTSI2SDrm_Int (rd _ b s i off _)
  (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 32 64 (sse-load 32 b s i off))))
(defun CVTSI642SDrm_Int (rd _ b s i off _)
  (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 64 64 (sse-load 64 b s i off))))
(defun CVTSI2SSrm_Int (rd _ b s i off _)
  (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 32 32 (sse-load 32 b s i off))))
(defun CVTSI642SSrm_Int (rd _ b s i off _)
  (set-sse rd (sse-convert 'cast_sfloat *sse-rmode* 64 32 (sse-load 64 b s i off))))

(defun CVTSD2SSrr_Int (rd _ rm) (set-sse rd (sse-convert 'fconvert *sse-rmode* 64 32 rm)))
(defun CVTSS2SDrr_Int (rd _ rm) (set-sse rd (sse-convert 'fconvert *sse-rmode* 32 64 rm)))
(defun CVTSD2SSrm_Int (rd _ b s i off _)
  (set-sse rd (sse-convert 'fconvert *sse-rmode* 64 32 (sse-load 64 b s i off))))
(defun CVTSS2SDrm_Int (rd _ b s i off _)
  (set-sse rd (sse-convert 'fconvert *sse-rmode* 32 64 (sse-load 32 b s i off))))
(defun CVTPS2PDrr (rd rm)
  (set-sse rd (concat (sse-convert 'fconvert *sse-rmode* 32 64 (extract 63 32 rm))
                      (sse-convert 'fconvert *sse-rmode* 32 64 (extract 31 0 rm)))))

;; the truncating conversions round toward zero, the others with MXCSR
(defmacro to-int (rmode rs rt rd x) (set-gpr rd (sse-to-int rmode rs rt x)))

(defun CVTTSD2SIrr_Int (rd rm) (to-int 'rtz 64 32 rd rm))
(defun CVTTSD2SI64rr_Int (rd rm) (to-int 'rtz 64 64 rd rm))
(defun CVTTSS2SIrr_Int (rd rm) (to-int 'rtz 32 32 rd rm))
(defun CVTTSS2SI64rr_Int (rd rm) (to-int 'rtz 32 64 rd rm))
(defun CVTSD2SIrr_Int (rd rm) (to-int *sse-rmode* 64 32 rd rm))
(defun CVTSD2SI64rr_Int (rd rm) (to-int *sse-rmode* 64 64 rd rm))
(defun CVTSS2SIrr_Int (rd rm) (to-int *sse-rmode* 32 32 rd rm))
(defun CVTSS2SI64rr_Int (rd rm) (to-int *sse-rmode* 32 64 rd rm))
(defun CVTTSD2SIrm_Int (rd b s i off _) (to-int 'rtz 64 32 rd (sse-load 64 b s i off)))
(defun CVTTSD2SI64rm_Int (rd b s i off _) (to-int 'rtz 64 64 rd (sse-load 64 b s i off)))
(defun CVTTSS2SIrm_Int (rd b s i off _) (to-int 'rtz 32 32 rd (sse-load 32 b s i off)))
(defun CVTTSS2SI64rm_Int (rd b s i off _) (to-int 'rtz 32 64 rd (sse-load 32 b s i off)))
(defun CVTSD2SIrm_Int (rd b s i off _) (to-int *sse-rmode* 64 32 rd (sse-load 64 b s i off)))
(defun CVTSD2SI64rm_Int (rd b s i off _) (to-int *sse-rmode* 64 64 rd (sse-load 64 b s i off)))
(defun CVTSS2SIrm_Int (rd b s i off _) (to-int *sse-rmode* 32 32 rd (sse-load 32 b s i off)))
(defun CVTSS2SI64rm_Int (rd b s i off _) (to-int *sse-rmode* 32 64 rd (sse-load 32 b s i off)))

;; comparisons, ZF, PF and CF are 111 if the operands are unordered,
;; and otherwise 000, 001 and 100 if the first one is greater, less or
;; equal, OF, SF and AF are cleared

(defun compare-floats (rt x y)
  (let ((is-nan-x (sse-is-nan rt x))
        (is-nan-y (sse-is-nan rt y))
        (x<y (sse-forder rt x y))
        (y<x (sse-forder rt y x)))
    (set PF (logor is-nan-x is-nan-y))
    (set CF (logor PF x<y))
    (set ZF (logor PF (not (logor x<y y<x))))
    (set OF 0:1)
    (set SF 0:1)
    (set AF 0:1)))

(defun UCOMISDrr (rn rm) (compare-floats 64 rn rm))
(defun UCOMISSrr (rn rm) (compare-floats 32 rn rm))
(defun COMISDrr (rn rm) (compare-floats 64 rn rm))
(defun COMISSrr (rn rm) (compare-floats 32 rn rm))
(defun UCOMISDrm (rn b s i off _) (compare-floats 64 rn (sse-load 64 b s i off)))
(defun UCOMISSrm (rn b s i off _) (compare-floats 32 rn (sse-load 32 b s i off)))
(defun COMISDrm (rn b s i off _) (compare-floats 64 rn (sse-load 64 b s i off)))
(defun COMISSrm (rn b s i off _) (compare-floats 32 rn (sse-load 32 b s i off)))

;; the barriers have no effect, as LFENCE and SFENCE
(defun MFENCE () (empty))

;; rounding to integral values, the rounding mode is the bits 1:0 of
;; the immediate, or the one of MXCSR if its bit 2 is set
(defun sse-round (rm rt x)
  (intrinsic (symbol-concat 'fround rm *sse-format* (symbol-of-size rt) :sep '_)
             (cast-low rt x)
             :result rt))

(defun sse-round-imm (rt x imm)
  (if (= (logand imm 4) 4) (sse-round *sse-rmode* rt x)
    (case (logand imm 3)
      0 (sse-round 'rne rt x)
      1 (sse-round 'rtn rt x)
      2 (sse-round 'rtp rt x)
      3 (sse-round 'rtz rt x))))

(defun ROUNDSDri_Int (rd _ rm imm) (set-sse rd (sse-round-imm 64 rm imm)))
(defun ROUNDSSri_Int (rd _ rm imm) (set-sse rd (sse-round-imm 32 rm imm)))

;;; X87 FLOATING-POINT INSTRUCTIONS
;;
;; The registers ST0-ST7 are the registers of the stack, relative to
;; its top, as the operands name them, so a push rotates them, ST0 is
;; the new value, which overwrites the old ST7, and a pop rotates them
;; back, ST7 is the popped value. The tags, the status word, e.g., its
;; condition codes C0-C3, and the exceptions are not modeled. The
;; operations are of the 80-bit extended format, rounded to nearest,
;; ties to even, as the precision control and the rounding control of
;; FPU_CONTROL of the System V ABI tell, the conversions to the integers
;; and to the smaller formats, which the compilers precede with the
;; changes of FPU_CONTROL, round as its rounding control, the bits
;; 11:10, tells.

;; The top of the stack, TOP of FPU_STATUS, and the tags of FPU_TAG, of
;; the physical registers, which the pushes and the pops keep, as the
;; registers ST0-ST7 are renamed: the empty register has the tag 11, and
;; the others 00, which FNSTENV classifies, as the processor does, see
;; [x87-tags].
(defun x87-top () (extract 13 11 FPU_STATUS))

(defun x87-set-top (top)
  (set FPU_STATUS (logor (logand FPU_STATUS 0xc7ff:16)
                         (lshift (cast-unsigned 16 top) 11))))

(defun x87-set-tag (i empty)
  (let ((shift (* 2 (cast-unsigned 16 i))))
    (set FPU_TAG (logor (logand FPU_TAG (lnot (lshift 3:16 shift)))
                        (if empty (lshift 3:16 shift) 0:16)))))

(defun x87-push (x)
  (let ((top (- (x87-top) 1:3)))
    (x87-set-top top)
    (x87-set-tag top false))
  (let ((v x))
    (set ST7 ST6)
    (set ST6 ST5)
    (set ST5 ST4)
    (set ST4 ST3)
    (set ST3 ST2)
    (set ST2 ST1)
    (set ST1 ST0)
    (set ST0 v)))

(defun x87-pop ()
  (let ((top (x87-top)))
    (x87-set-tag top true)
    (x87-set-top (+ top 1:3)))
  (let ((v ST0))
    (set ST0 ST1)
    (set ST1 ST2)
    (set ST2 ST3)
    (set ST3 ST4)
    (set ST4 ST5)
    (set ST5 ST6)
    (set ST6 ST7)
    (set ST7 v)))

(defun x87-binary (name x y)
  (intrinsic
   (symbol-concat name 'rne *sse-format* '80 :sep '_)
   x y
   :result 80))

(defun x87-unary (name rm x)
  (intrinsic
   (symbol-concat name rm *sse-format* '80 :sep '_)
   x
   :result 80))

(defun x87-from-float (rs x)
  "(x87-from-float RS X) is the RS-bit float X extended to 80 bits"
  (intrinsic
   (symbol-concat 'fconvert 'rne *sse-format* (symbol-of-size rs) '80 :sep '_)
   x
   :result 80))

(defun x87-from-int (rs x)
  "(x87-from-int RS X) is the RS-bit signed integer X as a float"
  (intrinsic
   (symbol-concat 'cast_sfloat 'rne *sse-format* (symbol-of-size rs) '80 :sep '_)
   x
   :result 80))

(defun x87-to-float (rm rt x)
  (intrinsic
   (symbol-concat 'fconvert rm *sse-format* '80 (symbol-of-size rt) :sep '_)
   x
   :result rt))

(defun x87-to-int (rm rt x)
  (intrinsic
   (symbol-concat 'cast_sint rm *sse-format* '80 (symbol-of-size rt) :sep '_)
   x
   :result rt))

(defun x87-rc () (extract 11 10 FPU_CONTROL))

(defmacro x87-rounded (op rt x)
  "(x87-rounded OP RT X) is (OP RM RT X) with the rounding mode RM of
   the rounding control, OP is a statement, as the conversions in the
   branches are"
  (case (x87-rc)
    0 (op 'rne rt x)
    1 (op 'rtn rt x)
    2 (op 'rtp rt x)
    (op 'rtz rt x)))

(defun x87-round-st0 (rm _ x) (set ST0 (x87-unary 'fround rm x)))

;; the 80-bit store is two stores, of the significand and of the sign
;; and exponent, in the little-endian order
(defun x87-store-80 (addr x)
  (store-word addr (cast-low 64 x))
  (store-word (+ addr 8) (cast-high 16 x)))

;; the invalid conversions, e.g., of a NaN, or of a number out of the
;; range of the integer, are the integer indefinite value, as the
;; intrinsics of x86 convert them
(defun x87-store-int (rm rt x) (x87-to-int rm rt x))

;; loads and stores

(defun x87-load-float (rs base scale index off seg)
  (x87-from-float rs (load-n rs (ea base scale index off seg))))

(defun LD_F32m (b s i off seg) (x87-push (x87-load-float 32 b s i off seg)))
(defun LD_F64m (b s i off seg) (x87-push (x87-load-float 64 b s i off seg)))
(defun LD_F80m (b s i off seg) (x87-push (load-n 80 (ea b s i off seg))))
(defun LD_Frr (r) (x87-push r))
(defun LD_F0 () (x87-push 0:80))
(defun LD_F1 () (x87-push 0x3fff8000000000000000:80))
(defun FLDPI () (x87-push 0x4000c90fdaa22168c235:80))
(defun FLDL2E () (x87-push 0x3fffb8aa3b295c17f0bc:80))
(defun FLDL2T () (x87-push 0x4000d49a784bcd1b8afe:80))
(defun FLDLG2 () (x87-push 0x3ffd9a209a84fbcff799:80))
(defun FLDLN2 () (x87-push 0x3ffeb17217f7d1cf79ac:80))
(defun ILD_F16m (b s i off seg) (x87-push (x87-from-int 16 (load-n 16 (ea b s i off seg)))))
(defun ILD_F32m (b s i off seg) (x87-push (x87-from-int 32 (load-n 32 (ea b s i off seg)))))
(defun ILD_F64m (b s i off seg) (x87-push (x87-from-int 64 (load-n 64 (ea b s i off seg)))))

(defmacro x87-store-as (convert rt base scale index off seg)
  (let ((addr (ea base scale index off seg)))
    (case (x87-rc)
      0 (store-n rt addr (convert 'rne rt ST0))
      1 (store-n rt addr (convert 'rtn rt ST0))
      2 (store-n rt addr (convert 'rtp rt ST0))
      (store-n rt addr (convert 'rtz rt ST0)))))

(defun x87-store-float (rt base scale index off seg)
  (x87-store-as x87-to-float rt base scale index off seg))

(defun x87-store-integer (rt base scale index off seg)
  (x87-store-as x87-store-int rt base scale index off seg))

(defun x87-store-truncated (rt base scale index off seg)
  (store-n rt (ea base scale index off seg) (x87-store-int 'rtz rt ST0)))

(defun ST_F32m (b s i off seg) (x87-store-float 32 b s i off seg))
(defun ST_F64m (b s i off seg) (x87-store-float 64 b s i off seg))
(defun ST_FP32m (b s i off seg) (x87-store-float 32 b s i off seg) (x87-pop))
(defun ST_FP64m (b s i off seg) (x87-store-float 64 b s i off seg) (x87-pop))
(defun ST_FP80m (b s i off seg) (x87-store-80 (ea b s i off seg) ST0) (x87-pop))
(defun ST_Frr (r) (set$ r ST0))
(defun ST_FPrr (r) (set$ r ST0) (x87-pop))
(defun IST_F16m (b s i off seg) (x87-store-integer 16 b s i off seg))
(defun IST_F32m (b s i off seg) (x87-store-integer 32 b s i off seg))
(defun IST_FP16m (b s i off seg) (x87-store-integer 16 b s i off seg) (x87-pop))
(defun IST_FP32m (b s i off seg) (x87-store-integer 32 b s i off seg) (x87-pop))
(defun IST_FP64m (b s i off seg) (x87-store-integer 64 b s i off seg) (x87-pop))
(defun ISTT_FP16m (b s i off seg) (x87-store-truncated 16 b s i off seg) (x87-pop))
(defun ISTT_FP32m (b s i off seg) (x87-store-truncated 32 b s i off seg) (x87-pop))
(defun ISTT_FP64m (b s i off seg) (x87-store-truncated 64 b s i off seg) (x87-pop))

;; arithmetic, the names of the register forms are of the semantics,
;; e.g., SUBR_FrST0 is ST(i) := ST0 - ST(i), whose AT&T mnemonic is
;; fsub, and the P forms pop

(defmacro x87-rr (name r x y)
  (set$ r (x87-binary name x y)))

(defun ADD_FST0r (r) (x87-rr 'fadd 'ST0 ST0 r))
(defun ADD_FrST0 (r) (x87-rr 'fadd r r ST0))
(defun ADD_FPrST0 (r) (x87-rr 'fadd r r ST0) (x87-pop))
(defun SUB_FST0r (r) (x87-rr 'fsub 'ST0 ST0 r))
(defun SUBR_FST0r (r) (x87-rr 'fsub 'ST0 r ST0))
(defun SUB_FrST0 (r) (x87-rr 'fsub r r ST0))
(defun SUBR_FrST0 (r) (x87-rr 'fsub r ST0 r))
(defun SUB_FPrST0 (r) (x87-rr 'fsub r r ST0) (x87-pop))
(defun SUBR_FPrST0 (r) (x87-rr 'fsub r ST0 r) (x87-pop))
(defun MUL_FST0r (r) (x87-rr 'fmul 'ST0 ST0 r))
(defun MUL_FrST0 (r) (x87-rr 'fmul r r ST0))
(defun MUL_FPrST0 (r) (x87-rr 'fmul r r ST0) (x87-pop))
(defun DIV_FST0r (r) (x87-rr 'fdiv 'ST0 ST0 r))
(defun DIVR_FST0r (r) (x87-rr 'fdiv 'ST0 r ST0))
(defun DIV_FrST0 (r) (x87-rr 'fdiv r r ST0))
(defun DIVR_FrST0 (r) (x87-rr 'fdiv r ST0 r))
(defun DIV_FPrST0 (r) (x87-rr 'fdiv r r ST0) (x87-pop))
(defun DIVR_FPrST0 (r) (x87-rr 'fdiv r ST0 r) (x87-pop))

(defun x87-mem-float (rs b s i off seg) (x87-load-float rs b s i off seg))
(defun x87-mem-int (rs b s i off seg) (x87-from-int rs (load-n rs (ea b s i off seg))))

(defun ADD_F32m (b s i off seg) (set ST0 (x87-binary 'fadd ST0 (x87-mem-float 32 b s i off seg))))
(defun ADD_F64m (b s i off seg) (set ST0 (x87-binary 'fadd ST0 (x87-mem-float 64 b s i off seg))))
(defun ADD_FI16m (b s i off seg) (set ST0 (x87-binary 'fadd ST0 (x87-mem-int 16 b s i off seg))))
(defun ADD_FI32m (b s i off seg) (set ST0 (x87-binary 'fadd ST0 (x87-mem-int 32 b s i off seg))))
(defun SUB_F32m (b s i off seg) (set ST0 (x87-binary 'fsub ST0 (x87-mem-float 32 b s i off seg))))
(defun SUB_F64m (b s i off seg) (set ST0 (x87-binary 'fsub ST0 (x87-mem-float 64 b s i off seg))))
(defun SUB_FI16m (b s i off seg) (set ST0 (x87-binary 'fsub ST0 (x87-mem-int 16 b s i off seg))))
(defun SUB_FI32m (b s i off seg) (set ST0 (x87-binary 'fsub ST0 (x87-mem-int 32 b s i off seg))))
(defun SUBR_F32m (b s i off seg) (set ST0 (x87-binary 'fsub (x87-mem-float 32 b s i off seg) ST0)))
(defun SUBR_F64m (b s i off seg) (set ST0 (x87-binary 'fsub (x87-mem-float 64 b s i off seg) ST0)))
(defun SUBR_FI16m (b s i off seg) (set ST0 (x87-binary 'fsub (x87-mem-int 16 b s i off seg) ST0)))
(defun SUBR_FI32m (b s i off seg) (set ST0 (x87-binary 'fsub (x87-mem-int 32 b s i off seg) ST0)))
(defun MUL_F32m (b s i off seg) (set ST0 (x87-binary 'fmul ST0 (x87-mem-float 32 b s i off seg))))
(defun MUL_F64m (b s i off seg) (set ST0 (x87-binary 'fmul ST0 (x87-mem-float 64 b s i off seg))))
(defun MUL_FI16m (b s i off seg) (set ST0 (x87-binary 'fmul ST0 (x87-mem-int 16 b s i off seg))))
(defun MUL_FI32m (b s i off seg) (set ST0 (x87-binary 'fmul ST0 (x87-mem-int 32 b s i off seg))))
(defun DIV_F32m (b s i off seg) (set ST0 (x87-binary 'fdiv ST0 (x87-mem-float 32 b s i off seg))))
(defun DIV_F64m (b s i off seg) (set ST0 (x87-binary 'fdiv ST0 (x87-mem-float 64 b s i off seg))))
(defun DIV_FI16m (b s i off seg) (set ST0 (x87-binary 'fdiv ST0 (x87-mem-int 16 b s i off seg))))
(defun DIV_FI32m (b s i off seg) (set ST0 (x87-binary 'fdiv ST0 (x87-mem-int 32 b s i off seg))))
(defun DIVR_F32m (b s i off seg) (set ST0 (x87-binary 'fdiv (x87-mem-float 32 b s i off seg) ST0)))
(defun DIVR_F64m (b s i off seg) (set ST0 (x87-binary 'fdiv (x87-mem-float 64 b s i off seg) ST0)))
(defun DIVR_FI16m (b s i off seg) (set ST0 (x87-binary 'fdiv (x87-mem-int 16 b s i off seg) ST0)))
(defun DIVR_FI32m (b s i off seg) (set ST0 (x87-binary 'fdiv (x87-mem-int 32 b s i off seg) ST0)))

(defun SQRT_F () (set ST0 (x87-unary 'fsqrt 'rne ST0)))
(defun FRNDINT () (x87-rounded x87-round-st0 80 ST0))
(defun CHS_F () (set ST0 (logxor ST0 0x80000000000000000000:80)))
(defun ABS_F () (set ST0 (logand ST0 0x7fffffffffffffffffff:80)))

(defun XCH_F (r)
  (let ((x ST0))
    (set ST0 r)
    (set$ r x)))

;; the rotations of the stack, which don't change the tags
(defun x87-rotate-down ()
  (let ((v ST0))
    (set ST0 ST1)
    (set ST1 ST2)
    (set ST2 ST3)
    (set ST3 ST4)
    (set ST4 ST5)
    (set ST5 ST6)
    (set ST6 ST7)
    (set ST7 v)))

(defun FINCSTP () (x87-rotate-down) (x87-set-top (+ (x87-top) 1:3)))
(defun FDECSTP ()
  (x87-set-top (- (x87-top) 1:3))
  (let ((v ST7))
    (set ST7 ST6)
    (set ST6 ST5)
    (set ST5 ST4)
    (set ST4 ST3)
    (set ST3 ST2)
    (set ST2 ST1)
    (set ST1 ST0)
    (set ST0 v)))
(defun FFREE (_) (empty))

;; The status word of x87, whose exceptions are not raised, as the
;; operations are of the intrinsics, the condition codes C0-C3, of FXAM,
;; and the top of the stack, which is not modeled, as the stack is the
;; registers ST0-ST7, and its tags.
(defun FNCLEX () (set FPU_STATUS (logand FPU_STATUS 0x7f00:16)))

;; the default control word, to the nearest, of 64 bits, all exceptions
;; masked, the status cleared, and the stack empty
(defun FNINIT ()
  (set FPU_CONTROL 0x37f:16)
  (set FPU_STATUS 0:16)
  (set FPU_TAG 0xffff:16))

(defun FNSTSW16r () (set-ax FPU_STATUS))
(defun FNSTSWm (base scale index off seg)
  (store-n 16 (ea base scale index off seg) FPU_STATUS))

;; the tag of the value: valid 00, zero 01, and special 10, i.e., a NaN,
;; an infinity, a denormal, or an unsupported one
(defun x87-classify (x)
  (let ((e (extract 78 64 x))
        (j (extract 63 63 x)))
    (if (= (extract 78 0 x) 0) 0b01:2
      (if (or (= e 0x7fff) (= e 0) (not j)) 0b10:2 0b00:2))))

;; the register ST of the physical register I
(defun x87-physical (i)
  (case (- i (x87-top))
    0 ST0 1 ST1 2 ST2 3 ST3 4 ST4 5 ST5 6 ST6 ST7))

;; the tag word, whose empty registers have the tag 11, and the others
;; the tags of their values
(defun x87-tags ()
  (concat
   (x87-tag-of 7:3) (x87-tag-of 6:3) (x87-tag-of 5:3) (x87-tag-of 4:3)
   (x87-tag-of 3:3) (x87-tag-of 2:3) (x87-tag-of 1:3) (x87-tag-of 0:3)))

(defun x87-tag-of (i)
  (let ((empty (= (extract 1 0 (rshift FPU_TAG (* 2 (cast-unsigned 16 i)))) 3)))
    (if empty 0b11:2 (x87-classify (x87-physical i)))))

;; the environment, of the 32-bit and the 64-bit modes, of 28 bytes: the
;; control, the status, and the tag words, and the pointers of the last
;; instruction and operand, which are not modeled, as zeros; FNSTENV
;; masks all exceptions then
(defun FSTENVm (base scale index off seg)
  (let ((a (ea base scale index off seg)))
    (store-n 32 a (cast-unsigned 32 FPU_CONTROL))
    (store-n 32 (+ a 4) (cast-unsigned 32 FPU_STATUS))
    (store-n 32 (+ a 8) (cast-unsigned 32 (x87-tags)))
    (store-n 32 (+ a 12) 0:32)
    (store-n 32 (+ a 16) 0:32)
    (store-n 32 (+ a 20) 0:32)
    (store-n 32 (+ a 24) 0:32)
    (set FPU_CONTROL (logor FPU_CONTROL 0x3f:16))))

(defun FLDENVm (base scale index off seg)
  (let ((a (ea base scale index off seg)))
    (set FPU_CONTROL (load-n 16 a))
    (set FPU_STATUS (load-n 16 (+ a 4)))
    (set FPU_TAG (load-n 16 (+ a 8)))))

;; the class of ST0, in C3, C2, and C0, and its sign in C1: the NaN 001,
;; the normal 010, the infinity 011, the zero 100, the denormal 110, and
;; the unsupported, e.g., the unnormal, 000, as the stack is not empty
(defun XAM_F ()
  (let ((x ST0)
        (e (extract 78 64 x))
        (j (extract 63 63 x))
        (f (extract 62 0 x))
        (c (if (= e 0x7fff)
               (if (and j (= f 0)) 0b011 (if j 0b001 0b000))
             (if (= e 0)
                 (if (and (not j) (= f 0)) 0b100 0b110)
               (if j 0b010 0b000)))))
    (set FPU_STATUS
         (logor (logand FPU_STATUS 0xb8ff:16)
                (lshift (cast-unsigned 16 (extract 2 2 c)) 14)
                (lshift (cast-unsigned 16 (extract 1 1 c)) 10)
                (lshift (cast-unsigned 16 (extract 79 79 x)) 9)
                (lshift (cast-unsigned 16 (extract 0 0 c)) 8)))))

;; ST0 times 2 to ST1, rounded toward zero, which is clamped, so that the
;; product overflows or underflows, as the powers of two are exact, in
;; two steps, whose exponents are in the range of the format
(defun x87-pow2 (n)
  (concat (cast-low 16 (+ n 16383)) 0x8000000000000000:64))

(defun FSCALE ()
  (let ((n (x87-to-int 'rtz 32 ST1))
        (n (if (< 40000 n) 40000 (if (< n -40000) -40000 n)))
        (h (arshift n 1)))
    (set ST0 (x87-binary 'fmul (x87-binary 'fmul ST0 (x87-pow2 h))
                         (x87-pow2 (- n h))))))

;; the comparisons, which set ZF, PF and CF, as UCOMISD does

(defun UCOM_FIr (r) (compare-floats 80 ST0 r))
(defun UCOM_FIPr (r) (compare-floats 80 ST0 r) (x87-pop))
(defun COM_FIr (r) (compare-floats 80 ST0 r))
(defun COM_FIPr (r) (compare-floats 80 ST0 r) (x87-pop))

;; the conditional moves by the flags

(defmacro x87-cmov (c r) (when c (set ST0 r)))

(defun CMOVB_F (r) (x87-cmov CF r))
(defun CMOVE_F (r) (x87-cmov ZF r))
(defun CMOVBE_F (r) (x87-cmov (logor CF ZF) r))
(defun CMOVP_F (r) (x87-cmov PF r))
(defun CMOVNB_F (r) (x87-cmov (not CF) r))
(defun CMOVNE_F (r) (x87-cmov (not ZF) r))
(defun CMOVNBE_F (r) (x87-cmov (not (logor CF ZF)) r))
(defun CMOVNP_F (r) (x87-cmov (not PF) r))

;;; PACKED AND SCALAR FLOATING-POINT INSTRUCTIONS OF SSE AND AVX
;;
;; The packed operations apply to the 32-bit or 64-bit lanes of the
;; 128-bit operands, the 256-bit operations of AVX to each half. The
;; legacy SSE instructions keep the upper half of the YMM register, the
;; VEX-encoded 128-bit instructions clear it, as set-vex does, and the
;; scalar instructions take the other lanes of the result from their
;; first source.

(defun fp-add (rt x y) (sse-binary 'fadd rt x y))
(defun fp-sub (rt x y) (sse-binary 'fsub rt x y))
(defun fp-mul (rt x y) (sse-binary 'fmul rt x y))
(defun fp-div (rt x y) (sse-binary 'fdiv rt x y))
(defun fp-min (rt x y) (sse-min rt x y))
(defun fp-max (rt x y) (sse-max rt x y))
(defun fp-sqrt (rt x) (sse-unary 'fsqrt rt x))
(defun fp-round (rt x imm) (sse-round-imm rt x imm))

(defmacro fp-lanes (f rt x y)
  "(fp-lanes F RT X Y) applies (F RT XI YI) to the RT-bit lanes of the
   128-bit X and Y"
  (if (= rt 64)
      (concat (f 64 (extract 127 64 x) (extract 127 64 y))
              (f 64 (extract 63 0 x) (extract 63 0 y)))
    (concat (f 32 (extract 127 96 x) (extract 127 96 y))
            (f 32 (extract 95 64 x) (extract 95 64 y))
            (f 32 (extract 63 32 x) (extract 63 32 y))
            (f 32 (extract 31 0 x) (extract 31 0 y)))))

(defmacro fp-ylanes (f rt x y)
  (concat (fp-lanes f rt (cast-high 128 x) (cast-high 128 y))
          (fp-lanes f rt (cast-low 128 x) (cast-low 128 y))))

(defmacro fp-lanes-i (f rt x y i)
  "(fp-lanes-i F RT X Y I) applies (F RT XI YI I) to the lanes"
  (if (= rt 64)
      (concat (f 64 (extract 127 64 x) (extract 127 64 y) i)
              (f 64 (extract 63 0 x) (extract 63 0 y) i))
    (concat (f 32 (extract 127 96 x) (extract 127 96 y) i)
            (f 32 (extract 95 64 x) (extract 95 64 y) i)
            (f 32 (extract 63 32 x) (extract 63 32 y) i)
            (f 32 (extract 31 0 x) (extract 31 0 y) i))))

(defmacro fp-ylanes-i (f rt x y i)
  (concat (fp-lanes-i f rt (cast-high 128 x) (cast-high 128 y) i)
          (fp-lanes-i f rt (cast-low 128 x) (cast-low 128 y) i)))

(defmacro fp-lanes1 (f rt x)
  "(fp-lanes1 F RT X) applies (F RT XI) to the lanes of X"
  (if (= rt 64)
      (concat (f 64 (extract 127 64 x))
              (f 64 (extract 63 0 x)))
    (concat (f 32 (extract 127 96 x))
            (f 32 (extract 95 64 x))
            (f 32 (extract 63 32 x))
            (f 32 (extract 31 0 x)))))

(defmacro fp-ylanes1 (f rt x)
  (concat (fp-lanes1 f rt (cast-high 128 x))
          (fp-lanes1 f rt (cast-low 128 x))))

(defmacro fp-lanes1-i (f rt x i)
  (if (= rt 64)
      (concat (f 64 (extract 127 64 x) i)
              (f 64 (extract 63 0 x) i))
    (concat (f 32 (extract 127 96 x) i)
            (f 32 (extract 95 64 x) i)
            (f 32 (extract 63 32 x) i)
            (f 32 (extract 31 0 x) i))))

(defmacro fp-ylanes1-i (f rt x i)
  (concat (fp-lanes1-i f rt (cast-high 128 x) i)
          (fp-lanes1-i f rt (cast-low 128 x) i)))

(defmacro fp-scalar (f rt x y)
  "(fp-scalar F RT X Y) is X with its low lane (F RT X0 Y0)"
  (concat (extract 127 rt x) (f rt (cast-low rt x) (cast-low rt y))))

(defmacro fp-scalar-i (f rt x y i)
  (concat (extract 127 rt x) (f rt (cast-low rt x) (cast-low rt y) i)))

(defmacro fp-scalar1 (f rt x y)
  "(fp-scalar1 F RT X Y) is X with its low lane (F RT Y0)"
  (concat (extract 127 rt x) (f rt (cast-low rt y))))

(defmacro fp-scalar1-i (f rt x y i)
  (concat (extract 127 rt x) (f rt (cast-low rt y) i)))

(defun fp-load (n b s i off seg) (load-n n (ea b s i off seg)))

;; the comparisons by the predicate of the immediate, its bits 3:0, as
;; the bit 4 only selects the signaling of the exceptions, which are
;; not modeled, the result is a lane of ones, if the predicate holds

(defun fp-predicate (rt x y imm)
  (let ((less (sse-forder rt x y))
        (more (sse-forder rt y x))
        (unordered (logor (sse-is-nan rt x) (sse-is-nan rt y)))
        (equal (not (logor unordered less more))))
    (case (logand imm 15)
      0 equal
      1 less
      2 (logor less equal)
      3 unordered
      4 (not equal)
      5 (not less)
      6 (not (logor less equal))
      7 (not unordered)
      8 (logor equal unordered)
      9 (logor less unordered)
      10 (logor less equal unordered)
      11 0:1
      12 (logor less more)
      13 (logor more equal)
      14 more
      1:1)))

(defun fp-cmp (rt x y imm)
  (if (fp-predicate rt x y imm) (ones rt) (zeros rt)))

;; the conversions of the lanes

(defun fp-sint-to-float (rt x) (sse-convert 'cast_sfloat *sse-rmode* rt rt x))
(defun fp-float-to-sint (rt x) (sse-to-int *sse-rmode* rt rt x))
(defun fp-float-to-sint-rtz (rt x) (sse-to-int 'rtz rt rt x))
(defun fp-int32-to-double (x) (sse-convert 'cast_sfloat *sse-rmode* 32 64 x))
(defun fp-float-to-double (x) (sse-convert 'fconvert *sse-rmode* 32 64 x))
(defun fp-double-to-float (x) (sse-convert 'fconvert *sse-rmode* 64 32 x))
(defun fp-double-to-int32 (x) (sse-to-int *sse-rmode* 64 32 x))
(defun fp-double-to-int32-rtz (x) (sse-to-int 'rtz 64 32 x))

(defmacro fp-widen2 (f x)
  "(fp-widen2 F X) applies F to the two low 32-bit lanes of X"
  (concat (f (extract 63 32 x)) (f (extract 31 0 x))))

(defmacro fp-widen4 (f x)
  (concat (f (extract 127 96 x)) (f (extract 95 64 x))
          (f (extract 63 32 x)) (f (extract 31 0 x))))

(defmacro fp-narrow2 (f x)
  "(fp-narrow2 F X) applies F to the two 64-bit lanes of the 128-bit X,
   the upper half of the result is cleared"
  (concat 0:64 (f (extract 127 64 x)) (f (extract 63 0 x))))

(defmacro fp-narrow4 (f x)
  (concat (f (extract 255 192 x)) (f (extract 191 128 x))
          (f (extract 127 64 x)) (f (extract 63 0 x))))

;; the alternating and the horizontal operations

(defun fp-addsub (rt x y)
  (if (= rt 64)
      (concat (fp-add 64 (extract 127 64 x) (extract 127 64 y))
              (fp-sub 64 (extract 63 0 x) (extract 63 0 y)))
    (concat (fp-add 32 (extract 127 96 x) (extract 127 96 y))
            (fp-sub 32 (extract 95 64 x) (extract 95 64 y))
            (fp-add 32 (extract 63 32 x) (extract 63 32 y))
            (fp-sub 32 (extract 31 0 x) (extract 31 0 y)))))

(defmacro fp-horizontal (f rt x y)
  "(fp-horizontal F RT X Y) applies F to the adjacent pairs of lanes of
   X, the low half of the result, and of Y"
  (if (= rt 64)
      (concat (f 64 (extract 63 0 y) (extract 127 64 y))
              (f 64 (extract 63 0 x) (extract 127 64 x)))
    (concat (f 32 (extract 95 64 y) (extract 127 96 y))
            (f 32 (extract 31 0 y) (extract 63 32 y))
            (f 32 (extract 95 64 x) (extract 127 96 x))
            (f 32 (extract 31 0 x) (extract 63 32 x)))))

(defun fp-hadd (rt x y) (fp-horizontal fp-add rt x y))
(defun fp-hsub (rt x y) (fp-horizontal fp-sub rt x y))

(defmacro fp-yhalves (f rt x y)
  (concat (f rt (cast-high 128 x) (cast-high 128 y))
          (f rt (cast-low 128 x) (cast-low 128 y))))

;; the dot products, the bits 7:4 of the immediate select the products,
;; the others are +0.0, and the bits 3:0 the lanes of the sum, the others
;; are cleared

(defun fp-dot-term (rt x y imm n)
  (if (= (logand (rshift imm n) 1) 1) (fp-mul rt x y) (zeros rt)))

(defun fp-dot-lane (rt sum imm n)
  (if (= (logand (rshift imm n) 1) 1) sum (zeros rt)))

(defun fp-dpps (rt x y imm)
  (let ((s (fp-add 32
                   (fp-add 32 (fp-dot-term 32 (extract 31 0 x) (extract 31 0 y) imm 4)
                           (fp-dot-term 32 (extract 63 32 x) (extract 63 32 y) imm 5))
                   (fp-add 32 (fp-dot-term 32 (extract 95 64 x) (extract 95 64 y) imm 6)
                           (fp-dot-term 32 (extract 127 96 x) (extract 127 96 y) imm 7)))))
    (concat (fp-dot-lane 32 s imm 3) (fp-dot-lane 32 s imm 2)
            (fp-dot-lane 32 s imm 1) (fp-dot-lane 32 s imm 0))))

(defun fp-dppd (rt x y imm)
  (let ((s (fp-add 64 (fp-dot-term 64 (extract 63 0 x) (extract 63 0 y) imm 4)
                   (fp-dot-term 64 (extract 127 64 x) (extract 127 64 y) imm 5))))
    (concat (fp-dot-lane 64 s imm 1) (fp-dot-lane 64 s imm 0))))

(defmacro fp-yhalves-i (f rt x y i)
  (concat (f rt (cast-high 128 x) (cast-high 128 y) i)
          (f rt (cast-low 128 x) (cast-low 128 y) i)))

;; the fused multiply-add, (fp-fma RT A B C) is A * B + C, rounded once,
;; the negations of the products and of the addends flip the signs

(defun fp-fma (rt a b c)
  (intrinsic
   (symbol-concat 'fmad *sse-rmode* *sse-format* (symbol-of-size rt) :sep '_)
   a b c
   :result rt))

;; the NaN operand is the result, as it is, not negated
(defun fp-neg (rt x)
  (if (sse-is-nan rt x) x (logxor x (lshift (cast-unsigned rt 1) (- rt 1)))))

(defun fma-madd (rt a b c) (fp-fma rt a b c))
(defun fma-msub (rt a b c) (fp-fma rt a b (fp-neg rt c)))
(defun fma-nmadd (rt a b c) (fp-fma rt (fp-neg rt a) b c))
(defun fma-nmsub (rt a b c) (fp-fma rt (fp-neg rt a) b (fp-neg rt c)))

(defmacro fma-lanes (f rt a b c)
  (if (= rt 64)
      (concat (f 64 (extract 127 64 a) (extract 127 64 b) (extract 127 64 c))
              (f 64 (extract 63 0 a) (extract 63 0 b) (extract 63 0 c)))
    (concat (f 32 (extract 127 96 a) (extract 127 96 b) (extract 127 96 c))
            (f 32 (extract 95 64 a) (extract 95 64 b) (extract 95 64 c))
            (f 32 (extract 63 32 a) (extract 63 32 b) (extract 63 32 c))
            (f 32 (extract 31 0 a) (extract 31 0 b) (extract 31 0 c)))))

(defmacro fma-ylanes (f rt a b c)
  (concat (fma-lanes f rt (cast-high 128 a) (cast-high 128 b) (cast-high 128 c))
          (fma-lanes f rt (cast-low 128 a) (cast-low 128 b) (cast-low 128 c))))

;; the even lanes of FMADDSUB subtract, the odd ones add, and FMSUBADD
;; the other way around
(defmacro fma-alternate (even odd rt a b c)
  (if (= rt 64)
      (concat (odd 64 (extract 127 64 a) (extract 127 64 b) (extract 127 64 c))
              (even 64 (extract 63 0 a) (extract 63 0 b) (extract 63 0 c)))
    (concat (odd 32 (extract 127 96 a) (extract 127 96 b) (extract 127 96 c))
            (even 32 (extract 95 64 a) (extract 95 64 b) (extract 95 64 c))
            (odd 32 (extract 63 32 a) (extract 63 32 b) (extract 63 32 c))
            (even 32 (extract 31 0 a) (extract 31 0 b) (extract 31 0 c)))))

(defun fma-maddsub (rt a b c) (fma-alternate fma-msub fma-madd rt a b c))
(defun fma-msubadd (rt a b c) (fma-alternate fma-madd fma-msub rt a b c))

(defmacro fma-yalternate (f rt a b c)
  (concat (f rt (cast-high 128 a) (cast-high 128 b) (cast-high 128 c))
          (f rt (cast-low 128 a) (cast-low 128 b) (cast-low 128 c))))

;; the arithmetic, the minimum and the maximum

(defun VADDPSrr (rd x y) (set-vex rd (fp-lanes fp-add 32 x y)))
(defun VADDPSrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-add 32 x (fp-load 128 b s i off seg))))
(defun VADDPSYrr (rd x y) (set$ rd (fp-ylanes fp-add 32 x y)))
(defun VADDPSYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-add 32 x (fp-load 256 b s i off seg))))
(defun VADDPDrr (rd x y) (set-vex rd (fp-lanes fp-add 64 x y)))
(defun VADDPDrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-add 64 x (fp-load 128 b s i off seg))))
(defun VADDPDYrr (rd x y) (set$ rd (fp-ylanes fp-add 64 x y)))
(defun VADDPDYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-add 64 x (fp-load 256 b s i off seg))))
(defun VADDSSrr_Int (rd x y) (set-vex rd (fp-scalar fp-add 32 x y)))
(defun VADDSSrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-add 32 x (fp-load 32 b s i off seg))))
(defun VADDSDrr_Int (rd x y) (set-vex rd (fp-scalar fp-add 64 x y)))
(defun VADDSDrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-add 64 x (fp-load 64 b s i off seg))))
(defun VSUBPSrr (rd x y) (set-vex rd (fp-lanes fp-sub 32 x y)))
(defun VSUBPSrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-sub 32 x (fp-load 128 b s i off seg))))
(defun VSUBPSYrr (rd x y) (set$ rd (fp-ylanes fp-sub 32 x y)))
(defun VSUBPSYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-sub 32 x (fp-load 256 b s i off seg))))
(defun VSUBPDrr (rd x y) (set-vex rd (fp-lanes fp-sub 64 x y)))
(defun VSUBPDrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-sub 64 x (fp-load 128 b s i off seg))))
(defun VSUBPDYrr (rd x y) (set$ rd (fp-ylanes fp-sub 64 x y)))
(defun VSUBPDYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-sub 64 x (fp-load 256 b s i off seg))))
(defun VSUBSSrr_Int (rd x y) (set-vex rd (fp-scalar fp-sub 32 x y)))
(defun VSUBSSrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-sub 32 x (fp-load 32 b s i off seg))))
(defun VSUBSDrr_Int (rd x y) (set-vex rd (fp-scalar fp-sub 64 x y)))
(defun VSUBSDrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-sub 64 x (fp-load 64 b s i off seg))))
(defun VMULPSrr (rd x y) (set-vex rd (fp-lanes fp-mul 32 x y)))
(defun VMULPSrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-mul 32 x (fp-load 128 b s i off seg))))
(defun VMULPSYrr (rd x y) (set$ rd (fp-ylanes fp-mul 32 x y)))
(defun VMULPSYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-mul 32 x (fp-load 256 b s i off seg))))
(defun VMULPDrr (rd x y) (set-vex rd (fp-lanes fp-mul 64 x y)))
(defun VMULPDrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-mul 64 x (fp-load 128 b s i off seg))))
(defun VMULPDYrr (rd x y) (set$ rd (fp-ylanes fp-mul 64 x y)))
(defun VMULPDYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-mul 64 x (fp-load 256 b s i off seg))))
(defun VMULSSrr_Int (rd x y) (set-vex rd (fp-scalar fp-mul 32 x y)))
(defun VMULSSrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-mul 32 x (fp-load 32 b s i off seg))))
(defun VMULSDrr_Int (rd x y) (set-vex rd (fp-scalar fp-mul 64 x y)))
(defun VMULSDrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-mul 64 x (fp-load 64 b s i off seg))))
(defun VDIVPSrr (rd x y) (set-vex rd (fp-lanes fp-div 32 x y)))
(defun VDIVPSrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-div 32 x (fp-load 128 b s i off seg))))
(defun VDIVPSYrr (rd x y) (set$ rd (fp-ylanes fp-div 32 x y)))
(defun VDIVPSYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-div 32 x (fp-load 256 b s i off seg))))
(defun VDIVPDrr (rd x y) (set-vex rd (fp-lanes fp-div 64 x y)))
(defun VDIVPDrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-div 64 x (fp-load 128 b s i off seg))))
(defun VDIVPDYrr (rd x y) (set$ rd (fp-ylanes fp-div 64 x y)))
(defun VDIVPDYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-div 64 x (fp-load 256 b s i off seg))))
(defun VDIVSSrr_Int (rd x y) (set-vex rd (fp-scalar fp-div 32 x y)))
(defun VDIVSSrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-div 32 x (fp-load 32 b s i off seg))))
(defun VDIVSDrr_Int (rd x y) (set-vex rd (fp-scalar fp-div 64 x y)))
(defun VDIVSDrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-div 64 x (fp-load 64 b s i off seg))))
(defun MINPSrr (rd x y) (set$ rd (fp-lanes fp-min 32 x y)))
(defun MINPSrm (rd x b s i off seg) (set$ rd (fp-lanes fp-min 32 x (fp-load 128 b s i off seg))))
(defun VMINPSrr (rd x y) (set-vex rd (fp-lanes fp-min 32 x y)))
(defun VMINPSrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-min 32 x (fp-load 128 b s i off seg))))
(defun VMINPSYrr (rd x y) (set$ rd (fp-ylanes fp-min 32 x y)))
(defun VMINPSYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-min 32 x (fp-load 256 b s i off seg))))
(defun MINPDrr (rd x y) (set$ rd (fp-lanes fp-min 64 x y)))
(defun MINPDrm (rd x b s i off seg) (set$ rd (fp-lanes fp-min 64 x (fp-load 128 b s i off seg))))
(defun VMINPDrr (rd x y) (set-vex rd (fp-lanes fp-min 64 x y)))
(defun VMINPDrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-min 64 x (fp-load 128 b s i off seg))))
(defun VMINPDYrr (rd x y) (set$ rd (fp-ylanes fp-min 64 x y)))
(defun VMINPDYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-min 64 x (fp-load 256 b s i off seg))))
(defun VMINSSrr_Int (rd x y) (set-vex rd (fp-scalar fp-min 32 x y)))
(defun VMINSSrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-min 32 x (fp-load 32 b s i off seg))))
(defun VMINSDrr_Int (rd x y) (set-vex rd (fp-scalar fp-min 64 x y)))
(defun VMINSDrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-min 64 x (fp-load 64 b s i off seg))))
(defun MAXPSrr (rd x y) (set$ rd (fp-lanes fp-max 32 x y)))
(defun MAXPSrm (rd x b s i off seg) (set$ rd (fp-lanes fp-max 32 x (fp-load 128 b s i off seg))))
(defun VMAXPSrr (rd x y) (set-vex rd (fp-lanes fp-max 32 x y)))
(defun VMAXPSrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-max 32 x (fp-load 128 b s i off seg))))
(defun VMAXPSYrr (rd x y) (set$ rd (fp-ylanes fp-max 32 x y)))
(defun VMAXPSYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-max 32 x (fp-load 256 b s i off seg))))
(defun MAXPDrr (rd x y) (set$ rd (fp-lanes fp-max 64 x y)))
(defun MAXPDrm (rd x b s i off seg) (set$ rd (fp-lanes fp-max 64 x (fp-load 128 b s i off seg))))
(defun VMAXPDrr (rd x y) (set-vex rd (fp-lanes fp-max 64 x y)))
(defun VMAXPDrm (rd x b s i off seg) (set-vex rd (fp-lanes fp-max 64 x (fp-load 128 b s i off seg))))
(defun VMAXPDYrr (rd x y) (set$ rd (fp-ylanes fp-max 64 x y)))
(defun VMAXPDYrm (rd x b s i off seg) (set$ rd (fp-ylanes fp-max 64 x (fp-load 256 b s i off seg))))
(defun VMAXSSrr_Int (rd x y) (set-vex rd (fp-scalar fp-max 32 x y)))
(defun VMAXSSrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-max 32 x (fp-load 32 b s i off seg))))
(defun VMAXSDrr_Int (rd x y) (set-vex rd (fp-scalar fp-max 64 x y)))
(defun VMAXSDrm_Int (rd x b s i off seg) (set-vex rd (fp-scalar fp-max 64 x (fp-load 64 b s i off seg))))

;; the square roots and the rounding

(defun SQRTPSr (rd x) (set$ rd (fp-lanes1 fp-sqrt 32 x)))
(defun SQRTPSm (rd b s i off seg) (set$ rd (fp-lanes1 fp-sqrt 32 (fp-load 128 b s i off seg))))
(defun VSQRTPSr (rd x) (set-vex rd (fp-lanes1 fp-sqrt 32 x)))
(defun VSQRTPSm (rd b s i off seg) (set-vex rd (fp-lanes1 fp-sqrt 32 (fp-load 128 b s i off seg))))
(defun VSQRTPSYr (rd x) (set$ rd (fp-ylanes1 fp-sqrt 32 x)))
(defun VSQRTPSYm (rd b s i off seg) (set$ rd (fp-ylanes1 fp-sqrt 32 (fp-load 256 b s i off seg))))
(defun ROUNDPSri (rd x imm) (set$ rd (fp-lanes1-i fp-round 32 x imm)))
(defun ROUNDPSmi (rd b s i off seg imm) (set$ rd (fp-lanes1-i fp-round 32 (fp-load 128 b s i off seg) imm)))
(defun VROUNDPSri (rd x imm) (set-vex rd (fp-lanes1-i fp-round 32 x imm)))
(defun VROUNDPSmi (rd b s i off seg imm) (set-vex rd (fp-lanes1-i fp-round 32 (fp-load 128 b s i off seg) imm)))
(defun VROUNDPSYri (rd x imm) (set$ rd (fp-ylanes1-i fp-round 32 x imm)))
(defun VROUNDPSYmi (rd b s i off seg imm) (set$ rd (fp-ylanes1-i fp-round 32 (fp-load 256 b s i off seg) imm)))
(defun SQRTPDm (rd b s i off seg) (set$ rd (fp-lanes1 fp-sqrt 64 (fp-load 128 b s i off seg))))
(defun VSQRTPDr (rd x) (set-vex rd (fp-lanes1 fp-sqrt 64 x)))
(defun VSQRTPDm (rd b s i off seg) (set-vex rd (fp-lanes1 fp-sqrt 64 (fp-load 128 b s i off seg))))
(defun VSQRTPDYr (rd x) (set$ rd (fp-ylanes1 fp-sqrt 64 x)))
(defun VSQRTPDYm (rd b s i off seg) (set$ rd (fp-ylanes1 fp-sqrt 64 (fp-load 256 b s i off seg))))
(defun ROUNDPDri (rd x imm) (set$ rd (fp-lanes1-i fp-round 64 x imm)))
(defun ROUNDPDmi (rd b s i off seg imm) (set$ rd (fp-lanes1-i fp-round 64 (fp-load 128 b s i off seg) imm)))
(defun VROUNDPDri (rd x imm) (set-vex rd (fp-lanes1-i fp-round 64 x imm)))
(defun VROUNDPDmi (rd b s i off seg imm) (set-vex rd (fp-lanes1-i fp-round 64 (fp-load 128 b s i off seg) imm)))
(defun VROUNDPDYri (rd x imm) (set$ rd (fp-ylanes1-i fp-round 64 x imm)))
(defun VROUNDPDYmi (rd b s i off seg imm) (set$ rd (fp-ylanes1-i fp-round 64 (fp-load 256 b s i off seg) imm)))
(defun VSQRTSSr_Int (rd x y) (set-vex rd (fp-scalar1 fp-sqrt 32 x y)))
(defun VSQRTSSm_Int (rd x b s i off seg) (set-vex rd (fp-scalar1 fp-sqrt 32 x (fp-load 32 b s i off seg))))
(defun ROUNDSSmi_Int (rd x b s i off seg imm) (set$ rd (fp-scalar1-i fp-round 32 x (fp-load 32 b s i off seg) imm)))
(defun VROUNDSSri_Int (rd x y imm) (set-vex rd (fp-scalar1-i fp-round 32 x y imm)))
(defun VROUNDSSmi_Int (rd x b s i off seg imm) (set-vex rd (fp-scalar1-i fp-round 32 x (fp-load 32 b s i off seg) imm)))
(defun VSQRTSDr_Int (rd x y) (set-vex rd (fp-scalar1 fp-sqrt 64 x y)))
(defun VSQRTSDm_Int (rd x b s i off seg) (set-vex rd (fp-scalar1 fp-sqrt 64 x (fp-load 64 b s i off seg))))
(defun ROUNDSDmi_Int (rd x b s i off seg imm) (set$ rd (fp-scalar1-i fp-round 64 x (fp-load 64 b s i off seg) imm)))
(defun VROUNDSDri_Int (rd x y imm) (set-vex rd (fp-scalar1-i fp-round 64 x y imm)))
(defun VROUNDSDmi_Int (rd x b s i off seg imm) (set-vex rd (fp-scalar1-i fp-round 64 x (fp-load 64 b s i off seg) imm)))

;; the comparisons

(defun CMPPSrri (rd x y imm) (set$ rd (fp-lanes-i fp-cmp 32 x y imm)))
(defun CMPPSrmi (rd x b s i off seg imm) (set$ rd (fp-lanes-i fp-cmp 32 x (fp-load 128 b s i off seg) imm)))
(defun VCMPPSrri (rd x y imm) (set-vex rd (fp-lanes-i fp-cmp 32 x y imm)))
(defun VCMPPSrmi (rd x b s i off seg imm) (set-vex rd (fp-lanes-i fp-cmp 32 x (fp-load 128 b s i off seg) imm)))
(defun VCMPPSYrri (rd x y imm) (set$ rd (fp-ylanes-i fp-cmp 32 x y imm)))
(defun VCMPPSYrmi (rd x b s i off seg imm) (set$ rd (fp-ylanes-i fp-cmp 32 x (fp-load 256 b s i off seg) imm)))
(defun CMPPDrri (rd x y imm) (set$ rd (fp-lanes-i fp-cmp 64 x y imm)))
(defun CMPPDrmi (rd x b s i off seg imm) (set$ rd (fp-lanes-i fp-cmp 64 x (fp-load 128 b s i off seg) imm)))
(defun VCMPPDrri (rd x y imm) (set-vex rd (fp-lanes-i fp-cmp 64 x y imm)))
(defun VCMPPDrmi (rd x b s i off seg imm) (set-vex rd (fp-lanes-i fp-cmp 64 x (fp-load 128 b s i off seg) imm)))
(defun VCMPPDYrri (rd x y imm) (set$ rd (fp-ylanes-i fp-cmp 64 x y imm)))
(defun VCMPPDYrmi (rd x b s i off seg imm) (set$ rd (fp-ylanes-i fp-cmp 64 x (fp-load 256 b s i off seg) imm)))
(defun CMPSSrri_Int (rd x y imm) (set$ rd (fp-scalar-i fp-cmp 32 x y imm)))
(defun CMPSSrmi_Int (rd x b s i off seg imm) (set$ rd (fp-scalar-i fp-cmp 32 x (fp-load 32 b s i off seg) imm)))
(defun VCMPSSrri_Int (rd x y imm) (set-vex rd (fp-scalar-i fp-cmp 32 x y imm)))
(defun VCMPSSrmi_Int (rd x b s i off seg imm) (set-vex rd (fp-scalar-i fp-cmp 32 x (fp-load 32 b s i off seg) imm)))
(defun CMPSDrri_Int (rd x y imm) (set$ rd (fp-scalar-i fp-cmp 64 x y imm)))
(defun CMPSDrmi_Int (rd x b s i off seg imm) (set$ rd (fp-scalar-i fp-cmp 64 x (fp-load 64 b s i off seg) imm)))
(defun VCMPSDrri_Int (rd x y imm) (set-vex rd (fp-scalar-i fp-cmp 64 x y imm)))
(defun VCMPSDrmi_Int (rd x b s i off seg imm) (set-vex rd (fp-scalar-i fp-cmp 64 x (fp-load 64 b s i off seg) imm)))

(defun VUCOMISSrr (x y) (compare-floats 32 x y))
(defun VUCOMISSrm (x b s i off seg) (compare-floats 32 x (fp-load 32 b s i off seg)))
(defun VCOMISSrr (x y) (compare-floats 32 x y))
(defun VCOMISSrm (x b s i off seg) (compare-floats 32 x (fp-load 32 b s i off seg)))
(defun VUCOMISDrr (x y) (compare-floats 64 x y))
(defun VUCOMISDrm (x b s i off seg) (compare-floats 64 x (fp-load 64 b s i off seg)))
(defun VCOMISDrr (x y) (compare-floats 64 x y))
(defun VCOMISDrm (x b s i off seg) (compare-floats 64 x (fp-load 64 b s i off seg)))

;; the conversions

(defun CVTDQ2PSrr (rd x) (set$ rd (fp-lanes1 fp-sint-to-float 32 x)))
(defun CVTDQ2PSrm (rd b s i off seg) (set$ rd (fp-lanes1 fp-sint-to-float 32 (fp-load 128 b s i off seg))))
(defun VCVTDQ2PSrr (rd x) (set-vex rd (fp-lanes1 fp-sint-to-float 32 x)))
(defun VCVTDQ2PSrm (rd b s i off seg) (set-vex rd (fp-lanes1 fp-sint-to-float 32 (fp-load 128 b s i off seg))))
(defun VCVTDQ2PSYrr (rd x) (set$ rd (fp-ylanes1 fp-sint-to-float 32 x)))
(defun VCVTDQ2PSYrm (rd b s i off seg) (set$ rd (fp-ylanes1 fp-sint-to-float 32 (fp-load 256 b s i off seg))))
(defun CVTPS2DQrr (rd x) (set$ rd (fp-lanes1 fp-float-to-sint 32 x)))
(defun CVTPS2DQrm (rd b s i off seg) (set$ rd (fp-lanes1 fp-float-to-sint 32 (fp-load 128 b s i off seg))))
(defun VCVTPS2DQrr (rd x) (set-vex rd (fp-lanes1 fp-float-to-sint 32 x)))
(defun VCVTPS2DQrm (rd b s i off seg) (set-vex rd (fp-lanes1 fp-float-to-sint 32 (fp-load 128 b s i off seg))))
(defun VCVTPS2DQYrr (rd x) (set$ rd (fp-ylanes1 fp-float-to-sint 32 x)))
(defun VCVTPS2DQYrm (rd b s i off seg) (set$ rd (fp-ylanes1 fp-float-to-sint 32 (fp-load 256 b s i off seg))))
(defun CVTTPS2DQrr (rd x) (set$ rd (fp-lanes1 fp-float-to-sint-rtz 32 x)))
(defun CVTTPS2DQrm (rd b s i off seg) (set$ rd (fp-lanes1 fp-float-to-sint-rtz 32 (fp-load 128 b s i off seg))))
(defun VCVTTPS2DQrr (rd x) (set-vex rd (fp-lanes1 fp-float-to-sint-rtz 32 x)))
(defun VCVTTPS2DQrm (rd b s i off seg) (set-vex rd (fp-lanes1 fp-float-to-sint-rtz 32 (fp-load 128 b s i off seg))))
(defun VCVTTPS2DQYrr (rd x) (set$ rd (fp-ylanes1 fp-float-to-sint-rtz 32 x)))
(defun VCVTTPS2DQYrm (rd b s i off seg) (set$ rd (fp-ylanes1 fp-float-to-sint-rtz 32 (fp-load 256 b s i off seg))))
(defun CVTDQ2PDrr (rd x) (set$ rd (fp-widen2 fp-int32-to-double x)))
(defun CVTDQ2PDrm (rd b s i off seg) (set$ rd (fp-widen2 fp-int32-to-double (fp-load 64 b s i off seg))))
(defun VCVTDQ2PDrr (rd x) (set-vex rd (fp-widen2 fp-int32-to-double x)))
(defun VCVTDQ2PDrm (rd b s i off seg) (set-vex rd (fp-widen2 fp-int32-to-double (fp-load 64 b s i off seg))))
(defun VCVTDQ2PDYrr (rd x) (set$ rd (fp-widen4 fp-int32-to-double x)))
(defun VCVTDQ2PDYrm (rd b s i off seg) (set$ rd (fp-widen4 fp-int32-to-double (fp-load 128 b s i off seg))))
(defun CVTPS2PDrm (rd b s i off seg) (set$ rd (fp-widen2 fp-float-to-double (fp-load 64 b s i off seg))))
(defun VCVTPS2PDrr (rd x) (set-vex rd (fp-widen2 fp-float-to-double x)))
(defun VCVTPS2PDrm (rd b s i off seg) (set-vex rd (fp-widen2 fp-float-to-double (fp-load 64 b s i off seg))))
(defun VCVTPS2PDYrr (rd x) (set$ rd (fp-widen4 fp-float-to-double x)))
(defun VCVTPS2PDYrm (rd b s i off seg) (set$ rd (fp-widen4 fp-float-to-double (fp-load 128 b s i off seg))))
(defun CVTPD2PSrr (rd x) (set$ rd (fp-narrow2 fp-double-to-float x)))
(defun CVTPD2PSrm (rd b s i off seg) (set$ rd (fp-narrow2 fp-double-to-float (fp-load 128 b s i off seg))))
(defun VCVTPD2PSrr (rd x) (set-vex rd (fp-narrow2 fp-double-to-float x)))
(defun VCVTPD2PSrm (rd b s i off seg) (set-vex rd (fp-narrow2 fp-double-to-float (fp-load 128 b s i off seg))))
(defun VCVTPD2PSYrr (rd x) (set-vex rd (fp-narrow4 fp-double-to-float x)))
(defun VCVTPD2PSYrm (rd b s i off seg) (set-vex rd (fp-narrow4 fp-double-to-float (fp-load 256 b s i off seg))))
(defun CVTPD2DQrr (rd x) (set$ rd (fp-narrow2 fp-double-to-int32 x)))
(defun CVTPD2DQrm (rd b s i off seg) (set$ rd (fp-narrow2 fp-double-to-int32 (fp-load 128 b s i off seg))))
(defun VCVTPD2DQrr (rd x) (set-vex rd (fp-narrow2 fp-double-to-int32 x)))
(defun VCVTPD2DQrm (rd b s i off seg) (set-vex rd (fp-narrow2 fp-double-to-int32 (fp-load 128 b s i off seg))))
(defun VCVTPD2DQYrr (rd x) (set-vex rd (fp-narrow4 fp-double-to-int32 x)))
(defun VCVTPD2DQYrm (rd b s i off seg) (set-vex rd (fp-narrow4 fp-double-to-int32 (fp-load 256 b s i off seg))))
(defun CVTTPD2DQrr (rd x) (set$ rd (fp-narrow2 fp-double-to-int32-rtz x)))
(defun CVTTPD2DQrm (rd b s i off seg) (set$ rd (fp-narrow2 fp-double-to-int32-rtz (fp-load 128 b s i off seg))))
(defun VCVTTPD2DQrr (rd x) (set-vex rd (fp-narrow2 fp-double-to-int32-rtz x)))
(defun VCVTTPD2DQrm (rd b s i off seg) (set-vex rd (fp-narrow2 fp-double-to-int32-rtz (fp-load 128 b s i off seg))))
(defun VCVTTPD2DQYrr (rd x) (set-vex rd (fp-narrow4 fp-double-to-int32-rtz x)))
(defun VCVTTPD2DQYrm (rd b s i off seg) (set-vex rd (fp-narrow4 fp-double-to-int32-rtz (fp-load 256 b s i off seg))))
(defun VCVTSD2SSrr_Int (rd x y) (set-vex rd (concat (extract 127 32 x) (fp-double-to-float (cast-low 64 y)))))
(defun VCVTSD2SSrm_Int (rd x b s i off seg) (set-vex rd (concat (extract 127 32 x) (fp-double-to-float (fp-load 64 b s i off seg)))))
(defun VCVTSS2SDrr_Int (rd x y) (set-vex rd (concat (extract 127 64 x) (fp-float-to-double (cast-low 32 y)))))
(defun VCVTSS2SDrm_Int (rd x b s i off seg) (set-vex rd (concat (extract 127 64 x) (fp-float-to-double (fp-load 32 b s i off seg)))))
(defun VCVTSI2SSrr_Int (rd x y) (set-vex rd (concat (extract 127 32 x) (sse-convert 'cast_sfloat *sse-rmode* 32 32 y))))
(defun VCVTSI2SSrm_Int (rd x b s i off seg) (set-vex rd (concat (extract 127 32 x) (sse-convert 'cast_sfloat *sse-rmode* 32 32 (fp-load 32 b s i off seg)))))
(defun VCVTSI2SDrr_Int (rd x y) (set-vex rd (concat (extract 127 64 x) (sse-convert 'cast_sfloat *sse-rmode* 32 64 y))))
(defun VCVTSI2SDrm_Int (rd x b s i off seg) (set-vex rd (concat (extract 127 64 x) (sse-convert 'cast_sfloat *sse-rmode* 32 64 (fp-load 32 b s i off seg)))))
(defun VCVTSI642SSrr_Int (rd x y) (set-vex rd (concat (extract 127 32 x) (sse-convert 'cast_sfloat *sse-rmode* 64 32 y))))
(defun VCVTSI642SSrm_Int (rd x b s i off seg) (set-vex rd (concat (extract 127 32 x) (sse-convert 'cast_sfloat *sse-rmode* 64 32 (fp-load 64 b s i off seg)))))
(defun VCVTSI642SDrr_Int (rd x y) (set-vex rd (concat (extract 127 64 x) (sse-convert 'cast_sfloat *sse-rmode* 64 64 y))))
(defun VCVTSI642SDrm_Int (rd x b s i off seg) (set-vex rd (concat (extract 127 64 x) (sse-convert 'cast_sfloat *sse-rmode* 64 64 (fp-load 64 b s i off seg)))))
(defun VCVTTSS2SIrr_Int (rd x) (to-int 'rtz 32 32 rd x))
(defun VCVTTSS2SIrm_Int (rd b s i off seg) (to-int 'rtz 32 32 rd (fp-load 32 b s i off seg)))
(defun VCVTTSS2SI64rr_Int (rd x) (to-int 'rtz 32 64 rd x))
(defun VCVTTSS2SI64rm_Int (rd b s i off seg) (to-int 'rtz 32 64 rd (fp-load 32 b s i off seg)))
(defun VCVTTSD2SIrr_Int (rd x) (to-int 'rtz 64 32 rd x))
(defun VCVTTSD2SIrm_Int (rd b s i off seg) (to-int 'rtz 64 32 rd (fp-load 64 b s i off seg)))
(defun VCVTTSD2SI64rr_Int (rd x) (to-int 'rtz 64 64 rd x))
(defun VCVTTSD2SI64rm_Int (rd b s i off seg) (to-int 'rtz 64 64 rd (fp-load 64 b s i off seg)))
(defun VCVTSS2SIrr_Int (rd x) (to-int *sse-rmode* 32 32 rd x))
(defun VCVTSS2SIrm_Int (rd b s i off seg) (to-int *sse-rmode* 32 32 rd (fp-load 32 b s i off seg)))
(defun VCVTSS2SI64rr_Int (rd x) (to-int *sse-rmode* 32 64 rd x))
(defun VCVTSS2SI64rm_Int (rd b s i off seg) (to-int *sse-rmode* 32 64 rd (fp-load 32 b s i off seg)))
(defun VCVTSD2SIrr_Int (rd x) (to-int *sse-rmode* 64 32 rd x))
(defun VCVTSD2SIrm_Int (rd b s i off seg) (to-int *sse-rmode* 64 32 rd (fp-load 64 b s i off seg)))
(defun VCVTSD2SI64rr_Int (rd x) (to-int *sse-rmode* 64 64 rd x))
(defun VCVTSD2SI64rm_Int (rd b s i off seg) (to-int *sse-rmode* 64 64 rd (fp-load 64 b s i off seg)))

;; the alternating, the horizontal and the dot products

(defun ADDSUBPSrr (rd x y) (set$ rd (fp-addsub 32 x y)))
(defun ADDSUBPSrm (rd x b s i off seg) (set$ rd (fp-addsub 32 x (fp-load 128 b s i off seg))))
(defun VADDSUBPSrr (rd x y) (set-vex rd (fp-addsub 32 x y)))
(defun VADDSUBPSrm (rd x b s i off seg) (set-vex rd (fp-addsub 32 x (fp-load 128 b s i off seg))))
(defun VADDSUBPSYrr (rd x y) (set$ rd (fp-yhalves fp-addsub 32 x y)))
(defun VADDSUBPSYrm (rd x b s i off seg) (set$ rd (fp-yhalves fp-addsub 32 x (fp-load 256 b s i off seg))))
(defun ADDSUBPDrr (rd x y) (set$ rd (fp-addsub 64 x y)))
(defun ADDSUBPDrm (rd x b s i off seg) (set$ rd (fp-addsub 64 x (fp-load 128 b s i off seg))))
(defun VADDSUBPDrr (rd x y) (set-vex rd (fp-addsub 64 x y)))
(defun VADDSUBPDrm (rd x b s i off seg) (set-vex rd (fp-addsub 64 x (fp-load 128 b s i off seg))))
(defun VADDSUBPDYrr (rd x y) (set$ rd (fp-yhalves fp-addsub 64 x y)))
(defun VADDSUBPDYrm (rd x b s i off seg) (set$ rd (fp-yhalves fp-addsub 64 x (fp-load 256 b s i off seg))))
(defun HADDPSrr (rd x y) (set$ rd (fp-hadd 32 x y)))
(defun HADDPSrm (rd x b s i off seg) (set$ rd (fp-hadd 32 x (fp-load 128 b s i off seg))))
(defun VHADDPSrr (rd x y) (set-vex rd (fp-hadd 32 x y)))
(defun VHADDPSrm (rd x b s i off seg) (set-vex rd (fp-hadd 32 x (fp-load 128 b s i off seg))))
(defun VHADDPSYrr (rd x y) (set$ rd (fp-yhalves fp-hadd 32 x y)))
(defun VHADDPSYrm (rd x b s i off seg) (set$ rd (fp-yhalves fp-hadd 32 x (fp-load 256 b s i off seg))))
(defun HADDPDrr (rd x y) (set$ rd (fp-hadd 64 x y)))
(defun HADDPDrm (rd x b s i off seg) (set$ rd (fp-hadd 64 x (fp-load 128 b s i off seg))))
(defun VHADDPDrr (rd x y) (set-vex rd (fp-hadd 64 x y)))
(defun VHADDPDrm (rd x b s i off seg) (set-vex rd (fp-hadd 64 x (fp-load 128 b s i off seg))))
(defun VHADDPDYrr (rd x y) (set$ rd (fp-yhalves fp-hadd 64 x y)))
(defun VHADDPDYrm (rd x b s i off seg) (set$ rd (fp-yhalves fp-hadd 64 x (fp-load 256 b s i off seg))))
(defun HSUBPSrr (rd x y) (set$ rd (fp-hsub 32 x y)))
(defun HSUBPSrm (rd x b s i off seg) (set$ rd (fp-hsub 32 x (fp-load 128 b s i off seg))))
(defun VHSUBPSrr (rd x y) (set-vex rd (fp-hsub 32 x y)))
(defun VHSUBPSrm (rd x b s i off seg) (set-vex rd (fp-hsub 32 x (fp-load 128 b s i off seg))))
(defun VHSUBPSYrr (rd x y) (set$ rd (fp-yhalves fp-hsub 32 x y)))
(defun VHSUBPSYrm (rd x b s i off seg) (set$ rd (fp-yhalves fp-hsub 32 x (fp-load 256 b s i off seg))))
(defun HSUBPDrr (rd x y) (set$ rd (fp-hsub 64 x y)))
(defun HSUBPDrm (rd x b s i off seg) (set$ rd (fp-hsub 64 x (fp-load 128 b s i off seg))))
(defun VHSUBPDrr (rd x y) (set-vex rd (fp-hsub 64 x y)))
(defun VHSUBPDrm (rd x b s i off seg) (set-vex rd (fp-hsub 64 x (fp-load 128 b s i off seg))))
(defun VHSUBPDYrr (rd x y) (set$ rd (fp-yhalves fp-hsub 64 x y)))
(defun VHSUBPDYrm (rd x b s i off seg) (set$ rd (fp-yhalves fp-hsub 64 x (fp-load 256 b s i off seg))))
(defun DPPSrri (rd x y imm) (set$ rd (fp-dpps 32 x y imm)))
(defun DPPSrmi (rd x b s i off seg imm) (set$ rd (fp-dpps 32 x (fp-load 128 b s i off seg) imm)))
(defun VDPPSrri (rd x y imm) (set-vex rd (fp-dpps 32 x y imm)))
(defun VDPPSrmi (rd x b s i off seg imm) (set-vex rd (fp-dpps 32 x (fp-load 128 b s i off seg) imm)))
(defun VDPPSYrri (rd x y imm) (set$ rd (fp-yhalves-i fp-dpps 32 x y imm)))
(defun VDPPSYrmi (rd x b s i off seg imm) (set$ rd (fp-yhalves-i fp-dpps 32 x (fp-load 256 b s i off seg) imm)))
(defun DPPDrri (rd x y imm) (set$ rd (fp-dppd 64 x y imm)))
(defun DPPDrmi (rd x b s i off seg imm) (set$ rd (fp-dppd 64 x (fp-load 128 b s i off seg) imm)))
(defun VDPPDrri (rd x y imm) (set-vex rd (fp-dppd 64 x y imm)))
(defun VDPPDrmi (rd x b s i off seg imm) (set-vex rd (fp-dppd 64 x (fp-load 128 b s i off seg) imm)))

;; the fused multiply-add, the 132, 213 and 231 forms multiply the
;; first and the third, the second and the first, the second and the
;; third operands and add the other one, the memory is the third

(defun VFMADD132PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-madd 32 x1 x3 x2)))
(defun VFMADD132PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-madd 32 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMADD132PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-madd 32 x1 x3 x2)))
(defun VFMADD132PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-madd 32 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMADD132PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-madd 64 x1 x3 x2)))
(defun VFMADD132PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-madd 64 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMADD132PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-madd 64 x1 x3 x2)))
(defun VFMADD132PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-madd 64 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMADD132SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-madd 32 (cast-low 32 x1) (cast-low 32 x3) (cast-low 32 x2)))))
(defun VFMADD132SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-madd 32 (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x2)))))
(defun VFMADD132SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-madd 64 (cast-low 64 x1) (cast-low 64 x3) (cast-low 64 x2)))))
(defun VFMADD132SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-madd 64 (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x2)))))
(defun VFMADD213PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-madd 32 x2 x1 x3)))
(defun VFMADD213PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-madd 32 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMADD213PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-madd 32 x2 x1 x3)))
(defun VFMADD213PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-madd 32 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMADD213PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-madd 64 x2 x1 x3)))
(defun VFMADD213PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-madd 64 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMADD213PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-madd 64 x2 x1 x3)))
(defun VFMADD213PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-madd 64 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMADD213SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-madd 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 x3)))))
(defun VFMADD213SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-madd 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg))))))
(defun VFMADD213SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-madd 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 x3)))))
(defun VFMADD213SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-madd 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg))))))
(defun VFMADD231PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-madd 32 x2 x3 x1)))
(defun VFMADD231PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-madd 32 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMADD231PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-madd 32 x2 x3 x1)))
(defun VFMADD231PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-madd 32 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMADD231PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-madd 64 x2 x3 x1)))
(defun VFMADD231PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-madd 64 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMADD231PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-madd 64 x2 x3 x1)))
(defun VFMADD231PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-madd 64 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMADD231SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-madd 32 (cast-low 32 x2) (cast-low 32 x3) (cast-low 32 x1)))))
(defun VFMADD231SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-madd 32 (cast-low 32 x2) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x1)))))
(defun VFMADD231SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-madd 64 (cast-low 64 x2) (cast-low 64 x3) (cast-low 64 x1)))))
(defun VFMADD231SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-madd 64 (cast-low 64 x2) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x1)))))
(defun VFMSUB132PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-msub 32 x1 x3 x2)))
(defun VFMSUB132PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-msub 32 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMSUB132PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-msub 32 x1 x3 x2)))
(defun VFMSUB132PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-msub 32 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMSUB132PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-msub 64 x1 x3 x2)))
(defun VFMSUB132PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-msub 64 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMSUB132PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-msub 64 x1 x3 x2)))
(defun VFMSUB132PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-msub 64 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMSUB132SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-msub 32 (cast-low 32 x1) (cast-low 32 x3) (cast-low 32 x2)))))
(defun VFMSUB132SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-msub 32 (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x2)))))
(defun VFMSUB132SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-msub 64 (cast-low 64 x1) (cast-low 64 x3) (cast-low 64 x2)))))
(defun VFMSUB132SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-msub 64 (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x2)))))
(defun VFMSUB213PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-msub 32 x2 x1 x3)))
(defun VFMSUB213PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-msub 32 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMSUB213PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-msub 32 x2 x1 x3)))
(defun VFMSUB213PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-msub 32 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMSUB213PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-msub 64 x2 x1 x3)))
(defun VFMSUB213PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-msub 64 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMSUB213PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-msub 64 x2 x1 x3)))
(defun VFMSUB213PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-msub 64 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMSUB213SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-msub 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 x3)))))
(defun VFMSUB213SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-msub 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg))))))
(defun VFMSUB213SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-msub 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 x3)))))
(defun VFMSUB213SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-msub 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg))))))
(defun VFMSUB231PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-msub 32 x2 x3 x1)))
(defun VFMSUB231PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-msub 32 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMSUB231PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-msub 32 x2 x3 x1)))
(defun VFMSUB231PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-msub 32 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMSUB231PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-msub 64 x2 x3 x1)))
(defun VFMSUB231PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-msub 64 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMSUB231PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-msub 64 x2 x3 x1)))
(defun VFMSUB231PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-msub 64 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMSUB231SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-msub 32 (cast-low 32 x2) (cast-low 32 x3) (cast-low 32 x1)))))
(defun VFMSUB231SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-msub 32 (cast-low 32 x2) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x1)))))
(defun VFMSUB231SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-msub 64 (cast-low 64 x2) (cast-low 64 x3) (cast-low 64 x1)))))
(defun VFMSUB231SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-msub 64 (cast-low 64 x2) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x1)))))
(defun VFNMADD132PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmadd 32 x1 x3 x2)))
(defun VFNMADD132PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmadd 32 x1 (fp-load 128 b s i off seg) x2)))
(defun VFNMADD132PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmadd 32 x1 x3 x2)))
(defun VFNMADD132PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmadd 32 x1 (fp-load 256 b s i off seg) x2)))
(defun VFNMADD132PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmadd 64 x1 x3 x2)))
(defun VFNMADD132PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmadd 64 x1 (fp-load 128 b s i off seg) x2)))
(defun VFNMADD132PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmadd 64 x1 x3 x2)))
(defun VFNMADD132PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmadd 64 x1 (fp-load 256 b s i off seg) x2)))
(defun VFNMADD132SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-nmadd 32 (cast-low 32 x1) (cast-low 32 x3) (cast-low 32 x2)))))
(defun VFNMADD132SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-nmadd 32 (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x2)))))
(defun VFNMADD132SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-nmadd 64 (cast-low 64 x1) (cast-low 64 x3) (cast-low 64 x2)))))
(defun VFNMADD132SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-nmadd 64 (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x2)))))
(defun VFNMADD213PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmadd 32 x2 x1 x3)))
(defun VFNMADD213PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmadd 32 x2 x1 (fp-load 128 b s i off seg))))
(defun VFNMADD213PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmadd 32 x2 x1 x3)))
(defun VFNMADD213PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmadd 32 x2 x1 (fp-load 256 b s i off seg))))
(defun VFNMADD213PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmadd 64 x2 x1 x3)))
(defun VFNMADD213PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmadd 64 x2 x1 (fp-load 128 b s i off seg))))
(defun VFNMADD213PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmadd 64 x2 x1 x3)))
(defun VFNMADD213PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmadd 64 x2 x1 (fp-load 256 b s i off seg))))
(defun VFNMADD213SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-nmadd 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 x3)))))
(defun VFNMADD213SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-nmadd 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg))))))
(defun VFNMADD213SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-nmadd 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 x3)))))
(defun VFNMADD213SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-nmadd 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg))))))
(defun VFNMADD231PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmadd 32 x2 x3 x1)))
(defun VFNMADD231PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmadd 32 x2 (fp-load 128 b s i off seg) x1)))
(defun VFNMADD231PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmadd 32 x2 x3 x1)))
(defun VFNMADD231PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmadd 32 x2 (fp-load 256 b s i off seg) x1)))
(defun VFNMADD231PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmadd 64 x2 x3 x1)))
(defun VFNMADD231PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmadd 64 x2 (fp-load 128 b s i off seg) x1)))
(defun VFNMADD231PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmadd 64 x2 x3 x1)))
(defun VFNMADD231PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmadd 64 x2 (fp-load 256 b s i off seg) x1)))
(defun VFNMADD231SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-nmadd 32 (cast-low 32 x2) (cast-low 32 x3) (cast-low 32 x1)))))
(defun VFNMADD231SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-nmadd 32 (cast-low 32 x2) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x1)))))
(defun VFNMADD231SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-nmadd 64 (cast-low 64 x2) (cast-low 64 x3) (cast-low 64 x1)))))
(defun VFNMADD231SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-nmadd 64 (cast-low 64 x2) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x1)))))
(defun VFNMSUB132PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmsub 32 x1 x3 x2)))
(defun VFNMSUB132PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmsub 32 x1 (fp-load 128 b s i off seg) x2)))
(defun VFNMSUB132PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmsub 32 x1 x3 x2)))
(defun VFNMSUB132PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmsub 32 x1 (fp-load 256 b s i off seg) x2)))
(defun VFNMSUB132PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmsub 64 x1 x3 x2)))
(defun VFNMSUB132PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmsub 64 x1 (fp-load 128 b s i off seg) x2)))
(defun VFNMSUB132PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmsub 64 x1 x3 x2)))
(defun VFNMSUB132PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmsub 64 x1 (fp-load 256 b s i off seg) x2)))
(defun VFNMSUB132SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-nmsub 32 (cast-low 32 x1) (cast-low 32 x3) (cast-low 32 x2)))))
(defun VFNMSUB132SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-nmsub 32 (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x2)))))
(defun VFNMSUB132SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-nmsub 64 (cast-low 64 x1) (cast-low 64 x3) (cast-low 64 x2)))))
(defun VFNMSUB132SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-nmsub 64 (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x2)))))
(defun VFNMSUB213PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmsub 32 x2 x1 x3)))
(defun VFNMSUB213PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmsub 32 x2 x1 (fp-load 128 b s i off seg))))
(defun VFNMSUB213PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmsub 32 x2 x1 x3)))
(defun VFNMSUB213PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmsub 32 x2 x1 (fp-load 256 b s i off seg))))
(defun VFNMSUB213PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmsub 64 x2 x1 x3)))
(defun VFNMSUB213PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmsub 64 x2 x1 (fp-load 128 b s i off seg))))
(defun VFNMSUB213PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmsub 64 x2 x1 x3)))
(defun VFNMSUB213PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmsub 64 x2 x1 (fp-load 256 b s i off seg))))
(defun VFNMSUB213SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-nmsub 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 x3)))))
(defun VFNMSUB213SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-nmsub 32 (cast-low 32 x2) (cast-low 32 x1) (cast-low 32 (fp-load 32 b s i off seg))))))
(defun VFNMSUB213SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-nmsub 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 x3)))))
(defun VFNMSUB213SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-nmsub 64 (cast-low 64 x2) (cast-low 64 x1) (cast-low 64 (fp-load 64 b s i off seg))))))
(defun VFNMSUB231PSr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmsub 32 x2 x3 x1)))
(defun VFNMSUB231PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmsub 32 x2 (fp-load 128 b s i off seg) x1)))
(defun VFNMSUB231PSYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmsub 32 x2 x3 x1)))
(defun VFNMSUB231PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmsub 32 x2 (fp-load 256 b s i off seg) x1)))
(defun VFNMSUB231PDr (rd x1 x2 x3) (set-vex rd (fma-lanes fma-nmsub 64 x2 x3 x1)))
(defun VFNMSUB231PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-lanes fma-nmsub 64 x2 (fp-load 128 b s i off seg) x1)))
(defun VFNMSUB231PDYr (rd x1 x2 x3) (set$ rd (fma-ylanes fma-nmsub 64 x2 x3 x1)))
(defun VFNMSUB231PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-ylanes fma-nmsub 64 x2 (fp-load 256 b s i off seg) x1)))
(defun VFNMSUB231SSr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 32 x1) (fma-nmsub 32 (cast-low 32 x2) (cast-low 32 x3) (cast-low 32 x1)))))
(defun VFNMSUB231SSm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 32 x1) (fma-nmsub 32 (cast-low 32 x2) (cast-low 32 (fp-load 32 b s i off seg)) (cast-low 32 x1)))))
(defun VFNMSUB231SDr_Int (rd x1 x2 x3) (set-vex rd (concat (extract 127 64 x1) (fma-nmsub 64 (cast-low 64 x2) (cast-low 64 x3) (cast-low 64 x1)))))
(defun VFNMSUB231SDm_Int (rd x1 x2 b s i off seg) (set-vex rd (concat (extract 127 64 x1) (fma-nmsub 64 (cast-low 64 x2) (cast-low 64 (fp-load 64 b s i off seg)) (cast-low 64 x1)))))
(defun VFMADDSUB132PSr (rd x1 x2 x3) (set-vex rd (fma-maddsub 32 x1 x3 x2)))
(defun VFMADDSUB132PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-maddsub 32 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMADDSUB132PSYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-maddsub 32 x1 x3 x2)))
(defun VFMADDSUB132PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-maddsub 32 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMADDSUB132PDr (rd x1 x2 x3) (set-vex rd (fma-maddsub 64 x1 x3 x2)))
(defun VFMADDSUB132PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-maddsub 64 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMADDSUB132PDYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-maddsub 64 x1 x3 x2)))
(defun VFMADDSUB132PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-maddsub 64 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMADDSUB213PSr (rd x1 x2 x3) (set-vex rd (fma-maddsub 32 x2 x1 x3)))
(defun VFMADDSUB213PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-maddsub 32 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMADDSUB213PSYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-maddsub 32 x2 x1 x3)))
(defun VFMADDSUB213PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-maddsub 32 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMADDSUB213PDr (rd x1 x2 x3) (set-vex rd (fma-maddsub 64 x2 x1 x3)))
(defun VFMADDSUB213PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-maddsub 64 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMADDSUB213PDYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-maddsub 64 x2 x1 x3)))
(defun VFMADDSUB213PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-maddsub 64 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMADDSUB231PSr (rd x1 x2 x3) (set-vex rd (fma-maddsub 32 x2 x3 x1)))
(defun VFMADDSUB231PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-maddsub 32 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMADDSUB231PSYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-maddsub 32 x2 x3 x1)))
(defun VFMADDSUB231PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-maddsub 32 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMADDSUB231PDr (rd x1 x2 x3) (set-vex rd (fma-maddsub 64 x2 x3 x1)))
(defun VFMADDSUB231PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-maddsub 64 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMADDSUB231PDYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-maddsub 64 x2 x3 x1)))
(defun VFMADDSUB231PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-maddsub 64 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMSUBADD132PSr (rd x1 x2 x3) (set-vex rd (fma-msubadd 32 x1 x3 x2)))
(defun VFMSUBADD132PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-msubadd 32 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMSUBADD132PSYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-msubadd 32 x1 x3 x2)))
(defun VFMSUBADD132PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-msubadd 32 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMSUBADD132PDr (rd x1 x2 x3) (set-vex rd (fma-msubadd 64 x1 x3 x2)))
(defun VFMSUBADD132PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-msubadd 64 x1 (fp-load 128 b s i off seg) x2)))
(defun VFMSUBADD132PDYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-msubadd 64 x1 x3 x2)))
(defun VFMSUBADD132PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-msubadd 64 x1 (fp-load 256 b s i off seg) x2)))
(defun VFMSUBADD213PSr (rd x1 x2 x3) (set-vex rd (fma-msubadd 32 x2 x1 x3)))
(defun VFMSUBADD213PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-msubadd 32 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMSUBADD213PSYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-msubadd 32 x2 x1 x3)))
(defun VFMSUBADD213PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-msubadd 32 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMSUBADD213PDr (rd x1 x2 x3) (set-vex rd (fma-msubadd 64 x2 x1 x3)))
(defun VFMSUBADD213PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-msubadd 64 x2 x1 (fp-load 128 b s i off seg))))
(defun VFMSUBADD213PDYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-msubadd 64 x2 x1 x3)))
(defun VFMSUBADD213PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-msubadd 64 x2 x1 (fp-load 256 b s i off seg))))
(defun VFMSUBADD231PSr (rd x1 x2 x3) (set-vex rd (fma-msubadd 32 x2 x3 x1)))
(defun VFMSUBADD231PSm (rd x1 x2 b s i off seg) (set-vex rd (fma-msubadd 32 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMSUBADD231PSYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-msubadd 32 x2 x3 x1)))
(defun VFMSUBADD231PSYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-msubadd 32 x2 (fp-load 256 b s i off seg) x1)))
(defun VFMSUBADD231PDr (rd x1 x2 x3) (set-vex rd (fma-msubadd 64 x2 x3 x1)))
(defun VFMSUBADD231PDm (rd x1 x2 b s i off seg) (set-vex rd (fma-msubadd 64 x2 (fp-load 128 b s i off seg) x1)))
(defun VFMSUBADD231PDYr (rd x1 x2 x3) (set$ rd (fma-yalternate fma-msubadd 64 x2 x3 x1)))
(defun VFMSUBADD231PDYm (rd x1 x2 b s i off seg) (set$ rd (fma-yalternate fma-msubadd 64 x2 (fp-load 256 b s i off seg) x1)))
;; the conversions of F16C, of the half-precision floats, VCVTPS2PH
;; rounds by the bits 1:0 of the immediate, or as MXCSR, if its bit 2
;; is set

(defun fp-half-to-float (x) (sse-convert 'fconvert *sse-rmode* 16 32 x))

(defun fp-float-to-half-by (rm x) (sse-convert 'fconvert rm 32 16 x))

(defun fp-float-to-half (x imm)
  (if (= (logand imm 4) 4) (fp-float-to-half-by *sse-rmode* x)
    (case (logand imm 3)
      0 (fp-float-to-half-by 'rne x)
      1 (fp-float-to-half-by 'rtn x)
      2 (fp-float-to-half-by 'rtp x)
      (fp-float-to-half-by 'rtz x))))

(defun fp-halves-to-floats (n x)
  (if (= n 4)
      (concat (fp-half-to-float (extract 63 48 x)) (fp-half-to-float (extract 47 32 x))
              (fp-half-to-float (extract 31 16 x)) (fp-half-to-float (extract 15 0 x)))
    (concat (fp-half-to-float (extract 127 112 x)) (fp-half-to-float (extract 111 96 x))
            (fp-half-to-float (extract 95 80 x)) (fp-half-to-float (extract 79 64 x))
            (fp-half-to-float (extract 63 48 x)) (fp-half-to-float (extract 47 32 x))
            (fp-half-to-float (extract 31 16 x)) (fp-half-to-float (extract 15 0 x)))))

(defun fp-floats-to-halves4 (x imm)
  (concat (fp-float-to-half (extract 127 96 x) imm) (fp-float-to-half (extract 95 64 x) imm)
          (fp-float-to-half (extract 63 32 x) imm) (fp-float-to-half (extract 31 0 x) imm)))

(defun fp-floats-to-halves8 (x imm)
  (concat (fp-floats-to-halves4 (cast-high 128 x) imm)
          (fp-floats-to-halves4 (cast-low 128 x) imm)))

(defun VCVTPH2PSrr (rd x) (set-vex rd (fp-halves-to-floats 4 (cast-low 64 x))))
(defun VCVTPH2PSrm (rd b s i off seg) (set-vex rd (fp-halves-to-floats 4 (fp-load 64 b s i off seg))))
(defun VCVTPH2PSYrr (rd x) (set$ rd (fp-halves-to-floats 8 (cast-low 128 x))))
(defun VCVTPH2PSYrm (rd b s i off seg) (set$ rd (fp-halves-to-floats 8 (fp-load 128 b s i off seg))))
(defun VCVTPS2PHrr (rd x imm) (set-vex rd (cast-unsigned 128 (fp-floats-to-halves4 x imm))))
(defun VCVTPS2PHYrr (rd x imm) (set-vex rd (fp-floats-to-halves8 x imm)))
(defun VCVTPS2PHmr (b s i off seg x imm) (store-n 64 (ea b s i off seg) (fp-floats-to-halves4 x imm)))
(defun VCVTPS2PHYmr (b s i off seg x imm) (store-n 128 (ea b s i off seg) (fp-floats-to-halves8 x imm)))

