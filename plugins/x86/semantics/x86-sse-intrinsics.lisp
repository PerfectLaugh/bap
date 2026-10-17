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

(defun MFENCE ()
  (intrinsic 'mfence))

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
