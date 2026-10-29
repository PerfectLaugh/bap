(declare (context (target x86)))
(require x86-common)

(in-package x86-common)

;;; SSE INTEGER, SHUFFLE AND INSERTION INSTRUCTIONS
;;
;; The packed operations apply a function to each lane of the 128-bit
;; operands, the lanes are numbered from the least significant one.

(defmacro lanes8 (op x y)
  "(lanes8 OP X Y) applies OP to each of the 16 bytes of X and Y"
  (concat (op (extract 127 120 x) (extract 127 120 y))
          (op (extract 119 112 x) (extract 119 112 y))
          (op (extract 111 104 x) (extract 111 104 y))
          (op (extract 103 96 x) (extract 103 96 y))
          (op (extract 95 88 x) (extract 95 88 y))
          (op (extract 87 80 x) (extract 87 80 y))
          (op (extract 79 72 x) (extract 79 72 y))
          (op (extract 71 64 x) (extract 71 64 y))
          (op (extract 63 56 x) (extract 63 56 y))
          (op (extract 55 48 x) (extract 55 48 y))
          (op (extract 47 40 x) (extract 47 40 y))
          (op (extract 39 32 x) (extract 39 32 y))
          (op (extract 31 24 x) (extract 31 24 y))
          (op (extract 23 16 x) (extract 23 16 y))
          (op (extract 15 8 x) (extract 15 8 y))
          (op (extract 7 0 x) (extract 7 0 y))))

(defmacro lanes16 (op x y)
  "(lanes16 OP X Y) applies OP to each of the 8 words of X and Y"
  (concat (op (extract 127 112 x) (extract 127 112 y))
          (op (extract 111 96 x) (extract 111 96 y))
          (op (extract 95 80 x) (extract 95 80 y))
          (op (extract 79 64 x) (extract 79 64 y))
          (op (extract 63 48 x) (extract 63 48 y))
          (op (extract 47 32 x) (extract 47 32 y))
          (op (extract 31 16 x) (extract 31 16 y))
          (op (extract 15 0 x) (extract 15 0 y))))

(defmacro lanes32 (op x y)
  "(lanes32 OP X Y) applies OP to each of the 4 doublewords of X and Y"
  (concat (op (extract 127 96 x) (extract 127 96 y))
          (op (extract 95 64 x) (extract 95 64 y))
          (op (extract 63 32 x) (extract 63 32 y))
          (op (extract 31 0 x) (extract 31 0 y))))

(defmacro lanes64 (op x y)
  "(lanes64 OP X Y) applies OP to each of the 2 quadwords of X and Y"
  (concat (op (extract 127 64 x) (extract 127 64 y))
          (op (extract 63 0 x) (extract 63 0 y))))

(defmacro packed-rr (lanes op rd rn rm)
  (set$ rd (lanes op rn rm)))

;; the saturating arithmetic is computed in wider signed numbers, as
;; cast-saturate takes a signed number, two bits wider for the unsigned
;; sums

(defun widen-signed (x) (cast-signed (+ (word-width x) 1) x))
(defun widen-unsigned (x) (cast-unsigned (+ (word-width x) 2) x))

(defun add-ssat (x y)
  (cast-saturate :signed (word-width x) (+ (widen-signed x) (widen-signed y))))
(defun sub-ssat (x y)
  (cast-saturate :signed (word-width x) (- (widen-signed x) (widen-signed y))))
(defun add-usat (x y)
  (cast-saturate :unsigned (word-width x)
                 (+ (widen-unsigned x) (widen-unsigned y))))
(defun sub-usat (x y)
  (if (< x y) (cast-unsigned (word-width x) 0:1) (- x y)))

(defun PADDSBrr (rd rn rm) (packed-rr lanes8 add-ssat rd rn rm))
(defun PADDSWrr (rd rn rm) (packed-rr lanes16 add-ssat rd rn rm))
(defun PSUBSBrr (rd rn rm) (packed-rr lanes8 sub-ssat rd rn rm))
(defun PSUBSWrr (rd rn rm) (packed-rr lanes16 sub-ssat rd rn rm))
(defun PADDUSBrr (rd rn rm) (packed-rr lanes8 add-usat rd rn rm))
(defun PADDUSWrr (rd rn rm) (packed-rr lanes16 add-usat rd rn rm))
(defun PSUBUSBrr (rd rn rm) (packed-rr lanes8 sub-usat rd rn rm))
(defun PSUBUSWrr (rd rn rm) (packed-rr lanes16 sub-usat rd rn rm))

;; multiplications

(defun mul-low (x y) (* x y))
(defun mul-high-signed (x y)
  (let ((w (word-width x)))
    (cast-high w (* (cast-signed (* 2 w) x) (cast-signed (* 2 w) y)))))
(defun mul-high-unsigned (x y)
  (let ((w (word-width x)))
    (cast-high w (* (cast-unsigned (* 2 w) x) (cast-unsigned (* 2 w) y)))))

;; the sum of the products of the signed words in a doubleword
(defun madd-words (x y)
  (+ (* (cast-signed 32 (extract 31 16 x)) (cast-signed 32 (extract 31 16 y)))
     (* (cast-signed 32 (extract 15 0 x)) (cast-signed 32 (extract 15 0 y)))))

(defun PMULLWrr (rd rn rm) (packed-rr lanes16 mul-low rd rn rm))
(defun PMULLDrr (rd rn rm) (packed-rr lanes32 mul-low rd rn rm))
(defun PMULHWrr (rd rn rm) (packed-rr lanes16 mul-high-signed rd rn rm))
(defun PMULHUWrr (rd rn rm) (packed-rr lanes16 mul-high-unsigned rd rn rm))
(defun PMADDWDrr (rd rn rm) (packed-rr lanes32 madd-words rd rn rm))

;; the sum of the absolute differences of the bytes of each quadword
(defun absdiff (x y)
  (cast-unsigned 16 (if (< x y) (- y x) (- x y))))

(defun sad-bytes (x y)
  (cast-unsigned 64
                 (+ (absdiff (extract 63 56 x) (extract 63 56 y))
                    (absdiff (extract 55 48 x) (extract 55 48 y))
                    (absdiff (extract 47 40 x) (extract 47 40 y))
                    (absdiff (extract 39 32 x) (extract 39 32 y))
                    (absdiff (extract 31 24 x) (extract 31 24 y))
                    (absdiff (extract 23 16 x) (extract 23 16 y))
                    (absdiff (extract 15 8 x) (extract 15 8 y))
                    (absdiff (extract 7 0 x) (extract 7 0 y)))))

(defun PSADBWrr (rd rn rm) (packed-rr lanes64 sad-bytes rd rn rm))

;; shuffles of the words, the selector of each lane is two bits of the
;; immediate, the other half of the destination is the one of the source

(defun select-word (x n)
  "(select-word X N) is the word N of the 64-bit X"
  (cast-low 16 (rshift x (* 16 (logand n 3)))))

(defun shuffle-words (x ctl)
  (concat (select-word x (rshift ctl 6))
          (select-word x (rshift ctl 4))
          (select-word x (rshift ctl 2))
          (select-word x ctl)))

(defun PSHUFLWri (rd rn ctl)
  (set$ rd (concat (extract 127 64 rn) (shuffle-words (extract 63 0 rn) ctl))))

(defun PSHUFHWri (rd rn ctl)
  (set$ rd (concat (shuffle-words (extract 127 64 rn) ctl) (extract 63 0 rn))))

;; SHUFPD selects the low quadword from the destination and the high
;; one from the source
(defun select-quad (x n)
  (if (= (logand n 1) 0) (extract 63 0 x) (extract 127 64 x)))

(defun SHUFPDrri (rd rn rm ctl)
  (set$ rd (concat (select-quad rm (rshift ctl 1)) (select-quad rn ctl))))

;; interleaving of the low or high halves

(defun UNPCKLPSrr (rd rn rm)
  (set$ rd (concat (extract 63 32 rm) (extract 63 32 rn)
                   (extract 31 0 rm) (extract 31 0 rn))))
(defun UNPCKHPSrr (rd rn rm)
  (set$ rd (concat (extract 127 96 rm) (extract 127 96 rn)
                   (extract 95 64 rm) (extract 95 64 rn))))
(defun UNPCKLPDrr (rd rn rm)
  (set$ rd (concat (extract 63 0 rm) (extract 63 0 rn))))
(defun UNPCKHPDrr (rd rn rm)
  (set$ rd (concat (extract 127 64 rm) (extract 127 64 rn))))

;; the sign bits of the lanes
(defun MOVMSKPSrr (rd rn)
  (set-gpr rd (cast-unsigned 32 (concat (select 127 rn) (select 95 rn)
                                        (select 63 rn) (select 31 rn)))))
(defun MOVMSKPDrr (rd rn)
  (set-gpr rd (cast-unsigned 32 (concat (select 127 rn) (select 63 rn)))))

;; extraction and insertion of a lane, the index is the immediate
;; modulo the number of lanes

(defun lane-position (size n)
  (* size (logand n (- (/ 128 size) 1))))

(defun extract-lane (size x n)
  (cast-low size (rshift x (lane-position size n))))

(defun insert-lane (size x v n)
  (let ((pos (lane-position size n))
        (mask (lshift (cast-unsigned 128 (ones size)) pos)))
    (logor (logand x (lnot mask))
           (lshift (cast-unsigned 128 (cast-low size v)) pos))))

(defun PEXTRBrri (rd rn n) (set-gpr rd (cast-unsigned 32 (extract-lane 8 rn n))))
(defun PEXTRWrri (rd rn n) (set-gpr rd (cast-unsigned 32 (extract-lane 16 rn n))))
(defun PEXTRDrri (rd rn n) (set-gpr rd (extract-lane 32 rn n)))
(defun PEXTRQrri (rd rn n) (set-gpr rd (extract-lane 64 rn n)))

(defun PINSRBrri (rd rn rm n) (set$ rd (insert-lane 8 rn rm n)))
(defun PINSRWrri (rd rn rm n) (set$ rd (insert-lane 16 rn rm n)))
(defun PINSRDrri (rd rn rm n) (set$ rd (insert-lane 32 rn rm n)))
(defun PINSRQrri (rd rn rm n) (set$ rd (insert-lane 64 rn rm n)))

;;; SHUFFLES, MULTIPLICATIONS, PACKING AND BITWISE OPERATIONS

;; shufps (shuffle packed single precision floating-point values)
;; Example (intel): shufps xmm0, xmm1, 1
;; Reference: Vol.2B 4-647
(defun SHUFPSrri (dst _ src ctl)
  (shufps dst src ctl))

(defun SHUFPSrmi (dst _ base scale index off _ ctl)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (shufps dst src ctl)))

;; the two low words are selected from DST and the two high words
;; from SRC
(defun shufps (dst src ctl)
  (declare (visibility :private))
  (set$ dst (concat
             (select4 src (extract 7 6 ctl))
             (select4 src (extract 5 4 ctl))
             (select4 dst (extract 3 2 ctl))
             (select4 dst (extract 1 0 ctl)))))

;; (select4 R N) selects an Nth 32-bit word from R.
;; Reference: Vol. 2B 4-648
(defun select4 (src ctl)
  (declare (visibility :private))
  (case ctl
    0 (extract 31 0 src)
    1 (extract 63 32 src)
    2 (extract 95 64 src)
    3 (extract 127 96 src)
    (error "expects a 2-bit selector")))

;; pmuludq
;; Reference: Vol. 2B 4-370
(defun PMULDQrr (dst x src)
  (pmul set$ cast-signed dst x src))

(defun PMULDQrm (dst x base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (pmul set$ cast-signed dst x src)))

(defun PMULUDQrr (dst x src)
  (pmul set$ cast-unsigned dst x src))

(defun PMULUDQrm (dst x base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (pmul set$ cast-unsigned dst x src)))

(defun VPMULDQrr (dst x src)
  (pmul setv cast-signed dst x src))

(defun VPMULDQrm (dst x base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (pmul setv cast-signed dst x src)))

(defun VPMULUDQrr (dst x src)
  (pmul setv cast-unsigned dst x src))

(defun VPMULUDQrm (dst x base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (pmul setv cast-unsigned dst x src)))

(defun VPMULDQYrr (dst x src)
  (pmuly cast-signed dst x src))

(defun VPMULDQYrm (dst x base scale index off _)
  (let ((src (load-bits 256 (operand-address base scale index off))))
    (pmuly cast-signed dst x src)))

(defun VPMULUDQYrr (dst x src)
  (pmuly cast-unsigned dst x src))

(defun VPMULUDQYrm (dst x base scale index off _)
  (let ((src (load-bits 256 (operand-address base scale index off))))
    (pmuly cast-unsigned dst x src)))

(defmacro pmul (set cast dst x src)
  (declare (visibility :private))
  (let ((hi (* (cast 64 (extract 95 64 x))
               (cast 64 (extract 95 64 src))))
        (lo (* (cast 64 (extract 31  0 x))
               (cast 64 (extract 31  0 src)))))
    (set dst (concat hi lo))))

(defmacro pmuly (cast dst x src)
  (declare (visibility :private))
  (let ((w4 (* (cast 64 (extract 223 192 x))
               (cast 64 (extract 223 192 src))))
        (w3 (* (cast 64 (extract 159 128 x))
               (cast 64 (extract 159 128 src))))
        (w2 (* (cast 64 (extract 95 64 x))
               (cast 64 (extract 95 64 src))))
        (w1 (* (cast 64 (extract 31  0 x))
               (cast 64 (extract 31  0 src)))))
    (set$ dst (concat w4 w3 w2 w1))))


;; pack{u,s}sdw/pack{u,s}swb
;; converts 4 32-bit words into 8 16-bit words
(defun PACKSSDWrr (dst _ src)
  (set$ dst (packsdw/128 :signed dst src)))

(defun PACKSSDWrm (dst _ base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (set$ dst (packsdw/128 :signed dst src))))

(defun VPACKSSDWrr (dst src1 src2)
  (set-vex dst (packsdw/128 :signed src1 src2)))

(defun VPACKSSDWYrr (dst src1 src2)
  (set$ dst (packsdw/256 :signed src1 src2)))

(defun VPACKSSDWrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 128 (operand-address base scale index off))))
    (set-vex dst (packsdw/128 :signed src1 src2))))

(defun VPACKSSDWYrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 256 (operand-address base scale index off))))
    (set$ dst (packsdw/256 :signed src1 src2))))


(defun PACKUSDWrr (dst _ src)
  (set$ dst (packsdw/128 :unsigned dst src)))

(defun PACKUSDWrm (dst _ base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (set$ dst (packsdw/128 :unsigned dst src))))

(defun VPACKUSDWrr (dst src1 src2)
  (set-vex dst (packsdw/128 :unsigned src1 src2)))

(defun VPACKUSDWYrr (dst src1 src2)
  (set$ dst (packsdw/256 :unsigned src1 src2)))

(defun VPACKUSDWrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 128 (operand-address base scale index off))))
    (set-vex dst (packsdw/128 :unsigned src1 src2))))

(defun VPACKUSDWYrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 256 (operand-address base scale index off))))
    (set$ dst (packsdw/256 :unsigned src1 src2))))

(defun packsdw/128 (kind src1 src2)
  (let ((w0 (extract-saturate kind 16  31  0 src1))
        (w1 (extract-saturate kind 16  63 32 src1))
        (w2 (extract-saturate kind 16  95 64 src1))
        (w3 (extract-saturate kind 16 127 96 src1))
        (w4 (extract-saturate kind 16  31  0 src2))
        (w5 (extract-saturate kind 16  63 32 src2))
        (w6 (extract-saturate kind 16  95 64 src2))
        (w7 (extract-saturate kind 16 127 96 src2)))
    (concat w7 w6 w5 w4 w3 w2 w1 w0)))

(defun packsdw/256 (kind src1 src2)
  (let ((w0  (extract-saturate kind 16  31   0 src1))
        (w1  (extract-saturate kind 16  63  32 src1))
        (w2  (extract-saturate kind 16  95  64 src1))
        (w3  (extract-saturate kind 16 127  96 src1))
        (w4  (extract-saturate kind 16  31   0 src2))
        (w5  (extract-saturate kind 16  63  32 src2))
        (w6  (extract-saturate kind 16  95  64 src2))
        (w7  (extract-saturate kind 16 127  96 src2))
        (w8  (extract-saturate kind 16 159 128 src1))
        (w9  (extract-saturate kind 16 191 160 src1))
        (w10 (extract-saturate kind 16 223 192 src1))
        (w11 (extract-saturate kind 16 255 224 src1))
        (w12 (extract-saturate kind 16 159 128 src2))
        (w13 (extract-saturate kind 16 191 160 src2))
        (w14 (extract-saturate kind 16 223 192 src2))
        (w15 (extract-saturate kind 16 255 224 src2)))
    (concat w15 w14 w13 w12 w11 w10 w9 w8
            w7  w6  w5  w4  w3  w2 w1 w0)))

(defun PACKSSWBrr (dst _ src)
  (set$ dst (packswb/128 :signed dst src)))

(defun VPACKSSWBrr (dst src1 src2)
  (set-vex dst (packswb/128 :signed src1 src2)))

(defun VPACKSSWBYrr (dst src1 src2)
  (set$ dst (packswb/256 :signed src1 src2)))

(defun PACKSSWBrm (dst _ base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (set$ dst (packswb/128 :signed dst src))))

(defun VPACKSSWBrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 128 (operand-address base scale index off))))
    (set-vex dst (packswb/128 :signed src1 src2))))

(defun VPACKSSWBYrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 256 (operand-address base scale index off))))
    (set$ dst (packswb/256 :signed src1 src2))))


(defun PACKUSWBrr (dst _ src)
  (set$ dst (packswb/128 :unsigned dst src)))

(defun VPACKUSWBrr (dst src1 src2)
  (set-vex dst (packswb/128 :unsigned src1 src2)))

(defun VPACKUSWBYrr (dst src1 src2)
  (set$ dst (packswb/256 :unsigned src1 src2)))

(defun PACKUSWBrm (dst _ base scale index off _)
  (let ((src (load-bits 128 (operand-address base scale index off))))
    (set$ dst (packswb/128 :unsigned dst src))))

(defun VPACKUSWBrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 128 (operand-address base scale index off))))
    (set-vex dst (packswb/128 :unsigned src1 src2))))

(defun VPACKUSWBYrm (dst src1 base scale index off _)
  (let ((src2 (load-bits 256 (operand-address base scale index off))))
    (set$ dst (packswb/256 :unsigned src1 src2))))

(defun packswb/128 (kind src1 src2)
  (let ((b0  (extract-saturate kind 8  15   0 src1))
        (b1  (extract-saturate kind 8  31  16 src1))
        (b2  (extract-saturate kind 8  47  32 src1))
        (b3  (extract-saturate kind 8  63  48 src1))
        (b4  (extract-saturate kind 8  79  64 src1))
        (b5  (extract-saturate kind 8  95  80 src1))
        (b6  (extract-saturate kind 8 111  96 src1))
        (b7  (extract-saturate kind 8 127 112 src1))
        (b8  (extract-saturate kind 8  15   0 src2))
        (b9  (extract-saturate kind 8  31  16 src2))
        (b10 (extract-saturate kind 8  47  32 src2))
        (b11 (extract-saturate kind 8  63  48 src2))
        (b12 (extract-saturate kind 8  79  64 src2))
        (b13 (extract-saturate kind 8  95  80 src2))
        (b14 (extract-saturate kind 8 111  96 src2))
        (b15 (extract-saturate kind 8 127 112 src2)))
    (concat b15 b14 b13 b12 b11 b10 b9 b8
            b7  b6  b5  b4  b3  b2 b1 b0)))

(defun packswb/256 (kind src1 src2)
  (let ((b0  (extract-saturate kind 8  15   0 src1))
        (b1  (extract-saturate kind 8  31  16 src1))
        (b2  (extract-saturate kind 8  47  32 src1))
        (b3  (extract-saturate kind 8  63  48 src1))
        (b4  (extract-saturate kind 8  79  64 src1))
        (b5  (extract-saturate kind 8  95  80 src1))
        (b6  (extract-saturate kind 8 111  96 src1))
        (b7  (extract-saturate kind 8 127 112 src1))
        (b8  (extract-saturate kind 8  15   0 src2))
        (b9  (extract-saturate kind 8  31  16 src2))
        (b10 (extract-saturate kind 8  47  32 src2))
        (b11 (extract-saturate kind 8  63  48 src2))
        (b12 (extract-saturate kind 8  79  64 src2))
        (b13 (extract-saturate kind 8  95  80 src2))
        (b14 (extract-saturate kind 8 111  96 src2))
        (b15 (extract-saturate kind 8 127 112 src2))
        (b16 (extract-saturate kind 8 143 128 src1))
        (b17 (extract-saturate kind 8 159 144 src1))
        (b18 (extract-saturate kind 8 175 160 src1))
        (b19 (extract-saturate kind 8 191 176 src1))
        (b20 (extract-saturate kind 8 207 192 src1))
        (b21 (extract-saturate kind 8 223 208 src1))
        (b22 (extract-saturate kind 8 239 224 src1))
        (b23 (extract-saturate kind 8 255 240 src1))
        (b24 (extract-saturate kind 8 143 128 src2))
        (b25 (extract-saturate kind 8 159 144 src2))
        (b26 (extract-saturate kind 8 175 160 src2))
        (b27 (extract-saturate kind 8 191 176 src2))
        (b28 (extract-saturate kind 8 207 192 src2))
        (b29 (extract-saturate kind 8 223 208 src2))
        (b30 (extract-saturate kind 8 239 224 src2))
        (b31 (extract-saturate kind 8 255 240 src2)))
    (concat b31 b30 b29 b28 b27 b26 b25 b24
            b23 b22 b21 b20 b19 b18 b17 b16
            b15 b14 b13 b12 b11 b10  b9  b8
            b7  b6  b5  b4  b3  b2  b1  b0)))

(defun extract-saturate (type size hi lo src)
  (let ((x (extract hi lo src)))
    (cast-saturate type size x)))

;; the 32-bit mode has the registers YMM0-YMM7 only
(defun VZEROUPPER ()
  (declare (context (bits 64)))
  (dolist zero-high-128-bits
    'YMM0 'YMM1 'YMM2  'YMM3  'YMM4  'YMM5  'YMM6  'YMM7
    'YMM8 'YMM9 'YMM10 'YMM11 'YMM12 'YMM13 'YMM14 'YMM15))

(defun VZEROUPPER ()
  (declare (context (bits 32)))
  (dolist zero-high-128-bits
    'YMM0 'YMM1 'YMM2  'YMM3  'YMM4  'YMM5  'YMM6  'YMM7))

(defun zero-high-128-bits (reg)
  (set$ reg (concat 0:128 (cast-low 128 (unquote reg)))))

(defun VZEROALL ()
  (declare (context (bits 64)))
  (dolist zero-register
    'YMM0 'YMM1 'YMM2  'YMM3  'YMM4  'YMM5  'YMM6  'YMM7
    'YMM8 'YMM9 'YMM10 'YMM11 'YMM12 'YMM13 'YMM14 'YMM15))

(defun VZEROALL ()
  (declare (context (bits 32)))
  (dolist zero-register
    'YMM0 'YMM1 'YMM2  'YMM3  'YMM4  'YMM5  'YMM6  'YMM7))

(defun zero-register (reg) (set$ reg 0:256))

;; MOVNTDQ - Store packed Integers Using Non-Temporal Hint
(defun MOVNTDQmr (base scale index off _ src)
  (non-temporal-store-word (operand-address base scale index off) 0 src))

(defun VMOVNTDQmr (base scale index off _ src)
  (non-temporal-store-word (operand-address base scale index off) 0 src))

(defun VMOVNTDQYmr (base scale index off _ src)
  (non-temporal-store-word (operand-address base scale index off) 0 src))

;; to be overriden by specialized analyses
(defun non-temporal-store-word (base off src)
  (store-word (+ base off) src))

;; [v]andp{s,d}
(defun ANDPSrr (rd rn rm)
  (bitwise-rrr set$ ident logand rd rn rm))

(defun ANDPDrr (rd rn rm)
  (bitwise-rrr set$ ident logand rd rn rm))

(defun VANDPSrr (rd rn rm)
  (bitwise-rrr setv ident logand rd rn rm))

(defun VANDPDrr (rd rn rm)
  (bitwise-rrr setv ident logand rd rn rm))

(defun VANDPDYrr (rd rn rm)
  (bitwise-rrr set$ ident logand rd rn rm))

(defun ANDPSrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logand rd rn ptr scale index off))

(defun ANDPDrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logand rd rn ptr scale index off))

(defun VANDPSrm (rd rn ptr scale index off _)
  (bitwise-rrm setv ident logand rd rn ptr scale index off))

(defun VANDPDrm (rd rn ptr scale index off _)
  (bitwise-rrm setv ident logand rd rn ptr scale index off))

(defun VANDPSYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logand rd rn ptr scale index off))

(defun VANDPDYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logand rd rn ptr scale index off))

;; [v]orp{s,d}
(defun ORPSrr (rd rn rm)
  (bitwise-rrr set$ ident logor rd rn rm))

(defun ORPDrr (rd rn rm)
  (bitwise-rrr set$ ident logor rd rn rm))

(defun VORPSrr (rd rn rm)
  (bitwise-rrr setv ident logor rd rn rm))

(defun VORPDrr (rd rn rm)
  (bitwise-rrr setv ident logor rd rn rm))

(defun VORPDYrr (rd rn rm)
  (bitwise-rrr set$ ident logor rd rn rm))

(defun ORPSrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logor rd rn ptr scale index off))

(defun ORPDrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logor rd rn ptr scale index off))

(defun VORPSrm (rd rn ptr scale index off _)
  (bitwise-rrm setv ident logor rd rn ptr scale index off))

(defun VORPDrm (rd rn ptr scale index off _)
  (bitwise-rrm setv ident logor rd rn ptr scale index off))

(defun VORPSYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logor rd rn ptr scale index off))

(defun VORPDYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logor rd rn ptr scale index off))

;; [v]xorp{s,d}
(defun XORPSrr (rd rn rm)
  (bitwise-rrr set$ ident logxor rd rn rm))

(defun XORPDrr (rd rn rm)
  (bitwise-rrr set$ ident logxor rd rn rm))

(defun VXORPSrr (rd rn rm)
  (bitwise-rrr setv ident logxor rd rn rm))

(defun VXORPDrr (rd rn rm)
  (bitwise-rrr setv ident logxor rd rn rm))

(defun VXORPDYrr (rd rn rm)
  (bitwise-rrr set$ ident logxor rd rn rm))

(defun XORPSrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logxor rd rn ptr scale index off))

(defun XORPDrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logxor rd rn ptr scale index off))

(defun VXORPSrm (rd rn ptr scale index off _)
  (bitwise-rrm setv ident logxor rd rn ptr scale index off))

(defun VXORPDrm (rd rn ptr scale index off _)
  (bitwise-rrm setv ident logxor rd rn ptr scale index off))

(defun VXORPSYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logxor rd rn ptr scale index off))

(defun VXORPDYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ ident logxor rd rn ptr scale index off))


;; [v]andnp{s,d}
(defun ANDNPSrr (rd rn rm)
  (bitwise-rrr set$ lnot logand rd rn rm))

(defun ANDNPDrr (rd rn rm)
  (bitwise-rrr set$ lnot logand rd rn rm))

(defun VANDNPSrr (rd rn rm)
  (bitwise-rrr setv lnot logand rd rn rm))

(defun VANDNPDrr (rd rn rm)
  (bitwise-rrr setv lnot logand rd rn rm))

(defun VANDNPDYrr (rd rn rm)
  (bitwise-rrr set$ lnot logand rd rn rm))

(defun ANDNPSrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ lnot logand rd rn ptr scale index off))

(defun ANDNPDrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ lnot logand rd rn ptr scale index off))

(defun VANDNPSrm (rd rn ptr scale index off _)
  (bitwise-rrm setv lnot logand rd rn ptr scale index off))

(defun VANDNPDrm (rd rn ptr scale index off _)
  (bitwise-rrm setv lnot logand rd rn ptr scale index off))

(defun VANDNPSYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ lnot logand rd rn ptr scale index off))

(defun VANDNPDYrm (rd rn ptr scale index off _)
  (bitwise-rrm set$ lnot logand rd rn ptr scale index off))

(defun setv (r x)
  "(setv XMMx X) assigns X to lower bits of XMMx and zeros the upper.
   (word-width X) must be 128"
  (set$ (alias-base-register r)
        (concat (cast-unsigned (word-width x) 0) x)))

(defmacro bitwise-rrr (set opo opi rd rn rm)
  (set rd (opi (opo rn) rm)))

(defmacro bitwise-rrm (set opo opi rd rn ptr scale index off)
  (set rd (opi (opo rn) (load-bits (word-width (unquote rn)) (operand-address ptr scale index off)))))
