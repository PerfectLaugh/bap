(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; A SMALL SUBSET OF ADVANCED SIMD (NEON) INSTRUCTIONS
;;;
;;; Only the data-moving and integer-add forms that show up in compiler-
;;; emitted inline memcpy/initialisation code are modelled here. Lane-wise
;;; addition is implemented with the standard SWAR idiom so that carries do
;;; not propagate across lane boundaries: for a per-lane high-bit mask m,
;;;   a +lane b = ((a & ~m) + (b & ~m)) ^ ((a ^ b) & m)

(defmacro vadd-lanes (rd rn rm mask)
  (set$ rd (logxor (+ (logand rn (lnot mask)) (logand rm (lnot mask)))
                   (logand (logxor rn rm) mask))))

;; 16 lanes of 8 bits.
(defun ADDv16i8 (rd rn rm)
  (vadd-lanes rd rn rm 0x80808080808080808080808080808080:128))

;; 2 lanes of 64 bits.
(defun ADDv2i64 (rd rn rm)
  (vadd-lanes rd rn rm 0x80000000000000008000000000000000:128))

;; Scalar pairwise add: Dd = Qn.d[0] + Qn.d[1].
(defun ADDPv2i64p (dd qn)
  (setd dd (+ (cast-low 64 qn) (cast-high 64 qn))))

;; MOVI Vd.16B, #imm8 : broadcast the 8-bit immediate into all 16 bytes.
(defun MOVIv16b_ns (qd imm)
  (set$ qd (replicate (cast-low 8 imm) 16)))
