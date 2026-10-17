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

;; MOVI and MVNI, the immediate is replicated into the lanes, the
;; 64-bit forms clear the upper half of the register

(defun movi-byte-mask (imm)
  "(movi-byte-mask IMM) is the 64-bit word with the byte i set to ones
   if the bit i of IMM is set"
  (concat (replicate-to-fill (select 7 imm) 8)
          (replicate-to-fill (select 6 imm) 8)
          (replicate-to-fill (select 5 imm) 8)
          (replicate-to-fill (select 4 imm) 8)
          (replicate-to-fill (select 3 imm) 8)
          (replicate-to-fill (select 2 imm) 8)
          (replicate-to-fill (select 1 imm) 8)
          (replicate-to-fill (select 0 imm) 8)))

(defun movi-lane (size imm sh)
  "(movi-lane SIZE IMM SH) is the 8-bit IMM shifted left by SH in a
   lane of SIZE bits"
  (lshift (cast-unsigned size (cast-low 8 imm)) sh))

(defun movi-lane-msl (size imm sh)
  "(movi-lane-msl SIZE IMM SH) is the 8-bit IMM shifted left by the
   amount in the low byte of SH, shifting ones in"
  (let ((amt (logand sh 0xff)))
    (logor (movi-lane size imm amt)
           (lnot (lshift (lnot (cast-unsigned size 0)) amt)))))

(defun movi-q (lane n) (replicate lane n))
(defun movi-d (lane n) (cast-unsigned 128 (replicate lane n)))

(defun MOVIv2d_ns (qd imm) (set$ qd (movi-q (movi-byte-mask imm) 2)))
(defun MOVIv8b_ns (qd imm) (set$ qd (movi-d (cast-low 8 imm) 8)))
(defun MOVIv4i32 (qd imm sh) (set$ qd (movi-q (movi-lane 32 imm sh) 4)))
(defun MOVIv2i32 (qd imm sh) (set$ qd (movi-d (movi-lane 32 imm sh) 2)))
(defun MOVIv8i16 (qd imm sh) (set$ qd (movi-q (movi-lane 16 imm sh) 8)))
(defun MOVIv4i16 (qd imm sh) (set$ qd (movi-d (movi-lane 16 imm sh) 4)))
(defun MOVIv4s_msl (qd imm sh) (set$ qd (movi-q (movi-lane-msl 32 imm sh) 4)))
(defun MOVIv2s_msl (qd imm sh) (set$ qd (movi-d (movi-lane-msl 32 imm sh) 2)))
(defun MVNIv4i32 (qd imm sh) (set$ qd (movi-q (lnot (movi-lane 32 imm sh)) 4)))
(defun MVNIv2i32 (qd imm sh) (set$ qd (movi-d (lnot (movi-lane 32 imm sh)) 2)))
(defun MVNIv8i16 (qd imm sh) (set$ qd (movi-q (lnot (movi-lane 16 imm sh)) 8)))
(defun MVNIv4i16 (qd imm sh) (set$ qd (movi-d (lnot (movi-lane 16 imm sh)) 4)))
(defun MVNIv4s_msl (qd imm sh) (set$ qd (movi-q (lnot (movi-lane-msl 32 imm sh)) 4)))
(defun MVNIv2s_msl (qd imm sh) (set$ qd (movi-d (lnot (movi-lane-msl 32 imm sh)) 2)))
