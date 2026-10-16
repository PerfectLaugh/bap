(declare (context (target arm-family)
                  (bits 64)))


(in-package aarch64)

;;; LOADS, MOVES, STORES

;; LD...

(defun LDRXui (dst reg off)
  (set$ dst (load-word (+ reg (lshift off 3)))))

(defun LDRSWui (dst base off)
  (set$ dst (cast-signed
             (word)
             (load-hword (+ base (lshift off 2))))))

(defun LDRWui (dst reg off)
  (setw dst
        (cast-unsigned (word) (load-hword (+ reg (lshift off 2))))))

(defun LDRBBui (dst reg off)
  (setw dst
        (cast-unsigned (word) (load-byte (+ reg off)))))

(defun LDRHHui (dst reg off)
  (setw dst
        (cast-unsigned (word) (load-bits 16 (+ reg (lshift off 1))))))

;; unscaled (LDUR*) loads: the 9-bit offset is already decoded as a
;; signed value and is not scaled by the access size.
(defun LDURXi (dst reg off)
  (set$ dst (load-word (+ reg off))))

(defun LDURWi (dst reg off)
  (setw dst (cast-unsigned (word) (load-hword (+ reg off)))))

(defun LDURHHi (dst reg off)
  (setw dst (cast-unsigned (word) (load-bits 16 (+ reg off)))))

(defun LDURBBi (dst reg off)
  (setw dst (cast-unsigned (word) (load-byte (+ reg off)))))

(defun LDRBBroX (dst reg off _ _)
  (set$ dst
        (cast-unsigned (word) (load-byte (+ reg off)))))

(defun LDRWroX (rt rn rm _ shift)
  (setw rt (cast-unsigned (word) (load-hword (+ rn (lshift rm (* shift 2)))))))

;; register-offset byte loads where the index is a W register that is
;; sign- or zero-extended according to the option bit (1 = SXTW).
(defun LDRBBroW (rt rn rm signed _)
  (let ((idx (if signed (signed-extend 32 rm) (unsigned-extend 32 rm))))
    (setw rt (cast-unsigned (word) (load-byte (+ rn idx))))))

;; post-indexed loads: access [base], then write base+simm back to the
;; first (tied) operand, which is the base register.
(defun LDRBBpost (wb dst base simm)
  (setw dst (cast-unsigned (word) (load-byte base)))
  (set$ wb (+ base simm)))

(defun LDRHHpost (wb dst base simm)
  (setw dst (cast-unsigned (word) (load-bits 16 base)))
  (set$ wb (+ base simm)))

(defun LDPXpost (dst r1 r2 base off)
  (let ((addr base)
        (off (lshift off 3)))
    (set$ r1 (load-word addr))
    (set$ r2 (load-word (+ addr (sizeof word))))
    (set$ dst (+ dst off))))

(defun LDPXi (r1 r2 base off)
  (let ((addr (+ base (lshift off 3))))
    (set$ r1 (load-word addr))
    (set$ r2 (load-word (+ addr (sizeof word))))))

(defun LDPWi (r1 r2 base off)
  (let ((addr (+ base (lshift off 2))))
    (setw r1 (cast-unsigned (word) (load-hword addr)))
    (setw r2 (cast-unsigned (word) (load-hword (+ addr 4))))))

(defun LDRXroX (rt rn rm _ shift)
  (set$ rt (load-word (+ rn (lshift rm (* shift 3))))))

;; Register-offset loads and stores. The address is the base plus the
;; index, which is shifted by the log2 of the access size (scale) when
;; the S bit (shift) is set. The index of the ro*W forms is a W register
;; that is sign-extended (SXTW) when the option bit (signed) is set and
;; zero-extended (UXTW) otherwise. The index of the ro*X forms is used
;; as is (LSL or SXTX).

(defun roW-address (rn rm signed shift scale)
  (+ rn (lshift (if signed (signed-extend 32 rm) (unsigned-extend 32 rm))
                (* shift scale))))

(defun roX-address (rn rm shift scale)
  (+ rn (lshift rm (* shift scale))))

(defun LDRXroW (rt rn rm signed shift)
  (set$ rt (load-word (roW-address rn rm signed shift 3))))

(defun LDRWroW (rt rn rm signed shift)
  (setw rt (cast-unsigned (word) (load-hword (roW-address rn rm signed shift 2)))))

(defun LDRHHroW (rt rn rm signed shift)
  (setw rt (cast-unsigned (word) (load-bits 16 (roW-address rn rm signed shift 1)))))

(defun LDRHHroX (rt rn rm _ shift)
  (setw rt (cast-unsigned (word) (load-bits 16 (roX-address rn rm shift 1)))))

(defun LDRSWroW (rt rn rm signed shift)
  (set$ rt (cast-signed (word) (load-hword (roW-address rn rm signed shift 2)))))

(defun LDRSWroX (rt rn rm _ shift)
  (set$ rt (cast-signed (word) (load-hword (roX-address rn rm shift 2)))))

(defun LDRSHXroW (rt rn rm signed shift)
  (set$ rt (cast-signed (word) (load-bits 16 (roW-address rn rm signed shift 1)))))

(defun LDRSHXroX (rt rn rm _ shift)
  (set$ rt (cast-signed (word) (load-bits 16 (roX-address rn rm shift 1)))))

(defun LDRSHWroW (rt rn rm signed shift)
  (setw rt (cast-unsigned (word)
                          (cast-signed 32 (load-bits 16 (roW-address rn rm signed shift 1))))))

(defun LDRSHWroX (rt rn rm _ shift)
  (setw rt (cast-unsigned (word)
                          (cast-signed 32 (load-bits 16 (roX-address rn rm shift 1))))))

(defun LDRSBXroW (rt rn rm signed shift)
  (set$ rt (cast-signed (word) (load-byte (roW-address rn rm signed shift 0)))))

(defun LDRSBXroX (rt rn rm _ shift)
  (set$ rt (cast-signed (word) (load-byte (roX-address rn rm shift 0)))))

(defun LDRSBWroW (rt rn rm signed shift)
  (setw rt (cast-unsigned (word)
                          (cast-signed 32 (load-byte (roW-address rn rm signed shift 0))))))

(defun LDRSBWroX (rt rn rm _ shift)
  (setw rt (cast-unsigned (word)
                          (cast-signed 32 (load-byte (roX-address rn rm shift 0))))))

(defun STRXroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 3) rt))

(defun STRWroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 2) (cast-low 32 rt)))

(defun STRWroX (rt rn rm _ shift)
  (store-word (roX-address rn rm shift 2) (cast-low 32 rt)))

(defun STRHHroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 1) (cast-low 16 rt)))

(defun STRHHroX (rt rn rm _ shift)
  (store-word (roX-address rn rm shift 1) (cast-low 16 rt)))

;; the prefetch hints have no effect on the semantics
(defun PRFMroW (_ _ _ _ _) (empty))
(defun PRFMroX (_ _ _ _ _) (empty))

;; MOV...

(defmacro MOVZ*i (set dst imm off)
  (set dst (lshift imm off)))

(defun MOVZWi (dst imm off) (MOVZ*i setw dst imm off))
(defun MOVZXi (dst imm off) (MOVZ*i set$ dst imm off))

(defmacro MOVN*i (set dst imm off)
  (set dst (lnot (lshift imm off))))

(defun MOVNWi (dst imm off) (MOVN*i setw dst imm off))
(defun MOVNXi (dst imm off) (MOVN*i set$ dst imm off))

(defmacro MOVK*i (set width dst reg imm off)
  "Inserts the 16-bit imm at bit position off of reg, keeping the other
   bits. (set, width) select the X-form (set$, 64) or the W-form (setw, 32);
   the W-form writes through setw so that the upper 32 bits are cleared."
  (let ((mask (lnot (lshift (cast-unsigned width 0xffff:16) off))))
    (set dst (logor (logand (cast-low width reg) mask)
                    (cast-low width (lshift (cast-unsigned width imm) off))))))

(defun MOVKWi (dst reg imm off) (MOVK*i setw 32 dst reg imm off))
(defun MOVKXi (dst reg imm off) (MOVK*i set$ 64 dst reg imm off))

;; ST...

(defun STRBBui (src reg off)
  (store-byte (+ reg off) src))

(defun STPXpre (dst t1 t2 _ off)
  (let ((off (lshift off 3)))
    (store-word (+ dst off) t1)
    (store-word (+ dst off (sizeof word)) t2)
    (set$ dst (+ dst off))))

(defun STPXi (t1 t2 base off)
  (let ((off (lshift off 3)))
    (store-word (+ base off) t1)
    (store-word (+ base off (sizeof word)) t2)))

(defun STPWi (t1 t2 base off)
  (let ((off (lshift off 2)))
    (store-word (+ base off) (cast-low 32 t1))
    (store-word (+ base off 4) (cast-low 32 t2))))

(defun STRXui (src reg off)
  (let ((off (lshift off 3)))
    (store-word (+ reg off) src)))

(defun STRWui (src reg off)
  (let ((off (lshift off 2)))
    (store-word (+ reg off) (cast-low 32 src))))

(defun STRHHui (src reg off)
  (store-word (+ reg (lshift off 1)) (cast-low 16 src)))

(defun STRXroX (rt rn rm _ shift)
  (store-word (+ rn (lshift rm (* shift 3))) rt))

(defun STRBBroX (rt rn rm _ _)
  (store-byte (+ rn rm) (cast-low 8 rt)))

(defun STRBBroW (rt rn rm signed _)
  (let ((idx (if signed (signed-extend 32 rm) (unsigned-extend 32 rm))))
    (store-byte (+ rn idx) (cast-low 8 rt))))

(defun STRBBpost (wb src base simm)
  (store-byte base (cast-low 8 src))
  (set$ wb (+ base simm)))

;; 128-bit (Q) and 64-bit (D) SIMD element loads/stores. These only move
;; data, so they are modelled as plain loads/stores of the whole element.
(defun LDRQui (dst reg off)
  (set$ dst (load-bits 128 (+ reg (lshift off 4)))))

(defun STRQui (src reg off)
  (store-word (+ reg (lshift off 4)) (cast-low 128 src)))

(defun LDRQroX (rt rn rm _ shift)
  (set$ rt (load-bits 128 (+ rn (lshift rm (* shift 4))))))

(defun STRQroX (rt rn rm _ shift)
  (store-word (+ rn (lshift rm (* shift 4))) (cast-low 128 rt)))

(defun LDRQroW (rt rn rm signed shift)
  (set$ rt (load-bits 128 (roW-address rn rm signed shift 4))))

(defun STRQroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 4) (cast-low 128 rt)))

(defun LDRDroW (rt rn rm signed shift)
  (setd rt (load-word (roW-address rn rm signed shift 3))))

(defun LDRDroX (rt rn rm _ shift)
  (setd rt (load-word (roX-address rn rm shift 3))))

(defun LDRSroW (rt rn rm signed shift)
  (setd rt (load-hword (roW-address rn rm signed shift 2))))

(defun LDRSroX (rt rn rm _ shift)
  (setd rt (load-hword (roX-address rn rm shift 2))))

(defun LDRHroW (rt rn rm signed shift)
  (setd rt (load-bits 16 (roW-address rn rm signed shift 1))))

(defun LDRHroX (rt rn rm _ shift)
  (setd rt (load-bits 16 (roX-address rn rm shift 1))))

(defun LDRBroW (rt rn rm signed shift)
  (setd rt (load-byte (roW-address rn rm signed shift 0))))

(defun LDRBroX (rt rn rm _ shift)
  (setd rt (load-byte (roX-address rn rm shift 0))))

(defun STRDroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 3) (cast-low 64 rt)))

(defun STRDroX (rt rn rm _ shift)
  (store-word (roX-address rn rm shift 3) (cast-low 64 rt)))

(defun STRSroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 2) (cast-low 32 rt)))

(defun STRSroX (rt rn rm _ shift)
  (store-word (roX-address rn rm shift 2) (cast-low 32 rt)))

(defun STRHroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 1) (cast-low 16 rt)))

(defun STRHroX (rt rn rm _ shift)
  (store-word (roX-address rn rm shift 1) (cast-low 16 rt)))

(defun STRBroW (rt rn rm signed shift)
  (store-word (roW-address rn rm signed shift 0) (cast-low 8 rt)))

(defun STRBroX (rt rn rm _ shift)
  (store-word (roX-address rn rm shift 0) (cast-low 8 rt)))

(defun LDRDui (dst reg off)
  (setd dst (load-word (+ reg (lshift off 3)))))

(defun STRDui (src reg off)
  (store-word (+ reg (lshift off 3)) (cast-low 64 src)))

(defmacro STUR*i (src base off size)
  "Takes `size` bits from src and stores at base + off"
  (store-word (+ base off) (cast-low size src)))

(defun STURXi  (src base off) (STUR*i src base off 64))

(defun STURWi  (src base off) (STUR*i src base off 32))

(defun STURHHi  (src base off) (STUR*i src base off 16))

(defun STURBBi (src base off) (STUR*i src base off 8))
