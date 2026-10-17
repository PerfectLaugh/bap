(declare (context (target mips-family)))

(defpackage mips (:use core target))
(defpackage llvm-mips32 (:use mips))
(defpackage llvm-mips32le (:use mips))
(defpackage llvm-mips64 (:use mips))
(defpackage llvm-mips64le (:use mips))

(in-package mips)

;;; MIPS32 AND MIPS64 RELEASE 2 INTEGER INSTRUCTIONS
;;
;; The registers are words, 32 or 64 bits. The operations on 32-bit
;; values use the low halves of the 64-bit registers and sign-extend
;; their results, as the 64-bit processors do. The branches are lifted
;; without their delay slots, which the disassembler places, and the
;; offsets of the conditional branches are relative to the branch.

(defun sext32 (x)
  "(sext32 X) is the low 32 bits of X sign-extended to a word"
  (cast-signed (word-width) (cast-low 32 x)))

(defun zext (x)
  "(zext X) is X zero-extended to a word"
  (cast-unsigned (word-width) x))

(defun low32 (x) (cast-low 32 x))

(defun low-mask (n size)
  "(low-mask N SIZE) is the SIZE-bit mask of the N low bits"
  (if (< n size)
      (- (lshift (cast-unsigned size 1:1) n) (cast-unsigned size 1:1))
    (cast-signed size 1:1)))

;; the arithmetic that traps on a signed overflow calls the overflow
;; intrinsic instead of writing the register
(defun signed-overflow (size x y r)
  (logand (= (msb (cast-low size x)) (msb (cast-low size y)))
          (/= (msb (cast-low size x)) (msb (cast-low size r)))))

(defun add-trapping (rd x y)
  (let ((r (+ (low32 x) (low32 y))))
    (if (signed-overflow 32 x y r)
        (intrinsic 'integer-overflow)
      (set$ rd (sext32 r)))))

(defun sub-trapping (rd x y)
  (let ((r (- (low32 x) (low32 y))))
    (if (signed-overflow 32 x (lnot (low32 y)) r)
        (intrinsic 'integer-overflow)
      (set$ rd (sext32 r)))))

(defun dadd-trapping (rd x y)
  (let ((r (+ x y)))
    (if (signed-overflow 64 x y r)
        (intrinsic 'integer-overflow)
      (set$ rd r))))

(defun dsub-trapping (rd x y)
  (let ((r (- x y)))
    (if (signed-overflow 64 x (lnot y) r)
        (intrinsic 'integer-overflow)
      (set$ rd r))))

(defun ADD (rd rs rt) (add-trapping rd rs rt))
(defun ADDi (rt rs imm) (add-trapping rt rs imm))
(defun ADDiu (rt rs imm) (set$ rt (sext32 (+ rs imm))))
(defun ADDu (rd rs rt) (set$ rd (sext32 (+ rs rt))))
(defun SUB (rd rs rt) (sub-trapping rd rs rt))
(defun SUBu (rd rs rt) (set$ rd (sext32 (- rs rt))))
(defun DADD (rd rs rt) (dadd-trapping rd rs rt))
(defun DADDi (rt rs imm) (dadd-trapping rt rs imm))
(defun DADDiu (rt rs imm) (set$ rt (+ rs imm)))
(defun DADDu (rd rs rt) (set$ rd (+ rs rt)))
(defun DSUB (rd rs rt) (dsub-trapping rd rs rt))
(defun DSUBu (rd rs rt) (set$ rd (- rs rt)))

(defun SLT (rd rs rt) (set$ rd (zext (s< rs rt))))
(defun SLTi (rt rs imm) (set$ rt (zext (s< rs imm))))
(defun SLTiu (rt rs imm) (set$ rt (zext (< rs imm))))
(defun SLTu (rd rs rt) (set$ rd (zext (< rs rt))))
(defun LUi (rt imm) (set$ rt (sext32 (lshift imm 16))))

;; the immediates of the logical operations are zero-extended
(defun AND (rd rs rt) (set$ rd (logand rs rt)))
(defun ANDi (rt rs imm) (set$ rt (logand rs imm)))
(defun OR (rd rs rt) (set$ rd (logor rs rt)))
(defun ORi (rt rs imm) (set$ rt (logor rs imm)))
(defun XOR (rd rs rt) (set$ rd (logxor rs rt)))
(defun XORi (rt rs imm) (set$ rt (logxor rs imm)))
(defun NOR (rd rs rt) (set$ rd (lnot (logor rs rt))))

;; shifts and rotations, the variable amounts are taken modulo the size
(defun SLL (rd rt sa) (set$ rd (sext32 (lshift (low32 rt) sa))))
(defun SRL (rd rt sa) (set$ rd (sext32 (rshift (low32 rt) sa))))
(defun SRA (rd rt sa) (set$ rd (sext32 (arshift (low32 rt) sa))))
(defun ROTR (rd rt sa) (set$ rd (sext32 (rotate-right (low32 rt) sa))))
(defun SLLV (rd rt rs) (SLL rd rt (logand rs 31)))
(defun SRLV (rd rt rs) (SRL rd rt (logand rs 31)))
(defun SRAV (rd rt rs) (SRA rd rt (logand rs 31)))
(defun ROTRV (rd rt rs) (ROTR rd rt (logand rs 31)))

(defun DSLL (rd rt sa) (set$ rd (lshift rt sa)))
(defun DSRL (rd rt sa) (set$ rd (rshift rt sa)))
(defun DSRA (rd rt sa) (set$ rd (arshift rt sa)))
(defun DROTR (rd rt sa) (set$ rd (rotate-right rt sa)))
(defun DSLL32 (rd rt sa) (DSLL rd rt (+ sa 32)))
(defun DSRL32 (rd rt sa) (DSRL rd rt (+ sa 32)))
(defun DSRA32 (rd rt sa) (DSRA rd rt (+ sa 32)))
(defun DROTR32 (rd rt sa) (DROTR rd rt (+ sa 32)))
(defun DSLLV (rd rt rs) (DSLL rd rt (logand rs 63)))
(defun DSRLV (rd rt rs) (DSRL rd rt (logand rs 63)))
(defun DSRAV (rd rt rs) (DSRA rd rt (logand rs 63)))
(defun DROTRV (rd rt rs) (DROTR rd rt (logand rs 63)))

;; multiplication and division, the results are in HI and LO

(defun set-hilo (high low)
  (set HI (sext32 high))
  (set LO (sext32 low)))

(defmacro mult (cast rs rt)
  (let ((p (* (cast 64 (low32 rs)) (cast 64 (low32 rt)))))
    (set-hilo (cast-high 32 p) (cast-low 32 p))))

(defmacro dmult (cast rs rt)
  (let ((p (* (cast 128 rs) (cast 128 rt))))
    (set HI (cast-high 64 p))
    (set LO (cast-low 64 p))))

(defun MULT (rs rt) (mult cast-signed rs rt))
(defun MULTu (rs rt) (mult cast-unsigned rs rt))
(defun DMULT (rs rt) (dmult cast-signed rs rt))
(defun DMULTu (rs rt) (dmult cast-unsigned rs rt))

;; the quotient is rounded toward zero and the remainder has the sign of
;; the dividend, the results of a division by zero are unpredictable
(defun SDIV (rs rt)
  (let ((x (low32 rs))
        (y (low32 rt))
        (q (s/ x y)))
    (set-hilo (- x (* q y)) q)))

(defun UDIV (rs rt)
  (let ((x (low32 rs))
        (y (low32 rt))
        (q (/ x y)))
    (set-hilo (- x (* q y)) q)))

(defun DSDIV (rs rt)
  (let ((q (s/ rs rt)))
    (set HI (- rs (* q rt)))
    (set LO q)))

(defun DUDIV (rs rt)
  (let ((q (/ rs rt)))
    (set HI (- rs (* q rt)))
    (set LO q)))

(defun MFHI (rd) (set$ rd HI))
(defun MFLO (rd) (set$ rd LO))
(defun MTHI (rs) (set HI rs))
(defun MTLO (rs) (set LO rs))

(defun MUL (rd rs rt) (set$ rd (sext32 (* (low32 rs) (low32 rt)))))

;; HI and LO accumulate a 64-bit product
(defmacro accumulate (op cast rs rt)
  (let ((acc (concat (low32 HI) (low32 LO)))
        (p (* (cast 64 (low32 rs)) (cast 64 (low32 rt))))
        (r (op acc p)))
    (set-hilo (cast-high 32 r) (cast-low 32 r))))

(defun MADD (rs rt) (accumulate + cast-signed rs rt))
(defun MADDU (rs rt) (accumulate + cast-unsigned rs rt))
(defun MSUB (rs rt) (accumulate - cast-signed rs rt))
(defun MSUBU (rs rt) (accumulate - cast-unsigned rs rt))

;; bit operations

(defun CLZ (rd rs) (set$ rd (zext (clz (low32 rs)))))
(defun CLO (rd rs) (set$ rd (zext (clz (lnot (low32 rs))))))
(defun DCLZ (rd rs) (set$ rd (zext (clz rs))))
(defun DCLO (rd rs) (set$ rd (zext (clz (lnot rs)))))
(defun SEB (rd rt) (set$ rd (cast-signed (word-width) (cast-low 8 rt))))
(defun SEH (rd rt) (set$ rd (cast-signed (word-width) (cast-low 16 rt))))

(defun swap-bytes-in-halves (x)
  "swaps the bytes of each 16-bit half of X"
  (let ((m (cast-unsigned (word-width x) 0x00ff00ff00ff00ff)))
    (logor (logand (rshift x 8) m) (lshift (logand x m) 8))))

(defun WSBH (rd rt) (set$ rd (sext32 (swap-bytes-in-halves (low32 rt)))))
(defun DSBH (rd rt) (set$ rd (swap-bytes-in-halves rt)))
(defun DSHD (rd rt)
  (set$ rd (concat (extract 15 0 rt) (extract 31 16 rt)
                   (extract 47 32 rt) (extract 63 48 rt))))

(defun extract-field (x pos size)
  (logand (rshift x pos) (low-mask size (word-width x))))

(defun insert-field (x y pos size)
  "(insert-field X Y POS SIZE) replaces the SIZE bits of X at POS with
   the low SIZE bits of Y"
  (let ((m (lshift (low-mask size (word-width x)) pos)))
    (logor (logand x (lnot m)) (logand (lshift y pos) m))))

(defun EXT (rt rs pos size) (set$ rt (sext32 (extract-field (low32 rs) pos size))))
(defun INS (rt rs pos size _)
  (set$ rt (sext32 (insert-field (low32 rt) (low32 rs) pos size))))
(defun DEXT (rt rs pos size) (set$ rt (extract-field rs pos size)))
;; the disassembler decodes DINSM and DINSU as DINS, without the tied operand
(defun DINS (rt rs pos size) (set$ rt (insert-field rt rs pos size)))

(defun MOVN_I_I (rd rs rt _) (when (not (is-zero rt)) (set$ rd rs)))
(defun MOVZ_I_I (rd rs rt _) (when (is-zero rt) (set$ rd rs)))

;; loads and stores

(defun LB (rt base off) (set$ rt (cast-signed (word-width) (load-byte (+ base off)))))
(defun LBu (rt base off) (set$ rt (zext (load-byte (+ base off)))))
(defun LH (rt base off)
  (set$ rt (cast-signed (word-width) (cast-low 16 (load-bits 16 (+ base off))))))
(defun LHu (rt base off) (set$ rt (zext (cast-low 16 (load-bits 16 (+ base off))))))
(defun LW (rt base off) (set$ rt (sext32 (load-bits 32 (+ base off)))))
(defun LWu (rt base off) (set$ rt (zext (low32 (load-bits 32 (+ base off))))))
(defun LD (rt base off) (set$ rt (cast-low 64 (load-bits 64 (+ base off)))))
(defun LL (rt base off) (LW rt base off))
(defun LLD (rt base off) (LD rt base off))

(defun SB (rt base off) (store-byte (+ base off) (cast-low 8 rt)))
(defun SH (rt base off) (store-word (+ base off) (cast-low 16 rt)))
(defun SW (rt base off) (store-word (+ base off) (low32 rt)))
(defun SD (rt base off) (store-word (+ base off) (cast-low 64 rt)))

;; the store-conditional succeeds, as the reservation isn't modeled
(defun SC (rt _ base off)
  (SW rt base off)
  (set$ rt (zext 1:1)))

(defun SCD (rt _ base off)
  (SD rt base off)
  (set$ rt (zext 1:1)))

;; The unaligned loads and stores access the bytes of the aligned word
;; that contains the address from the address to an end of the word, the
;; left variants the bytes in the most significant part of the register,
;; the right ones in the least significant part. For a big-endian word,
;; the left part starts at the address, so the register is shifted by
;; the offset of the address in the word, for a little-endian word, by
;; the size less one less the offset.

(defun big-endian ()
  "the bi-endian targets are big-endian by default"
  true)

(defun big-endian ()
  (declare (context (endianness le)))
  false)

(defun left-shift (n addr)
  "the shift in bits of the left part of an N-byte word at ADDR"
  (let ((k (logand addr (- n 1))))
    (* 8 (if (big-endian) k (- (- n 1) k)))))

(defun right-shift (n addr)
  "the shift in bits of the right part of an N-byte word at ADDR"
  (let ((k (logand addr (- n 1))))
    (* 8 (if (big-endian) (- (- n 1) k) k))))

(defun aligned (n addr) (logand addr (lnot (- n 1))))

(defun load-left (size rt addr)
  (let ((n (/ size 8))
        (s (left-shift n addr))
        (w (cast-low size (load-bits size (aligned n addr))))
        (old (cast-low size rt)))
    (logor (lshift w s)
           (logand old (lnot (lshift (cast-signed size 1:1) s))))))

(defun load-right (size rt addr)
  (let ((n (/ size 8))
        (s (right-shift n addr))
        (w (cast-low size (load-bits size (aligned n addr))))
        (old (cast-low size rt))
        (m (rshift (cast-signed size 1:1) s)))
    (logor (rshift w s) (logand old (lnot m)))))

(defun store-left (size rt addr)
  (let ((n (/ size 8))
        (a (aligned n addr))
        (s (left-shift n addr))
        (w (cast-low size (load-bits size a)))
        (m (rshift (cast-signed size 1:1) s)))
    (store-word a (logor (logand w (lnot m))
                         (rshift (cast-low size rt) s)))))

(defun store-right (size rt addr)
  (let ((n (/ size 8))
        (a (aligned n addr))
        (s (right-shift n addr))
        (w (cast-low size (load-bits size a)))
        (m (lshift (cast-signed size 1:1) s)))
    (store-word a (logor (logand w (lnot m))
                         (lshift (cast-low size rt) s)))))

(defun LWL (rt base off) (set$ rt (sext32 (load-left 32 rt (+ base off)))))
(defun LWR (rt base off) (set$ rt (sext32 (load-right 32 rt (+ base off)))))
(defun LDL (rt base off) (set$ rt (load-left 64 rt (+ base off))))
(defun LDR (rt base off) (set$ rt (load-right 64 rt (+ base off))))
(defun SWL (rt base off) (store-left 32 rt (+ base off)))
(defun SWR (rt base off) (store-right 32 rt (+ base off)))
(defun SDL (rt base off) (store-left 64 rt (+ base off)))
(defun SDR (rt base off) (store-right 64 rt (+ base off)))

;; branches and jumps, the link is the address after the delay slot

(defun link () (+ (get-program-counter) 8))

(defun branch (cnd off)
  (when cnd (exec-addr (+ (get-program-counter) off))))

(defun BEQ (rs rt off) (branch (= rs rt) off))
(defun BNE (rs rt off) (branch (/= rs rt) off))
(defun BGEZ (rs off) (branch (s>= rs 0) off))
(defun BGTZ (rs off) (branch (s> rs 0) off))
(defun BLEZ (rs off) (branch (s<= rs 0) off))
(defun BLTZ (rs off) (branch (s< rs 0) off))

;; the likely branches nullify their delay slots if they are not taken
(defun BEQL (rs rt off) (BEQ rs rt off))
(defun BNEL (rs rt off) (BNE rs rt off))
(defun BGEZL (rs off) (BGEZ rs off))
(defun BGTZL (rs off) (BGTZ rs off))
(defun BLEZL (rs off) (BLEZ rs off))
(defun BLTZL (rs off) (BLTZ rs off))

;; the link is written whether the branch is taken or not
(defun BGEZAL (rs off)
  (let ((cnd (s>= rs 0)))
    (set RA (link))
    (branch cnd off)))

(defun BLTZAL (rs off)
  (let ((cnd (s< rs 0)))
    (set RA (link))
    (branch cnd off)))

(defun J (target) (exec-addr target))
(defun JAL (target)
  (set RA (link))
  (exec-addr target))

(defun JR (rs) (exec-addr rs))
(defun JALR (rd rs)
  (let ((dst rs))
    (set$ rd (link))
    (exec-addr dst)))

;; the other instructions

(defun SYNC (_) (empty))
(defun EHB () (empty))
(defun SYSCALL (code) (intrinsic 'syscall code))
(defun BREAK (code _) (intrinsic 'breakpoint code))
(defun TEQ (rs rt code) (when (= rs rt) (intrinsic 'trap code)))
(defun TNE (rs rt code) (when (/= rs rt) (intrinsic 'trap code)))
