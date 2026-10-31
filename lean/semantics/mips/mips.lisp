(declare (context (target mips-family)))

(defpackage mips (:use core target))
(defpackage llvm-mips32 (:use mips))
(defpackage llvm-mips32le (:use mips))
(defpackage llvm-mips64 (:use mips))
(defpackage llvm-mips64le (:use mips))
(defpackage llvm-mips32r6 (:use mips))
(defpackage llvm-mips32r6le (:use mips))
(defpackage llvm-mips64r6 (:use mips))
(defpackage llvm-mips64r6le (:use mips))

(require bits)

(in-package mips)

;; the release 6 targets, whose instructions are defined at the end of
;; the file, and whose FPU is of IEEE 754-2008, see below. They also
;; load `mips-r6`, which says so.
(defun release6 () false)

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
        (intrinsic 'integer-overflow :aborts)
      (set$ rd (sext32 r)))))

(defun sub-trapping (rd x y)
  (let ((r (- (low32 x) (low32 y))))
    (if (signed-overflow 32 x (lnot (low32 y)) r)
        (intrinsic 'integer-overflow :aborts)
      (set$ rd (sext32 r)))))

(defun dadd-trapping (rd x y)
  (let ((r (+ x y)))
    (if (signed-overflow 64 x y r)
        (intrinsic 'integer-overflow :aborts)
      (set$ rd r))))

(defun dsub-trapping (rd x y)
  (let ((r (- x y)))
    (if (signed-overflow 64 x (lnot y) r)
        (intrinsic 'integer-overflow :aborts)
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
;; the dividend, the results of a division by zero, and of the overflow
;; of the signed one, are unpredictable: they are of the division by 1,
;; as of QEMU, i.e., the dividend and 0, instead of a fault
(defun divisor (signed x y)
  "the divisor Y, or 1 if Y is 0 or if the signed X / Y overflows"
  (let ((bad (logor (is-zero y)
                    (logand signed
                            (logand (= y (lnot (cast-unsigned (word-width y) 0)))
                                    (= x (lshift (cast-unsigned (word-width x) 1)
                                                 (- (word-width x) 1)))))))
        (m (neg (cast-unsigned (word-width y) bad))))
    (logor (logand m (cast-unsigned (word-width y) 1)) (logand (lnot m) y))))

(defun SDIV (rs rt)
  (let ((x (low32 rs))
        (y (divisor true x (low32 rt)))
        (q (s/ x y)))
    (set-hilo (- x (* q y)) q)))

(defun UDIV (rs rt)
  (let ((x (low32 rs))
        (y (divisor false x (low32 rt)))
        (q (/ x y)))
    (set-hilo (- x (* q y)) q)))

(defun DSDIV (rs rt)
  (let ((y (divisor true rs rt))
        (q (s/ rs y)))
    (set HI (- rs (* q y)))
    (set LO q)))

(defun DUDIV (rs rt)
  (let ((y (divisor false rs rt))
        (q (/ rs y)))
    (set HI (- rs (* q y)))
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

;; the likely calls nullify their delay slots if they are not taken
(defun BGEZALL (rs off) (BGEZAL rs off))
(defun BLTZALL (rs off) (BLTZAL rs off))

(defun region (target)
  "the target of J and JAL, whose upper bits are of the address of the
   delay slot, as the instruction encodes only the lower 28 bits, e.g.,
   of the code at the top of the address space"
  (logor (logand (+ (get-program-counter) 4) (lnot 0x0fffffff)) target))

(defun RDHWR (rt hwr sel)
  "reads the hardware register 29, UserLocal, e.g., the thread pointer
   of Linux, the other hardware registers are not modeled"
  (when (= (symbol hwr) 'HWR29)
    (set$ rt USERLOCAL)))

(defun J (target) (exec-addr (region target)))
(defun JAL (target)
  (set RA (link))
  (exec-addr (region target)))

(defun JR (rs) (exec-addr rs))
(defun JALR (rd rs)
  (let ((dst rs))
    (set$ rd (link))
    (exec-addr dst)))

;; the other instructions

(defun SYNC (_) (empty))
(defun EHB () (empty))
(defun SYSCALL (code) (intrinsic 'syscall code))
(defun BREAK (code _) (intrinsic 'breakpoint code :aborts))
(defun TEQ (rs rt code) (when (= rs rt) (intrinsic 'trap code :aborts)))
(defun TNE (rs rt code) (when (/= rs rt) (intrinsic 'trap code :aborts)))

;;; FLOATING-POINT INSTRUCTIONS (COP1)
;;
;; The operands of the instructions name the registers as LLVM does:
;; F<n> is the n-th 32-bit register, the single precision values; D<n>
;; is the n-th even-odd pair of the 32-bit registers, F<2n> and
;; F<2n+1>, the doubles of the 32-bit FPU (Status.FR = 0); D<n>_64 is
;; the n-th 64-bit register of the 64-bit FPU (Status.FR = 1), whose
;; opcodes end in D64. The target declares only the registers F0-F31,
;; which are words, i.e., 32-bit on MIPS32 and 64-bit on MIPS64, so a
;; double on MIPS32 is the pair of the registers that starts at the
;; register of its operand, and on MIPS64 the register itself, and a
;; single on MIPS64 is the low half of the register, whose high half is
;; kept when the single is written (the manual leaves it unpredictable).
;;
;; The condition codes are the registers FCC0-FCC7, the bits of FCSR,
;; named by the operands of the instructions, FCSR itself isn't
;; declared, so its other fields aren't modeled: the rounding
;; mode is to nearest (the reset value of FCSR.RM), and the exceptions
;; aren't modeled, they are disabled at the reset. The NaNs are of the
;; legacy encoding of the Release 2 (FCSR.NAN2008 = 0), whose quiet
;; bit, the most significant bit of the fraction, is set in the
;; signaling NaNs: an operation, whose operand is a signaling NaN, or
;; which is invalid, e.g., 0/0, returns the default NaN, 0x7FBFFFFF or
;; 0x7FF7FFFFFFFFFFFF, and else the quiet NaN of its first operand,
;; that is a NaN. The Release 6 has the NaNs of IEEE 754-2008
;; (FCSR.NAN2008 = 1), whose quiet bit is clear in the signaling NaNs:
;; a signaling NaN operand is quieted, i.e., its quiet bit is set,
;; instead, the default NaN is 0x7FC00000 or 0x7FF8000000000000, and
;; the invalid conversions to integers saturate, a NaN converts to 0.
;;
;; The values are chosen with fp-select, which masks them, instead of
;; with a dynamic if, as Primus, which evaluates both arms of an
;; expression, fails on the variables of a branch, that isn't taken.

(defun fpr (r)
  "(fpr R) is the symbol of the F register, that holds the single,
   or the low word or the whole of the double, of the operand R"
  (case (symbol r)
    'F0 'F0  'F1 'F1  'F2 'F2  'F3 'F3
    'F4 'F4  'F5 'F5  'F6 'F6  'F7 'F7
    'F8 'F8  'F9 'F9  'F10 'F10  'F11 'F11
    'F12 'F12  'F13 'F13  'F14 'F14  'F15 'F15
    'F16 'F16  'F17 'F17  'F18 'F18  'F19 'F19
    'F20 'F20  'F21 'F21  'F22 'F22  'F23 'F23
    'F24 'F24  'F25 'F25  'F26 'F26  'F27 'F27
    'F28 'F28  'F29 'F29  'F30 'F30  'F31 'F31
    'D0 'F0  'D1 'F2  'D2 'F4  'D3 'F6
    'D4 'F8  'D5 'F10  'D6 'F12  'D7 'F14
    'D8 'F16  'D9 'F18  'D10 'F20  'D11 'F22
    'D12 'F24  'D13 'F26  'D14 'F28  'D15 'F30
    'D0_64 'F0  'D1_64 'F1  'D2_64 'F2  'D3_64 'F3
    'D4_64 'F4  'D5_64 'F5  'D6_64 'F6  'D7_64 'F7
    'D8_64 'F8  'D9_64 'F9  'D10_64 'F10  'D11_64 'F11
    'D12_64 'F12  'D13_64 'F13  'D14_64 'F14  'D15_64 'F15
    'D16_64 'F16  'D17_64 'F17  'D18_64 'F18  'D19_64 'F19
    'D20_64 'F20  'D21_64 'F21  'D22_64 'F22  'D23_64 'F23
    'D24_64 'F24  'D25_64 'F25  'D26_64 'F26  'D27_64 'F27
    'D28_64 'F28  'D29_64 'F29  'D30_64 'F30  'D31_64 'F31))

(defun fpr-next (s)
  "(fpr-next S) is the symbol of the F register after the register S"
  (case (symbol s)
    'F0 'F1  'F1 'F2  'F2 'F3  'F3 'F4
    'F4 'F5  'F5 'F6  'F6 'F7  'F7 'F8
    'F8 'F9  'F9 'F10  'F10 'F11  'F11 'F12
    'F12 'F13  'F13 'F14  'F14 'F15  'F15 'F16
    'F16 'F17  'F17 'F18  'F18 'F19  'F19 'F20
    'F20 'F21  'F21 'F22  'F22 'F23  'F23 'F24
    'F24 'F25  'F25 'F26  'F26 'F27  'F27 'F28
    'F28 'F29  'F29 'F30  'F30 'F31))

;; the registers

(defun fpr64 ()
  "true if the F registers are 64-bit, also on the MIPS32 of the
   Release 6"
  (logor (= (word-width) 64) (release6)))

(defun get-s (r)
  "(get-s R) is the single of the operand R"
  (cast-low 32 (unquote (fpr r))))

(defun get-d (r)
  "(get-d R) is the double of the operand R"
  (let ((s (fpr r)))
    (if (fpr64)
        (cast-low 64 (unquote s))
      (concat (unquote (fpr-next s)) (unquote s)))))

(defun get-hi (r)
  "(get-hi R) is the high word of the double of the operand R"
  (cast-high 32 (get-d r)))

;; the register is named by a symbol, so it is an argument, and not a
;; variable of a let, which a set$ would assign instead
(defun set-fpr (s x) (set$ s x))

(defun set-s (r x)
  "(set-s R X) writes the single X to the operand R"
  (let ((s (fpr r)))
    (if (fpr64)
        (set-fpr s (concat (cast-high 32 (unquote s)) (cast-low 32 x)))
      (set-fpr s (cast-low 32 x)))))

(defun set-d (r x)
  "(set-d R X) writes the double X to the operand R"
  (let ((s (fpr r)))
    (if (fpr64)
        (set-fpr s (cast-low 64 x))
      (prog (set-fpr s (cast-low 32 x))
            (set-fpr (fpr-next s) (cast-high 32 x))))))

(defun set-hi (r x)
  "(set-hi R X) writes X to the high word of the double of the operand R"
  (let ((s (fpr r)))
    (if (fpr64)
        (set$ s (concat (cast-low 32 x) (cast-low 32 (unquote s))))
      (set$ (fpr-next s) (cast-low 32 x)))))

;; the condition codes, which are 1-bit
(defun fcc (cc) (not (is-zero (unquote cc))))
(defun set-fcc (cc x) (set$ cc x))

;; the values

(defun fp-select (c x y)
  "(fp-select C X Y) is X if C is true and Y otherwise, X and Y must
   have the same width"
  (let ((m (neg (cast-unsigned (word-width x) c))))
    (logor (logand m x) (logand (lnot m) y))))

(defun fp-frac (x)
  "the number of the fraction bits of the single or the double X"
  (if (= (word-width x) 32) 23 52))

(defun fp-nan (x)
  "(fp-nan X) is true if X is a NaN"
  (let ((f (fp-frac x)))
    (logand (= (extract (- (word-width x) 2) f x)
               (lnot (cast-unsigned (- (word-width x) f 1) 0)))
            (not (is-zero (cast-low f x))))))

(defun fp-quiet-bit (x)
  "(fp-quiet-bit X) is the most significant bit of the fraction of X"
  (select (- (fp-frac x) 1) x))

(defun fp-snan (x)
  "(fp-snan X) is true if X is a signaling NaN"
  (logand (fp-nan x)
          (if (release6) (not (fp-quiet-bit x)) (fp-quiet-bit x))))

(defun fp-default-nan (x)
  "the default NaN in the format of X"
  (if (release6)
      (if (= (word-width x) 32)
          (cast-low 32 0x7fc00000)
        0x7ff8000000000000:64)
    (if (= (word-width x) 32)
        (cast-low 32 0x7fbfffff)
      0x7ff7ffffffffffff:64)))

(defun fp-quiet (x)
  "(fp-quiet X) is the signaling NaN X quieted, which is the default NaN
   of the legacy encoding"
  (if (release6)
      (logor x (lshift (cast-unsigned (word-width x) 1:1) (- (fp-frac x) 1)))
    (fp-default-nan x)))

(defun fp-lt (x y)
  "(fp-lt X Y) is true if X < Y, false if they are unordered"
  (intrinsic (symbol-concat 'forder 'ieee754_binary (fp-size (word-width x))
                            :sep '_)
             x y :result 1))

(defun fp-neg (x) (concat (lnot (msb x)) (cast-low (- (word-width x) 1) x)))
(defun fp-abs (x) (concat 0:1 (cast-low (- (word-width x) 1) x)))

(defun fp-result1 (r x)
  "(fp-result1 R X) is the result R of an operation on X or the NaN"
  (fp-select (fp-snan x) (fp-quiet x)
    (fp-select (fp-nan x) x
      (fp-select (fp-nan r) (fp-default-nan x) r))))

(defun fp-result2 (r x y)
  "(fp-result2 R X Y) is the result R of an operation on X and Y or the
   NaN"
  (fp-select (fp-snan x) (fp-quiet x)
    (fp-select (fp-snan y) (fp-quiet y)
    (fp-select (fp-nan x) x
      (fp-select (fp-nan y) y
        (fp-select (fp-nan r) (fp-default-nan x) r))))))

(defun fp-size (n)
  (case n
    8 '8
    32 '32
    64 '64))

(defun fp-intrinsic2 (name x y)
  "(fp-intrinsic2 NAME X Y) calls the intrinsic of Primus, that runs the
   operation NAME on X and Y, rounded to nearest, exactly"
  (intrinsic (symbol-concat name 'rne 'ieee754_binary
                            (fp-size (word-width x)) :sep '_)
             x y :result (word-width x)))

(defun fp-add (x y) (fp-result2 (fp-intrinsic2 'fadd x y) x y))
(defun fp-sub (x y) (fp-result2 (fp-intrinsic2 'fsub x y) x y))
(defun fp-mul (x y) (fp-result2 (fp-intrinsic2 'fmul x y) x y))
(defun fp-div (x y) (fp-result2 (fp-intrinsic2 'fdiv x y) x y))
(defun fp-sqrt (x)
  (fp-result1 (intrinsic (symbol-concat 'fsqrt 'rne 'ieee754_binary
                                        (fp-size (word-width x)) :sep '_)
                         x :result (word-width x))
              x))

;; the multiply-add of the Release 2 isn't fused, it rounds the product
;; and the sum, the negated forms negate the result, also a NaN
(defun fp-madd (r s t) (fp-add (fp-mul s t) r))
(defun fp-msub (r s t) (fp-sub (fp-mul s t) r))

;; ARITHMETIC

(defun FADD_S (fd fs ft) (set-s fd (fp-add (get-s fs) (get-s ft))))
(defun FADD_D32 (fd fs ft) (set-d fd (fp-add (get-d fs) (get-d ft))))
(defun FADD_D64 (fd fs ft) (set-d fd (fp-add (get-d fs) (get-d ft))))
(defun FSUB_S (fd fs ft) (set-s fd (fp-sub (get-s fs) (get-s ft))))
(defun FSUB_D32 (fd fs ft) (set-d fd (fp-sub (get-d fs) (get-d ft))))
(defun FSUB_D64 (fd fs ft) (set-d fd (fp-sub (get-d fs) (get-d ft))))
(defun FMUL_S (fd fs ft) (set-s fd (fp-mul (get-s fs) (get-s ft))))
(defun FMUL_D32 (fd fs ft) (set-d fd (fp-mul (get-d fs) (get-d ft))))
(defun FMUL_D64 (fd fs ft) (set-d fd (fp-mul (get-d fs) (get-d ft))))
(defun FDIV_S (fd fs ft) (set-s fd (fp-div (get-s fs) (get-s ft))))
(defun FDIV_D32 (fd fs ft) (set-d fd (fp-div (get-d fs) (get-d ft))))
(defun FDIV_D64 (fd fs ft) (set-d fd (fp-div (get-d fs) (get-d ft))))
(defun FSQRT_S (fd fs) (set-s fd (fp-sqrt (get-s fs))))
(defun FSQRT_D32 (fd fs) (set-d fd (fp-sqrt (get-d fs))))
(defun FSQRT_D64 (fd fs) (set-d fd (fp-sqrt (get-d fs))))

;; the sign of a NaN is changed too, as the legacy ABS and NEG do
(defun FABS_S (fd fs) (set-s fd (fp-abs (get-s fs))))
(defun FABS_D32 (fd fs) (set-d fd (fp-abs (get-d fs))))
(defun FABS_D64 (fd fs) (set-d fd (fp-abs (get-d fs))))
(defun FNEG_S (fd fs) (set-s fd (fp-neg (get-s fs))))
(defun FNEG_D32 (fd fs) (set-d fd (fp-neg (get-d fs))))
(defun FNEG_D64 (fd fs) (set-d fd (fp-neg (get-d fs))))

;; (MADD fd fr fs ft) is fs * ft + fr
(defun MADD_S (fd fr fs ft) (set-s fd (fp-madd (get-s fr) (get-s fs) (get-s ft))))
(defun MADD_D32 (fd fr fs ft) (set-d fd (fp-madd (get-d fr) (get-d fs) (get-d ft))))
(defun MADD_D64 (fd fr fs ft) (set-d fd (fp-madd (get-d fr) (get-d fs) (get-d ft))))
(defun MSUB_S (fd fr fs ft) (set-s fd (fp-msub (get-s fr) (get-s fs) (get-s ft))))
(defun MSUB_D32 (fd fr fs ft) (set-d fd (fp-msub (get-d fr) (get-d fs) (get-d ft))))
(defun MSUB_D64 (fd fr fs ft) (set-d fd (fp-msub (get-d fr) (get-d fs) (get-d ft))))
(defun NMADD_S (fd fr fs ft) (set-s fd (fp-neg (fp-madd (get-s fr) (get-s fs) (get-s ft)))))
(defun NMADD_D32 (fd fr fs ft) (set-d fd (fp-neg (fp-madd (get-d fr) (get-d fs) (get-d ft)))))
(defun NMADD_D64 (fd fr fs ft) (set-d fd (fp-neg (fp-madd (get-d fr) (get-d fs) (get-d ft)))))
(defun NMSUB_S (fd fr fs ft) (set-s fd (fp-neg (fp-msub (get-s fr) (get-s fs) (get-s ft)))))
(defun NMSUB_D32 (fd fr fs ft) (set-d fd (fp-neg (fp-msub (get-d fr) (get-d fs) (get-d ft)))))
(defun NMSUB_D64 (fd fr fs ft) (set-d fd (fp-neg (fp-msub (get-d fr) (get-d fs) (get-d ft)))))

;; MOVES

(defun FMOV_S (fd fs) (set-s fd (get-s fs)))
(defun FMOV_D32 (fd fs) (set-d fd (get-d fs)))
(defun FMOV_D64 (fd fs) (set-d fd (get-d fs)))

(defun MTC1 (fs rt) (set-s fs rt))
(defun MTC1_D64 (fs rt) (set-s fs rt))
(defun MFC1 (rt fs) (set$ rt (sext32 (get-s fs))))
(defun MFC1_D64 (rt fs) (set$ rt (sext32 (get-s fs))))
(defun MTHC1_D32 (fs _ rt) (set-hi fs rt))
(defun MTHC1_D64 (fs _ rt) (set-hi fs rt))
(defun MFHC1_D32 (rt fs) (set$ rt (sext32 (get-hi fs))))
(defun MFHC1_D64 (rt fs) (set$ rt (sext32 (get-hi fs))))
(defun DMTC1 (fs rt) (set-d fs rt))
(defun DMFC1 (rt fs) (set$ rt (get-d fs)))

;; the conditional moves, the last operand is tied to the destination
(defun MOVT_I (rd rs cc _) (when (fcc cc) (set$ rd rs)))
(defun MOVF_I (rd rs cc _) (when (not (fcc cc)) (set$ rd rs)))
(defun MOVT_I64 (rd rs cc _) (MOVT_I rd rs cc _))
(defun MOVF_I64 (rd rs cc _) (MOVF_I rd rs cc _))
(defun MOVT_S (fd fs cc _) (when (fcc cc) (FMOV_S fd fs)))
(defun MOVF_S (fd fs cc _) (when (not (fcc cc)) (FMOV_S fd fs)))
(defun MOVT_D32 (fd fs cc _) (when (fcc cc) (FMOV_D32 fd fs)))
(defun MOVF_D32 (fd fs cc _) (when (not (fcc cc)) (FMOV_D32 fd fs)))
(defun MOVT_D64 (fd fs cc _) (when (fcc cc) (FMOV_D64 fd fs)))
(defun MOVF_D64 (fd fs cc _) (when (not (fcc cc)) (FMOV_D64 fd fs)))
(defun MOVN_I_S (fd fs rt _) (when (not (is-zero rt)) (FMOV_S fd fs)))
(defun MOVZ_I_S (fd fs rt _) (when (is-zero rt) (FMOV_S fd fs)))
(defun MOVN_I64_S (fd fs rt _) (MOVN_I_S fd fs rt _))
(defun MOVZ_I64_S (fd fs rt _) (MOVZ_I_S fd fs rt _))
(defun MOVN_I_D32 (fd fs rt _) (when (not (is-zero rt)) (FMOV_D32 fd fs)))
(defun MOVZ_I_D32 (fd fs rt _) (when (is-zero rt) (FMOV_D32 fd fs)))
(defun MOVN_I_D64 (fd fs rt _) (when (not (is-zero rt)) (FMOV_D64 fd fs)))
(defun MOVZ_I_D64 (fd fs rt _) (when (is-zero rt) (FMOV_D64 fd fs)))
(defun MOVN_I64_D64 (fd fs rt _) (MOVN_I_D64 fd fs rt _))
(defun MOVZ_I64_D64 (fd fs rt _) (MOVZ_I_D64 fd fs rt _))
(defun MOVN_I64_I (rd rs rt _) (MOVN_I_I rd rs rt _))
(defun MOVZ_I64_I (rd rs rt _) (MOVZ_I_I rd rs rt _))
(defun MOVN_I_I64 (rd rs rt _) (MOVN_I_I rd rs rt _))
(defun MOVZ_I_I64 (rd rs rt _) (MOVZ_I_I rd rs rt _))
(defun MOVN_I64_I64 (rd rs rt _) (MOVN_I_I rd rs rt _))
(defun MOVZ_I64_I64 (rd rs rt _) (MOVZ_I_I rd rs rt _))

;; LOADS AND STORES

(defun LWC1 (ft base off) (set-s ft (load-bits 32 (+ base off))))
(defun SWC1 (ft base off) (store-word (+ base off) (get-s ft)))
(defun LDC1 (ft base off) (set-d ft (load-bits 64 (+ base off))))
(defun SDC1 (ft base off) (store-word (+ base off) (get-d ft)))
(defun LDC164 (ft base off) (LDC1 ft base off))
(defun SDC164 (ft base off) (SDC1 ft base off))
(defun LWXC1 (fd base index) (LWC1 fd base index))
(defun SWXC1 (fs base index) (SWC1 fs base index))
(defun LWXC164 (fd base index) (LWC1 fd base index))
(defun SWXC164 (fs base index) (SWC1 fs base index))
(defun LDXC1 (fd base index) (LDC1 fd base index))
(defun SDXC1 (fs base index) (SDC1 fs base index))
(defun LDXC164 (fd base index) (LDC1 fd base index))
(defun SDXC164 (fs base index) (SDC1 fs base index))
;; the unaligned ones clear the low 3 bits of the address
(defun LUXC1 (fd base index) (set-d fd (load-bits 64 (aligned 8 (+ base index)))))
(defun SUXC1 (fs base index) (store-word (aligned 8 (+ base index)) (get-d fs)))
(defun LUXC164 (fd base index) (LUXC1 fd base index))
(defun SUXC164 (fs base index) (SUXC1 fs base index))

;; CONVERSIONS

(defun fp-int-bound (x n)
  "(fp-int-bound X N) is 2^(N-1) in the format of X"
  (if (= (word-width x) 32)
      (cast-low 32 (if (= n 32) 0x4f000000 0x5f000000))
    (if (= n 32) 0x41e0000000000000:64 0x43e0000000000000:64)))

;; a NaN, an infinity, or a value, that is out of the range after the
;; rounding, is invalid, and converts to the largest integer, or on the
;; Release 6, saturates, and a NaN converts to 0
(defun fp-invalid-int (n x)
  "(fp-invalid-int N X) is the N-bit integer of the invalid X"
  (let ((max (rshift (cast-signed n 1:1) 1)))
    (if (release6)
        (fp-select (fp-nan x) (cast-unsigned n 0)
                   (fp-select (msb x) (lnot max) max))
      max)))

(defun fp-to-int (mode n x)
  "(fp-to-int MODE N X) is X rounded with MODE, one of 'rne, 'rtz, 'rtn
   and 'rtp, to an N-bit integer"
  (let ((m (word-width x))
        (r (intrinsic (symbol-concat 'fround mode 'ieee754_binary
                                     (fp-size m) :sep '_)
                      x :result m))
        (b (fp-int-bound x n)))
    (fp-select (logand (fp-lt r b) (not (fp-lt r (fp-neg b))))
               (intrinsic (symbol-concat 'cast_sint 'rtz 'ieee754_binary
                                         (fp-size m) (fp-size n) :sep '_)
                          r :result n)
               (fp-invalid-int n x))))

(defun fp-of-int (n x)
  "(fp-of-int N X) is the signed integer X converted to the N-bit
   format"
  (intrinsic (symbol-concat 'cast_sfloat 'rne 'ieee754_binary
                            (fp-size (word-width x)) (fp-size n) :sep '_)
             x :result n))

(defun fp-convert-nan (x n)
  "(fp-convert-nan X N) is the NaN X converted to the N-bit format,
   with the fraction truncated or extended, and quieted, or of the
   legacy encoding, the default NaN if X is a signaling NaN"
  (let ((r (if (= n 64)
               (concat (msb x) (cast-low 11 0x7ff) (cast-low 23 x)
                       (cast-low 29 0))
             (concat (msb x) (cast-low 8 0xff) (extract 51 29 x)))))
    (if (release6)
        (fp-quiet r)
      (fp-select (fp-snan x) (fp-default-nan r) r))))

(defun fp-convert (x n)
  (fp-select (fp-nan x) (fp-convert-nan x n)
             (intrinsic (symbol-concat 'fconvert 'rne 'ieee754_binary
                                       (fp-size (word-width x)) (fp-size n)
                                       :sep '_)
                        x :result n)))

(defun CVT_D32_S (fd fs) (set-d fd (fp-convert (get-s fs) 64)))
(defun CVT_D64_S (fd fs) (set-d fd (fp-convert (get-s fs) 64)))
(defun CVT_S_D32 (fd fs) (set-s fd (fp-convert (get-d fs) 32)))
(defun CVT_S_D64 (fd fs) (set-s fd (fp-convert (get-d fs) 32)))
(defun CVT_S_W (fd fs) (set-s fd (fp-of-int 32 (get-s fs))))
(defun CVT_D32_W (fd fs) (set-d fd (fp-of-int 64 (get-s fs))))
(defun CVT_D64_W (fd fs) (set-d fd (fp-of-int 64 (get-s fs))))
(defun CVT_S_L (fd fs) (set-s fd (fp-of-int 32 (get-d fs))))
(defun CVT_D64_L (fd fs) (set-d fd (fp-of-int 64 (get-d fs))))

;; the conversions of the current rounding mode round to nearest
(defun CVT_W_S (fd fs) (set-s fd (fp-to-int 'rne 32 (get-s fs))))
(defun CVT_W_D32 (fd fs) (set-s fd (fp-to-int 'rne 32 (get-d fs))))
(defun CVT_W_D64 (fd fs) (set-s fd (fp-to-int 'rne 32 (get-d fs))))
(defun CVT_L_S (fd fs) (set-d fd (fp-to-int 'rne 64 (get-s fs))))
(defun CVT_L_D64 (fd fs) (set-d fd (fp-to-int 'rne 64 (get-d fs))))
(defun ROUND_W_S (fd fs) (set-s fd (fp-to-int 'rne 32 (get-s fs))))
(defun ROUND_W_D32 (fd fs) (set-s fd (fp-to-int 'rne 32 (get-d fs))))
(defun ROUND_W_D64 (fd fs) (set-s fd (fp-to-int 'rne 32 (get-d fs))))
(defun ROUND_L_S (fd fs) (set-d fd (fp-to-int 'rne 64 (get-s fs))))
(defun ROUND_L_D64 (fd fs) (set-d fd (fp-to-int 'rne 64 (get-d fs))))
(defun TRUNC_W_S (fd fs) (set-s fd (fp-to-int 'rtz 32 (get-s fs))))
(defun TRUNC_W_D32 (fd fs) (set-s fd (fp-to-int 'rtz 32 (get-d fs))))
(defun TRUNC_W_D64 (fd fs) (set-s fd (fp-to-int 'rtz 32 (get-d fs))))
(defun TRUNC_L_S (fd fs) (set-d fd (fp-to-int 'rtz 64 (get-s fs))))
(defun TRUNC_L_D64 (fd fs) (set-d fd (fp-to-int 'rtz 64 (get-d fs))))
(defun FLOOR_W_S (fd fs) (set-s fd (fp-to-int 'rtn 32 (get-s fs))))
(defun FLOOR_W_D32 (fd fs) (set-s fd (fp-to-int 'rtn 32 (get-d fs))))
(defun FLOOR_W_D64 (fd fs) (set-s fd (fp-to-int 'rtn 32 (get-d fs))))
(defun FLOOR_L_S (fd fs) (set-d fd (fp-to-int 'rtn 64 (get-s fs))))
(defun FLOOR_L_D64 (fd fs) (set-d fd (fp-to-int 'rtn 64 (get-d fs))))
(defun CEIL_W_S (fd fs) (set-s fd (fp-to-int 'rtp 32 (get-s fs))))
(defun CEIL_W_D32 (fd fs) (set-s fd (fp-to-int 'rtp 32 (get-d fs))))
(defun CEIL_W_D64 (fd fs) (set-s fd (fp-to-int 'rtp 32 (get-d fs))))
(defun CEIL_L_S (fd fs) (set-d fd (fp-to-int 'rtp 64 (get-s fs))))
(defun CEIL_L_D64 (fd fs) (set-d fd (fp-to-int 'rtp 64 (get-d fs))))

;; COMPARISONS
;;
;; The bits 0, 1 and 2 of the condition of C.cond.fmt select the
;; unordered, the equal and the less than relations, the bit 3 makes a
;; quiet NaN signal an invalid operation, whose exception is disabled.

(defun fp-compare (c x y)
  (let ((un (logor (fp-nan x) (fp-nan y)))
        (lt (logand (not un) (fp-lt x y)))
        (eq (logand (not un) (not lt) (not (fp-lt y x)))))
    (logor (logand (select 0 c) un)
           (logand (select 1 c) eq)
           (logand (select 2 c) lt))))

(defun c-s (c cc fs ft) (set-fcc cc (fp-compare c (get-s fs) (get-s ft))))
(defun c-d (c cc fs ft) (set-fcc cc (fp-compare c (get-d fs) (get-d ft))))

(defun C_F_S (cc fs ft) (c-s 0 cc fs ft))
(defun C_F_D32 (cc fs ft) (c-d 0 cc fs ft))
(defun C_F_D64 (cc fs ft) (c-d 0 cc fs ft))
(defun C_UN_S (cc fs ft) (c-s 1 cc fs ft))
(defun C_UN_D32 (cc fs ft) (c-d 1 cc fs ft))
(defun C_UN_D64 (cc fs ft) (c-d 1 cc fs ft))
(defun C_EQ_S (cc fs ft) (c-s 2 cc fs ft))
(defun C_EQ_D32 (cc fs ft) (c-d 2 cc fs ft))
(defun C_EQ_D64 (cc fs ft) (c-d 2 cc fs ft))
(defun C_UEQ_S (cc fs ft) (c-s 3 cc fs ft))
(defun C_UEQ_D32 (cc fs ft) (c-d 3 cc fs ft))
(defun C_UEQ_D64 (cc fs ft) (c-d 3 cc fs ft))
(defun C_OLT_S (cc fs ft) (c-s 4 cc fs ft))
(defun C_OLT_D32 (cc fs ft) (c-d 4 cc fs ft))
(defun C_OLT_D64 (cc fs ft) (c-d 4 cc fs ft))
(defun C_ULT_S (cc fs ft) (c-s 5 cc fs ft))
(defun C_ULT_D32 (cc fs ft) (c-d 5 cc fs ft))
(defun C_ULT_D64 (cc fs ft) (c-d 5 cc fs ft))
(defun C_OLE_S (cc fs ft) (c-s 6 cc fs ft))
(defun C_OLE_D32 (cc fs ft) (c-d 6 cc fs ft))
(defun C_OLE_D64 (cc fs ft) (c-d 6 cc fs ft))
(defun C_ULE_S (cc fs ft) (c-s 7 cc fs ft))
(defun C_ULE_D32 (cc fs ft) (c-d 7 cc fs ft))
(defun C_ULE_D64 (cc fs ft) (c-d 7 cc fs ft))
(defun C_SF_S (cc fs ft) (c-s 0 cc fs ft))
(defun C_SF_D32 (cc fs ft) (c-d 0 cc fs ft))
(defun C_SF_D64 (cc fs ft) (c-d 0 cc fs ft))
(defun C_NGLE_S (cc fs ft) (c-s 1 cc fs ft))
(defun C_NGLE_D32 (cc fs ft) (c-d 1 cc fs ft))
(defun C_NGLE_D64 (cc fs ft) (c-d 1 cc fs ft))
(defun C_SEQ_S (cc fs ft) (c-s 2 cc fs ft))
(defun C_SEQ_D32 (cc fs ft) (c-d 2 cc fs ft))
(defun C_SEQ_D64 (cc fs ft) (c-d 2 cc fs ft))
(defun C_NGL_S (cc fs ft) (c-s 3 cc fs ft))
(defun C_NGL_D32 (cc fs ft) (c-d 3 cc fs ft))
(defun C_NGL_D64 (cc fs ft) (c-d 3 cc fs ft))
(defun C_LT_S (cc fs ft) (c-s 4 cc fs ft))
(defun C_LT_D32 (cc fs ft) (c-d 4 cc fs ft))
(defun C_LT_D64 (cc fs ft) (c-d 4 cc fs ft))
(defun C_NGE_S (cc fs ft) (c-s 5 cc fs ft))
(defun C_NGE_D32 (cc fs ft) (c-d 5 cc fs ft))
(defun C_NGE_D64 (cc fs ft) (c-d 5 cc fs ft))
(defun C_LE_S (cc fs ft) (c-s 6 cc fs ft))
(defun C_LE_D32 (cc fs ft) (c-d 6 cc fs ft))
(defun C_LE_D64 (cc fs ft) (c-d 6 cc fs ft))
(defun C_NGT_S (cc fs ft) (c-s 7 cc fs ft))
(defun C_NGT_D32 (cc fs ft) (c-d 7 cc fs ft))
(defun C_NGT_D64 (cc fs ft) (c-d 7 cc fs ft))

;; the branches on the condition codes, the likely ones nullify their
;; delay slots if they are not taken
(defun BC1T (cc off) (branch (fcc cc) off))
(defun BC1F (cc off) (branch (not (fcc cc)) off))
(defun BC1TL (cc off) (BC1T cc off))
(defun BC1FL (cc off) (BC1F cc off))

;;; MIPS32 AND MIPS64 RELEASE 6 INSTRUCTIONS
;;
;; The Release 6 removes HI and LO, the likely branches, the condition
;; codes of the FPU and the unfused multiply-add, and adds the
;; instructions below. Its compact branches have no delay slot, so their
;; link is the address of the next instruction, the forbidden slot.
;; LLVM names the operations on the 64-bit registers of some of the
;; MIPS32 instructions with the suffix 64, e.g., BEQZC64.

(defun sext16 (x)
  "(sext16 X) is the low 16 bits of X sign-extended to a word"
  (cast-signed (word-width) (cast-low 16 x)))

(defun compact-link () (+ (get-program-counter) 4))

;; MULTIPLICATION AND DIVISION, the results are in the registers, the
;; divisions by zero and the overflows are of the division by 1, as of
;; QEMU, see divisor above

(defmacro mul-high (cast rs rt)
  (sext32 (cast-high 32 (* (cast 64 (low32 rs)) (cast 64 (low32 rt))))))

(defmacro dmul-high (cast rs rt)
  (cast-high 64 (* (cast 128 rs) (cast 128 rt))))

(defun MUL_R6 (rd rs rt) (MUL rd rs rt))
(defun MULU (rd rs rt) (MUL rd rs rt))
(defun MUH (rd rs rt) (set$ rd (mul-high cast-signed rs rt)))
(defun MUHU (rd rs rt) (set$ rd (mul-high cast-unsigned rs rt)))
(defun DMUL_R6 (rd rs rt) (set$ rd (* rs rt)))
(defun DMULU (rd rs rt) (set$ rd (* rs rt)))
(defun DMUH (rd rs rt) (set$ rd (dmul-high cast-signed rs rt)))
(defun DMUHU (rd rs rt) (set$ rd (dmul-high cast-unsigned rs rt)))

(defmacro quotient (div signed x y)
  (let ((d (divisor signed x y)))
    (div x d)))

(defmacro remainder (div signed x y)
  (let ((d (divisor signed x y)))
    (- x (* (div x d) d))))

(defun DIV (rd rs rt) (set$ rd (sext32 (quotient s/ true (low32 rs) (low32 rt)))))
(defun MOD (rd rs rt) (set$ rd (sext32 (remainder s/ true (low32 rs) (low32 rt)))))
(defun DIVU (rd rs rt) (set$ rd (sext32 (quotient / false (low32 rs) (low32 rt)))))
(defun MODU (rd rs rt) (set$ rd (sext32 (remainder / false (low32 rs) (low32 rt)))))
(defun DDIV (rd rs rt) (set$ rd (quotient s/ true rs rt)))
(defun DMOD (rd rs rt) (set$ rd (remainder s/ true rs rt)))
(defun DDIVU (rd rs rt) (set$ rd (quotient / false rs rt)))
(defun DMODU (rd rs rt) (set$ rd (remainder / false rs rt)))

;; ARITHMETIC AND BIT OPERATIONS

(defun mask-of (c)
  "(mask-of C) is the word of ones if C is true and of zeros otherwise"
  (neg (zext c)))

(defun SELEQZ (rd rs rt) (set$ rd (logand rs (mask-of (is-zero rt)))))
(defun SELNEZ (rd rs rt) (set$ rd (logand rs (mask-of (not (is-zero rt))))))
(defun SELEQZ64 (rd rs rt) (SELEQZ rd rs rt))
(defun SELNEZ64 (rd rs rt) (SELNEZ rd rs rt))

;; the immediates are the upper parts of the addends
(defun AUI (rt rs imm) (set$ rt (sext32 (+ rs (lshift imm 16)))))
(defun DAUI (rt rs imm) (set$ rt (+ rs (lshift (sext16 imm) 16))))
(defun DAHI (rs _ imm) (set$ rs (+ rs (lshift (sext16 imm) 32))))
(defun DATI (rs _ imm) (set$ rs (+ rs (lshift (sext16 imm) 48))))

;; the shift amount of LSA is the operand, i.e., the encoded one plus 1
(defun LSA_R6 (rd rs rt sa) (set$ rd (sext32 (+ (lshift (low32 rs) sa) rt))))
(defun DLSA_R6 (rd rs rt sa) (set$ rd (+ (lshift rs sa) rt)))

;; (ALIGN rd rs rt bp) concatenates rt and rs and extracts a word at the
;; byte bp from the most significant end
(defun ALIGN (rd rs rt bp)
  (set$ rd (sext32 (logor (lshift (low32 rt) (* 8 bp))
                          (rshift (low32 rs) (- 32 (* 8 bp)))))))
(defun DALIGN (rd rs rt bp)
  (set$ rd (logor (lshift rt (* 8 bp)) (rshift rs (- 64 (* 8 bp))))))

(defun swap-bits (x n m)
  "swaps the adjacent N-bit groups of X, which the mask M selects"
  (let ((m (cast-unsigned (word-width x) m)))
    (logor (logand (rshift x n) m) (lshift (logand x m) n))))

(defun reverse-bits-in-bytes (x)
  (swap-bits (swap-bits (swap-bits x 1 0x5555555555555555)
                        2 0x3333333333333333)
             4 0x0f0f0f0f0f0f0f0f))

(defun BITSWAP (rd rt) (set$ rd (sext32 (reverse-bits-in-bytes (low32 rt)))))
(defun DBITSWAP (rd rt) (set$ rd (reverse-bits-in-bytes rt)))

(defun CLZ_R6 (rd rs) (CLZ rd rs))
(defun CLO_R6 (rd rs) (CLO rd rs))
(defun DCLZ_R6 (rd rs) (DCLZ rd rs))
(defun DCLO_R6 (rd rs) (DCLO rd rs))

;; THE PC-RELATIVE INSTRUCTIONS, whose offsets are scaled by LLVM

(defun ADDIUPC (rs off) (set$ rs (+ (get-program-counter) off)))
(defun AUIPC (rs imm) (set$ rs (+ (get-program-counter) (lshift imm 16))))
(defun ALUIPC (rs imm)
  (set$ rs (logand (+ (get-program-counter) (lshift imm 16)) (lnot 0xffff))))
(defun LWPC (rs off) (LW rs (get-program-counter) off))
(defun LWUPC (rs off) (LWu rs (get-program-counter) off))
;; the address of LDPC is of the doubleword of the instruction
(defun LDPC (rs off) (LD rs (aligned 8 (get-program-counter)) off))

;; the offsets of the loads and stores are 9-bit
(defun LL_R6 (rt base off) (LL rt base off))
(defun LL64_R6 (rt base off) (LL rt base off))
(defun LLD_R6 (rt base off) (LLD rt base off))
(defun SC_R6 (rt _ base off) (SC rt _ base off))
(defun SC64_R6 (rt _ base off) (SC rt _ base off))
(defun SCD_R6 (rt _ base off) (SCD rt _ base off))

;; BRANCHES AND JUMPS

(defun BC (off) (exec-addr (+ (get-program-counter) off)))
(defun BALC (off)
  (set RA (compact-link))
  (BC off))

(defun BEQZC (rs off) (branch (is-zero rs) off))
(defun BNEZC (rs off) (branch (not (is-zero rs)) off))
(defun BLEZC (rt off) (branch (s<= rt 0) off))
(defun BGEZC (rt off) (branch (s>= rt 0) off))
(defun BGTZC (rt off) (branch (s> rt 0) off))
(defun BLTZC (rt off) (branch (s< rt 0) off))
(defun BEQC (rs rt off) (branch (= rs rt) off))
(defun BNEC (rs rt off) (branch (/= rs rt) off))
(defun BLTC (rs rt off) (branch (s< rs rt) off))
(defun BGEC (rs rt off) (branch (s>= rs rt) off))
(defun BLTUC (rs rt off) (branch (< rs rt) off))
(defun BGEUC (rs rt off) (branch (>= rs rt) off))
(defun BEQZC64 (rs off) (BEQZC rs off))
(defun BNEZC64 (rs off) (BNEZC rs off))
(defun BLEZC64 (rt off) (BLEZC rt off))
(defun BGEZC64 (rt off) (BGEZC rt off))
(defun BGTZC64 (rt off) (BGTZC rt off))
(defun BLTZC64 (rt off) (BLTZC rt off))
(defun BEQC64 (rs rt off) (BEQC rs rt off))
(defun BNEC64 (rs rt off) (BNEC rs rt off))
(defun BLTC64 (rs rt off) (BLTC rs rt off))
(defun BGEC64 (rs rt off) (BGEC rs rt off))
(defun BLTUC64 (rs rt off) (BLTUC rs rt off))
(defun BGEUC64 (rs rt off) (BGEUC rs rt off))

;; the link is written whether the branch is taken or not
(defun branch-link (cnd off)
  (set RA (compact-link))
  (branch cnd off))

(defun BEQZALC (rt off) (branch-link (is-zero rt) off))
(defun BNEZALC (rt off) (branch-link (not (is-zero rt)) off))
(defun BLEZALC (rt off) (branch-link (s<= rt 0) off))
(defun BGEZALC (rt off) (branch-link (s>= rt 0) off))
(defun BGTZALC (rt off) (branch-link (s> rt 0) off))
(defun BLTZALC (rt off) (branch-link (s< rt 0) off))

;; the 32-bit addition overflows, also if an operand isn't a
;; sign-extended word, as on MIPS64
(defun add-overflows (rs rt)
  (let ((r (+ (low32 rs) (low32 rt))))
    (logor (signed-overflow 32 rs rt r)
           (/= rs (sext32 rs))
           (/= rt (sext32 rt)))))

(defun BOVC (rs rt off) (branch (add-overflows rs rt) off))
(defun BNVC (rs rt off) (branch (not (add-overflows rs rt)) off))

;; the offsets of JIC and JIALC are 16-bit and not scaled
(defun JIC (rt off) (exec-addr (+ rt (sext16 off))))
(defun JIALC (rt off)
  (let ((dst (+ rt (sext16 off))))
    (set RA (compact-link))
    (exec-addr dst)))
(defun JIC64 (rt off) (JIC rt off))
(defun JIALC64 (rt off) (JIALC rt off))

;; BAL and NAL are BGEZAL and BLTZAL of the register 0, with the delay
;; slot
(defun BAL (off)
  (set RA (link))
  (BC off))
(defun NAL () (set RA (link)))

;; the hazard barriers are not modeled
(defun JR_HB (rs) (JR rs))
(defun JR_HB_R6 (rs) (JR rs))
(defun JR_HB64 (rs) (JR rs))
(defun JR_HB64_R6 (rs) (JR rs))
(defun JALR_HB (rd rs) (JALR rd rs))
(defun JALR_HB64 (rd rs) (JALR rd rs))
(defun JALR64 (rd rs) (JALR rd rs))

;; FLOATING-POINT INSTRUCTIONS
;;
;; The F registers are 64-bit, see fpr64, the NaNs are of IEEE 754-2008,
;; see fp-snan, and the instructions use bit 0 of an F register as the
;; condition instead of the condition codes.

(defun fp-bit0 (r) (select 0 (get-s r)))

;; (SEL fd fd ft fs) is ft if bit 0 of fd is set, and fs otherwise
(defun SEL_S (fd _ fs ft) (set-s fd (fp-select (fp-bit0 fd) (get-s ft) (get-s fs))))
(defun SEL_D (fd _ fs ft) (set-d fd (fp-select (fp-bit0 fd) (get-d ft) (get-d fs))))
(defun SELEQZ_S (fd fs ft) (set-s fd (logand (get-s fs) (neg (cast-unsigned 32 (not (fp-bit0 ft)))))))
(defun SELEQZ_D (fd fs ft) (set-d fd (logand (get-d fs) (neg (cast-unsigned 64 (not (fp-bit0 ft)))))))
(defun SELNEZ_S (fd fs ft) (set-s fd (logand (get-s fs) (neg (cast-unsigned 32 (fp-bit0 ft))))))
(defun SELNEZ_D (fd fs ft) (set-d fd (logand (get-d fs) (neg (cast-unsigned 64 (fp-bit0 ft))))))

;; the branches on bit 0 of an F register, with the delay slot
(defun BC1EQZ (ft off) (branch (not (fp-bit0 ft)) off))
(defun BC1NEZ (ft off) (branch (fp-bit0 ft) off))

;; the comparisons write the mask of the result, the signaling ones
;; (bit 3 of the condition) only signal an invalid operation on a quiet
;; NaN, whose exception is disabled, so the condition is of fp-compare

(defun cmp-s (c fd fs ft)
  (set-s fd (cast-signed 32 (fp-compare c (get-s fs) (get-s ft)))))
(defun cmp-d (c fd fs ft)
  (set-d fd (cast-signed 64 (fp-compare c (get-d fs) (get-d ft)))))

(defun CMP_F_S (fd fs ft) (cmp-s 0 fd fs ft))
(defun CMP_F_D (fd fs ft) (cmp-d 0 fd fs ft))
(defun CMP_UN_S (fd fs ft) (cmp-s 1 fd fs ft))
(defun CMP_UN_D (fd fs ft) (cmp-d 1 fd fs ft))
(defun CMP_EQ_S (fd fs ft) (cmp-s 2 fd fs ft))
(defun CMP_EQ_D (fd fs ft) (cmp-d 2 fd fs ft))
(defun CMP_UEQ_S (fd fs ft) (cmp-s 3 fd fs ft))
(defun CMP_UEQ_D (fd fs ft) (cmp-d 3 fd fs ft))
(defun CMP_LT_S (fd fs ft) (cmp-s 4 fd fs ft))
(defun CMP_LT_D (fd fs ft) (cmp-d 4 fd fs ft))
(defun CMP_ULT_S (fd fs ft) (cmp-s 5 fd fs ft))
(defun CMP_ULT_D (fd fs ft) (cmp-d 5 fd fs ft))
(defun CMP_LE_S (fd fs ft) (cmp-s 6 fd fs ft))
(defun CMP_LE_D (fd fs ft) (cmp-d 6 fd fs ft))
(defun CMP_ULE_S (fd fs ft) (cmp-s 7 fd fs ft))
(defun CMP_ULE_D (fd fs ft) (cmp-d 7 fd fs ft))
(defun CMP_SAF_S (fd fs ft) (cmp-s 0 fd fs ft))
(defun CMP_SAF_D (fd fs ft) (cmp-d 0 fd fs ft))
(defun CMP_SUN_S (fd fs ft) (cmp-s 1 fd fs ft))
(defun CMP_SUN_D (fd fs ft) (cmp-d 1 fd fs ft))
(defun CMP_SEQ_S (fd fs ft) (cmp-s 2 fd fs ft))
(defun CMP_SEQ_D (fd fs ft) (cmp-d 2 fd fs ft))
(defun CMP_SUEQ_S (fd fs ft) (cmp-s 3 fd fs ft))
(defun CMP_SUEQ_D (fd fs ft) (cmp-d 3 fd fs ft))
(defun CMP_SLT_S (fd fs ft) (cmp-s 4 fd fs ft))
(defun CMP_SLT_D (fd fs ft) (cmp-d 4 fd fs ft))
(defun CMP_SULT_S (fd fs ft) (cmp-s 5 fd fs ft))
(defun CMP_SULT_D (fd fs ft) (cmp-d 5 fd fs ft))
(defun CMP_SLE_S (fd fs ft) (cmp-s 6 fd fs ft))
(defun CMP_SLE_D (fd fs ft) (cmp-d 6 fd fs ft))
(defun CMP_SULE_S (fd fs ft) (cmp-s 7 fd fs ft))
(defun CMP_SULE_D (fd fs ft) (cmp-d 7 fd fs ft))

;; The multiply-add is fused, i.e., it rounds only once, the product is
;; computed with the fmad intrinsic. The result is a signaling NaN of
;; the addend, of the first and of the second factor, in that order,
;; quieted, then a quiet one, as of QEMU, also when the product is of an
;; infinity and a zero, and else the default NaN, if it is invalid. The
;; negated product of MSUBF doesn't negate a NaN operand.

(defun fp-fmad (d s t)
  "(fp-fmad D S T) is D + S * T rounded once"
  (intrinsic (symbol-concat 'fmad 'rne 'ieee754_binary
                            (fp-size (word-width d)) :sep '_)
             s t d :result (word-width d)))

(defun fp-result3 (r d s t)
  "(fp-result3 R D S T) is the result R of a multiply-add of D, S and T
   or the NaN"
  (fp-select (fp-snan d) (fp-quiet d)
    (fp-select (fp-snan s) (fp-quiet s)
      (fp-select (fp-snan t) (fp-quiet t)
        (fp-select (fp-nan d) d
          (fp-select (fp-nan s) s
            (fp-select (fp-nan t) t
              (fp-select (fp-nan r) (fp-default-nan d) r))))))))

(defun fp-maddf (d s t) (fp-result3 (fp-fmad d s t) d s t))
(defun fp-msubf (d s t) (fp-result3 (fp-fmad d (fp-neg s) t) d s t))

;; (MADDF fd fd fs ft) is fd + fs * ft, and MSUBF is fd - fs * ft
(defun MADDF_S (fd _ fs ft) (set-s fd (fp-maddf (get-s fd) (get-s fs) (get-s ft))))
(defun MADDF_D (fd _ fs ft) (set-d fd (fp-maddf (get-d fd) (get-d fs) (get-d ft))))
(defun MSUBF_S (fd _ fs ft) (set-s fd (fp-msubf (get-s fd) (get-s fs) (get-s ft))))
(defun MSUBF_D (fd _ fs ft) (set-d fd (fp-msubf (get-d fd) (get-d fs) (get-d ft))))

;; The minimum and the maximum are minNum and maxNum of IEEE 754-2008: a
;; quiet NaN is ignored if the other operand is a number, a signaling
;; NaN is quieted. The negative zero is less than the positive one. The
;; MINA and MAXA compare the absolute values, and, if they are equal,
;; the values.

(defun fp-min-num (x y)
  (fp-select (fp-lt x y) x (fp-select (fp-lt y x) y (fp-select (msb x) x y))))

(defun fp-max-num (x y)
  (fp-select (fp-lt x y) y (fp-select (fp-lt y x) x (fp-select (msb x) y x))))

(defun fp-min-mag (x y)
  (fp-select (fp-lt (fp-abs x) (fp-abs y)) x
    (fp-select (fp-lt (fp-abs y) (fp-abs x)) y (fp-min-num x y))))

(defun fp-max-mag (x y)
  (fp-select (fp-lt (fp-abs x) (fp-abs y)) y
    (fp-select (fp-lt (fp-abs y) (fp-abs x)) x (fp-max-num x y))))

(defun fp-num-result (r x y)
  "(fp-num-result R X Y) is the result R of minNum or maxNum of X and Y
   or the NaN"
  (fp-select (logor (fp-snan x) (fp-snan y)) (fp-result2 r x y)
    (fp-select (fp-nan x) (fp-select (fp-nan y) x y)
      (fp-select (fp-nan y) x r))))

(defun MIN_S (fd fs ft)
  (let ((x (get-s fs)) (y (get-s ft))) (set-s fd (fp-num-result (fp-min-num x y) x y))))
(defun MIN_D (fd fs ft)
  (let ((x (get-d fs)) (y (get-d ft))) (set-d fd (fp-num-result (fp-min-num x y) x y))))
(defun MAX_S (fd fs ft)
  (let ((x (get-s fs)) (y (get-s ft))) (set-s fd (fp-num-result (fp-max-num x y) x y))))
(defun MAX_D (fd fs ft)
  (let ((x (get-d fs)) (y (get-d ft))) (set-d fd (fp-num-result (fp-max-num x y) x y))))
(defun MINA_S (fd fs ft)
  (let ((x (get-s fs)) (y (get-s ft))) (set-s fd (fp-num-result (fp-min-mag x y) x y))))
(defun MINA_D (fd fs ft)
  (let ((x (get-d fs)) (y (get-d ft))) (set-d fd (fp-num-result (fp-min-mag x y) x y))))
(defun MAXA_S (fd fs ft)
  (let ((x (get-s fs)) (y (get-s ft))) (set-s fd (fp-num-result (fp-max-mag x y) x y))))
(defun MAXA_D (fd fs ft)
  (let ((x (get-d fs)) (y (get-d ft))) (set-d fd (fp-num-result (fp-max-mag x y) x y))))

;; the rounding to an integral value, of the current rounding mode,
;; which is to nearest
(defun fp-rint (x)
  (fp-result1 (intrinsic (symbol-concat 'fround 'rne 'ieee754_binary
                                        (fp-size (word-width x)) :sep '_)
                         x :result (word-width x))
              x))

(defun RINT_S (fd fs) (set-s fd (fp-rint (get-s fs))))
(defun RINT_D (fd fs) (set-d fd (fp-rint (get-d fs))))

;; the class is the mask of one of the bits: 0 a signaling NaN, 1 a
;; quiet NaN, 2-5 a negative infinity, normal, subnormal, and zero, and
;; 6-9 the positive ones
(defun fp-class (x)
  (let ((w (word-width x))
        (f (fp-frac x))
        (e (extract (- w 2) f x))
        (top (= e (lnot (cast-unsigned (- w f 1) 0))))
        (zexp (is-zero e))
        (zfrac (is-zero (cast-low f x)))
        (neg (msb x))
        (inf (logand top zfrac))
        (norm (not (logor top zexp)))
        (sub (logand zexp (not zfrac)))
        (zero (logand zexp zfrac)))
    (logor (fp-class-bit w 0 (fp-snan x))
           (fp-class-bit w 1 (logand (fp-nan x) (not (fp-snan x))))
           (fp-class-bit w 2 (logand neg inf))
           (fp-class-bit w 3 (logand neg norm))
           (fp-class-bit w 4 (logand neg sub))
           (fp-class-bit w 5 (logand neg zero))
           (fp-class-bit w 6 (logand (not neg) inf))
           (fp-class-bit w 7 (logand (not neg) norm))
           (fp-class-bit w 8 (logand (not neg) sub))
           (fp-class-bit w 9 (logand (not neg) zero)))))

(defun fp-class-bit (w n c) (lshift (cast-unsigned w c) n))

(defun CLASS_S (fd fs) (set-s fd (fp-class (get-s fs))))
(defun CLASS_D (fd fs) (set-d fd (fp-class (get-d fs))))
