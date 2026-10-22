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
;; that is a NaN.
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
  "true if the F registers are 64-bit"
  (= (word-width) 64))

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

(defun set-s (r x)
  "(set-s R X) writes the single X to the operand R"
  (let ((s (fpr r)))
    (if (fpr64)
        (set$ s (concat (cast-high 32 (unquote s)) (cast-low 32 x)))
      (set$ s (cast-low 32 x)))))

(defun set-d (r x)
  "(set-d R X) writes the double X to the operand R"
  (let ((s (fpr r)))
    (if (fpr64)
        (set$ s (cast-low 64 x))
      (prog (set$ s (cast-low 32 x))
            (set$ (fpr-next s) (cast-high 32 x))))))

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

(defun fp-snan (x)
  "(fp-snan X) is true if X is a signaling NaN of the legacy encoding"
  (logand (fp-nan x) (select (- (fp-frac x) 1) x)))

(defun fp-default-nan (x)
  "the default NaN of the legacy encoding in the format of X"
  (if (= (word-width x) 32)
      (cast-low 32 0x7fbfffff)
    0x7ff7ffffffffffff:64))

(defun fp-lt (x y)
  "(fp-lt X Y) is true if X < Y, false if they are unordered"
  (intrinsic (symbol-concat 'forder 'ieee754_binary (fp-size (word-width x))
                            :sep '_)
             x y :result 1))

(defun fp-neg (x) (concat (lnot (msb x)) (cast-low (- (word-width x) 1) x)))
(defun fp-abs (x) (concat 0:1 (cast-low (- (word-width x) 1) x)))

(defun fp-result1 (r x)
  "(fp-result1 R X) is the result R of an operation on X or the NaN"
  (fp-select (fp-snan x) (fp-default-nan x)
    (fp-select (fp-nan x) x
      (fp-select (fp-nan r) (fp-default-nan x) r))))

(defun fp-result2 (r x y)
  "(fp-result2 R X Y) is the result R of an operation on X and Y or the
   NaN"
  (fp-select (logor (fp-snan x) (fp-snan y)) (fp-default-nan x)
    (fp-select (fp-nan x) x
      (fp-select (fp-nan y) y
        (fp-select (fp-nan r) (fp-default-nan x) r)))))

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
;; rounding, is invalid, and converts to the largest integer
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
               (rshift (cast-signed n 1:1) 1))))

(defun fp-of-int (n x)
  "(fp-of-int N X) is the signed integer X converted to the N-bit
   format"
  (intrinsic (symbol-concat 'cast_sfloat 'rne 'ieee754_binary
                            (fp-size (word-width x)) (fp-size n) :sep '_)
             x :result n))

(defun fp-convert-nan (x n)
  "(fp-convert-nan X N) is the NaN X converted to the N-bit format,
   with the fraction truncated or extended, or the default NaN if X is
   a signaling NaN"
  (if (= n 64)
      (fp-select (fp-snan x) 0x7ff7ffffffffffff:64
                 (concat (msb x) (cast-low 11 0x7ff) (cast-low 23 x)
                         (cast-low 29 0)))
    (fp-select (fp-snan x) (cast-low 32 0x7fbfffff)
               (concat (msb x) (cast-low 8 0xff) (extract 51 29 x)))))

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
