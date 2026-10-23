(declare (context (target riscv)))
(defpackage riscv (:use core target program))
(defpackage llvm-riscv64 (:use riscv riscv64))
(defpackage llvm-riscv32 (:use riscv riscv32))
(in-package riscv)

;;; Core Arithmetic

(defun ADDI (dst src off)
  (set$ dst (+ src off)))

(defun C_ADDI (dst src off)
  (set$ dst (+ src off)))

(defun add3 (dst src off)
  (declare (visibility :private))
  (set$ dst (cast-signed
             (word-width)
             (cast-low 32
                       (+ src off)))))

(defun ADDIW (dst src off)
  (add3 dst src off))

(defun C_ADDIW (dst src off)
  (add3 dst src off))

(defun ADDW (dst src off)
  (add3 dst src off))

(defun C_ADDW (rd r1 r2)
  (add3 rd r1 r2))

(defun C_ADD (rd r1 r2)
  (set$ rd (+ r1 r2)))

(defun C_ADDI4SPN (dst src off)
  (set$ dst (+ src off)))

(defun C_ADDI16SP (dst src off)
  (set$ dst (+ src off)))

(defun SUB (rd r1 r2)
  (set$ rd (- r1 r2)))

(defun C_SUB (rd r1 r2)
  (set$ rd (- r1 r2)))


;;; Moves

(defun C_MV (dst src)
  (set$ dst src))

(defun upper-immediate (imm)
  "the 20 bits of IMM in the upper bits of a word of 32 bits, extended by
   their sign to the width of the registers, as on RV64"
  (declare (visibility :private))
  (cast-signed (word-width) (cast-low 32 (lshift imm 12))))

(defun C_LUI (dst imm)
  (set$ dst (upper-immediate imm)))

(defun AUIPC (dst off)
  (set$ dst (+ (get-program-counter) (upper-immediate off))))

(defun LUI (dst imm)
  (set$ dst (upper-immediate imm)))

(defun LI (dst imm)
  (set$ dst (cast-signed (word-width) imm)))

(defun C_LI (dst imm)
  (set$ dst (cast-signed (word-width) imm)))



;;; Memory operations
(defun LD (dst reg off)
  (set$ dst (core:load-word (+ reg off))))

(defun C_LD (dst reg off)
  (set$ dst (core:load-word (+ reg off))))

(defmacro load-word (cast bits dst reg off)
  "loads the BITS bits to DST, extended by CAST to the width of the
   register, of RV32 and RV64 alike"
  (set$ dst (cast (word-width) (load-bits bits (+ reg off)))))

(defun LW (dst reg off)
  (load-word cast-signed 32 dst reg off))

(defun C_LW (dst reg off)
  (load-word cast-signed 32 dst reg off))

(defun LH (dst reg off)
  (load-word cast-signed 16 dst reg off))

(defun LWU (dst reg off)
  (load-word cast-unsigned 32 dst reg off))

(defun LB (dst reg off)
  (set$ dst (cast-signed (word-width) (load-byte (+ reg off)))))

(defun LBU (dst reg off)
  (set$ dst (cast-unsigned (word-width) (load-byte (+ reg off)))))

(defun LHU (dst reg off)
  (load-word cast-unsigned 16 dst reg off))

(defun C_LDSP (dst reg off)
  (set$ dst (core:load-word (+ reg off))))

(defun C_SDSP (val sp imm)
  (store-word (+ sp imm) val))

(defun SDSP (val sp imm)
  (store-word (+ sp imm) val))

(defun SD (val reg imm)
  (store-word (+ reg imm) val))

(defun C_SD (val reg imm)
  (store-word (+ reg imm) val))

(defun SW (val reg imm)
  (store-word (+ reg imm) (cast-low 32 val)))

(defun SH (val reg imm)
  (store-word (+ reg imm) (cast-low 16 val)))

(defun SB (val reg imm)
  (store-byte (+ reg imm) val))

;;; Bitwise Operations

(defun ANDI (dst src off)
  (set$ dst (logand src off)))

(defun ORI (dst src off)
  (set$ dst (logor src off)))

(defun XORI (dst src off)
  (set$ dst (logxor src off)))

(defun SRLI (dst reg off)
  (set$ dst (rshift reg off)))

(defun C_SRLI (dst reg off)
  (set$ dst (rshift reg off)))

(defun C_SRAI (dst src imm)
  (set$ dst (arshift src imm)))

(defun SRAI (dst src imm)
  (set$ dst (arshift src imm)))

(defun SLLI (dst reg off)
  (set$ dst (lshift reg off)))

(defun C_SLLI (dst reg off)
  (set$ dst (lshift reg off)))

;;; Comparison
(defun set-if (dst cond)
  "(set-if DST COND) sets DST to 1, if COND holds, and to 0 otherwise"
  (declare (visibility :private))
  (set$ dst (if cond 1 0)))

(defun SLTI (dst src off)
  (set-if dst (s< src off)))

(defun SLTIU (dst src off)
  (set-if dst (< src off)))

(defun SLT (dst r1 r2)
  (set-if dst (s< r1 r2)))

(defun SLTU (dst r1 r2)
  (set-if dst (< r1 r2)))

;;; Jumps
(defun JAL (lr off)
  (let ((pc (get-program-counter)))
    (set$ lr (+ pc 4))
    (exec-addr (+ pc off))))

(defun JALR (lr rs off)
  "jumps to RS+OFF, whose lower bit is cleared, and saves the address of
   the next instruction in LR, after it computes the target, as LR may
   be RS"
  (let ((pc (get-program-counter))
        (dst (logand (+ rs off) (lnot 1))))
    (set$ lr (+ pc 4))
    (exec-addr dst)))

(defun C_JR (dst)
  (exec-addr dst))

(defun C_J (dst)
  (exec-addr (+ (get-program-counter) dst)))

(defun C_JALR (dst)
  (set X1 (+ (get-program-counter) 2))
  (exec-addr dst))

(defun conditional-jump (cmp off)
  (declare (visibility :private))
  (let ((pc (get-program-counter)))
    (when cmp
      (exec-addr (+ pc off)))))

(defun BEQ (rs1 rs2 off)
  (conditional-jump (= rs1 rs2) off))

(defun BLT (rs1 rs2 off)
  (conditional-jump (s< rs1 rs2) off))

(defun BNE (rs1 rs2 off)
  (conditional-jump (/= rs1 rs2) off))

(defun BGE (rs1 rs2 off)
  (conditional-jump (s>= rs1 rs2) off))

(defun BLTU (rs1 rs2 off)
  (conditional-jump (< rs1 rs2) off))

(defun BGEU (rs1 rs2 off)
  (conditional-jump (>= rs1 rs2) off))

(defun C_BEQ (rs1 rs2 off)
  (conditional-jump (= rs1 rs2) off))

(defun C_BLT (rs1 rs2 off)
  (conditional-jump (s< rs1 rs2) off))

(defun C_BNE (rs1 rs2 off)
  (conditional-jump (/= rs1 rs2) off))

(defun C_BGE (rs1 rs2 off)
  (conditional-jump (s>= rs1 rs2) off))

(defun BEQZ (rs1 off)
  (conditional-jump (is-zero rs1) off))

(defun C_BEQZ (rs1 off)
  (conditional-jump (is-zero rs1) off))

(defun BNEZ (rs1 off)
  (conditional-jump (not (is-zero rs1)) off))

(defun C_BNEZ (rs1 off)
  (conditional-jump (not (is-zero rs1)) off))


(defun C_NOP ()
  (empty))

;; the hints, which have no effect: C.NOP with an immediate, the
;; prefetches of Zicbop, and WFI, as no interrupt is modeled
(defun C_NOP_HINT (_) (empty))
(defun PREFETCH_R (_ _) (empty))
(defun PREFETCH_W (_ _) (empty))
(defun PREFETCH_I (_ _) (empty))
(defun WFI () (empty))

(defun NOP ()
  (empty))


;;; The register forms of the operations, and the word operations of
;;; RV64, which compute the lower 32 bits, whose result is extended by
;;; its sign, and the shifts, whose amount is the lower bits of the
;;; register, five for the words and log2 XLEN bits otherwise

(defun ADD (rd r1 r2)
  (set$ rd (+ r1 r2)))

(defun AND (rd r1 r2)
  (set$ rd (logand r1 r2)))

(defun OR (rd r1 r2)
  (set$ rd (logor r1 r2)))

(defun XOR (rd r1 r2)
  (set$ rd (logxor r1 r2)))

(defun C_AND (rd r1 r2)
  (set$ rd (logand r1 r2)))

(defun C_OR (rd r1 r2)
  (set$ rd (logor r1 r2)))

(defun C_XOR (rd r1 r2)
  (set$ rd (logxor r1 r2)))

(defun C_ANDI (rd r1 imm)
  (set$ rd (logand r1 imm)))

(defun shift-amount (x)
  (declare (visibility :private))
  (logand x (- (word-width) 1)))

(defun SLL (rd r1 r2)
  (set$ rd (lshift r1 (shift-amount r2))))

(defun SRL (rd r1 r2)
  (set$ rd (rshift r1 (shift-amount r2))))

(defun SRA (rd r1 r2)
  (set$ rd (arshift r1 (shift-amount r2))))

(defun word-result (rd x)
  "sets RD to the lower 32 bits of X, extended by their sign"
  (declare (visibility :private))
  (set$ rd (cast-signed (word-width) (cast-low 32 x))))

(defun SUBW (rd r1 r2)
  (word-result rd (- r1 r2)))

(defun C_SUBW (rd r1 r2)
  (word-result rd (- r1 r2)))

(defun SLLIW (rd r1 imm)
  (word-result rd (lshift (cast-low 32 r1) imm)))

(defun SRLIW (rd r1 imm)
  (word-result rd (rshift (cast-low 32 r1) imm)))

(defun SRAIW (rd r1 imm)
  (word-result rd (arshift (cast-low 32 r1) imm)))

(defun SLLW (rd r1 r2)
  (word-result rd (lshift (cast-low 32 r1) (logand r2 31))))

(defun SRLW (rd r1 r2)
  (word-result rd (rshift (cast-low 32 r1) (logand r2 31))))

(defun SRAW (rd r1 r2)
  (word-result rd (arshift (cast-low 32 r1) (logand r2 31))))

;;; The loads and stores of the stack pointer, of the compressed set

(defun C_LWSP (dst sp off)
  (load-word cast-signed 32 dst sp off))

(defun C_SWSP (val sp off)
  (store-word (+ sp off) (cast-low 32 val)))

(defun C_SW (val reg off)
  (store-word (+ reg off) (cast-low 32 val)))

;;; The multiplication and the division (the M extension): the high
;;; parts of the products are computed in the double width, the division
;;; by zero is all ones, and its remainder is the dividend, and the
;;; signed division of the least number by -1 is the least number

(defun MUL (rd r1 r2)
  (set$ rd (* r1 r2)))

(defun MULW (rd r1 r2)
  (word-result rd (* r1 r2)))

(defun MULH (rd r1 r2)
  (let ((w (word-width)))
    (set$ rd (cast-high w (* (cast-signed (* 2 w) r1)
                             (cast-signed (* 2 w) r2))))))

(defun MULHU (rd r1 r2)
  (let ((w (word-width)))
    (set$ rd (cast-high w (* (cast-unsigned (* 2 w) r1)
                             (cast-unsigned (* 2 w) r2))))))

(defun MULHSU (rd r1 r2)
  (let ((w (word-width)))
    (set$ rd (cast-high w (* (cast-signed (* 2 w) r1)
                             (cast-unsigned (* 2 w) r2))))))

;; the quotients and the remainders are selected without a branch, and
;; the divisor of the selected one is never zero, as Primus evaluates
;; both arms of an expression, and fails on the division by zero

(defun divide (signed x y)
  "(divide SIGNED X Y) is the quotient of X by Y, all ones if Y is 0,
   and -X if Y is -1, and SIGNED, e.g., the least number by -1"
  (declare (visibility :private))
  (let ((zero (is-zero y))
        (m1 (logand signed (= y (lnot (cast-unsigned (word-width y) 0)))))
        (d (fsel (logor zero m1) (cast-unsigned (word-width y) 1) y)))
    (fsel zero (lnot (cast-unsigned (word-width y) 0))
          (fsel m1 (neg x) (if signed (s/ x d) (/ x d))))))

(defun remainder (signed x y)
  "(remainder SIGNED X Y) is the remainder of X by Y, X if Y is 0, and
   0 if Y is -1, and SIGNED"
  (declare (visibility :private))
  (let ((zero (is-zero y))
        (m1 (logand signed (= y (lnot (cast-unsigned (word-width y) 0)))))
        (d (fsel (logor zero m1) (cast-unsigned (word-width y) 1) y)))
    (fsel zero x
          (fsel m1 (cast-unsigned (word-width y) 0)
                (if signed (signed-mod x d) (mod x d))))))

(defun DIVU (rd r1 r2) (set$ rd (divide false r1 r2)))
(defun REMU (rd r1 r2) (set$ rd (remainder false r1 r2)))
(defun DIV (rd r1 r2) (set$ rd (divide true r1 r2)))
(defun REM (rd r1 r2) (set$ rd (remainder true r1 r2)))

(defun DIVUW (rd r1 r2)
  (word-result rd (divide false (cast-low 32 r1) (cast-low 32 r2))))
(defun REMUW (rd r1 r2)
  (word-result rd (remainder false (cast-low 32 r1) (cast-low 32 r2))))
(defun DIVW (rd r1 r2)
  (word-result rd (divide true (cast-low 32 r1) (cast-low 32 r2))))
(defun REMW (rd r1 r2)
  (word-result rd (remainder true (cast-low 32 r1) (cast-low 32 r2))))

(defun FENCE (pred succ)
  (empty))

(defun FENCE_TSO ()
  (empty))

(defun FENCE_I ()
  (empty))

;; the system call, which the emulators run, e.g., the threads of Linux
(defun ECALL () (intrinsic 'syscall))

;; the breakpoints, and the instruction, that is defined to be illegal
(defun EBREAK () (intrinsic 'breakpoint :aborts))
(defun C_EBREAK () (intrinsic 'breakpoint :aborts))
(defun C_UNIMP () (intrinsic 'undefined-instruction :aborts))


;;; ATOMICS, the A extension, whose orderings are of no concern here, as
;;; the instructions run one at a time; the reservations of LR are not
;;; modeled, and SC succeeds; the operands are RD, RS2, and RS1

(defun AMOADD_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (+ old x))
    (word-result rd old)))
(defun AMOADD_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (+ old x))
    (word-result rd old)))
(defun AMOADD_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (+ old x))
    (word-result rd old)))
(defun AMOADD_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (+ old x))
    (word-result rd old)))
(defun AMOADD_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (+ old x))
    (set$ rd old)))
(defun AMOADD_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (+ old x))
    (set$ rd old)))
(defun AMOADD_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (+ old x))
    (set$ rd old)))
(defun AMOADD_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (+ old x))
    (set$ rd old)))
(defun AMOSWAP_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 x)
    (word-result rd old)))
(defun AMOSWAP_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 x)
    (word-result rd old)))
(defun AMOSWAP_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 x)
    (word-result rd old)))
(defun AMOSWAP_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 x)
    (word-result rd old)))
(defun AMOSWAP_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 x)
    (set$ rd old)))
(defun AMOSWAP_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 x)
    (set$ rd old)))
(defun AMOSWAP_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 x)
    (set$ rd old)))
(defun AMOSWAP_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 x)
    (set$ rd old)))
(defun AMOAND_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logand old x))
    (word-result rd old)))
(defun AMOAND_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logand old x))
    (word-result rd old)))
(defun AMOAND_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logand old x))
    (word-result rd old)))
(defun AMOAND_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logand old x))
    (word-result rd old)))
(defun AMOAND_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logand old x))
    (set$ rd old)))
(defun AMOAND_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logand old x))
    (set$ rd old)))
(defun AMOAND_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logand old x))
    (set$ rd old)))
(defun AMOAND_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logand old x))
    (set$ rd old)))
(defun AMOOR_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logor old x))
    (word-result rd old)))
(defun AMOOR_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logor old x))
    (word-result rd old)))
(defun AMOOR_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logor old x))
    (word-result rd old)))
(defun AMOOR_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logor old x))
    (word-result rd old)))
(defun AMOOR_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logor old x))
    (set$ rd old)))
(defun AMOOR_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logor old x))
    (set$ rd old)))
(defun AMOOR_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logor old x))
    (set$ rd old)))
(defun AMOOR_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logor old x))
    (set$ rd old)))
(defun AMOXOR_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logxor old x))
    (word-result rd old)))
(defun AMOXOR_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logxor old x))
    (word-result rd old)))
(defun AMOXOR_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logxor old x))
    (word-result rd old)))
(defun AMOXOR_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logxor old x))
    (word-result rd old)))
(defun AMOXOR_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logxor old x))
    (set$ rd old)))
(defun AMOXOR_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logxor old x))
    (set$ rd old)))
(defun AMOXOR_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logxor old x))
    (set$ rd old)))
(defun AMOXOR_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logxor old x))
    (set$ rd old)))
(defun AMOMAX_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s> old x) old x))
    (word-result rd old)))
(defun AMOMAX_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s> old x) old x))
    (word-result rd old)))
(defun AMOMAX_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s> old x) old x))
    (word-result rd old)))
(defun AMOMAX_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s> old x) old x))
    (word-result rd old)))
(defun AMOMAX_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s> old x) old x))
    (set$ rd old)))
(defun AMOMAX_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s> old x) old x))
    (set$ rd old)))
(defun AMOMAX_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s> old x) old x))
    (set$ rd old)))
(defun AMOMAX_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s> old x) old x))
    (set$ rd old)))
(defun AMOMIN_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s< old x) old x))
    (word-result rd old)))
(defun AMOMIN_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s< old x) old x))
    (word-result rd old)))
(defun AMOMIN_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s< old x) old x))
    (word-result rd old)))
(defun AMOMIN_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s< old x) old x))
    (word-result rd old)))
(defun AMOMIN_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s< old x) old x))
    (set$ rd old)))
(defun AMOMIN_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s< old x) old x))
    (set$ rd old)))
(defun AMOMIN_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s< old x) old x))
    (set$ rd old)))
(defun AMOMIN_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s< old x) old x))
    (set$ rd old)))
(defun AMOMAXU_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (> old x) old x))
    (word-result rd old)))
(defun AMOMAXU_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (> old x) old x))
    (word-result rd old)))
(defun AMOMAXU_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (> old x) old x))
    (word-result rd old)))
(defun AMOMAXU_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (> old x) old x))
    (word-result rd old)))
(defun AMOMAXU_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (> old x) old x))
    (set$ rd old)))
(defun AMOMAXU_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (> old x) old x))
    (set$ rd old)))
(defun AMOMAXU_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (> old x) old x))
    (set$ rd old)))
(defun AMOMAXU_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (> old x) old x))
    (set$ rd old)))
(defun AMOMINU_W (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (< old x) old x))
    (word-result rd old)))
(defun AMOMINU_W_AQ (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (< old x) old x))
    (word-result rd old)))
(defun AMOMINU_W_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (< old x) old x))
    (word-result rd old)))
(defun AMOMINU_W_AQ_RL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (< old x) old x))
    (word-result rd old)))
(defun AMOMINU_D (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (< old x) old x))
    (set$ rd old)))
(defun AMOMINU_D_AQ (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (< old x) old x))
    (set$ rd old)))
(defun AMOMINU_D_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (< old x) old x))
    (set$ rd old)))
(defun AMOMINU_D_AQ_RL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (< old x) old x))
    (set$ rd old)))
(defun LR_W (rd rs1) (word-result rd (load-bits 32 rs1)))
(defun LR_D (rd rs1) (set$ rd (core:load-word rs1)))
(defun SC_W (rd rs2 rs1)
  (store-word rs1 (cast-low 32 rs2))
  (set$ rd 0))
(defun SC_D (rd rs2 rs1)
  (store-word rs1 rs2)
  (set$ rd 0))
(defun LR_W_AQ (rd rs1) (word-result rd (load-bits 32 rs1)))
(defun LR_D_AQ (rd rs1) (set$ rd (core:load-word rs1)))
(defun SC_W_AQ (rd rs2 rs1)
  (store-word rs1 (cast-low 32 rs2))
  (set$ rd 0))
(defun SC_D_AQ (rd rs2 rs1)
  (store-word rs1 rs2)
  (set$ rd 0))
(defun LR_W_RL (rd rs1) (word-result rd (load-bits 32 rs1)))
(defun LR_D_RL (rd rs1) (set$ rd (core:load-word rs1)))
(defun SC_W_RL (rd rs2 rs1)
  (store-word rs1 (cast-low 32 rs2))
  (set$ rd 0))
(defun SC_D_RL (rd rs2 rs1)
  (store-word rs1 rs2)
  (set$ rd 0))
(defun LR_W_AQ_RL (rd rs1) (word-result rd (load-bits 32 rs1)))
(defun LR_D_AQ_RL (rd rs1) (set$ rd (core:load-word rs1)))
(defun SC_W_AQ_RL (rd rs2 rs1)
  (store-word rs1 (cast-low 32 rs2))
  (set$ rd 0))
(defun SC_D_AQ_RL (rd rs2 rs1)
  (store-word rs1 rs2)
  (set$ rd 0))

;; the orderings of both, as some versions of LLVM name them
(defun AMOADD_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (+ old x))
    (word-result rd old)))

(defun AMOADD_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (+ old x))
    (set$ rd old)))

(defun AMOSWAP_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 x)
    (word-result rd old)))

(defun AMOSWAP_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 x)
    (set$ rd old)))

(defun AMOAND_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logand old x))
    (word-result rd old)))

(defun AMOAND_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logand old x))
    (set$ rd old)))

(defun AMOOR_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logor old x))
    (word-result rd old)))

(defun AMOOR_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logor old x))
    (set$ rd old)))

(defun AMOXOR_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (logxor old x))
    (word-result rd old)))

(defun AMOXOR_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (logxor old x))
    (set$ rd old)))

(defun AMOMAX_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s> old x) old x))
    (word-result rd old)))

(defun AMOMAX_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s> old x) old x))
    (set$ rd old)))

(defun AMOMIN_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (s< old x) old x))
    (word-result rd old)))

(defun AMOMIN_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (s< old x) old x))
    (set$ rd old)))

(defun AMOMAXU_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (> old x) old x))
    (word-result rd old)))

(defun AMOMAXU_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (> old x) old x))
    (set$ rd old)))

(defun AMOMINU_W_AQRL (rd rs2 rs1)
  (let ((old (load-bits 32 rs1))
        (x (cast-low 32 rs2)))
    (store-word rs1 (if (< old x) old x))
    (word-result rd old)))

(defun AMOMINU_D_AQRL (rd rs2 rs1)
  (let ((old (core:load-word rs1))
        (x rs2))
    (store-word rs1 (if (< old x) old x))
    (set$ rd old)))

(defun LR_W_AQRL (rd rs1) (word-result rd (load-bits 32 rs1)))

(defun LR_D_AQRL (rd rs1) (set$ rd (core:load-word rs1)))

(defun SC_W_AQRL (rd rs2 rs1)
  (store-word rs1 (cast-low 32 rs2))
  (set$ rd 0))

(defun SC_D_AQRL (rd rs2 rs1)
  (store-word rs1 rs2)
  (set$ rd 0))


;;; FLOATING POINT, the F and D extensions
;;
;; The operations are the calls of the intrinsics of IEEE 754,
;; <op>_<rmode>_ieee754_binary_<size>, and, for the conversions,
;; <op>_<rmode>_ieee754_binary_<from>_<to>, which Primus runs exactly,
;; with the canonical NaNs, and the saturated integers, of RISC-V, see
;; ieee754-intrinsics.lisp. The fused multiply-adds round once, with
;; fmad. The rounding mode is the static rm field of the instruction,
;; and the dynamic one (7) is to nearest, ties to even, as frm, as
;; fcsr, is not modeled, neither are the accrued exception flags.
;;
;; The F registers are of 64 bits (FLEN), on RV32 too, and the
;; single-precision values in them are NaN-boxed, i.e., their upper 32
;; bits are ones, which the writes set, and a read of a value, that is
;; not boxed, is the canonical NaN.

(require bits)

(defun fpr-name (r)
  "the name of the F register of the operand R, which LLVM names by
   its format, e.g., F10_D, F10_F, or F10_H, all of them F10"
  (declare (visibility :private))
  (case (symbol r)
    'F0_D 'F0 'F0_F 'F0 'F0_H 'F0
    'F1_D 'F1 'F1_F 'F1 'F1_H 'F1
    'F2_D 'F2 'F2_F 'F2 'F2_H 'F2
    'F3_D 'F3 'F3_F 'F3 'F3_H 'F3
    'F4_D 'F4 'F4_F 'F4 'F4_H 'F4
    'F5_D 'F5 'F5_F 'F5 'F5_H 'F5
    'F6_D 'F6 'F6_F 'F6 'F6_H 'F6
    'F7_D 'F7 'F7_F 'F7 'F7_H 'F7
    'F8_D 'F8 'F8_F 'F8 'F8_H 'F8
    'F9_D 'F9 'F9_F 'F9 'F9_H 'F9
    'F10_D 'F10 'F10_F 'F10 'F10_H 'F10
    'F11_D 'F11 'F11_F 'F11 'F11_H 'F11
    'F12_D 'F12 'F12_F 'F12 'F12_H 'F12
    'F13_D 'F13 'F13_F 'F13 'F13_H 'F13
    'F14_D 'F14 'F14_F 'F14 'F14_H 'F14
    'F15_D 'F15 'F15_F 'F15 'F15_H 'F15
    'F16_D 'F16 'F16_F 'F16 'F16_H 'F16
    'F17_D 'F17 'F17_F 'F17 'F17_H 'F17
    'F18_D 'F18 'F18_F 'F18 'F18_H 'F18
    'F19_D 'F19 'F19_F 'F19 'F19_H 'F19
    'F20_D 'F20 'F20_F 'F20 'F20_H 'F20
    'F21_D 'F21 'F21_F 'F21 'F21_H 'F21
    'F22_D 'F22 'F22_F 'F22 'F22_H 'F22
    'F23_D 'F23 'F23_F 'F23 'F23_H 'F23
    'F24_D 'F24 'F24_F 'F24 'F24_H 'F24
    'F25_D 'F25 'F25_F 'F25 'F25_H 'F25
    'F26_D 'F26 'F26_F 'F26 'F26_H 'F26
    'F27_D 'F27 'F27_F 'F27 'F27_H 'F27
    'F28_D 'F28 'F28_F 'F28 'F28_H 'F28
    'F29_D 'F29 'F29_F 'F29 'F29_H 'F29
    'F30_D 'F30 'F30_F 'F30 'F30_H 'F30
    'F31_D 'F31 'F31_F 'F31 'F31_H 'F31
    (symbol r)))


(defun fpr (r)
  "the raw bits of the F register of the operand R"
  (declare (visibility :private))
  (unquote (fpr-name r)))

(defun set-fpr (r x)
  (declare (visibility :private))
  (set-symbol-value (fpr-name r) x))

(defun fsel (c x y)
  "(fsel C X Y) is X if C, else Y, without a branch, as Primus evaluates
   both arms of an expression"
  (declare (visibility :private))
  (let ((m (neg (cast-unsigned (word-width x) c))))
    (logor (logand m x) (logand (lnot m) y))))

(defun fs (r)
  "the single-precision value of the F register of the operand R"
  (declare (visibility :private))
  (let ((v (fpr r)))
    (fsel (= (cast-high 32 v) 0xffffffff:32)
          (cast-low 32 v)
          0x7fc00000:32)))

(defun set-fs (r x)
  "boxes the single-precision X in the F register of the operand R"
  (declare (visibility :private))
  (set-fpr r (concat 0xffffffff:32 (cast-low 32 x))))

(defun fget (n r)
  (declare (visibility :private))
  (if (= n 64) (fpr r) (fs r)))

(defun fset (n r x)
  (declare (visibility :private))
  (if (= n 64) (set-fpr r x) (set-fs r x)))

(defun fsize (n)
  (declare (visibility :private))
  (case n 32 '32 64 '64 'unknown))

(defun frm (rm)
  "the rounding mode of the rm field, the dynamic one is to nearest"
  (declare (visibility :private))
  (case rm 0 'rne 1 'rtz 2 'rtn 3 'rtp 4 'rna 'rne))

(defun fcall (name rm n x y)
  (declare (visibility :private))
  (intrinsic (symbol-concat name (frm rm) 'ieee754_binary (fsize n) :sep '_)
             x y :result n))

(defun fbinary (name n rd rs1 rs2 rm)
  (declare (visibility :private))
  (fset n rd (fcall name rm n (fget n rs1) (fget n rs2))))

(defun fsquare-root (n rd rs1 rm)
  (declare (visibility :private))
  (fset n rd (intrinsic (symbol-concat 'fsqrt (frm rm) 'ieee754_binary
                                       (fsize n) :sep '_)
                        (fget n rs1) :result n)))

(defun fp-negate (x)
  (declare (visibility :private))
  (logxor x (lshift (cast-unsigned (word-width x) 1) (- (word-width x) 1))))

(defun ffused (n rd x y z rm)
  "RD is X * Y + Z, rounded once"
  (declare (visibility :private))
  (fset n rd (intrinsic (symbol-concat 'fmad (frm rm) 'ieee754_binary
                                       (fsize n) :sep '_)
                        x y z :result n)))

(defun fcanonical (n)
  (declare (visibility :private))
  (if (= n 64) 0x7ff8000000000000:64 0x7fc00000:32))

(defun fnan (x)
  "true if X is a NaN, i.e., its magnitude is above the infinity"
  (declare (visibility :private))
  (let ((n (word-width x)))
    (> (cast-low (- n 1) x)
       (cast-low (- n 1) (if (= n 64) 0x7ff0000000000000:64 0x7f800000:32)))))

(defun fkey (x)
  "the signed integer, whose order is the order of the numbers X, and
   which is 0 for both zeros"
  (declare (visibility :private))
  (let ((mag (cast-unsigned (word-width x) (cast-low (- (word-width x) 1) x))))
    (fsel (msb x) (neg mag) mag)))

(defun fordered (x y)
  (declare (visibility :private))
  (logand (not (fnan x)) (not (fnan y))))

(defun flt (x y)
  (declare (visibility :private))
  (logand (fordered x y) (s< (fkey x) (fkey y))))

(defun feq (x y)
  (declare (visibility :private))
  (logand (fordered x y) (= (fkey x) (fkey y))))

(defun fle (x y)
  (declare (visibility :private))
  (logand (fordered x y) (s<= (fkey x) (fkey y))))

(defun fcompare (cmp n rd rs1 rs2)
  (declare (visibility :private))
  (let ((x (fget n rs1)) (y (fget n rs2)))
    (set$ rd (cast-unsigned (word-width)
                            (case cmp
                              'eq (feq x y)
                              'lt (flt x y)
                              'le (fle x y))))))

(defun fminmax (max n rd rs1 rs2)
  "the minimumNumber and the maximumNumber of IEEE 754-2019, as the F
   extension 2.2: a NaN operand is ignored, both NaNs are the canonical
   NaN, and -0.0 is less than +0.0"
  (declare (visibility :private))
  (let ((x (fget n rs1))
        (y (fget n rs2))
        (lt (s< (fkey x) (fkey y)))
        (gt (s< (fkey y) (fkey x)))
        (r (if max
               (fsel lt y (fsel gt x (logand x y)))
             (fsel lt x (fsel gt y (logor x y))))))
    (fset n rd (fsel (logand (fnan x) (fnan y)) (fcanonical n)
                     (fsel (fnan x) y
                           (fsel (fnan y) x r))))))

(defun fsign-inject (op n rd rs1 rs2)
  (declare (visibility :private))
  (let ((x (fget n rs1))
        (y (fget n rs2))
        (s (case op
             'j (msb y)
             'n (not (msb y))
             'x (logxor (msb x) (msb y)))))
    (fset n rd (concat s (cast-low (- n 1) x)))))

(defun fclassify (n rd rs1)
  "the class of the number, one of its 10 bits: -inf, -normal,
   -subnormal, -0, +0, +subnormal, +normal, +inf, sNaN, and qNaN"
  (declare (visibility :private))
  (let ((x (fget n rs1))
        (f (if (= n 64) 52 23))
        (neg (msb x))
        (pos (not (msb x)))
        (frac (cast-low f x))
        (top (is-zero (lnot (extract (- n 2) f x))))
        (low (is-zero (extract (- n 2) f x)))
        (nofrac (is-zero frac))
        (quiet (select (- f 1) x))
        (inf (logand top nofrac))
        (nan (logand top (not nofrac)))
        (zero (logand low nofrac))
        (sub (logand low (not nofrac)))
        (normal (logand (not top) (not low))))
    (set$ rd (cast-unsigned
              (word-width)
              (concat (logand nan quiet)
                      (logand nan (not quiet))
                      (logand pos inf)
                      (logand pos normal)
                      (logand pos sub)
                      (logand pos zero)
                      (logand neg zero)
                      (logand neg sub)
                      (logand neg normal)
                      (logand neg inf))))))

(defun fto-int (signed m n rd rs1 rm)
  "converts the N-bit number to the M-bit integer, which is extended by
   its sign to the width of the register"
  (declare (visibility :private))
  (set$ rd (cast-signed
            (word-width)
            (intrinsic (symbol-concat (if signed 'cast_sint 'cast_int)
                                      (frm rm) 'ieee754_binary
                                      (fsize n) (fsize m) :sep '_)
                       (fget n rs1) :result m))))

(defun ffrom-int (signed m n rd rs1 rm)
  "converts the lower M bits of the register to the N-bit number"
  (declare (visibility :private))
  (fset n rd (intrinsic (symbol-concat (if signed 'cast_sfloat 'cast_float)
                                       (frm rm) 'ieee754_binary
                                       (fsize m) (fsize n) :sep '_)
                        (cast-low m rs1) :result n)))

(defun fp-convert (m n rd rs1 rm)
  "converts the M-bit number to the N-bit one"
  (declare (visibility :private))
  (fset n rd (intrinsic (symbol-concat 'fconvert (frm rm) 'ieee754_binary
                                       (fsize m) (fsize n) :sep '_)
                        (fget m rs1) :result n)))

;; loads and stores

(defun FLW (rd rs1 off) (set-fs rd (load-bits 32 (+ rs1 off))))
(defun C_FLW (rd rs1 off) (set-fs rd (load-bits 32 (+ rs1 off))))
(defun C_FLWSP (rd rs1 off) (set-fs rd (load-bits 32 (+ rs1 off))))
(defun FSW (rs2 rs1 off) (store-word (+ rs1 off) (cast-low 32 (fpr rs2))))
(defun C_FSW (rs2 rs1 off) (store-word (+ rs1 off) (cast-low 32 (fpr rs2))))
(defun C_FSWSP (rs2 rs1 off) (store-word (+ rs1 off) (cast-low 32 (fpr rs2))))

;; single precision

(defun FADD_S (rd rs1 rs2 rm) (fbinary 'fadd 32 rd rs1 rs2 rm))
(defun FSUB_S (rd rs1 rs2 rm) (fbinary 'fsub 32 rd rs1 rs2 rm))
(defun FMUL_S (rd rs1 rs2 rm) (fbinary 'fmul 32 rd rs1 rs2 rm))
(defun FDIV_S (rd rs1 rs2 rm) (fbinary 'fdiv 32 rd rs1 rs2 rm))
(defun FSQRT_S (rd rs1 rm) (fsquare-root 32 rd rs1 rm))
(defun FMIN_S (rd rs1 rs2) (fminmax false 32 rd rs1 rs2))
(defun FMAX_S (rd rs1 rs2) (fminmax true 32 rd rs1 rs2))

(defun FMADD_S (rd rs1 rs2 rs3 rm)
  (ffused 32 rd (fs rs1) (fs rs2) (fs rs3) rm))
(defun FMSUB_S (rd rs1 rs2 rs3 rm)
  (ffused 32 rd (fs rs1) (fs rs2) (fp-negate (fs rs3)) rm))
(defun FNMSUB_S (rd rs1 rs2 rs3 rm)
  (ffused 32 rd (fp-negate (fs rs1)) (fs rs2) (fs rs3) rm))
(defun FNMADD_S (rd rs1 rs2 rs3 rm)
  (ffused 32 rd (fp-negate (fs rs1)) (fs rs2) (fp-negate (fs rs3)) rm))

(defun FSGNJ_S (rd rs1 rs2) (fsign-inject 'j 32 rd rs1 rs2))
(defun FSGNJN_S (rd rs1 rs2) (fsign-inject 'n 32 rd rs1 rs2))
(defun FSGNJX_S (rd rs1 rs2) (fsign-inject 'x 32 rd rs1 rs2))

(defun FEQ_S (rd rs1 rs2) (fcompare 'eq 32 rd rs1 rs2))
(defun FLT_S (rd rs1 rs2) (fcompare 'lt 32 rd rs1 rs2))
(defun FLE_S (rd rs1 rs2) (fcompare 'le 32 rd rs1 rs2))
(defun FCLASS_S (rd rs1) (fclassify 32 rd rs1))

(defun FMV_X_W (rd rs1)
  "the raw bits, extended by their sign, of a boxed value or not"
  (set$ rd (cast-signed (word-width) (cast-low 32 (fpr rs1)))))
(defun FMV_W_X (rd rs1) (set-fs rd (cast-low 32 rs1)))

(defun FCVT_W_S (rd rs1 rm) (fto-int true 32 32 rd rs1 rm))
(defun FCVT_WU_S (rd rs1 rm) (fto-int false 32 32 rd rs1 rm))
(defun FCVT_S_W (rd rs1 rm) (ffrom-int true 32 32 rd rs1 rm))
(defun FCVT_S_WU (rd rs1 rm) (ffrom-int false 32 32 rd rs1 rm))

(defun FCVT_L_S (rd rs1 rm)
  (declare (context (bits 64)))
  (fto-int true 64 32 rd rs1 rm))
(defun FCVT_LU_S (rd rs1 rm)
  (declare (context (bits 64)))
  (fto-int false 64 32 rd rs1 rm))
(defun FCVT_S_L (rd rs1 rm)
  (declare (context (bits 64)))
  (ffrom-int true 64 32 rd rs1 rm))
(defun FCVT_S_LU (rd rs1 rm)
  (declare (context (bits 64)))
  (ffrom-int false 64 32 rd rs1 rm))

;; double precision; the conversions of the 64-bit integers, and the
;; moves of the 64-bit X registers, are of RV64

(defun FLD (rd rs1 off)
  (set-fpr rd (load-bits 64 (+ rs1 off))))
(defun C_FLD (rd rs1 off)
  (set-fpr rd (load-bits 64 (+ rs1 off))))
(defun C_FLDSP (rd rs1 off)
  (set-fpr rd (load-bits 64 (+ rs1 off))))
(defun FSD (rs2 rs1 off)
  (store-word (+ rs1 off) (fpr rs2)))
(defun C_FSD (rs2 rs1 off)
  (store-word (+ rs1 off) (fpr rs2)))
(defun C_FSDSP (rs2 rs1 off)
  (store-word (+ rs1 off) (fpr rs2)))

(defun FADD_D (rd rs1 rs2 rm)
  (fbinary 'fadd 64 rd rs1 rs2 rm))
(defun FSUB_D (rd rs1 rs2 rm)
  (fbinary 'fsub 64 rd rs1 rs2 rm))
(defun FMUL_D (rd rs1 rs2 rm)
  (fbinary 'fmul 64 rd rs1 rs2 rm))
(defun FDIV_D (rd rs1 rs2 rm)
  (fbinary 'fdiv 64 rd rs1 rs2 rm))
(defun FSQRT_D (rd rs1 rm)
  (fsquare-root 64 rd rs1 rm))
(defun FMIN_D (rd rs1 rs2)
  (fminmax false 64 rd rs1 rs2))
(defun FMAX_D (rd rs1 rs2)
  (fminmax true 64 rd rs1 rs2))

(defun FMADD_D (rd rs1 rs2 rs3 rm)
  (ffused 64 rd (fpr rs1) (fpr rs2) (fpr rs3) rm))
(defun FMSUB_D (rd rs1 rs2 rs3 rm)
  (ffused 64 rd (fpr rs1) (fpr rs2) (fp-negate (fpr rs3)) rm))
(defun FNMSUB_D (rd rs1 rs2 rs3 rm)
  (ffused 64 rd (fp-negate (fpr rs1)) (fpr rs2) (fpr rs3) rm))
(defun FNMADD_D (rd rs1 rs2 rs3 rm)
  (ffused 64 rd (fp-negate (fpr rs1)) (fpr rs2) (fp-negate (fpr rs3)) rm))

(defun FSGNJ_D (rd rs1 rs2)
  (fsign-inject 'j 64 rd rs1 rs2))
(defun FSGNJN_D (rd rs1 rs2)
  (fsign-inject 'n 64 rd rs1 rs2))
(defun FSGNJX_D (rd rs1 rs2)
  (fsign-inject 'x 64 rd rs1 rs2))

(defun FEQ_D (rd rs1 rs2)
  (fcompare 'eq 64 rd rs1 rs2))
(defun FLT_D (rd rs1 rs2)
  (fcompare 'lt 64 rd rs1 rs2))
(defun FLE_D (rd rs1 rs2)
  (fcompare 'le 64 rd rs1 rs2))
(defun FCLASS_D (rd rs1)
  (fclassify 64 rd rs1))

(defun FMV_X_D (rd rs1)
  (declare (context (bits 64)))
  (set$ rd (fpr rs1)))
(defun FMV_D_X (rd rs1)
  (declare (context (bits 64)))
  (set-fpr rd rs1))

(defun FCVT_W_D (rd rs1 rm)
  (fto-int true 32 64 rd rs1 rm))
(defun FCVT_WU_D (rd rs1 rm)
  (fto-int false 32 64 rd rs1 rm))
(defun FCVT_L_D (rd rs1 rm)
  (declare (context (bits 64)))
  (fto-int true 64 64 rd rs1 rm))
(defun FCVT_LU_D (rd rs1 rm)
  (declare (context (bits 64)))
  (fto-int false 64 64 rd rs1 rm))
(defun FCVT_D_W (rd rs1 rm)
  (ffrom-int true 32 64 rd rs1 rm))
(defun FCVT_D_WU (rd rs1 rm)
  (ffrom-int false 32 64 rd rs1 rm))
(defun FCVT_D_L (rd rs1 rm)
  (declare (context (bits 64)))
  (ffrom-int true 64 64 rd rs1 rm))
(defun FCVT_D_LU (rd rs1 rm)
  (declare (context (bits 64)))
  (ffrom-int false 64 64 rd rs1 rm))
(defun FCVT_S_D (rd rs1 rm)
  (fp-convert 64 32 rd rs1 rm))
(defun FCVT_D_S (rd rs1 rm)
  (fp-convert 32 64 rd rs1 rm))


;;; BIT MANIPULATION, the Zba, Zbb, and Zbs extensions, of which the W
;;; forms, and the unsigned words, .UW, are of RV64

(defun zext32 (x)
  "the lower 32 bits of X, extended by zeros to the width of the word"
  (declare (visibility :private))
  (cast-unsigned (word-width) (cast-low 32 x)))

(defun SH1ADD (rd rs1 rs2) (set$ rd (+ (lshift rs1 1) rs2)))
(defun SH2ADD (rd rs1 rs2) (set$ rd (+ (lshift rs1 2) rs2)))
(defun SH3ADD (rd rs1 rs2) (set$ rd (+ (lshift rs1 3) rs2)))
(defun SH1ADD_UW (rd rs1 rs2) (set$ rd (+ (lshift (zext32 rs1) 1) rs2)))
(defun SH2ADD_UW (rd rs1 rs2) (set$ rd (+ (lshift (zext32 rs1) 2) rs2)))
(defun SH3ADD_UW (rd rs1 rs2) (set$ rd (+ (lshift (zext32 rs1) 3) rs2)))
(defun ADD_UW (rd rs1 rs2) (set$ rd (+ (zext32 rs1) rs2)))
(defun SLLI_UW (rd rs1 sh) (set$ rd (lshift (zext32 rs1) sh)))

(defun ANDN (rd rs1 rs2) (set$ rd (logand rs1 (lnot rs2))))
(defun ORN (rd rs1 rs2) (set$ rd (logor rs1 (lnot rs2))))
(defun XNOR (rd rs1 rs2) (set$ rd (lnot (logxor rs1 rs2))))

(defun count-trailing-zeros (x)
  "the number of the trailing zeros of X, its width if X is 0"
  (declare (visibility :private))
  (popcount (logand (lnot x) (- x (cast-unsigned (word-width x) 1)))))

(defun count-result (rd n)
  (declare (visibility :private))
  (set$ rd (cast-unsigned (word-width) n)))

(defun CLZ (rd rs1) (count-result rd (clz rs1)))
(defun CTZ (rd rs1) (count-result rd (count-trailing-zeros rs1)))
(defun CPOP (rd rs1) (count-result rd (popcount rs1)))
(defun CLZW (rd rs1) (count-result rd (clz (cast-low 32 rs1))))
(defun CTZW (rd rs1) (count-result rd (count-trailing-zeros (cast-low 32 rs1))))
(defun CPOPW (rd rs1) (count-result rd (popcount (cast-low 32 rs1))))

(defun MAX (rd rs1 rs2) (set$ rd (fsel (s< rs1 rs2) rs2 rs1)))
(defun MIN (rd rs1 rs2) (set$ rd (fsel (s< rs1 rs2) rs1 rs2)))
(defun MAXU (rd rs1 rs2) (set$ rd (fsel (< rs1 rs2) rs2 rs1)))
(defun MINU (rd rs1 rs2) (set$ rd (fsel (< rs1 rs2) rs1 rs2)))

(defun SEXT_B (rd rs1) (set$ rd (cast-signed (word-width) (cast-low 8 rs1))))
(defun SEXT_H (rd rs1) (set$ rd (cast-signed (word-width) (cast-low 16 rs1))))
(defun ZEXT_H_RV32 (rd rs1) (set$ rd (cast-unsigned (word-width) (cast-low 16 rs1))))
(defun ZEXT_H_RV64 (rd rs1) (set$ rd (cast-unsigned (word-width) (cast-low 16 rs1))))

(defun rotation (x)
  "the amount of the rotations of the word, its lower log2 XLEN bits"
  (declare (visibility :private))
  (logand x (- (word-width) 1)))

(defun ROL (rd rs1 rs2) (set$ rd (rotate-left rs1 (rotation rs2))))
(defun ROR (rd rs1 rs2) (set$ rd (rotate-right rs1 (rotation rs2))))
(defun RORI (rd rs1 sh) (set$ rd (rotate-right rs1 sh)))
(defun ROLW (rd rs1 rs2)
  (word-result rd (rotate-left (cast-low 32 rs1) (cast-low 32 (logand rs2 31)))))
(defun RORW (rd rs1 rs2)
  (word-result rd (rotate-right (cast-low 32 rs1) (cast-low 32 (logand rs2 31)))))
(defun RORIW (rd rs1 sh)
  (word-result rd (rotate-right (cast-low 32 rs1) (cast-low 32 sh))))

(defun REV8_RV32 (rd rs1)
  (set$ rd (concat (extract 7 0 rs1) (extract 15 8 rs1)
                   (extract 23 16 rs1) (extract 31 24 rs1))))

(defun REV8_RV64 (rd rs1)
  (set$ rd (concat (extract 7 0 rs1) (extract 15 8 rs1)
                   (extract 23 16 rs1) (extract 31 24 rs1)
                   (extract 39 32 rs1) (extract 47 40 rs1)
                   (extract 55 48 rs1) (extract 63 56 rs1))))

(defun or-combine (b)
  "0xFF if the byte B is not zero, else 0"
  (declare (visibility :private))
  (cast-signed 8 (not (is-zero b))))

(defun ORC_B (rd rs1)
  (declare (context (bits 64)))
  (set$ rd (concat (or-combine (extract 63 56 rs1)) (or-combine (extract 55 48 rs1))
                   (or-combine (extract 47 40 rs1)) (or-combine (extract 39 32 rs1))
                   (or-combine (extract 31 24 rs1)) (or-combine (extract 23 16 rs1))
                   (or-combine (extract 15 8 rs1)) (or-combine (extract 7 0 rs1)))))

(defun ORC_B (rd rs1)
  (declare (context (bits 32)))
  (set$ rd (concat (or-combine (extract 31 24 rs1)) (or-combine (extract 23 16 rs1))
                   (or-combine (extract 15 8 rs1)) (or-combine (extract 7 0 rs1)))))

(defun single-bit (n)
  "the word, whose bit N, of the lower log2 XLEN bits of N, is set"
  (declare (visibility :private))
  (lshift (cast-unsigned (word-width) 1) (rotation n)))

(defun BSET (rd rs1 rs2) (set$ rd (logor rs1 (single-bit rs2))))
(defun BCLR (rd rs1 rs2) (set$ rd (logand rs1 (lnot (single-bit rs2)))))
(defun BINV (rd rs1 rs2) (set$ rd (logxor rs1 (single-bit rs2))))
(defun BEXT (rd rs1 rs2)
  (set$ rd (logand (rshift rs1 (rotation rs2)) (cast-unsigned (word-width) 1))))
(defun BSETI (rd rs1 n) (BSET rd rs1 n))
(defun BCLRI (rd rs1 n) (BCLR rd rs1 n))
(defun BINVI (rd rs1 n) (BINV rd rs1 n))
(defun BEXTI (rd rs1 n) (BEXT rd rs1 n))


;;; CONTROL AND STATUS REGISTERS, as far as the compilers emit them,
;;; i.e., the ones of the floating point: fflags (1), frm (2), and fcsr
;;; (3), which are not modeled, so their reads are 0, i.e., no
;;; exceptions, and the rounding to nearest, and their writes are
;;; ignored. The other registers, e.g., the counters, are read with the
;;; intrinsic riscv_csr_<number>, and written with riscv_set_csr_<number>.

(defun fcsr (csr)
  (declare (visibility :private))
  (logand (<= 1 csr) (<= csr 3)))

;; the counters, that the programs read, which the emulators provide,
;; e.g., from the clock, which they don't write
(defun counter (csr)
  (declare (visibility :private))
  (logand (<= 0xC00 csr) (<= csr 0xC02)))

(defun read-counter (csr)
  (declare (visibility :private))
  (case csr
    0xC00 (intrinsic 'riscv_csr_cycle :result (word-width))
    0xC01 (intrinsic 'riscv_csr_time :result (word-width))
    (intrinsic 'riscv_csr_instret :result (word-width))))

(defun csr-access (rd csr x write)
  "reads the CSR to RD, and writes X to it, if WRITE: the flags and the
   rounding mode of the floats, which are not modeled, are 0, and their
   writes are ignored, the counters are read, and the other CSRs, e.g.,
   of the extensions, that are not modeled, and the writes of the
   counters, are illegal, as in the user mode of Linux"
  (declare (visibility :private))
  (if (fcsr csr)
      (set$ rd 0)
    (if (logand (counter csr) (not write))
        (set$ rd (read-counter csr))
      (intrinsic 'undefined-instruction :aborts))))

(defun CSRRW (rd csr rs1) (csr-access rd csr rs1 true))
(defun CSRRS (rd csr rs1) (csr-access rd csr rs1 (/= (symbol rs1) 'X0)))
(defun CSRRC (rd csr rs1) (csr-access rd csr rs1 (/= (symbol rs1) 'X0)))
(defun CSRRWI (rd csr imm) (csr-access rd csr imm true))
(defun CSRRSI (rd csr imm) (csr-access rd csr imm (/= imm 0)))
(defun CSRRCI (rd csr imm) (csr-access rd csr imm (/= imm 0)))
