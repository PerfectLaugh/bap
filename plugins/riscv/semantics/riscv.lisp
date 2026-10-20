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
             (cast-low (/ (word-width) 2)
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

(defmacro load-word (cast part dst reg off)
  (set$ dst (cast (word-width)
                  (load-bits (/ (word-width) part) (+ reg off)))))

(defun LW (dst reg off)
  (load-word cast-signed 2 dst reg off))

(defun C_LW (dst reg off)
  (load-word cast-signed 2 dst reg off))

(defun LH (dst reg off)
  (load-word cast-signed 4 dst reg off))

(defun LWU (dst reg off)
  (load-word cast-unsigned 2 dst reg off))

(defun LB (dst reg off)
  (set$ dst (cast-signed (word-width) (load-byte (+ reg off)))))

(defun LBU (dst reg off)
  (set$ dst (cast-unsigned (word-width) (load-byte (+ reg off)))))

(defun LHU (dst reg off)
  (load-word cast-unsigned 4 dst reg off))

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
  (store-word (+ reg imm) (cast-low (/ (word-width) 2) val)))

(defun SH (val reg imm)
  (store-word (+ reg imm) (cast-low (/ (word-width) 4) val)))

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
  (load-word cast-signed 2 dst sp off))

(defun C_SWSP (val sp off)
  (store-word (+ sp off) (cast-low (/ (word-width) 2) val)))

(defun C_SW (val reg off)
  (store-word (+ reg off) (cast-low (/ (word-width) 2) val)))

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

(defun DIVU (rd r1 r2)
  (set$ rd (if (is-zero r2) (lnot 0) (/ r1 r2))))

(defun REMU (rd r1 r2)
  (set$ rd (if (is-zero r2) r1 (mod r1 r2))))

(defun DIV (rd r1 r2)
  (set$ rd (if (is-zero r2) (lnot 0)
             (if (= r2 (lnot 0)) (neg r1) (s/ r1 r2)))))

(defun REM (rd r1 r2)
  (set$ rd (if (is-zero r2) r1
             (if (= r2 (lnot 0)) 0 (signed-mod r1 r2)))))

(defun DIVUW (rd r1 r2)
  (let ((x (cast-low 32 r1))
        (y (cast-low 32 r2)))
    (word-result rd (if (is-zero y) (lnot 0) (/ x y)))))

(defun REMUW (rd r1 r2)
  (let ((x (cast-low 32 r1))
        (y (cast-low 32 r2)))
    (word-result rd (if (is-zero y) x (mod x y)))))

(defun DIVW (rd r1 r2)
  (let ((x (cast-low 32 r1))
        (y (cast-low 32 r2)))
    (word-result rd (if (is-zero y) (lnot 0)
                      (if (= y (lnot 0)) (neg x) (s/ x y))))))

(defun REMW (rd r1 r2)
  (let ((x (cast-low 32 r1))
        (y (cast-low 32 r2)))
    (word-result rd (if (is-zero y) x
                      (if (= y (lnot 0)) 0 (signed-mod x y))))))

(defun FENCE (pred succ)
  (empty))
