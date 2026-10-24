(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; SPECIAL INSTRUCTIONS

;; The barriers have no effect on a single thread.

(defun DMB (_) (empty))

;; the speculation barrier, which the decoder of FEAT_SB decodes, and
;; else decodes as MSR, see below
(defun SB () (empty))

(defun DSB (_) (empty))

(defun ISB (_) (empty))

;; The hints, e.g., YIELD, WFE, WFI, SEV, SEVL, DGH, ESB, PSB CSYNC,
;; TSB CSYNC, CSDB, and BTI, which have no effect on a single thread, and
;; the hints, that are not allocated, which the architecture runs as NOPs.
(defun HINT (_)
  (empty))

(defun NOP ()
  (empty))

(defun UDF (exn)
  (intrinsic 'undefined-instruction :aborts))

;; the breakpoint and the halting debug exceptions
(defun BRK (imm) (intrinsic 'breakpoint imm :aborts))
(defun HLT (imm) (intrinsic 'halt imm))

;; the supervisor call
(defun SVC (imm) (intrinsic 'svc imm))

;; The pointer authentication is not modeled, the instructions that
;; sign, authenticate or strip the authentication code of LR or X17
;; keep the register, so that a signed and authenticated return
;; address is the original one, as when the authentication succeeds.
(defun PACIASP () (empty))
(defun PACIBSP () (empty))
(defun AUTIASP () (empty))
(defun AUTIBSP () (empty))
(defun PACIAZ () (empty))
(defun PACIBZ () (empty))
(defun AUTIAZ () (empty))
(defun AUTIBZ () (empty))
(defun PACIA1716 () (empty))
(defun PACIB1716 () (empty))
(defun AUTIA1716 () (empty))
(defun AUTIB1716 () (empty))
(defun XPACLRI () (empty))

;; the instruction, that the processor doesn't have, e.g., the system
;; register, that it doesn't have, which raises the exception of the
;; undefined instructions, as SIGILL of Linux
(defun a64-undefined () (intrinsic 'undefined-instruction :aborts))

(defun a64-nzcv ()
  "the flags as the register NZCV"
  (logor (lshift (cast-unsigned 64 NF) 31) (lshift (cast-unsigned 64 ZF) 30)
         (lshift (cast-unsigned 64 CF) 29) (lshift (cast-unsigned 64 VF) 28)))

;; the virtual counter, which only Primus has, as the one of Unicorn is
;; of the host, advances by 1000 ticks of CNTFRQ_EL0, i.e., by 16 us, at
;; each read, so that the programs, that wait for it, see it advance
(defun a64-counter ()
  (set CNTVCT_EL0 (+ CNTVCT_EL0 1000))
  CNTVCT_EL0)

;; the cache maintenance by the virtual address, which has no effect, as
;; the caches are not modeled, but DC ZVA, which zeroes the block of
;; DCZID_EL0, 64 bytes, at the address, that it aligns
(defun a64-dc-zva (addr)
  (let ((a (logand addr (lnot 63))))
    (store-word a 0:64)
    (store-word (+ a 8) 0:64)
    (store-word (+ a 16) 0:64)
    (store-word (+ a 24) 0:64)
    (store-word (+ a 32) 0:64)
    (store-word (+ a 40) 0:64)
    (store-word (+ a 48) 0:64)
    (store-word (+ a 56) 0:64)))

(in-package llvm-aarch64)

;; The system registers by their encodings, op0:op1:CRn:CRm:op2, that
;; the programs read, the ones, that the processor of Unicorn has, with
;; its values, e.g., of its identification, as Linux emulates their reads
;; at EL0, and the counter, see [a64-counter].
(defun MRS (dst reg)
  (case reg
    0xde82 (set$ dst TPIDR_EL0)
    0xde83 (set$ dst TPIDRRO_EL0)
    0xda10 (set$ dst (a64-nzcv))
    0xda11 (set$ dst 0x3c0)                     ; DAIF, the interrupts are masked
    0xda20 (set$ dst (cast-unsigned 64 FPCR))
    0xda21 (set$ dst (cast-unsigned 64 FPSR))
    0xd807 (set$ dst 4)                         ; DCZID_EL0, the blocks of 64 bytes
    0xd801 (set$ dst 0x8444c004)                ; CTR_EL0
    0xdf00 (set$ dst 0x3b9aca0)                 ; CNTFRQ_EL0, 62.5 MHz
    0xdf01 (set$ dst (a64-counter))             ; CNTPCT_EL0
    0xdf02 (set$ dst (a64-counter))             ; CNTVCT_EL0
    0xc000 (set$ dst 0xf0510)                   ; MIDR_EL1
    0xc005 (set$ dst 0x80000000)                ; MPIDR_EL1
    0xc006 (set$ dst 0)                         ; REVIDR_EL1
    0xc020 (set$ dst 0x100112222)               ; ID_AA64PFR0_EL1
    0xc021 (set$ dst 1)                         ; ID_AA64PFR1_EL1
    0xc028 (set$ dst 0x10305506)                ; ID_AA64DFR0_EL1
    0xc030 (set$ dst 0x1021111110212120)        ; ID_AA64ISAR0_EL1
    0xc031 (set$ dst 0x11101211012)             ; ID_AA64ISAR1_EL1
    0xc038 (set$ dst 0x1124)                    ; ID_AA64MMFR0_EL1
    0xc039 (set$ dst 0x211120)                  ; ID_AA64MMFR1_EL1
    0xc03a (set$ dst 0x11)                      ; ID_AA64MMFR2_EL1
    (a64-undefined)))

;; The system registers, that the programs write, and SB, which the
;; disassembler decodes as MSR, the speculation barrier, which has no
;; effect on a single thread.
(defun MSR (reg src)
  (case reg
    0xde82 (set TPIDR_EL0 src)
    0xde83 (set TPIDRRO_EL0 src)
    0xda10 (set-nzcv (cast-low 4 (rshift src 28)))
    0xda20 (set FPCR (cast-low 32 src))
    0xda21 (set FPSR (cast-low 32 src))
    0x1987 (empty)                              ; SB
    (a64-undefined)))

;; The fields of PSTATE, that MSR sets to an immediate, which Unicorn
;; runs, at EL1, with no effect on the program: DAIFSet, DAIFClr, SPSel,
;; UAO, and PAN.
;; SMSTART and SMSTOP of SME, which the processor of Unicorn doesn't
;; have, as the programs, e.g., glibc, run them, only if it has SME
(defun MSRpstatesvcrImm1 (_ _) (a64-undefined))

(defun MSRpstateImm4 (field _)
  (case field
    0x1e (empty)
    0x1f (empty)
    0x05 (empty)
    0x03 (empty)
    0x04 (empty)
    (a64-undefined)))

;; The cache maintenance, by op1:CRn:CRm:op2: DC ZVA zeroes its block,
;; and DC CVAU, CIVAC, CVAC, CVAP, CVADP, IVAC, IC IVAU, IALLU, and
;; IALLUIS have no effect, as the caches are not modeled, and the code,
;; that the program writes, runs anew, when it is written.
(defun SYSxt (op1 crn crm op2 rt)
  (case (logor (lshift op1 11) (lshift crn 7) (lshift crm 3) op2)
    0x1ba1 (a64-dc-zva rt)
    0x1bd9 (empty)
    0x1bf1 (empty)
    0x1bd1 (empty)
    0x1be1 (empty)
    0x1be9 (empty)
    0x03b1 (empty)
    0x1ba9 (empty)
    0x03a8 (empty)
    0x0388 (empty)
    (a64-undefined)))
