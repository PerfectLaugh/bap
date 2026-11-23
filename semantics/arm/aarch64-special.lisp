(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; SPECIAL INSTRUCTIONS

;; The barriers have no effect on a single thread.

(defun DMB (_) (empty))

(defun DSB (_) (empty))

(defun ISB (_) (empty))

;; the speculation barrier, which the decoder of FEAT_SB decodes, and
;; else decodes as MSR, see below
(defun SB () (empty))

;; The hints, e.g., YIELD, WFE, WFI, SEV, SEVL, DGH, ESB, PSB CSYNC,
;; TSB CSYNC, CSDB, and BTI, which have no effect on a single thread, and
;; the hints, that are not allocated, which the architecture runs as NOPs.
(defun HINT (_)
  (empty))

(defun NOP ()
  (empty))

(defun UDF (exn)
  (intrinsic 'undefined-instruction :aborts))

;; the breakpoint, and the halt, which is UNDEFINED while halting isn't
;; allowed, as it isn't to a program of Linux
(defun BRK (imm) (intrinsic 'breakpoint imm :aborts))
(defun HLT (_) (intrinsic 'undefined-instruction :aborts))

;; the supervisor call
(defun SVC (imm) (intrinsic 'svc imm))

;; The processor doesn't have the pointer authentication, as what a
;; program is told of it says (AT_HWCAP has neither PACA nor PACG, and
;; ID_AA64ISAR1_EL1 has no APA, API, GPA or GPI). The instructions that
;; sign, authenticate or strip the code of LR or X17 are in the space of
;; the hints, and are NOPs there, so that a return address that is signed
;; and authenticated is the original one.
(defun PACIASP () (empty))
;; PACM, of FEAT_PAuth_LR, which the processor doesn't have, is the hint
;; that it is of, which is a NOP
(defun PACM () (empty))
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

;; The forms of the other registers and of the data keys, and PACGA,
;; aren't hints: without the pointer authentication they are UNDEFINED,
;; as are the branches, the returns and the loads that authenticate, see
;; aarch64-branch.lisp and aarch64-data-movement.lisp.
(defun a64-no-pauth () (intrinsic 'undefined-instruction :aborts))
(defun PACIA (_ _ _) (a64-no-pauth))
(defun PACIB (_ _ _) (a64-no-pauth))
(defun PACDA (_ _ _) (a64-no-pauth))
(defun PACDB (_ _ _) (a64-no-pauth))
(defun AUTIA (_ _ _) (a64-no-pauth))
(defun AUTIB (_ _ _) (a64-no-pauth))
(defun AUTDA (_ _ _) (a64-no-pauth))
(defun AUTDB (_ _ _) (a64-no-pauth))
(defun PACIZA (_ _) (a64-no-pauth))
(defun PACIZB (_ _) (a64-no-pauth))
(defun PACDZA (_ _) (a64-no-pauth))
(defun PACDZB (_ _) (a64-no-pauth))
(defun AUTIZA (_ _) (a64-no-pauth))
(defun AUTIZB (_ _) (a64-no-pauth))
(defun AUTDZA (_ _) (a64-no-pauth))
(defun AUTDZB (_ _) (a64-no-pauth))
(defun XPACI (_ _) (a64-no-pauth))
(defun XPACD (_ _) (a64-no-pauth))
(defun PACGA (_ _ _) (a64-no-pauth))

;; CHKFEAT clears the bits of X16 of the features that are enabled. The
;; only one is the guarded control stack, which is not modeled, so it is
;; not enabled and X16 stays.
(defun CHKFEAT () (empty))

;; The prefetch of a range is a hint, without an architectural effect.
(defun RPRFM (_ _ _) (empty))

;; the instruction, that the processor doesn't have, e.g., the system
;; register, that it doesn't have, which raises the exception of the
;; undefined instructions, as SIGILL of Linux
(defun a64-undefined () (intrinsic 'undefined-instruction :aborts))

(defun a64-nzcv ()
  "the flags as the register NZCV"
  (logor (lshift (cast-unsigned 64 NF) 31) (lshift (cast-unsigned 64 ZF) 30)
         (lshift (cast-unsigned 64 CF) 29) (lshift (cast-unsigned 64 VF) 28)))

;; the virtual counter, which what serves virtual-counter sets before
;; it is read: of a Linux machine, the clock of its kernel in ticks of
;; CNTFRQ_EL0, which goes on by the instructions that run, so that a
;; difference between two reads is the work done between them, and
;; clock_gettime never disagrees with it
(defun a64-counter ()
  (intrinsic 'virtual-counter)
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
;; at EL0, and the counter, see [a64-counter]. What is of EL1 is
;; undefined at EL0, where a program runs: the fields of PSTATE SPSel,
;; PAN and UAO, and SP_EL0; and so is DAIF, which EL0 has only with
;; SCTLR_EL1.UMA, that Linux doesn't set. Each is SIGILL of Linux.
;;
;; FPCR has the bits that the processor has: AHP, DN, FZ, RMode and FZ16.
;; The rest is RES0, which reads as zero: the traps of the exceptions,
;; which it doesn't have, the Len and Stride of the short vectors of
;; AArch32, and the bits of FEAT_AFP and FEAT_EBF16. FPSR has the flags
;; of AArch32, QC, IDC and the five cumulative exceptions.
(defun a64-fpcr-bits () 0x07c80000:32)
(defun a64-fpsr-bits () 0xf800009f:32)
(defun MRS (dst reg)
  (case reg
    0xde82 (set$ dst TPIDR_EL0)
    0xde83 (set$ dst TPIDRRO_EL0)
    0xde85 (set$ dst TPIDR2_EL0)
    0xda12 (set$ dst (sme-svcr))                ; SVCR
    0xda10 (set$ dst (a64-nzcv))
    0xda11 (a64-undefined)                      ; DAIF
    0xc210 (a64-undefined)                      ; SPSel
    0xc213 (a64-undefined)                      ; PAN
    0xc214 (a64-undefined)                      ; UAO
    0xc208 (a64-undefined)                      ; SP_EL0
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
    0xc031 (set$ dst 0x11100211002)             ; ID_AA64ISAR1_EL1
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
    0xde85 (set TPIDR2_EL0 src)
    0xda12 (sme-set-svcr src)
    0xda10 (set-nzcv (cast-low 4 (rshift src 28)))
    0xda20 (set FPCR (logand (cast-low 32 src) (a64-fpcr-bits)))
    0xda21 (set FPSR (logand (cast-low 32 src) (a64-fpsr-bits)))
    0xda11 (a64-undefined)                      ; DAIF
    0xc210 (a64-undefined)                      ; SPSel
    0xc213 (a64-undefined)                      ; PAN
    0xc214 (a64-undefined)                      ; UAO
    0xc208 (a64-undefined)                      ; SP_EL0
    0x1987 (empty)                              ; SB
    (a64-undefined)))

;; The only SYSL allocated at EL0 is GCSPOPM of the guarded control
;; stack, which is not modeled, so it is not enabled and is undefined,
;; as the implementation defined ones are, which the processor doesn't have.
(defun SYSLxt (_ _ _ _ _) (a64-undefined))

;; What is of EL1 or higher, or of debug state, is undefined at EL0: the
;; calls of the hypervisor and the secure monitor, the returns from an
;; exception and from debug state, which, of no operands, are given LR,
;; as RET is, the changes to debug state, APAS of the realms, and the
;; fields of PSTATE of MSR (immediate) of one bit, e.g., PM, which the
;; processor doesn't have
(defun APAS (_) (a64-undefined))
(defun DCPS1 (_) (a64-undefined))
(defun DCPS2 (_) (a64-undefined))
(defun DCPS3 (_) (a64-undefined))
(defun DRPS (_) (a64-undefined))
(defun ERET (_) (a64-undefined))
(defun ERETAA (_) (a64-undefined))
(defun ERETAB (_) (a64-undefined))
(defun HVC (_) (a64-undefined))
(defun SMC (_) (a64-undefined))
(defun MSRpstateImm1 (_ _) (a64-undefined))

;; SMSTART and SMSTOP of SME, of the mode (field 1), ZA (2) or both
;; (3), see aarch64-sme.lisp
(defun MSRpstatesvcrImm1 (field imm)
  (case field
    1 (sme-set-sm (cast-low 1 imm))
    2 (sme-set-za (cast-low 1 imm))
    3 (prog (sme-set-sm (cast-low 1 imm)) (sme-set-za (cast-low 1 imm)))
    (a64-undefined)))

;; The fields of PSTATE that MSR sets to an immediate of four bits:
;; DAIFSet and DAIFClr, which EL0 has only with SCTLR_EL1.UMA, that Linux
;; doesn't set, and SPSel, UAO and PAN, which are of EL1. Each is
;; undefined where a program runs, and SIGILL of Linux, by its field.
(defun MSRpstateImm4 (field _)
  (case field
    0x1e (a64-undefined)                        ; DAIFSet
    0x1f (a64-undefined)                        ; DAIFClr
    0x05 (a64-undefined)                        ; SPSel
    0x03 (a64-undefined)                        ; UAO
    0x04 (a64-undefined)                        ; PAN
    (a64-undefined)))

;; The cache maintenance, by op1:CRn:CRm:op2, that EL0 may run, as
;; Linux sets SCTLR_EL1.UCI and DZE: DC ZVA zeroes its block, and DC
;; CVAU, CIVAC, CVAC, CVAP, CVADP and IC IVAU have no effect, as the
;; caches are not modeled, and the code, that the program writes, runs
;; anew, when it is written. DC IVAC, which is of EL1, has no effect
;; too, as it always had here. The rest, e.g., IC IALLU and IALLUIS, DC
;; ISW and AT, are of EL1, and undefined at EL0.
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
    (a64-undefined)))
