(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; SPECIAL INSTRUCTIONS

;; The barriers have no effect on a single thread.

(defun DMB (_) (empty))

(defun DSB (_) (empty))

(defun ISB (_) (empty))

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

(in-package llvm-aarch64)

(defun MRS (dst reg)
  (if (= reg 0xde82)
      (set$ dst TPIDR_EL0)
    (empty)))
