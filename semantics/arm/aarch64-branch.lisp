(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; BRANCH INSTRUCTIONS

(defun relative-jump (off)
  (exec-addr (+ (get-program-counter) (lshift off 2))))

(defun B (off)
  (relative-jump off))

(defun Bcc (cnd off)
  (when (condition-holds cnd)
    (relative-jump off)))

(defun BL (off)
  (set LR (+ (get-program-counter) 4))
  (relative-jump off))

;; the target is read before LR is written, for BLR X30
(defun BLR (reg) (a64-call reg))

(defun BR (reg)
  (exec-addr reg))

(defmacro CB** (comparison reg off)
  "(CB** comparison reg off) implements CBZ and CBNZ by specifying
   the comparison (is-zero or non-zero)."
  (when (comparison reg)
    (relative-jump off)))

(defun CBZW  (reg off) (CB** is-zero  reg off))
(defun CBZX  (reg off) (CB** is-zero  reg off))
(defun CBNZW (reg off) (CB** non-zero reg off))
(defun CBNZX (reg off) (CB** non-zero reg off))

(defun RET (dst)
  (exec-addr dst))

(defmacro TB** (comparison reg pos off)
  "(TB** comparison reg pos off) implements TBZ and TBNZ
   by specifying the comparison (is-zero or non-zero)."
  (when (comparison (select pos reg))
    (relative-jump off)))

(defun TBZW  (reg pos off) (TB** is-zero  reg pos off))
(defun TBZX  (reg pos off) (TB** is-zero  reg pos off))
(defun TBNZW (reg pos off) (TB** non-zero reg pos off))
(defun TBNZX (reg pos off) (TB** non-zero reg pos off))

;; The branches that authenticate their target: the authentication isn't
;; modeled, see aarch64-special.lisp, so it succeeds and the target is the
;; register. The target is read before LR is written, as it can be LR.

(defun a64-call (target)
  (let ((pc target))
    (set LR (+ (get-program-counter) 4))
    (exec-addr pc)))

(defun BRAA (rn _) (exec-addr rn))
(defun BRAB (rn _) (exec-addr rn))
(defun BRAAZ (rn) (exec-addr rn))
(defun BRABZ (rn) (exec-addr rn))
(defun BLRAA (rn _) (a64-call rn))
(defun BLRAB (rn _) (a64-call rn))
(defun BLRAAZ (rn) (a64-call rn))
(defun BLRABZ (rn) (a64-call rn))
(defun RETAA (lr) (exec-addr lr))
(defun RETAB (lr) (exec-addr lr))
