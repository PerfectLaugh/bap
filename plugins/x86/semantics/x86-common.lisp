(declare (context (target x86)))

(defpackage x86-common (:use core target))
(defpackage x86-32 (:use x86-common))
(defpackage x86-64 (:use x86-common))
(defpackage llvm-x86 (:use x86-32))
(defpackage llvm-x86_64 (:use x86-64))

(in-package x86-common)

(defun HLT ()
  (intrinsic 'hlt))

(defun NOOP ()
  (empty))

(defun NOOPL (_ _ _ _ _)
  (empty))

(defun NOOPW (_ _ _ _ _)
  (empty))

;; xchgb reg, off(base)
;; Reference: Vol. 2D 6-32

(defun XCHG8rm (_ reg base _ _ off _)
  (let ((p (+ base off))
        (x (load-byte p)))
    (store-byte p reg)
    (set$ reg x)))

(defun XCHG8rr (dst src _ _)
  (let ((x dst))
    (set$ dst src)
    (set$ src x)))

(defun set-gpr (rd x)
  "(set-gpr RD X) sets the general purpose register RD to X, a 32-bit
   register clears the upper half of its 64-bit base"
  (declare (context (bits 64)))
  (if (= (word-width x) 32)
      (set$ (alias-base-register rd) (cast-unsigned 64 x))
    (set$ rd x)))

(defun set-gpr (rd x)
  (declare (context (bits 32)))
  (set$ rd x))

(defun operand-address (base scale index off)
  "(operand-address BASE SCALE INDEX OFF) is the address of a memory
   operand, BASE and INDEX may be absent, the base RIP is the address of
   the next instruction"
  (+ (if (= (symbol base) 'Nil) 0
       (if (= (symbol base) 'RIP) (get-next-program-counter) base))
     (if (= (symbol index) 'Nil) 0 (* scale index))
     off))
