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

;; the writes of EAX and EDX, which clear the upper halves of RAX and
;; RDX in the 64-bit mode
(defun set-eax (x) (declare (context (bits 64))) (set RAX (cast-unsigned 64 x)))
(defun set-eax (x) (declare (context (bits 32))) (set EAX x))
(defun set-edx (x) (declare (context (bits 64))) (set RDX (cast-unsigned 64 x)))
(defun set-edx (x) (declare (context (bits 32))) (set EDX x))
(defun set-ebx (x) (declare (context (bits 64))) (set RBX (cast-unsigned 64 x)))
(defun set-ebx (x) (declare (context (bits 32))) (set EBX x))
(defun set-ecx (x) (declare (context (bits 64))) (set RCX (cast-unsigned 64 x)))
(defun set-ecx (x) (declare (context (bits 32))) (set ECX x))

(defun operand-address (base scale index off)
  "(operand-address BASE SCALE INDEX OFF) is the address of a memory
   operand, BASE and INDEX may be absent, the base RIP is the address of
   the next instruction"
  (+ (if (= (symbol base) 'Nil) 0
       (if (= (symbol base) 'RIP) (get-next-program-counter) base))
     (if (= (symbol index) 'Nil) 0 (* scale index))
     off))

;;; MEMORY OPERANDS
;;
;; A memory operand is five operands: BASE, SCALE, INDEX, OFF and SEG,
;; only the FS and GS segments have a non-zero base.

(defun segment-base (seg)
  (case (symbol seg)
    'FS FS_BASE
    'GS GS_BASE
    0))

(defun ea (base scale index off seg)
  "(ea BASE SCALE INDEX OFF SEG) is the address of a memory operand"
  (+ (operand-address base scale index off) (segment-base seg)))

(defun load-n (n addr)
  "(load-n N ADDR) is the N-bit word at ADDR"
  (cast-low n (load-bits n addr)))

(defun store-n (n addr x)
  "(store-n N ADDR X) stores the low N bits of X at ADDR"
  (store-word addr (cast-low n x)))

;; the casts to a smaller size are truncations
(defun resize (n x)
  "(resize N X) is X zero-extended or truncated to N bits"
  (if (< (word-width x) n) (cast-unsigned n x) (cast-low n x)))

(defun one-of (x)
  "(one-of X) is 1 of the size of X"
  (cast-unsigned (word-width x) 1:1))

;;; FLAGS

(defun parity (r)
  "(parity R) is true if the low byte of R has an even number of ones"
  (let ((b (cast-low 8 r))
        (p (logxor b (rshift b 4)))
        (p (logxor p (rshift p 2)))
        (p (logxor p (rshift p 1))))
    (not (lsb p))))

(defun set-result-flags (r)
  (set SF (msb r))
  (set ZF (is-zero r))
  (set PF (parity r)))

(defun aux-carry (r x y) (lsb (rshift (logxor r x y) 4)))

(defun zext-like (x c)
  "(zext-like X C) is C zero-extended to the size of X"
  (cast-unsigned (word-width x) c))

(defun add-with-flags (x y c)
  "(add-with-flags X Y C) is X + Y + C, it sets the flags"
  (let ((r (+ x y (zext-like x c))))
    (set CF (carry r x y))
    (set OF (overflow r x y))
    (set AF (aux-carry r x y))
    (set-result-flags r)
    r))

(defun borrow (r x y)
  "(borrow R X Y) is true if R = X - Y - B borrows"
  (msb (logor (logand (lnot x) y) (logand (lnot (logxor x y)) r))))

(defun sub-with-flags (x y b)
  "(sub-with-flags X Y B) is X - Y - B, it sets the flags"
  (let ((r (- x y (zext-like x b))))
    (set CF (borrow r x y))
    (set OF (msb (logand (logxor x y) (logxor x r))))
    (set AF (aux-carry r x y))
    (set-result-flags r)
    r))

;; AF is undefined after the logical operations, it is not changed
(defun logic-with-flags (r)
  (set CF 0:1)
  (set OF 0:1)
  (set-result-flags r)
  r)
