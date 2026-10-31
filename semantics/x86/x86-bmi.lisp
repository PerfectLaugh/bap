(declare (context (target x86)))
(require x86-common)

(in-package x86-common)

;;; BMI1, BMI2 AND ADX INSTRUCTIONS, AND THE CARRY FLAG

(defun CLC () (set CF 0:1))
(defun STC () (set CF 1:1))
(defun CMC () (set CF (lnot CF)))

;; the flags of the BMI instructions with a result, OF is cleared and
;; AF and PF are undefined
(defun bmi-flags (r cf)
  (set ZF (is-zero r))
  (set SF (msb r))
  (set CF cf)
  (set OF 0:1))

(defun bmi-result (rd r cf)
  (bmi-flags r cf)
  (set-gpr rd r))

(defun andn (rd rn rm)
  (bmi-result rd (logand (lnot rn) rm) 0:1))


(defun blsi (rd rn)
  (bmi-result rd (logand (neg rn) rn) (not (is-zero rn))))

(defun blsmsk (rd rn)
  (let ((r (logxor (- rn (one-of rn)) rn)))
    (bmi-flags r (is-zero rn))
    (set ZF 0:1)
    (set-gpr rd r)))

(defun blsr (rd rn)
  (bmi-result rd (logand (- rn (one-of rn)) rn) (is-zero rn)))

(defun low-mask (w n)
  "(low-mask W N) is the W-bit mask of the N low bits, all of them if N
   is not less than W"
  (if (< n (cast-unsigned w w))
      (- (lshift (cast-unsigned w 1:1) n) (cast-unsigned w 1:1))
    (ones w)))

(defun bzhi (rd rn rm)
  (let ((w (word-width rn))
        (n (cast-unsigned w (extract 7 0 rm))))
    (bmi-result rd (logand rn (low-mask w n))
                (> n (cast-unsigned w (- w 1))))))

(defun bextr (rd rn rm)
  (let ((w (word-width rn))
        (start (cast-unsigned w (extract 7 0 rm)))
        (len (cast-unsigned w (extract 15 8 rm)))
        (r (logand (if (< start (cast-unsigned w w)) (rshift rn start) (cast-unsigned w 0:1))
                   (low-mask w len))))
    (set ZF (is-zero r))
    (set CF 0:1)
    (set OF 0:1)
    (set-gpr rd r)))

;; the count of the shifts is masked to the size of the operand
(defun shift-count (rn rm)
  (logand rm (- (word-width rn) 1)))

(defun sarx (rd rn rm) (set-gpr rd (arshift rn (shift-count rn rm))))
(defun shlx (rd rn rm) (set-gpr rd (lshift rn (shift-count rn rm))))
(defun shrx (rd rn rm) (set-gpr rd (rshift rn (shift-count rn rm))))
(defun rorx (rd rn n) (set-gpr rd (rotate-right rn n)))

(defun bit-of (x i)
  "(bit-of X I) is the bit I of X extended to the size of X"
  (cast-unsigned (word-width x) (lsb (rshift x i))))

(defun pdep (rd rn rm)
  "deposits the low bits of RN to the positions of the set bits of RM"
  (let ((w (word-width rn))
        (r (cast-unsigned w 0:1))
        (k (cast-unsigned w 0:1))
        (i 0))
    (while (< i w)
      (set r (logor r (lshift (logand (bit-of rm i) (rshift rn k)) i)))
      (set k (+ k (bit-of rm i)))
      (set i (+ i 1)))
    (set-gpr rd r)))

(defun pext (rd rn rm)
  "extracts the bits of RN at the positions of the set bits of RM to
   the low bits"
  (let ((w (word-width rn))
        (r (cast-unsigned w 0:1))
        (k (cast-unsigned w 0:1))
        (i 0))
    (while (< i w)
      (set r (logor r (lshift (logand (bit-of rm i) (rshift rn i)) k)))
      (set k (+ k (bit-of rm i)))
      (set i (+ i 1)))
    (set-gpr rd r)))

;; the high half of the product is written last, when both destinations
;; are the same register
(defun mulx (hi lo rn rdx)
  (let ((w (word-width rn))
        (p (* (cast-unsigned (* 2 w) rdx) (cast-unsigned (* 2 w) rn))))
    (set-gpr lo (cast-low w p))
    (set-gpr hi (cast-high w p))))

;; ADCX and ADOX add with the carry in CF and OF, which are the only
;; flags that they write
(defun adx (rd rn rm c)
  (let ((w (word-width rn))
        (s (+ (cast-unsigned (+ w 1) rn)
              (cast-unsigned (+ w 1) rm)
              (cast-unsigned (+ w 1) c))))
    (set-gpr rd (cast-low w s))
    (msb s)))

(defun ANDN32rr (rd rn rm) (andn rd rn rm))
(defun ANDN64rr (rd rn rm) (andn rd rn rm))
(defun BLSI32rr (rd rn) (blsi rd rn))
(defun BLSI64rr (rd rn) (blsi rd rn))
(defun BLSMSK32rr (rd rn) (blsmsk rd rn))
(defun BLSMSK64rr (rd rn) (blsmsk rd rn))
(defun BLSR32rr (rd rn) (blsr rd rn))
(defun BLSR64rr (rd rn) (blsr rd rn))
(defun BZHI32rr (rd rn rm) (bzhi rd rn rm))
(defun BZHI64rr (rd rn rm) (bzhi rd rn rm))
(defun BEXTR32rr (rd rn rm) (bextr rd rn rm))
(defun BEXTR64rr (rd rn rm) (bextr rd rn rm))
(defun SARX32rr (rd rn rm) (sarx rd rn rm))
(defun SARX64rr (rd rn rm) (sarx rd rn rm))
(defun SHLX32rr (rd rn rm) (shlx rd rn rm))
(defun SHLX64rr (rd rn rm) (shlx rd rn rm))
(defun SHRX32rr (rd rn rm) (shrx rd rn rm))
(defun SHRX64rr (rd rn rm) (shrx rd rn rm))
(defun RORX32ri (rd rn n) (rorx rd rn n))
(defun RORX64ri (rd rn n) (rorx rd rn n))
(defun PDEP32rr (rd rn rm) (pdep rd rn rm))
(defun PDEP64rr (rd rn rm) (pdep rd rn rm))
(defun PEXT32rr (rd rn rm) (pext rd rn rm))
(defun PEXT64rr (rd rn rm) (pext rd rn rm))
(defun MULX32rr (hi lo rn) (mulx hi lo rn EDX))
(defun MULX64rr (hi lo rn)
  (declare (context (bits 64)))
  (mulx hi lo rn RDX))
;; the memory forms: the same with what the memory holds
(defun ANDN32rm (rd rn b s i off seg) (andn rd rn (load-n 32 (ea b s i off seg))))
(defun BLSI32rm (rd b s i off seg) (blsi rd (load-n 32 (ea b s i off seg))))
(defun BLSMSK32rm (rd b s i off seg) (blsmsk rd (load-n 32 (ea b s i off seg))))
(defun BLSR32rm (rd b s i off seg) (blsr rd (load-n 32 (ea b s i off seg))))
(defun BZHI32rm (rd b s i off seg rm) (bzhi rd (load-n 32 (ea b s i off seg)) rm))
(defun BEXTR32rm (rd b s i off seg rm) (bextr rd (load-n 32 (ea b s i off seg)) rm))
(defun SARX32rm (rd b s i off seg rm) (sarx rd (load-n 32 (ea b s i off seg)) rm))
(defun SHLX32rm (rd b s i off seg rm) (shlx rd (load-n 32 (ea b s i off seg)) rm))
(defun SHRX32rm (rd b s i off seg rm) (shrx rd (load-n 32 (ea b s i off seg)) rm))
(defun RORX32mi (rd b s i off seg n) (rorx rd (load-n 32 (ea b s i off seg)) n))
(defun PDEP32rm (rd rn b s i off seg) (pdep rd rn (load-n 32 (ea b s i off seg))))
(defun PEXT32rm (rd rn b s i off seg) (pext rd rn (load-n 32 (ea b s i off seg))))
(defun ANDN64rm (rd rn b s i off seg) (andn rd rn (load-n 64 (ea b s i off seg))))
(defun BLSI64rm (rd b s i off seg) (blsi rd (load-n 64 (ea b s i off seg))))
(defun BLSMSK64rm (rd b s i off seg) (blsmsk rd (load-n 64 (ea b s i off seg))))
(defun BLSR64rm (rd b s i off seg) (blsr rd (load-n 64 (ea b s i off seg))))
(defun BZHI64rm (rd b s i off seg rm) (bzhi rd (load-n 64 (ea b s i off seg)) rm))
(defun BEXTR64rm (rd b s i off seg rm) (bextr rd (load-n 64 (ea b s i off seg)) rm))
(defun SARX64rm (rd b s i off seg rm) (sarx rd (load-n 64 (ea b s i off seg)) rm))
(defun SHLX64rm (rd b s i off seg rm) (shlx rd (load-n 64 (ea b s i off seg)) rm))
(defun SHRX64rm (rd b s i off seg rm) (shrx rd (load-n 64 (ea b s i off seg)) rm))
(defun RORX64mi (rd b s i off seg n) (rorx rd (load-n 64 (ea b s i off seg)) n))
(defun PDEP64rm (rd rn b s i off seg) (pdep rd rn (load-n 64 (ea b s i off seg))))
(defun PEXT64rm (rd rn b s i off seg) (pext rd rn (load-n 64 (ea b s i off seg))))
(defun MULX32rm (hi lo b s i off seg) (mulx hi lo (load-n 32 (ea b s i off seg)) EDX))
(defun MULX64rm (hi lo b s i off seg)
  (declare (context (bits 64)))
  (mulx hi lo (load-n 64 (ea b s i off seg)) RDX))
(defun ADCX32rr (rd rn rm) (set CF (adx rd rn rm CF)))
(defun ADCX64rr (rd rn rm) (set CF (adx rd rn rm CF)))
(defun ADOX32rr (rd rn rm) (set OF (adx rd rn rm OF)))
(defun ADOX64rr (rd rn rm) (set OF (adx rd rn rm OF)))
