(declare (context (target arm-family)
                  (bits 32)))

(in-package arm)

(require bits)
(require arm-bits)
(require arm-float)

;;; AARCH32 INTEGER OPERATIONS
;;
;; The operations shared by the A32 and T32 encodings, and the A32
;; instructions that the legacy lifter does not handle. As in
;; arm-float, the values are computed without dynamic if.

(defun a32-mux (c x y)
  "(a32-mux C X Y) is X if C is true and Y otherwise"
  (fp-select c x y))

(defmacro a32-cond (cnd body)
  "(a32-cond CND BODY) evaluates BODY if the condition CND holds"
  (when (condition-holds cnd) body))

;; division, by zero gives zero
(defmacro a32-div (div rd rn rm)
  (if (is-zero rm) (set$ rd 0) (set$ rd (div rn rm))))

;; signed saturation of the 33-bit sum or difference, sets Q on overflow
(defun a32-saturating-add (x y)
  "(a32-saturating-add X Y) is the sum of the signed X and Y saturated
   to 32 bits, it sets the Q flag if the sum is saturated"
  (let ((r (+ x y))
        (ov (logand (= (msb x) (msb y)) (/= (msb r) (msb x)))))
    (set QF (logor QF ov))
    (a32-mux ov (a32-mux (msb x) 0x80000000 0x7fffffff) r)))

(defun a32-saturating-sub (x y)
  "(a32-saturating-sub X Y) is the difference of the signed X and Y
   saturated to 32 bits, it sets the Q flag if it is saturated"
  (let ((r (- x y))
        (ov (logand (/= (msb x) (msb y)) (/= (msb r) (msb x)))))
    (set QF (logor QF ov))
    (a32-mux ov (a32-mux (msb x) 0x80000000 0x7fffffff) r)))

(defun a32-ssat (x n)
  "(a32-ssat X N) saturates the signed X to N bits, setting Q"
  (let ((hi (- (lshift 1 (- n 1)) 1))
        (lo (lnot hi))
        (over (s> x hi))
        (under (s< x lo)))
    (set QF (logor QF over under))
    (a32-mux over hi (a32-mux under lo x))))

(defun a32-usat (x n)
  "(a32-usat X N) saturates the signed X to the unsigned N bits, setting Q"
  (let ((hi (- (lshift 1 n) 1))
        (over (s> x hi))
        (under (s< x 0)))
    (set QF (logor QF over under))
    (a32-mux over hi (a32-mux under 0 x))))

(defun a32-sat-shift (x sh)
  "(a32-sat-shift X SH) is X shifted by the encoded SH of SSAT and USAT,
   lsl #n if the bit 5 is clear and asr #n otherwise, asr #0 is asr #32"
  (if (= 0 (logand sh 0x20))
      (lshift x (logand sh 0x1f))
    (arshift x (if (= 0 (logand sh 0x1f)) 31 (logand sh 0x1f)))))

(defun a32-half (x top)
  "(a32-half X TOP) is the signed top or bottom halfword of X"
  (cast-signed 32 (if top (cast-high 16 x) (cast-low 16 x))))

(defun a32-mul-high (x y)
  "(a32-mul-high X Y) is the upper word of the signed product"
  (cast-high 32 (* (cast-signed 64 x) (cast-signed 64 y))))

(defun a32-mla-high (x y a)
  "(a32-mla-high X Y A) is the upper word of A:0 plus the signed product"
  (cast-high 32 (+ (concat a (cast-unsigned 32 0))
                   (* (cast-signed 64 x) (cast-signed 64 y)))))

(defun a32-mls-high (x y a)
  (cast-high 32 (- (concat a (cast-unsigned 32 0))
                   (* (cast-signed 64 x) (cast-signed 64 y)))))

(defun a32-revsh (x)
  (cast-signed 32 (concat (extract 7 0 x) (extract 15 8 x))))

(defun UDIV (rd rn rm cnd _) (a32-cond cnd (a32-div / rd rn rm)))
(defun SDIV (rd rn rm cnd _) (a32-cond cnd (a32-div s/ rd rn rm)))
(defun QADD (rd rm rn cnd _) (a32-cond cnd (set$ rd (a32-saturating-add rm rn))))
(defun QSUB (rd rm rn cnd _) (a32-cond cnd (set$ rd (a32-saturating-sub rm rn))))
(defun SSAT (rd n rn sh cnd _)
  (a32-cond cnd (set$ rd (a32-ssat (a32-sat-shift rn sh) (+ n 1)))))
(defun USAT (rd n rn sh cnd _)
  (a32-cond cnd (set$ rd (a32-usat (a32-sat-shift rn sh) n))))
(defun SMULBT (rd rn rm cnd _)
  (a32-cond cnd (set$ rd (* (a32-half rn false) (a32-half rm true)))))
(defun SMULTB (rd rn rm cnd _)
  (a32-cond cnd (set$ rd (* (a32-half rn true) (a32-half rm false)))))
(defun SMULTT (rd rn rm cnd _)
  (a32-cond cnd (set$ rd (* (a32-half rn true) (a32-half rm true)))))
(defun SMMUL (rd rn rm cnd _) (a32-cond cnd (set$ rd (a32-mul-high rn rm))))
(defun SMMLA (rd rn rm ra cnd _) (a32-cond cnd (set$ rd (a32-mla-high rn rm ra))))
(defun SMMLS (rd rn rm ra cnd _) (a32-cond cnd (set$ rd (a32-mls-high rn rm ra))))
(defun REVSH (rd rm cnd _) (a32-cond cnd (set$ rd (a32-revsh rm))))
