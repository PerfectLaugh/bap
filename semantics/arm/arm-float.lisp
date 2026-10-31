(declare (context (target arm-family)))

(in-package arm)

(require bits)
(require arm-bits)

;;; FLOATING-POINT HELPERS
;;
;; Helpers shared by the AArch64 and the AArch32 (VFP) floating-point
;; semantics. They take the number of the exponent bits E and of the
;; fraction bits F of the format: 8 and 23 for single, 11 and 52 for
;; double precision.
;;
;; The helpers choose between values with fp-select and combine
;; conditions with logand and logor instead of if, and and or. A
;; dynamic if compiles to a branch that assigns its condition, so an
;; if nested in another one yields an expression that reads a
;; variable assigned only on one path, and Primus, which evaluates
;; both arms of an expression, fails on the other path.

(defun fp-select (c x y)
  "(fp-select C X Y) is X if C is true and Y otherwise, X and Y must
   have the same width"
  (let ((m (neg (cast-unsigned (word-width x) c))))
    (logor (logand m x) (logand (lnot m) y))))

(defun fp-neg (x)
  (concat (lnot (msb x)) (cast-low (- (word-width x) 1) x)))

(defun fp-abs (x)
  (concat (cast-low 1 0) (cast-low (- (word-width x) 1) x)))

(defun fp-zero (x)
  "(fp-zero X) is +0.0 in the format of X"
  (cast-unsigned (word-width x) 0))

(defun fp-quiet (x f)
  "(fp-quiet X F) sets the quiet bit of the NaN X"
  (logor x (lshift (cast-unsigned (word-width x) 1) (- f 1))))

(defun fp-is-quiet-nan (x f)
  (logand (is-nan x) (not (is-zero (select (- f 1) x)))))

(defun fp-exponent (x e f)
  "(fp-exponent X E F) is the biased exponent of X as a 64-bit word"
  (cast-unsigned 64 (extract (+ e f -1) f x)))

(defun fp-bias (e)
  "(fp-bias E) is the exponent bias as a 64-bit word, as the exponents"
  (- (lshift (cast-unsigned 64 1) (- e 1)) 1))

;; FPMin and FPMax. A NaN operand is returned quieted, and of equal
;; operands -0.0 is the smaller one. The NaN of the first operand is
;; returned when both are NaN, regardless of which one is signaling.
(defun fp-min (x y f)
  (fp-select (is-nan x) (fp-quiet x f)
    (fp-select (is-nan y) (fp-quiet y f)
      (fp-select (<. x y) x
        (fp-select (<. y x) y (logor x y))))))

(defun fp-max (x y f)
  (fp-select (is-nan x) (fp-quiet x f)
    (fp-select (is-nan y) (fp-quiet y f)
      (fp-select (<. x y) y
        (fp-select (<. y x) x (logand x y))))))

;; FPMinNum and FPMaxNum prefer a number to a quiet NaN.
(defun fp-minnm (x y f)
  (fp-select (logand (fp-is-quiet-nan x f) (not (is-nan y))) y
    (fp-select (logand (fp-is-quiet-nan y f) (not (is-nan x))) x
      (fp-min x y f))))

(defun fp-maxnm (x y f)
  (fp-select (logand (fp-is-quiet-nan x f) (not (is-nan y))) y
    (fp-select (logand (fp-is-quiet-nan y f) (not (is-nan x))) x
      (fp-max x y f))))

(defun fp-nzcv (x y)
  "(fp-nzcv X Y) is the 4-bit NZCV result of comparing X with Y, 0011
   if they are unordered, and otherwise 0110, 1000 or 0010 if X is
   equal to, less than or greater than Y."
  (cast-low 4 (fp-select (logor (is-nan x) (is-nan y)) 0b0011
                (fp-select (<. x y) 0b1000
                  (fp-select (<. y x) 0b0010 0b0110)))))

(defun fp-trunc (x e f)
  "(fp-trunc X E F) rounds X to an integral value toward zero"
  (let ((bias (fp-bias e))
        (expn (fp-exponent x e f)))
    (fp-select (< expn bias)
               (concat (msb x) (cast-unsigned (+ e f) 0))
               (fp-select (>= expn (+ bias f)) x
                          (logand x (lshift (lnot (fp-zero x))
                                            (- (+ bias f) expn)))))))

(defun fp-is-even (x half e f)
  "(fp-is-even X HALF E F) is true if the integral X is even"
  (let ((h (*. :rne x half)))
    (= h (fp-trunc h e f))))

(defun fp-round-integral (mode x one half e f)
  "(fp-round-integral MODE X ONE HALF E F) is FPRoundInt. MODE is
   one of 'n (to nearest, ties to even), 'a (to nearest, ties away
   from zero), 'p (toward +inf), 'm (toward -inf) and 'z (toward zero).
   ONE and HALF are 1.0 and 0.5 in the format of X."
  (let ((int (fp-trunc x e f))
        (d (fp-abs (-. :rne x int)))
        (away (fp-select (msb x) (-. :rne int one) (+. :rne int one)))
        (rounded
         (case mode
           'z int
           'p (fp-select (logand (not (msb x)) (not (is-fzero d))) away int)
           'm (fp-select (logand (msb x) (not (is-fzero d))) away int)
           'a (fp-select (<. d half) int away)
           'n (fp-select (logor (<. half d)
                                (logand (= d half)
                                        (not (fp-is-even int half e f))))
                         away int))))
    (fp-select (is-nan x) (fp-quiet x f)
               (fp-select (is-inf x) x rounded))))

(defun fp-to-int (signed n x e f)
  "(fp-to-int SIGNED N X E F) converts X to an N-bit integer rounding
   toward zero. Out of range values saturate and NaN converts to 0.
   SIGNED must be static."
  (let ((bias (fp-bias e))
        (expn (fp-exponent x e f))
        (coef (cast-unsigned 64 (concat (cast-low 1 1) (cast-low f x))))
        (mag (fp-select (< expn bias) (cast-unsigned 64 0)
                        (fp-select (>= expn (+ bias f))
                                   (lshift coef (- expn (+ bias f)))
                                   (rshift coef (- (+ bias f) expn)))))
        (top (lshift (cast-unsigned 64 1) (- n 1))))
    (cast-low n
              (fp-select (is-nan x) (cast-unsigned 64 0)
                (if signed
                    (fp-select (>= expn (- (+ bias n) 1))
                               (fp-select (msb x) top (- top 1))
                               (fp-select (msb x) (neg mag) mag))
                  (fp-select (msb x) (cast-unsigned 64 0)
                             (fp-select (>= expn (+ bias n))
                                        (lnot (cast-unsigned 64 0))
                                        mag)))))))

(defun vfp-expand-imm (imm e f)
  "(vfp-expand-imm IMM E F) is VFPExpandImm of the 8-bit IMM"
  (concat (select 7 imm)
          (lnot (select 6 imm))
          (replicate-to-fill (select 6 imm) (- e 3))
          (extract 5 0 imm)
          (cast-unsigned (- f 4) 0)))

