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
;; FPProcessNaNs: a signaling NaN comes before a quiet one, whichever is first.
(defun fp-is-signaling-nan (x f)
  (logand (is-nan x) (not (fp-is-quiet-nan x f))))

(defun fp-min (x y f)
  (fp-select (fp-is-signaling-nan x f) (fp-quiet x f)
    (fp-select (fp-is-signaling-nan y f) (fp-quiet y f)
      (fp-select (is-nan x) (fp-quiet x f)
        (fp-select (is-nan y) (fp-quiet y f)
          (fp-select (<. x y) x
            (fp-select (<. y x) y (logor x y))))))))

(defun fp-max (x y f)
  (fp-select (fp-is-signaling-nan x f) (fp-quiet x f)
    (fp-select (fp-is-signaling-nan y f) (fp-quiet y f)
      (fp-select (is-nan x) (fp-quiet x f)
        (fp-select (is-nan y) (fp-quiet y f)
          (fp-select (<. x y) y
            (fp-select (<. y x) x (logand x y))))))))

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

(defun fp-less-signaling (x y)
  "(fp-less-signaling X Y) is (<. X Y), which raises invalid of any NaN,
   quiet or not, as an ordered comparison does"
  (case (word-width x)
    16 (intrinsic 'forders_ieee754_binary_16 x y :result 1)
    32 (intrinsic 'forders_ieee754_binary_32 x y :result 1)
    (intrinsic 'forders_ieee754_binary_64 x y :result 1)))

(defun fp-nzcv-signaling (x y)
  "(fp-nzcv-signaling X Y) is (fp-nzcv X Y) of an ordered comparison, as
   FCMPE and VCMPE are"
  (cast-low 4 (fp-select (logor (is-nan x) (is-nan y)) 0b0011
                (fp-select (fp-less-signaling x y) 0b1000
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
  (let ((h (*. :rni x half)))
    (= h (fp-trunc h e f))))

(defun fp-round-integral (mode x one half e f)
  "(fp-round-integral MODE X ONE HALF E F) is FPRoundInt. MODE is
   one of 'n (to nearest, ties to even), 'a (to nearest, ties away
   from zero), 'p (toward +inf), 'm (toward -inf) and 'z (toward zero).
   ONE and HALF are 1.0 and 0.5 in the format of X."
  (let ((int (fp-trunc x e f))
        (d (fp-abs (-. :rni x int)))
        (away (fp-select (msb x) (-. :rni int one) (+. :rni int one)))
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

;; What a conversion to an integer raises, of R that is X rounded to an integral value.

(defun fp-cvt-invalid (signed n r e f)
  "(fp-cvt-invalid SIGNED N R E F) is whether the integral R doesn't fit
   an N-bit integer. SIGNED must be static."
  (let ((bias (fp-bias e))
        (expn (fp-exponent r e f)))
    (logor (is-nan r) (is-inf r)
           (if signed
               (logand (>= expn (- (+ bias n) 1))
                       (not (= r (fp-neg (lshift (cast-unsigned (word-width r) (+ bias n -1)) f)))))
             (logor (>= expn (+ bias n))
                    (logand (msb r) (>= expn bias)))))))

(defun fp-cvt-flags (signed n x r e f invalid inexact flush)
  "(fp-cvt-flags SIGNED N X R E F INVALID INEXACT FLUSH) is a 32-bit word of the bits
   INVALID and INEXACT for what the conversion of X, rounded to R, raises. With FLUSH,
   which is FZ, a denormal is a zero, which raises input denormal, the bit 7, and no more"
  (let ((bad (fp-cvt-invalid signed n r e f))
        (denormal (logand flush (= (fp-exponent x e f) (cast-unsigned 64 0)) (not (is-fzero x)))))
    (fp-select denormal (cast-unsigned 32 0x80)
      (logor (lshift (cast-unsigned 32 bad) invalid)
             (lshift (cast-unsigned 32 (logand (not bad) (not (= r x)))) inexact)))))

(defun fp-to-fixed (signed n x e f fbits)
  "(fp-to-fixed SIGNED N X E F FBITS) is FPToFixed: X times 2^FBITS as
   an N-bit integer rounded toward zero. It is fp-to-int with the
   exponent raised, as scaling by a power of two is exact, and it tests
   for NaN on the bits. SIGNED must be static."
  (let ((bias (fp-bias e))
        (raw (fp-exponent x e f))
        (expn (+ raw (cast-unsigned 64 fbits)))
        (coef (cast-unsigned 64 (concat (cast-low 1 1) (cast-low f x))))
        (mag (fp-select (< expn bias) (cast-unsigned 64 0)
                        (fp-select (>= expn (+ bias f))
                                   (lshift coef (- expn (+ bias f)))
                                   (rshift coef (- (+ bias f) expn)))))
        (top (lshift (cast-unsigned 64 1) (- n 1)))
        (nan (logand (= raw (- (lshift (cast-unsigned 64 1) e) 1))
                     (not (is-zero (cast-low f x))))))
    (cast-low n
              (fp-select nan (cast-unsigned 64 0)
                (if signed
                    (fp-select (>= expn (- (+ bias n) 1))
                               (fp-select (msb x) top (- top 1))
                               (fp-select (msb x) (neg mag) mag))
                  (fp-select (msb x) (cast-unsigned 64 0)
                             (fp-select (>= expn (+ bias n))
                                        (- (lshift (cast-unsigned 64 1) n) 1)
                                        mag)))))))

(defun fp-from-fixed (r fbits f)
  "(fp-from-fixed R FBITS F) is the float R, that a conversion from an
   integer gave, divided by 2^FBITS, on its exponent: R is zero, or at
   least one, so the result is exact and normal"
  (fp-select (is-fzero r) r
             (- r (lshift (cast-unsigned (word-width r) fbits) f))))

(defun vfp-expand-imm (imm e f)
  "(vfp-expand-imm IMM E F) is VFPExpandImm of the 8-bit IMM"
  (concat (select 7 imm)
          (lnot (select 6 imm))
          (replicate-to-fill (select 6 imm) (- e 3))
          (extract 5 0 imm)
          (cast-unsigned (- f 4) 0)))

