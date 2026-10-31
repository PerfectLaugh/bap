(declare (context (target powerpc-family)))
(require powerpc)

(in-package powerpc)

;;; THE VECTOR INSTRUCTIONS OF THE ISA 2.06 TO 3.1
;;
;; As in powerpc.lisp, the elements are numbered from the most significant
;; one, in both byte orders, and VSCR is not modeled except for what the
;; moves write: SAT is not set by the saturating operations, and the
;; floating-point ones are in the non-Java mode.

(defmacro lanes64-1 (op x)
  (concat (op (extract 127 64 x)) (op (extract 63 0 x))))
(defmacro lanes64 (op x y)
  (concat (op (extract 127 64 x) (extract 127 64 y))
          (op (extract 63 0 x) (extract 63 0 y))))
(defmacro lanes64-3 (op x y z)
  (concat (op (extract 127 64 x) (extract 127 64 y) (extract 127 64 z))
          (op (extract 63 0 x) (extract 63 0 y) (extract 63 0 z))))
(defmacro lanes64-e (op e x)
  (concat (op e (extract 127 64 x)) (op e (extract 63 0 x))))

(defun u128 (x) (cast-unsigned 128 x))
(defun MFVSCR (vd) (set$ vd (u128 VSCR)))
(defun MTVSCR (vb) (set VSCR (cast-low 32 vb)))

;; LOGICAL OPERATIONS

(defun VEQV (vd va vb) (set$ vd (lnot (logxor va vb))))
(defun VNAND (vd va vb) (set$ vd (lnot (logand va vb))))
(defun VORC (vd va vb) (set$ vd (logor va (lnot vb))))

;; ADDITIONS AND SUBTRACTIONS OF DOUBLEWORDS AND QUADWORDS

(defun VADDUDM (vd va vb) (set$ vd (lanes64 add va vb)))
(defun VSUBUDM (vd va vb) (set$ vd (lanes64 sub va vb)))
(defun VADDUQM (vd va vb) (set$ vd (+ va vb)))
(defun VSUBUQM (vd va vb) (set$ vd (- va vb)))

(defun wide-sum (x y c)
  (+ (cast-unsigned 129 x) (cast-unsigned 129 y) (cast-unsigned 129 (select 0 c))))
(defun low-of-sum (x y c) (cast-low 128 (wide-sum x y c)))
(defun carry-of-sum (x y c) (cast-unsigned 128 (cast-high 1 (wide-sum x y c))))
(defun VADDCUQ (vd va vb) (set$ vd (carry-of-sum va vb 0:1)))
(defun VADDEUQM (vd va vb vc) (set$ vd (low-of-sum va vb vc)))
(defun VADDECUQ (vd va vb vc) (set$ vd (carry-of-sum va vb vc)))
(defun VSUBCUQ (vd va vb) (set$ vd (carry-of-sum va (lnot vb) 1:1)))
(defun VSUBEUQM (vd va vb vc) (set$ vd (low-of-sum va (lnot vb) vc)))
(defun VSUBECUQ (vd va vb vc) (set$ vd (carry-of-sum va (lnot vb) vc)))

(defun abs-diff (x y) (pick (< x y) (- y x) (- x y)))
(defun VABSDUB (vd va vb) (set$ vd (lanes8 abs-diff va vb)))
(defun VABSDUH (vd va vb) (set$ vd (lanes16 abs-diff va vb)))
(defun VABSDUW (vd va vb) (set$ vd (lanes32 abs-diff va vb)))

(defun negate (x) (neg x))
(defun VNEGW (vd vb) (set$ vd (lanes32-1 negate vb)))
(defun VNEGD (vd vb) (set$ vd (lanes64-1 negate vb)))

(defun VMAXUD (vd va vb) (set$ vd (lanes64 umax va vb)))
(defun VMAXSD (vd va vb) (set$ vd (lanes64 smax va vb)))
(defun VMINUD (vd va vb) (set$ vd (lanes64 umin va vb)))
(defun VMINSD (vd va vb) (set$ vd (lanes64 smin va vb)))

;; PRODUCTS

(defun VMULUWM (vd va vb) (set$ vd (lanes32 mul-low va vb)))
(defun mul-low (x y) (* x y))
(defun VMULLD (vd va vb) (set$ vd (lanes64 mul-low va vb)))

(defun VMULEUW (vd va vb) (set$ vd (lanes64 mule-u va vb)))
(defun VMULESW (vd va vb) (set$ vd (lanes64 mule-s va vb)))
(defun VMULOUW (vd va vb) (set$ vd (lanes64 mulo-u va vb)))
(defun VMULOSW (vd va vb) (set$ vd (lanes64 mulo-s va vb)))
(defun VMULEUD (vd va vb) (set$ vd (mule-u va vb)))
(defun VMULESD (vd va vb) (set$ vd (mule-s va vb)))
(defun VMULOUD (vd va vb) (set$ vd (mulo-u va vb)))
(defun VMULOSD (vd va vb) (set$ vd (mulo-s va vb)))

(defun mulh-u (x y)
  (let ((w (word-width x)))
    (cast-high w (* (cast-unsigned (* 2 w) x) (cast-unsigned (* 2 w) y)))))
(defun mulh-s (x y)
  (let ((w (word-width x)))
    (cast-high w (* (cast-signed (* 2 w) x) (cast-signed (* 2 w) y)))))
(defun VMULHUW (vd va vb) (set$ vd (lanes32 mulh-u va vb)))
(defun VMULHSW (vd va vb) (set$ vd (lanes32 mulh-s va vb)))
(defun VMULHUD (vd va vb) (set$ vd (lanes64 mulh-u va vb)))
(defun VMULHSD (vd va vb) (set$ vd (lanes64 mulh-s va vb)))

(defun mhadd (x y z)
  (let ((p (* (cast-signed 32 x) (cast-signed 32 y))))
    (cast-saturate :signed 16 (+ (arshift p 15) (cast-signed 32 z)))))
(defun mhradd (x y z)
  (let ((p (+ (* (cast-signed 32 x) (cast-signed 32 y)) 0x4000:32)))
    (cast-saturate :signed 16 (+ (arshift p 15) (cast-signed 32 z)))))
(defun VMHADDSHS (rt ra rb rc) (set$ rt (lanes16-3 mhadd ra rb rc)))
(defun VMHRADDSHS (rt ra rb rc) (set$ rt (lanes16-3 mhradd ra rb rc)))

(defun usat (w x)
  (let ((m (cast-unsigned (word-width x) (cast-signed w 1:1))))
    (cast-low w (pick (> x m) m x))))

(defun msum-shs (x y z)
  (cast-saturate :signed 32
                 (+ (cast-signed 64 (mule-s x y)) (cast-signed 64 (mulo-s x y)) (cast-signed 64 z))))
(defun msum-uhs (x y z)
  (usat 32 (+ (u64 (mule-u x y)) (u64 (mulo-u x y)) (u64 z))))
(defun VMSUMSHS (rt ra rb rc) (set$ rt (lanes32-3 msum-shs ra rb rc)))
(defun VMSUMUHS (rt ra rb rc) (set$ rt (lanes32-3 msum-uhs ra rb rc)))

;; the sum of the products of the doublewords and the quadword VC
(defun msum-ud (x y z)
  (+ (cast-unsigned 256 (mule-u x y)) (cast-unsigned 256 (mulo-u x y)) (cast-unsigned 256 z)))
(defun VMSUMUDM (rt ra rb rc) (set$ rt (cast-low 128 (msum-ud ra rb rc))))
(defun VMSUMCUD (rt ra rb rc) (set$ rt (cast-high 128 (msum-ud ra rb rc))))

(defun times-ten (x c) (+ (* (cast-unsigned 256 x) 10:256) (cast-unsigned 256 c)))
(defun VMUL10UQ (vd va) (set$ vd (cast-low 128 (times-ten va 0:4))))
(defun VMUL10CUQ (vd va) (set$ vd (cast-high 128 (times-ten va 0:4))))
(defun VMUL10EUQ (vd va vb) (set$ vd (cast-low 128 (times-ten va (extract 3 0 vb)))))
(defun VMUL10ECUQ (vd va vb) (set$ vd (cast-high 128 (times-ten va (extract 3 0 vb)))))

;; the carry-less products, a sum of the products of the elements, each
;; of the elements of the result has the size of two of the operands

(defun clmul-from (x y i)
  (if (= i (/ (word-width x) 2)) (cast-unsigned (word-width x) 0:1)
    (logxor (pick (select i y) (lshift x (u-like x i)) (cast-unsigned (word-width x) 0:1))
            (clmul-from x y (+ i 1)))))
(defun u-like (x i) (cast-unsigned (word-width x) (cast-unsigned 16 i)))
(defun clmul (x y) (clmul-from x y 0))
(defun clmul-sum (x y)
  (let ((h (/ (word-width x) 2)))
    (logxor (clmul (cast-unsigned (word-width x) (cast-high h x)) (cast-unsigned (word-width x) (cast-high h y)))
            (clmul (cast-unsigned (word-width x) (cast-low h x)) (cast-unsigned (word-width x) (cast-low h y))))))
(defun VPMSUMB (vd va vb) (set$ vd (lanes16 clmul-sum va vb)))
(defun VPMSUMH (vd va vb) (set$ vd (lanes32 clmul-sum va vb)))
(defun VPMSUMW (vd va vb) (set$ vd (lanes64 clmul-sum va vb)))
(defun VPMSUMD (vd va vb) (set$ vd (clmul-sum va vb)))

;; DIVISIONS. The result of an invalid division is undefined: the
;; dividend for the quotients, as in the scalar ones, and zero for the
;; remainders.

(defun VDIVUW (vd va vb) (set$ vd (lanes32 udiv va vb)))
(defun VDIVSW (vd va vb) (set$ vd (lanes32 sdiv va vb)))
(defun VDIVUD (vd va vb) (set$ vd (lanes64 udiv va vb)))
(defun VDIVSD (vd va vb) (set$ vd (lanes64 sdiv va vb)))
(defun VDIVUQ (vd va vb) (set$ vd (udiv va vb)))
(defun VDIVSQ (vd va vb) (set$ vd (sdiv va vb)))
(defun VMODUW (vd va vb) (set$ vd (lanes32 umod va vb)))
(defun VMODSW (vd va vb) (set$ vd (lanes32 smod va vb)))
(defun VMODUD (vd va vb) (set$ vd (lanes64 umod va vb)))
(defun VMODSD (vd va vb) (set$ vd (lanes64 smod va vb)))
(defun VMODUQ (vd va vb) (set$ vd (umod va vb)))
(defun VMODSQ (vd va vb) (set$ vd (smod va vb)))

(defun zeros-below (x) (concat x (cast-unsigned (word-width x) 0:1)))
(defun dive-u (x y)
  (let ((w (word-width x)))
    (pick (is-zero y) x
          (cast-low w (udiv (zeros-below x) (cast-unsigned (* 2 w) y))))))
(defun dive-s (x y)
  (let ((w (word-width x)))
    (pick (is-zero y) x
          (cast-low w (sdiv (zeros-below x) (cast-signed (* 2 w) y))))))
;; of the words, the undefined result of a division by zero is zero, as
;; in QEMU, and of the longer ones it is the dividend
(defun dive-uw (x y) (pick (is-zero y) 0:32 (dive-u x y)))
(defun dive-sw (x y) (pick (is-zero y) 0:32 (dive-s x y)))
(defun VDIVEUW (vd va vb) (set$ vd (lanes32 dive-uw va vb)))
(defun VDIVESW (vd va vb) (set$ vd (lanes32 dive-sw va vb)))
(defun VDIVEUD (vd va vb) (set$ vd (lanes64 dive-u va vb)))
(defun VDIVESD (vd va vb) (set$ vd (lanes64 dive-s va vb)))
(defun VDIVEUQ (vd va vb) (set$ vd (dive-u va vb)))
(defun VDIVESQ (vd va vb) (set$ vd (dive-s va vb)))

;; COMPARISONS

(defun ne-mask (x y) (cast-signed (word-width x) (/= x y)))
(defun nez-mask (x y) (cast-signed (word-width x) (logor (/= x y) (is-zero x) (is-zero y))))

(defun VCMPEQUD (vd va vb) (set$ vd (lanes64 eq-mask va vb)))
(defun VCMPGTUD (vd va vb) (set$ vd (lanes64 gtu-mask va vb)))
(defun VCMPGTSD (vd va vb) (set$ vd (lanes64 gts-mask va vb)))
(defun VCMPEQUQ (vd va vb) (set$ vd (eq-mask va vb)))
(defun VCMPGTUQ (vd va vb) (set$ vd (gtu-mask va vb)))
(defun VCMPGTSQ (vd va vb) (set$ vd (gts-mask va vb)))
(defun VCMPNEB (vd va vb) (set$ vd (lanes8 ne-mask va vb)))
(defun VCMPNEH (vd va vb) (set$ vd (lanes16 ne-mask va vb)))
(defun VCMPNEW (vd va vb) (set$ vd (lanes32 ne-mask va vb)))
(defun VCMPNEZB (vd va vb) (set$ vd (lanes8 nez-mask va vb)))
(defun VCMPNEZH (vd va vb) (set$ vd (lanes16 nez-mask va vb)))
(defun VCMPNEZW (vd va vb) (set$ vd (lanes32 nez-mask va vb)))
(defun VCMPEQUD_rec (vd va vb) (VCMPEQUD vd va vb) (record-vector vd))
(defun VCMPGTUD_rec (vd va vb) (VCMPGTUD vd va vb) (record-vector vd))
(defun VCMPGTSD_rec (vd va vb) (VCMPGTSD vd va vb) (record-vector vd))
(defun VCMPEQUQ_rec (vd va vb) (VCMPEQUQ vd va vb) (record-vector vd))
(defun VCMPGTUQ_rec (vd va vb) (VCMPGTUQ vd va vb) (record-vector vd))
(defun VCMPGTSQ_rec (vd va vb) (VCMPGTSQ vd va vb) (record-vector vd))
(defun VCMPNEB_rec (vd va vb) (VCMPNEB vd va vb) (record-vector vd))
(defun VCMPNEH_rec (vd va vb) (VCMPNEH vd va vb) (record-vector vd))
(defun VCMPNEW_rec (vd va vb) (VCMPNEW vd va vb) (record-vector vd))
(defun VCMPNEZB_rec (vd va vb) (VCMPNEZB vd va vb) (record-vector vd))
(defun VCMPNEZH_rec (vd va vb) (VCMPNEZH vd va vb) (record-vector vd))
(defun VCMPNEZW_rec (vd va vb) (VCMPNEZW vd va vb) (record-vector vd))

(defun VCMPUQ (bf va vb) (set$ bf (concat (< va vb) (> va vb) (= va vb) 0:1)))
(defun VCMPSQ (bf va vb) (set$ bf (concat (s< va vb) (s> va vb) (= va vb) 0:1)))

;; the bits of X are clear if it isn't greater than Y, and if it isn't
;; less than -Y, a NaN is out of bounds; denormals are zeros
(defun bounds (x y)
  (let ((a (nj x)) (b (nj y))
        (un (logor (fp-nan a) (fp-nan b)))
        (le (logor (fp-lt-bits a b) (fp-eq-bits a b)))
        (mb (fp-neg b))
        (ge (logor (fp-lt-bits mb a) (fp-eq-bits a mb))))
    (concat (logor un (not le)) (logor un (not ge)) 0:30)))
(defun VCMPBFP (vd va vb) (set$ vd (lanes32 bounds va vb)))
(defun VCMPBFP_rec (vd va vb)
  (VCMPBFP vd va vb)
  (set CR6 (concat 0:2 (is-zero vd) 0:1)))

;; COUNTS

(defun lane-clz (x) (cast-unsigned (word-width x) (clz x)))
(defun lane-ctz (x) (cast-unsigned (word-width x) (clz (reverse-bits x))))
(defun lane-pop (x) (cast-unsigned (word-width x) (popcount x)))

(defun VCLZB (vd vb) (set$ vd (lanes8-1 lane-clz vb)))
(defun VCLZH (vd vb) (set$ vd (lanes16-1 lane-clz vb)))
(defun VCLZW (vd vb) (set$ vd (lanes32-1 lane-clz vb)))
(defun VCLZD (vd vb) (set$ vd (lanes64-1 lane-clz vb)))
(defun VCTZB (vd vb) (set$ vd (lanes8-1 lane-ctz vb)))
(defun VCTZH (vd vb) (set$ vd (lanes16-1 lane-ctz vb)))
(defun VCTZW (vd vb) (set$ vd (lanes32-1 lane-ctz vb)))
(defun VCTZD (vd vb) (set$ vd (lanes64-1 lane-ctz vb)))
(defun VPOPCNTB (vd vb) (set$ vd (lanes8-1 lane-pop vb)))
(defun VPOPCNTH (vd vb) (set$ vd (lanes16-1 lane-pop vb)))
(defun VPOPCNTW (vd vb) (set$ vd (lanes32-1 lane-pop vb)))
(defun VPOPCNTD (vd vb) (set$ vd (lanes64-1 lane-pop vb)))

;; the least significant bits of the bytes, from the first one
(defun byte-lsb (x) (select 0 x))
(defun VCLZLSBB (rt vb)
  (let ((m (lanes8-1 byte-lsb vb))) (set$ rt (zext (clz m)))))
(defun VCTZLSBB (rt vb)
  (let ((m (lanes8-1 byte-lsb vb))) (set$ rt (zext (clz (reverse-bits m))))))

(defun parity-of-bytes (x)
  (let ((m (logand x (/ (lnot (cast-unsigned (word-width x) 0:1)) (cast-unsigned (word-width x) 255:8)))))
    (cast-unsigned (word-width x) (select 0 (popcount-128 m)))))
(defun popcount-128 (x)
  (case (word-width x)
    32 (popcount x)
    64 (popcount x)
    (+ (cast-unsigned 8 (popcount (cast-high 64 x)))
       (cast-unsigned 8 (popcount (cast-low 64 x))))))
(defun VPRTYBW (vd vb) (set$ vd (lanes32-1 parity-of-bytes vb)))
(defun VPRTYBD (vd vb) (set$ vd (lanes64-1 parity-of-bytes vb)))
(defun VPRTYBQ (vd vb) (set$ vd (parity-of-bytes vb)))

;; the counts of the elements whose most significant bit is MP, in the
;; high bits of the register
(defun sum-bytes-16 (x)
  (+ (cast-unsigned 8 (extract 127 120 x)) (extract 119 112 x) (extract 111 104 x) (extract 103 96 x)
     (extract 95 88 x) (extract 87 80 x) (extract 79 72 x) (extract 71 64 x)
     (extract 63 56 x) (extract 55 48 x) (extract 47 40 x) (extract 39 32 x)
     (extract 31 24 x) (extract 23 16 x) (extract 15 8 x) (extract 7 0 x)))
(defun mp-bit (mp) (cast-low 1 mp))
(defun bytes-of-msbs (mp x) (cast-unsigned (word-width x) (= (msb x) mp)))
(defun VCNTMBB (rd vb mp)
  (let ((m (mp-bit mp)))
    (set$ rd (cast-low (word-width) (lshift (u64 (sum-bytes-16 (lanes8-e bytes-of-msbs m vb))) 56)))))
(defun VCNTMBH (rd vb mp)
  (let ((m (mp-bit mp)))
    (set$ rd (cast-low (word-width) (lshift (u64 (sum-bytes-16 (lanes16-e bytes-of-msbs m vb))) 57)))))
(defun VCNTMBW (rd vb mp)
  (let ((m (mp-bit mp)))
    (set$ rd (cast-low (word-width) (lshift (u64 (sum-bytes-16 (lanes32-e bytes-of-msbs m vb))) 58)))))
(defun VCNTMBD (rd vb mp)
  (let ((m (mp-bit mp)))
    (set$ rd (cast-low (word-width) (lshift (u64 (sum-bytes-16 (lanes64-e bytes-of-msbs m vb))) 59)))))

;; the masks: the most significant bits of the elements, spread over the
;; elements, gathered in a register, and from a register

(defun all-as-msb (x) (cast-signed (word-width x) (msb x)))
(defun VEXPANDBM (vd vb) (set$ vd (lanes8-1 all-as-msb vb)))
(defun VEXPANDHM (vd vb) (set$ vd (lanes16-1 all-as-msb vb)))
(defun VEXPANDWM (vd vb) (set$ vd (lanes32-1 all-as-msb vb)))
(defun VEXPANDDM (vd vb) (set$ vd (lanes64-1 all-as-msb vb)))
(defun VEXPANDQM (vd vb) (set$ vd (all-as-msb vb)))

(defun VEXTRACTBM (rt vb) (set$ rt (zext (lanes8-1 msb vb))))
(defun VEXTRACTHM (rt vb) (set$ rt (zext (lanes16-1 msb vb))))
(defun VEXTRACTWM (rt vb) (set$ rt (zext (lanes32-1 msb vb))))
(defun VEXTRACTDM (rt vb) (set$ rt (zext (lanes64-1 msb vb))))
(defun VEXTRACTQM (rt vb) (set$ rt (zext (msb vb))))

(defun spread-byte (m i) (cast-signed 8 (select i m)))
(defun spread-16 (m)
  (concat (spread-byte m 15) (spread-byte m 14) (spread-byte m 13) (spread-byte m 12)
          (spread-byte m 11) (spread-byte m 10) (spread-byte m 9) (spread-byte m 8)
          (spread-byte m 7) (spread-byte m 6) (spread-byte m 5) (spread-byte m 4)
          (spread-byte m 3) (spread-byte m 2) (spread-byte m 1) (spread-byte m 0)))
(defun spread-of (m i) (cast-signed 16 (select i m)))
(defun MTVSRBM (vd rb) (set$ vd (spread-16 (u64 rb))))
(defun MTVSRBMI (rt d) (set$ rt (spread-16 (u64 d))))
(defun MTVSRHM (vd rb)
  (let ((m (u64 rb)))
    (set$ vd (concat (spread-of m 7) (spread-of m 6) (spread-of m 5) (spread-of m 4)
                     (spread-of m 3) (spread-of m 2) (spread-of m 1) (spread-of m 0)))))
(defun MTVSRWM (vd rb)
  (let ((m (u64 rb)))
    (set$ vd (concat (cast-signed 32 (select 3 m)) (cast-signed 32 (select 2 m))
                     (cast-signed 32 (select 1 m)) (cast-signed 32 (select 0 m))))))
(defun MTVSRDM (vd rb)
  (let ((m (u64 rb)))
    (set$ vd (concat (cast-signed 64 (select 1 m)) (cast-signed 64 (select 0 m))))))
(defun MTVSRQM (vd rb) (set$ vd (cast-signed 128 (select 0 rb))))

;; the bit permutations; the indexes that are out of range select zeros

(defun bit-at (x i)
  (let ((w (word-width x))
        (k (cast-unsigned w i)))
    (logand (< k (cast-unsigned w (cast-unsigned 16 w)))
            (cast-low 1 (rshift x (- (cast-unsigned w (cast-unsigned 16 (- w 1))) k))))))
(defun bperm-dword (x sel)
  (cast-unsigned 64
    (concat (bit-at x (extract 63 56 sel)) (bit-at x (extract 55 48 sel))
            (bit-at x (extract 47 40 sel)) (bit-at x (extract 39 32 sel))
            (bit-at x (extract 31 24 sel)) (bit-at x (extract 23 16 sel))
            (bit-at x (extract 15 8 sel)) (bit-at x (extract 7 0 sel)))))
(defun VBPERMD (vd va vb) (set$ vd (lanes64 bperm-dword va vb)))
(defun VBPERMQ (vd va vb)
  (set$ vd (concat (cast-unsigned 64 (lanes8-e bit-at va vb)) (cast-unsigned 64 0:1))))

(defun VPDEPD (vd va vb) (set$ vd (lanes64 pdep va vb)))
(defun VPEXTD (vd va vb) (set$ vd (lanes64 pext va vb)))
(defun VCFUGED (vd va vb) (set$ vd (lanes64 cfuge va vb)))
(defun VCLZDM (vd va vb) (set$ vd (lanes64 cntlzdm va vb)))
(defun VCTZDM (vd va vb) (set$ vd (lanes64 cnttzdm va vb)))

;; the transposition of the matrix of the bits of the bytes
(defun gather-step (x m n)
  (let ((t0 (logand (logxor x (rshift x n)) m)))
    (logxor x t0 (lshift t0 n))))
(defun gather-bytes (x)
  (let ((a (gather-step x 0x00aa00aa00aa00aa:64 (u64 7)))
        (b (gather-step a 0x0000cccc0000cccc:64 (u64 14))))
    (gather-step b 0x00000000f0f0f0f0:64 (u64 28))))
(defun VGBBD (vd vb) (set$ vd (lanes64-1 gather-bytes vb)))

;; every N-th bit, from the first one, on the left of the register; N
;; is 2 to 7, the other values are reserved
(defun gather-nth (v n i k r)
  (if (>= i 128) r
    (gather-nth v n (+ i n) (+ k 1)
                (logor r (lshift (u64 (select (- 127 i) v)) (u64 (- 63 k)))))))
(defun VGNB (rd vb n)
  (set$ rd (if (< n 2)
               (intrinsic 'vgnb-reserved vb n :result (word-width))
             (zext (gather-nth vb n 0 0 (u64 0))))))

;; PERMUTATIONS

(defun permuted-byte-r (ab k)
  (cast-low 8 (rshift ab (* 8 (cast-unsigned 256 (logand k 31))))))
(defun VPERMR (rt ra rb rc)
  (let ((ab (concat ra rb)))
    (set$ rt (lanes8-e permuted-byte-r ab rc))))

(defun byte-of (x k)
  (cast-low 8 (rshift x (* 8 (cast-unsigned 128 (- 15:4 k))))))
(defun permxor-byte (s c)
  (logxor (byte-of (cast-high 128 s) (extract 7 4 c))
          (byte-of (cast-low 128 s) (extract 3 0 c))))
(defun VPERMXOR (rt ra rb rc)
  (let ((ab (concat ra rb)))
    (set$ rt (lanes8-e permxor-byte ab rc))))

(defun VMRGEW (vd va vb)
  (set$ vd (concat (extract 127 96 va) (extract 127 96 vb) (extract 63 32 va) (extract 63 32 vb))))
(defun VMRGOW (vd va vb)
  (set$ vd (concat (extract 95 64 va) (extract 95 64 vb) (extract 31 0 va) (extract 31 0 vb))))

;; PACKS AND UNPACKS

(defun ss8 (x) (cast-saturate :signed 8 x))
(defun su8 (x) (cast-saturate :unsigned 8 x))
(defun uu8 (x) (usat 8 x))
(defun ss16 (x) (cast-saturate :signed 16 x))
(defun su16 (x) (cast-saturate :unsigned 16 x))
(defun uu16 (x) (usat 16 x))
(defun ss32 (x) (cast-saturate :signed 32 x))
(defun su32 (x) (cast-saturate :unsigned 32 x))
(defun uu32 (x) (usat 32 x))
(defun low-half (x) (cast-low 32 x))

(defun VPKSHSS (vd va vb) (set$ vd (concat (lanes16-1 ss8 va) (lanes16-1 ss8 vb))))
(defun VPKSHUS (vd va vb) (set$ vd (concat (lanes16-1 su8 va) (lanes16-1 su8 vb))))
(defun VPKUHUS (vd va vb) (set$ vd (concat (lanes16-1 uu8 va) (lanes16-1 uu8 vb))))
(defun VPKSWSS (vd va vb) (set$ vd (concat (lanes32-1 ss16 va) (lanes32-1 ss16 vb))))
(defun VPKSWUS (vd va vb) (set$ vd (concat (lanes32-1 su16 va) (lanes32-1 su16 vb))))
(defun VPKUWUS (vd va vb) (set$ vd (concat (lanes32-1 uu16 va) (lanes32-1 uu16 vb))))
(defun VPKSDSS (vd va vb) (set$ vd (concat (lanes64-1 ss32 va) (lanes64-1 ss32 vb))))
(defun VPKSDUS (vd va vb) (set$ vd (concat (lanes64-1 su32 va) (lanes64-1 su32 vb))))
(defun VPKUDUS (vd va vb) (set$ vd (concat (lanes64-1 uu32 va) (lanes64-1 uu32 vb))))
(defun VPKUDUM (vd va vb) (set$ vd (concat (lanes64-1 low-half va) (lanes64-1 low-half vb))))

;; a pixel of 8-8-8-8 bits to 1-5-5-5 and back
(defun pack-pixel (x)
  (concat (select 24 x) (extract 23 19 x) (extract 15 11 x) (extract 7 3 x)))
(defun VPKPX (vd va vb) (set$ vd (concat (lanes32-1 pack-pixel va) (lanes32-1 pack-pixel vb))))
(defun unpack-pixel (x)
  (concat (cast-signed 8 (msb x)) 0:3 (extract 14 10 x) 0:3 (extract 9 5 x) 0:3 (extract 4 0 x)))
(defun VUPKHPX (vd vb)
  (set$ vd (concat (unpack-pixel (extract 127 112 vb)) (unpack-pixel (extract 111 96 vb))
                   (unpack-pixel (extract 95 80 vb)) (unpack-pixel (extract 79 64 vb)))))
(defun VUPKLPX (vd vb)
  (set$ vd (concat (unpack-pixel (extract 63 48 vb)) (unpack-pixel (extract 47 32 vb))
                   (unpack-pixel (extract 31 16 vb)) (unpack-pixel (extract 15 0 vb)))))

(defun VUPKHSW (vd vb)
  (set$ vd (concat (cast-signed 64 (extract 127 96 vb)) (cast-signed 64 (extract 95 64 vb)))))
(defun VUPKLSW (vd vb)
  (set$ vd (concat (cast-signed 64 (extract 63 32 vb)) (cast-signed 64 (extract 31 0 vb)))))

(defun sign-byte-of-word (x) (cast-signed 32 (cast-low 8 x)))
(defun sign-half-of-word (x) (cast-signed 32 (cast-low 16 x)))
(defun sign-byte-of-dword (x) (cast-signed 64 (cast-low 8 x)))
(defun sign-half-of-dword (x) (cast-signed 64 (cast-low 16 x)))
(defun sign-word-of-dword (x) (cast-signed 64 (cast-low 32 x)))
(defun VEXTSB2W (vd vb) (set$ vd (lanes32-1 sign-byte-of-word vb)))
(defun VEXTSH2W (vd vb) (set$ vd (lanes32-1 sign-half-of-word vb)))
(defun VEXTSB2D (vd vb) (set$ vd (lanes64-1 sign-byte-of-dword vb)))
(defun VEXTSH2D (vd vb) (set$ vd (lanes64-1 sign-half-of-dword vb)))
(defun VEXTSW2D (vd vb) (set$ vd (lanes64-1 sign-word-of-dword vb)))
(defun VEXTSD2Q (vd vb) (set$ vd (cast-signed 128 (cast-low 64 vb))))

;; EXTRACTS AND INSERTS. The offsets count bytes from the most
;; significant one of the register, or from the least significant one
;; for the variants that say it; what doesn't fit is not defined, a
;; load is of zeros and a store does nothing.

;; the element of SIZE bytes at the offset OFF from the left
(defun element-at (v size off)
  (cast-low (* 8 size) (rshift v (* 8 (- 16 size off)))))

(defun fixed-extract (vd vb size off)
  (set$ vd (concat (u64 (element-at vb size off)) (u64 0))))
(defun VEXTRACTUB (vd uim vb) (fixed-extract vd vb 1 uim))
(defun VEXTRACTUH (vd uim vb) (fixed-extract vd vb 2 uim))
(defun VEXTRACTUW (vd uim vb) (fixed-extract vd vb 4 uim))
(defun VEXTRACTD (vd uim vb) (fixed-extract vd vb 8 uim))

(defun insert-at (vd x size off)
  (let ((sh (* 8 (- 16 size off)))
        (m (lshift (u128 (cast-signed (* 8 size) 1:1)) sh)))
    (set$ vd (logor (logand vd (lnot m)) (lshift (u128 x) sh)))))
(defun VINSERTB (vd _ uim vb) (insert-at vd (extract 71 64 vb) 1 uim))
(defun VINSERTH (vd _ uim vb) (insert-at vd (extract 79 64 vb) 2 uim))
(defun VINSERTW (vd uim vb) (insert-at vd (extract 95 64 vb) 4 uim))
(defun VINSERTD (vd uim vb) (insert-at vd (extract 127 64 vb) 8 uim))
(defun VINSW (vd _ uim rb) (insert-at vd (low32 rb) 4 uim))
(defun VINSD (vd _ uim rb) (insert-at vd (u64 rb) 8 uim))

;; the element at an offset of the four low bits of a register, of the 16
;; bytes of X
(defun dynamic-shift (size off)
  (* (u128 8) (- (- (u128 16) (u128 size)) (u128 off))))
(defun extract-left (rt ra vb size)
  (let ((off (logand (u64 ra) 15:64)))
    (set$ rt (zext (u64 (cast-low (* 8 size) (rshift vb (dynamic-shift size off))))))))
(defun extract-right (rt ra vb size)
  (let ((off (logand (u64 ra) 15:64)))
    (set$ rt (zext (u64 (cast-low (* 8 size) (rshift vb (* (u128 8) (u128 off)))))))))
(defun VEXTUBLX (rt ra vb) (extract-left rt ra vb 1))
(defun VEXTUHLX (rt ra vb) (extract-left rt ra vb 2))
(defun VEXTUWLX (rt ra vb) (extract-left rt ra vb 4))
(defun VEXTUBRX (rt ra vb) (extract-right rt ra vb 1))
(defun VEXTUHRX (rt ra vb) (extract-right rt ra vb 2))
(defun VEXTUWRX (rt ra vb) (extract-right rt ra vb 4))

;; the offset is the five low bits of the register, the element of the
;; 32 bytes of RA and RB goes to the low bits of the first doubleword
(defun double-offset (size off right)
  (let ((k (logand (u64 off) 31:64)))
    (if (non-zero right) (- (u64 (- 32 size)) k) k)))
(defun extract-double (rt ra rb rc size right)
  (let ((off (double-offset size rc right))
        (fits (<= off (u64 (- 32 size))))
        (sh (* (cast-unsigned 256 (cast-unsigned 16 8)) (- (cast-unsigned 256 (u64 (- 32 size))) (cast-unsigned 256 off))))
        (x (u64 (cast-low (* 8 size) (rshift (concat ra rb) sh)))))
    (set$ rt (concat (pick fits x (u64 0)) (u64 0)))))
(defun VEXTDUBVLX (rt ra rb rc) (extract-double rt ra rb rc 1 0))
(defun VEXTDUHVLX (rt ra rb rc) (extract-double rt ra rb rc 2 0))
(defun VEXTDUWVLX (rt ra rb rc) (extract-double rt ra rb rc 4 0))
(defun VEXTDDVLX (rt ra rb rc) (extract-double rt ra rb rc 8 0))
(defun VEXTDUBVRX (rt ra rb rc) (extract-double rt ra rb rc 1 1))
(defun VEXTDUHVRX (rt ra rb rc) (extract-double rt ra rb rc 2 1))
(defun VEXTDUWVRX (rt ra rb rc) (extract-double rt ra rb rc 4 1))
(defun VEXTDDVRX (rt ra rb rc) (extract-double rt ra rb rc 8 1))

(defun insert-dynamic (vd x size off right)
  (let ((k (logand (u64 off) 15:64))
        (o (if (non-zero right) (- (u64 (- 16 size)) k) k))
        (fits (<= o (u64 (- 16 size))))
        (sh (* (u128 8) (- (u128 (- 16 size)) (u128 o))))
        (m (lshift (u128 (cast-signed (* 8 size) 1:1)) sh)))
    (set$ vd (pick fits (logor (logand vd (lnot m)) (lshift (u128 x) sh)) vd))))
(defun VINSBLX (vd _ ra rb) (insert-dynamic vd (cast-low 8 rb) 1 ra 0))
(defun VINSHLX (vd _ ra rb) (insert-dynamic vd (cast-low 16 rb) 2 ra 0))
(defun VINSWLX (vd _ ra rb) (insert-dynamic vd (low32 rb) 4 ra 0))
(defun VINSDLX (vd _ ra rb) (insert-dynamic vd (u64 rb) 8 ra 0))
(defun VINSBRX (vd _ ra rb) (insert-dynamic vd (cast-low 8 rb) 1 ra 1))
(defun VINSHRX (vd _ ra rb) (insert-dynamic vd (cast-low 16 rb) 2 ra 1))
(defun VINSWRX (vd _ ra rb) (insert-dynamic vd (low32 rb) 4 ra 1))
(defun VINSDRX (vd _ ra rb) (insert-dynamic vd (u64 rb) 8 ra 1))
(defun VINSBVLX (vd _ ra vb) (insert-dynamic vd (extract 71 64 vb) 1 ra 0))
(defun VINSHVLX (vd _ ra vb) (insert-dynamic vd (extract 79 64 vb) 2 ra 0))
(defun VINSWVLX (vd _ ra vb) (insert-dynamic vd (extract 95 64 vb) 4 ra 0))
(defun VINSBVRX (vd _ ra vb) (insert-dynamic vd (extract 71 64 vb) 1 ra 1))
(defun VINSHVRX (vd _ ra vb) (insert-dynamic vd (extract 79 64 vb) 2 ra 1))
(defun VINSWVRX (vd _ ra vb) (insert-dynamic vd (extract 95 64 vb) 4 ra 1))

;; the N rightmost bytes, or the N leftmost ones, are kept, N is the
;; whole register, and all of them are kept if it is at least 16
(defun VCLRLB (vd va rb)
  (let ((n (u64 rb)))
    (set$ vd (pick (< n (u64 16))
                   (logand va (rshift (lnot (u128 0)) (* (u128 8) (- (u128 16) (u128 n)))))
                   va))))
(defun VCLRRB (vd va rb)
  (let ((n (u64 rb)))
    (set$ vd (pick (< n (u64 16))
                   (logand va (lshift (lnot (u128 0)) (* (u128 8) (- (u128 16) (u128 n)))))
                   va))))

;; the string isolate: the elements up to the first zero, from the left
;; or from the right, are kept, the record form says if there is a zero

(defun nonzero-byte (x) (non-zero x))
(defun leading-kept (m) (cast-unsigned 128 (clz (lnot m))))
(defun trailing-kept (m) (cast-unsigned 128 (clz (reverse-bits (lnot m)))))
(defun keep-left (v n bits)
  (logand v (lshift (lnot (u128 0)) (* (u128 bits) (- (u128 (/ 128 bits)) n)))))
(defun keep-right (v n bits)
  (logand v (rshift (lnot (u128 0)) (* (u128 bits) (- (u128 (/ 128 bits)) n)))))
(defun VSTRIBL (vt vb)
  (let ((m (lanes8-1 nonzero-byte vb)))
    (set$ vt (keep-left vb (leading-kept m) 8))))
(defun VSTRIBR (vt vb)
  (let ((m (lanes8-1 nonzero-byte vb)))
    (set$ vt (keep-right vb (trailing-kept m) 8))))
(defun VSTRIHL (vt vb)
  (let ((m (lanes16-1 nonzero-byte vb)))
    (set$ vt (keep-left vb (leading-kept m) 16))))
(defun VSTRIHR (vt vb)
  (let ((m (lanes16-1 nonzero-byte vb)))
    (set$ vt (keep-right vb (trailing-kept m) 16))))
(defun record-string (found) (set CR6 (concat 0:2 found 0:1)))
(defun VSTRIBL_rec (vt vb)
  (let ((found (/= (lanes8-1 nonzero-byte vb) 0xffff:16)))
    (VSTRIBL vt vb)
    (record-string found)))
(defun VSTRIBR_rec (vt vb)
  (let ((found (/= (lanes8-1 nonzero-byte vb) 0xffff:16)))
    (VSTRIBR vt vb)
    (record-string found)))
(defun VSTRIHL_rec (vt vb)
  (let ((found (/= (lanes16-1 nonzero-byte vb) 0xff:8)))
    (VSTRIHL vt vb)
    (record-string found)))
(defun VSTRIHR_rec (vt vb)
  (let ((found (/= (lanes16-1 nonzero-byte vb) 0xff:8)))
    (VSTRIHR vt vb)
    (record-string found)))

;; SHIFTS AND ROTATIONS

(defun VSLD (vd va vb) (set$ vd (lanes64 shl va vb)))
(defun VSRD (vd va vb) (set$ vd (lanes64 shr va vb)))
(defun VSRAD (vd va vb) (set$ vd (lanes64 sar va vb)))
(defun VRLD (vd va vb) (set$ vd (lanes64 rol va vb)))

;; the count of the quadword is the 7 low bits of the first doubleword
(defun q-count (vb) (logand (rshift vb 64) 127:128))
(defun VSLQ (vd va vb) (set$ vd (lshift va (q-count vb))))
(defun VSRQ (vd va vb) (set$ vd (rshift va (q-count vb))))
(defun VSRAQ (vd va vb) (set$ vd (arshift va (q-count vb))))
(defun VRLQ (vd va vb) (set$ vd (rotate-left va (q-count vb))))

;; the bytes shifted by their own counts, with the bits of the next byte
(defun slv-byte (x n s)
  (cast-high 8 (lshift (concat x n) (cast-unsigned 16 (logand s 7:8)))))
(defun srv-byte (p x s)
  (cast-low 8 (rshift (concat p x) (cast-unsigned 16 (logand s 7:8)))))
(defun VSLV (vd va vb)
  (let ((next (lshift va 8:128)))
    (set$ vd (lanes8-3 slv-byte va next vb))))
(defun VSRV (vd va vb)
  (let ((prev (rshift va 8:128)))
    (set$ vd (lanes8-3 srv-byte prev va vb))))

(defun VSLDBI (rt ra rb sh)
  (set$ rt (cast-high 128 (lshift (concat ra rb) (cast-unsigned 256 (logand sh 7))))))
(defun VSRDBI (rt ra rb sh)
  (set$ rt (cast-low 128 (rshift (concat ra rb) (cast-unsigned 256 (logand sh 7))))))

;; the rotations under a mask: the bits of the element of VB are MB at
;; 16, ME at 8 and the count at 0, of the size of the bit number
(defun mask-of (x b e)
  (let ((ones (lnot (cast-unsigned (word-width x) 0:1)))
        (hi (rshift ones b))
        (lo (lshift ones (- (- (cast-unsigned (word-width x) (cast-unsigned 16 (word-width x)))
                               (one-like x))
                            e))))
    (pick (<= b e) (logand hi lo) (logor hi lo))))

(defun mask-field (x sh)
  (let ((bits (- (cast-unsigned (word-width x) (cast-unsigned 16 (word-width x))) (one-like x))))
    (logand (rshift x (cast-unsigned (word-width x) (cast-unsigned 16 sh))) bits)))

(defun rlnm (x c)
  (logand (rotate-left x (mask-field c 0)) (mask-of x (mask-field c 16) (mask-field c 8))))
(defun rlmi (x c t0)
  (let ((m (mask-of x (mask-field c 16) (mask-field c 8))))
    (logor (logand (rotate-left x (mask-field c 0)) m) (logand t0 (lnot m)))))

(defun VRLWNM (vd va vb) (set$ vd (lanes32 rlnm va vb)))
(defun VRLDNM (vd va vb) (set$ vd (lanes64 rlnm va vb)))
(defun VRLWMI (vd va vb _) (set$ vd (lanes32-3 rlmi va vb vd)))
(defun VRLDMI (vd va vb _) (set$ vd (lanes64-3 rlmi va vb vd)))

;; the fields are in the first doubleword of VB
(defun q-field (vb sh) (logand (rshift vb (+ 64:128 (u128 sh))) 127:128))
(defun VRLQNM (vd va vb)
  (let ((m (mask-of va (q-field vb 16) (q-field vb 8))))
    (set$ vd (logand (rotate-left va (q-field vb 0)) m))))
(defun VRLQMI (vd va vb _)
  (let ((m (mask-of va (q-field vb 16) (q-field vb 8))))
    (set$ vd (logor (logand (rotate-left va (q-field vb 0)) m) (logand vd (lnot m))))))

;; the sums across, of signed or unsigned elements, saturated

(defun sat-sw (x) (cast-saturate :signed 32 x))
(defun s64 (x) (cast-signed 64 x))
(defun sum4sb (x y)
  (sat-sw (+ (s64 (extract 31 24 x)) (s64 (extract 23 16 x)) (s64 (extract 15 8 x)) (s64 (extract 7 0 x)) (s64 y))))
(defun sum4ub (x y)
  (usat 32 (+ (u64 (extract 31 24 x)) (u64 (extract 23 16 x)) (u64 (extract 15 8 x)) (u64 (extract 7 0 x)) (u64 y))))
(defun sum4sh (x y)
  (sat-sw (+ (s64 (extract 31 16 x)) (s64 (extract 15 0 x)) (s64 y))))
(defun VSUM4SBS (vd va vb) (set$ vd (lanes32 sum4sb va vb)))
(defun VSUM4UBS (vd va vb) (set$ vd (lanes32 sum4ub va vb)))
(defun VSUM4SHS (vd va vb) (set$ vd (lanes32 sum4sh va vb)))
(defun sum2sw (x y)
  (u64 (sat-sw (+ (s64 (extract 63 32 x)) (s64 (extract 31 0 x)) (s64 (extract 31 0 y))))))
(defun VSUM2SWS (vd va vb) (set$ vd (lanes64 sum2sw va vb)))
(defun VSUMSWS (vd va vb)
  (set$ vd (u128 (sat-sw (+ (s64 (extract 127 96 va)) (s64 (extract 95 64 va))
                            (s64 (extract 63 32 va)) (s64 (extract 31 0 va))
                            (s64 (extract 31 0 vb)))))))

;; FLOATING-POINT OPERATIONS

;; the estimates: the reciprocals are exact, rounded, as in FRES, the
;; exponent and the logarithm are of the intrinsics

(defun refp (x)
  (let ((a (nj x)))
    (nj (pick (fp-nan a) (quiet32 a) (/. :rne 0x3f800000:32 a)))))
(defun rsqrtefp (x)
  (let ((a (nj x)))
    (nj (pick (fp-nan a) (quiet32 a) (/. :rne 0x3f800000:32 (fsqrt :rne a))))))
(defun exptefp (x) (intrinsic 'vexptefp (nj x) :result 32))
(defun logefp (x) (intrinsic 'vlogefp (nj x) :result 32))
(defun VREFP (vd vb) (set$ vd (lanes32-1 refp vb)))
(defun VRSQRTEFP (vd vb) (set$ vd (lanes32-1 rsqrtefp vb)))
(defun VEXPTEFP (vd vb) (set$ vd (lanes32-1 exptefp vb)))
(defun VLOGEFP (vd vb) (set$ vd (lanes32-1 logefp vb)))

;; the conversion to a fixed-point word, of UIMM fraction bits: the
;; single times 2^UIM as a double, rounded toward zero, saturated, a NaN
;; is zero
(defun fixed-source (uim x)
  (let ((d (single-to-double (nj x))))
    (pick (logor (is-zero (fp-exponent d)) (fp-nan d) (fp-inf d)) d
          (+ d (lshift (u64 uim) 52)))))
(defun ctsxs (uim x) (cast-low 32 (fp-to-signed (fixed-source uim x) 32 (u64 0))))
(defun ctuxs (uim x) (cast-low 32 (fp-to-unsigned (fixed-source uim x) 32 (u64 0))))
(defun VCTSXS (vd uim vb) (set$ vd (lanes32-e ctsxs uim vb)))
(defun VCTUXS (vd uim vb) (set$ vd (lanes32-e ctuxs uim vb)))

;; CRYPTOGRAPHY, the operations of AES are in no theory here, as in
;; the other targets; the SHA-2 functions are by their definitions

(defun VCIPHER (vd va vb) (set$ vd (intrinsic 'vcipher va vb :result 128)))
(defun VCIPHERLAST (vd va vb) (set$ vd (intrinsic 'vcipherlast va vb :result 128)))
(defun VNCIPHER (vd va vb) (set$ vd (intrinsic 'vncipher va vb :result 128)))
(defun VNCIPHERLAST (vd va vb) (set$ vd (intrinsic 'vncipherlast va vb :result 128)))
(defun VSBOX (vd va) (set$ vd (intrinsic 'vsbox va :result 128)))

(defun rotr (x n) (rotate-right x (cast-unsigned (word-width x) (cast-unsigned 16 n))))
(defun shr-n (x n) (rshift x (cast-unsigned (word-width x) (cast-unsigned 16 n))))
(defun xor3 (a b c) (logxor a b c))

(defun sha256-function (x st six)
  (if (non-zero st)
      (if (non-zero six)
          (xor3 (rotr x 6) (rotr x 11) (rotr x 25))
        (xor3 (rotr x 2) (rotr x 13) (rotr x 22)))
    (if (non-zero six)
        (xor3 (rotr x 17) (rotr x 19) (shr-n x 10))
      (xor3 (rotr x 7) (rotr x 18) (shr-n x 3)))))

(defun sha512-function (x st six)
  (if (non-zero st)
      (if (non-zero six)
          (xor3 (rotr x 14) (rotr x 18) (rotr x 41))
        (xor3 (rotr x 28) (rotr x 34) (rotr x 39)))
    (if (non-zero six)
        (xor3 (rotr x 19) (rotr x 61) (shr-n x 6))
      (xor3 (rotr x 1) (rotr x 8) (shr-n x 7)))))

(defun VSHASIGMAW (vd va st six)
  (set$ vd (concat (sha256-function (extract 127 96 va) st (logand six 8))
                   (sha256-function (extract 95 64 va) st (logand six 4))
                   (sha256-function (extract 63 32 va) st (logand six 2))
                   (sha256-function (extract 31 0 va) st (logand six 1)))))
(defun VSHASIGMAD (vd va st six)
  (set$ vd (concat (sha512-function (extract 127 64 va) st (logand six 8))
                   (sha512-function (extract 63 0 va) st (logand six 2)))))

;;; THE VECTOR INSTRUCTIONS THAT ONLY LLVM'S FUTURE DEFINITIONS HAVE
;;
;; They aren't in the published ISA 3.1, so they lift to intrinsics by
;; their names, and nothing about them is checked.

(defun VUCMPRHB (vt va vb) (set$ vt (intrinsic 'vucmprhb va vb :result 128)))
(defun VUCMPRHH (vt va vb) (set$ vt (intrinsic 'vucmprhh va vb :result 128)))
(defun VUCMPRHN (vt va vb) (set$ vt (intrinsic 'vucmprhn va vb :result 128)))
(defun VUCMPRLB (vt va vb) (set$ vt (intrinsic 'vucmprlb va vb :result 128)))
(defun VUCMPRLH (vt va vb) (set$ vt (intrinsic 'vucmprlh va vb :result 128)))
(defun VUCMPRLN (vt va vb) (set$ vt (intrinsic 'vucmprln va vb :result 128)))
(defun VUPKHSNTOB (vt vb) (set$ vt (intrinsic 'vupkhsntob vb :result 128)))
(defun VUPKLSNTOB (vt vb) (set$ vt (intrinsic 'vupklsntob vb :result 128)))
(defun VUPKINT4TOBF16 (vt vb uim) (set$ vt (intrinsic 'vupkint4tobf16 vb uim :result 128)))
(defun VUPKINT8TOFP32 (vt vb uim) (set$ vt (intrinsic 'vupkint8tofp32 vb uim :result 128)))
(defun VUPKINT4TOFP32 (vt vb uim) (set$ vt (intrinsic 'vupkint4tofp32 vb uim :result 128)))
(defun VUPKINT8TOBF16 (vt vb uim) (set$ vt (intrinsic 'vupkint8tobf16 vb uim :result 128)))
