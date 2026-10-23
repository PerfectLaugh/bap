(declare (context (target x86)))
(require x86-common)

(in-package x86-common)

;;; BIT OPERATIONS AND CONDITIONS

;; the condition codes of LLVM, as in the encodings of Jcc
(defun condition (cc)
  (case cc
    0 OF
    1 (not OF)
    2 CF
    3 (not CF)
    4 ZF
    5 (not ZF)
    6 (logor CF ZF)
    7 (not (logor CF ZF))
    8 SF
    9 (not SF)
    10 PF
    11 (not PF)
    12 (/= SF OF)
    13 (= SF OF)
    14 (logor ZF (/= SF OF))
    (not (logor ZF (/= SF OF)))))

(defun SETCCr (rd cc) (set$ rd (cast-unsigned 8 (condition cc))))
(defun SETCCm (base scale index off seg cc)
  (store-byte (ea base scale index off seg) (cast-unsigned 8 (condition cc))))

;; the destination of CMOV is written even if the condition is false,
;; which clears the upper half of a 64-bit register

(defun CMOV16rr (rd x y cc) (set-gpr rd (if (condition cc) y x)))
(defun CMOV16rm (rd x base scale index off seg cc)
  (set-gpr rd (if (condition cc) (load-n 16 (ea base scale index off seg)) x)))
(defun CMOV32rr (rd x y cc) (set-gpr rd (if (condition cc) y x)))
(defun CMOV32rm (rd x base scale index off seg cc)
  (set-gpr rd (if (condition cc) (load-n 32 (ea base scale index off seg)) x)))
(defun CMOV64rr (rd x y cc) (set-gpr rd (if (condition cc) y x)))
(defun CMOV64rm (rd x base scale index off seg cc)
  (set-gpr rd (if (condition cc) (load-n 64 (ea base scale index off seg)) x)))

;; BT copies the bit to CF, the bit offsets of the register forms
;; address the bit string that starts at the memory operand, the
;; immediates are taken modulo the size, the other flags but ZF are
;; undefined and are not changed
(defun bit-index (x i) (logand i (- (word-width x) 1)))
(defun bit-at (x i) (lsb (rshift x (bit-index x i))))
(defun bit-mask (x i) (lshift (cast-unsigned (word-width x) 1:1) (bit-index x i)))

(defun bts-op (x m) (logor x m))
(defun btr-op (x m) (logand x (lnot m)))
(defun btc-op (x m) (logxor x m))

(defmacro bt-rr (x i) (set CF (bit-at x i)))
(defmacro btx-rr (op rd x i)
  (prog
    (set CF (bit-at x i))
    (set-gpr rd (op x (bit-mask x i)))))

;; the address of the word of the bit I of the string at A
(defun bit-word (a n i)
  (+ a (* (/ n 8) (arshift (cast-signed (word-width a) i) (case n 16 4 32 5 6)))))

(defmacro bt-mr (n i base scale index off seg)
  (let ((x (load-n n (bit-word (ea base scale index off seg) n i))))
    (set CF (bit-at x (cast-low n i)))))

(defmacro btx-mr (op n i base scale index off seg)
  (let ((a (bit-word (ea base scale index off seg) n i))
        (x (load-n n a))
        (j (cast-low n i)))
    (set CF (bit-at x j))
    (store-n n a (op x (bit-mask x j)))))

(defmacro bt-mi (n i base scale index off seg)
  (let ((x (load-n n (ea base scale index off seg))))
    (set CF (bit-at x (cast-low n i)))))

(defmacro btx-mi (op n i base scale index off seg)
  (let ((a (ea base scale index off seg))
        (x (load-n n a))
        (j (cast-low n i)))
    (set CF (bit-at x j))
    (store-n n a (op x (bit-mask x j)))))

(defun BT16rr (x i) (bt-rr x (cast-low 16 i)))
(defun BT16ri8 (x i) (bt-rr x (cast-low 16 i)))
(defun BT16mr (base scale index off seg i) (bt-mr 16 i base scale index off seg))
(defun BT16mi8 (base scale index off seg i) (bt-mi 16 i base scale index off seg))
(defun BT32rr (x i) (bt-rr x (cast-low 32 i)))
(defun BT32ri8 (x i) (bt-rr x (cast-low 32 i)))
(defun BT32mr (base scale index off seg i) (bt-mr 32 i base scale index off seg))
(defun BT32mi8 (base scale index off seg i) (bt-mi 32 i base scale index off seg))
(defun BT64rr (x i) (bt-rr x (cast-low 64 i)))
(defun BT64ri8 (x i) (bt-rr x (cast-low 64 i)))
(defun BT64mr (base scale index off seg i) (bt-mr 64 i base scale index off seg))
(defun BT64mi8 (base scale index off seg i) (bt-mi 64 i base scale index off seg))
(defun BTS16rr (rd x i) (btx-rr bts-op rd x (cast-low 16 i)))
(defun BTS16ri8 (rd x i) (btx-rr bts-op rd x (cast-low 16 i)))
(defun BTS16mr (base scale index off seg i) (btx-mr bts-op 16 i base scale index off seg))
(defun BTS16mi8 (base scale index off seg i) (btx-mi bts-op 16 i base scale index off seg))
(defun BTS32rr (rd x i) (btx-rr bts-op rd x (cast-low 32 i)))
(defun BTS32ri8 (rd x i) (btx-rr bts-op rd x (cast-low 32 i)))
(defun BTS32mr (base scale index off seg i) (btx-mr bts-op 32 i base scale index off seg))
(defun BTS32mi8 (base scale index off seg i) (btx-mi bts-op 32 i base scale index off seg))
(defun BTS64rr (rd x i) (btx-rr bts-op rd x (cast-low 64 i)))
(defun BTS64ri8 (rd x i) (btx-rr bts-op rd x (cast-low 64 i)))
(defun BTS64mr (base scale index off seg i) (btx-mr bts-op 64 i base scale index off seg))
(defun BTS64mi8 (base scale index off seg i) (btx-mi bts-op 64 i base scale index off seg))
(defun BTR16rr (rd x i) (btx-rr btr-op rd x (cast-low 16 i)))
(defun BTR16ri8 (rd x i) (btx-rr btr-op rd x (cast-low 16 i)))
(defun BTR16mr (base scale index off seg i) (btx-mr btr-op 16 i base scale index off seg))
(defun BTR16mi8 (base scale index off seg i) (btx-mi btr-op 16 i base scale index off seg))
(defun BTR32rr (rd x i) (btx-rr btr-op rd x (cast-low 32 i)))
(defun BTR32ri8 (rd x i) (btx-rr btr-op rd x (cast-low 32 i)))
(defun BTR32mr (base scale index off seg i) (btx-mr btr-op 32 i base scale index off seg))
(defun BTR32mi8 (base scale index off seg i) (btx-mi btr-op 32 i base scale index off seg))
(defun BTR64rr (rd x i) (btx-rr btr-op rd x (cast-low 64 i)))
(defun BTR64ri8 (rd x i) (btx-rr btr-op rd x (cast-low 64 i)))
(defun BTR64mr (base scale index off seg i) (btx-mr btr-op 64 i base scale index off seg))
(defun BTR64mi8 (base scale index off seg i) (btx-mi btr-op 64 i base scale index off seg))
(defun BTC16rr (rd x i) (btx-rr btc-op rd x (cast-low 16 i)))
(defun BTC16ri8 (rd x i) (btx-rr btc-op rd x (cast-low 16 i)))
(defun BTC16mr (base scale index off seg i) (btx-mr btc-op 16 i base scale index off seg))
(defun BTC16mi8 (base scale index off seg i) (btx-mi btc-op 16 i base scale index off seg))
(defun BTC32rr (rd x i) (btx-rr btc-op rd x (cast-low 32 i)))
(defun BTC32ri8 (rd x i) (btx-rr btc-op rd x (cast-low 32 i)))
(defun BTC32mr (base scale index off seg i) (btx-mr btc-op 32 i base scale index off seg))
(defun BTC32mi8 (base scale index off seg i) (btx-mi btc-op 32 i base scale index off seg))
(defun BTC64rr (rd x i) (btx-rr btc-op rd x (cast-low 64 i)))
(defun BTC64ri8 (rd x i) (btx-rr btc-op rd x (cast-low 64 i)))
(defun BTC64mr (base scale index off seg i) (btx-mr btc-op 64 i base scale index off seg))
(defun BTC64mi8 (base scale index off seg i) (btx-mi btc-op 64 i base scale index off seg))

;; BSF and BSR don't change the destination if the source is zero, the
;; flags but ZF are undefined and are not changed
;; the counts are computed before the choice, as their computation is
;; a sequence of statements, whose temporaries the choice reads
(defun bsf-op (x y)
  (let ((r (resize (word-width x) (clz (reverse-bits y)))))
    (set ZF (is-zero y))
    (if (is-zero y) x r)))

(defun bsr-op (x y)
  (let ((r (- (resize (word-width x) (- (word-width y) 1))
              (resize (word-width x) (clz y)))))
    (set ZF (is-zero y))
    (if (is-zero y) x r)))

;; POPCNT clears the flags but ZF, LZCNT and TZCNT set CF if the source
;; is zero and ZF if the result is zero
(defun popcnt-op (y)
  (let ((r (resize (word-width y) (popcount y))))
    (set ZF (is-zero y))
    (set CF 0:1)
    (set OF 0:1)
    (set SF 0:1)
    (set AF 0:1)
    (set PF 0:1)
    r))

(defun count-flags (y r)
  (set CF (is-zero y))
  (set ZF (is-zero r))
  r)

(defun lzcnt-op (y) (count-flags y (resize (word-width y) (clz y))))
(defun tzcnt-op (y) (count-flags y (resize (word-width y) (clz (reverse-bits y)))))

(defun BSF16rr (rd x y) (set-gpr rd (bsf-op x y)))
(defun BSF16rm (rd x base scale index off seg) (set-gpr rd (bsf-op x (load-n 16 (ea base scale index off seg)))))
(defun BSF32rr (rd x y) (set-gpr rd (bsf-op x y)))
(defun BSF32rm (rd x base scale index off seg) (set-gpr rd (bsf-op x (load-n 32 (ea base scale index off seg)))))
(defun BSF64rr (rd x y) (set-gpr rd (bsf-op x y)))
(defun BSF64rm (rd x base scale index off seg) (set-gpr rd (bsf-op x (load-n 64 (ea base scale index off seg)))))
(defun BSR16rr (rd x y) (set-gpr rd (bsr-op x y)))
(defun BSR16rm (rd x base scale index off seg) (set-gpr rd (bsr-op x (load-n 16 (ea base scale index off seg)))))
(defun BSR32rr (rd x y) (set-gpr rd (bsr-op x y)))
(defun BSR32rm (rd x base scale index off seg) (set-gpr rd (bsr-op x (load-n 32 (ea base scale index off seg)))))
(defun BSR64rr (rd x y) (set-gpr rd (bsr-op x y)))
(defun BSR64rm (rd x base scale index off seg) (set-gpr rd (bsr-op x (load-n 64 (ea base scale index off seg)))))
(defun POPCNT16rr (rd y) (set-gpr rd (popcnt-op y)))
(defun POPCNT16rm (rd base scale index off seg) (set-gpr rd (popcnt-op (load-n 16 (ea base scale index off seg)))))
(defun POPCNT32rr (rd y) (set-gpr rd (popcnt-op y)))
(defun POPCNT32rm (rd base scale index off seg) (set-gpr rd (popcnt-op (load-n 32 (ea base scale index off seg)))))
(defun POPCNT64rr (rd y) (set-gpr rd (popcnt-op y)))
(defun POPCNT64rm (rd base scale index off seg) (set-gpr rd (popcnt-op (load-n 64 (ea base scale index off seg)))))
(defun LZCNT16rr (rd y) (set-gpr rd (lzcnt-op y)))
(defun LZCNT16rm (rd base scale index off seg) (set-gpr rd (lzcnt-op (load-n 16 (ea base scale index off seg)))))
(defun LZCNT32rr (rd y) (set-gpr rd (lzcnt-op y)))
(defun LZCNT32rm (rd base scale index off seg) (set-gpr rd (lzcnt-op (load-n 32 (ea base scale index off seg)))))
(defun LZCNT64rr (rd y) (set-gpr rd (lzcnt-op y)))
(defun LZCNT64rm (rd base scale index off seg) (set-gpr rd (lzcnt-op (load-n 64 (ea base scale index off seg)))))
(defun TZCNT16rr (rd y) (set-gpr rd (tzcnt-op y)))
(defun TZCNT16rm (rd base scale index off seg) (set-gpr rd (tzcnt-op (load-n 16 (ea base scale index off seg)))))
(defun TZCNT32rr (rd y) (set-gpr rd (tzcnt-op y)))
(defun TZCNT32rm (rd base scale index off seg) (set-gpr rd (tzcnt-op (load-n 32 (ea base scale index off seg)))))
(defun TZCNT64rr (rd y) (set-gpr rd (tzcnt-op y)))
(defun TZCNT64rm (rd base scale index off seg) (set-gpr rd (tzcnt-op (load-n 64 (ea base scale index off seg)))))

(defun BSWAP32r (rd x)
  (set-gpr rd (concat (extract 7 0 x) (extract 15 8 x)
                      (extract 23 16 x) (extract 31 24 x))))

;; MOVBE, the moves, that swap the bytes, of the loads and the stores
(defun bswap-n (n x)
  (case n
    16 (concat (extract 7 0 x) (extract 15 8 x))
    32 (concat (extract 7 0 x) (extract 15 8 x)
               (extract 23 16 x) (extract 31 24 x))
    (concat (extract 7 0 x) (extract 15 8 x)
            (extract 23 16 x) (extract 31 24 x)
            (extract 39 32 x) (extract 47 40 x)
            (extract 55 48 x) (extract 63 56 x))))

(defun MOVBE16rm (rd base scale index off seg)
  (set-gpr rd (bswap-n 16 (load-n 16 (ea base scale index off seg)))))
(defun MOVBE32rm (rd base scale index off seg)
  (set-gpr rd (bswap-n 32 (load-n 32 (ea base scale index off seg)))))
(defun MOVBE64rm (rd base scale index off seg)
  (set-gpr rd (bswap-n 64 (load-n 64 (ea base scale index off seg)))))
(defun MOVBE16mr (base scale index off seg x)
  (store-n 16 (ea base scale index off seg) (bswap-n 16 (cast-low 16 x))))
(defun MOVBE32mr (base scale index off seg x)
  (store-n 32 (ea base scale index off seg) (bswap-n 32 (cast-low 32 x))))
(defun MOVBE64mr (base scale index off seg x)
  (store-n 64 (ea base scale index off seg) (bswap-n 64 x)))

(defun BSWAP64r (rd x)
  (set-gpr rd (concat (extract 7 0 x) (extract 15 8 x)
                      (extract 23 16 x) (extract 31 24 x)
                      (extract 39 32 x) (extract 47 40 x)
                      (extract 55 48 x) (extract 63 56 x))))
