(declare (context (target powerpc-family)))

(defpackage powerpc (:use core target))
(defpackage llvm-powerpc32 (:use powerpc))
(defpackage llvm-powerpc32le (:use powerpc))
(defpackage llvm-powerpc64 (:use powerpc))
(defpackage llvm-powerpc64le (:use powerpc))

(in-package powerpc)

;;; POWER ISA 3.0 FIXED-POINT, BRANCH AND CONDITION REGISTER INSTRUCTIONS
;;
;; The registers are words, 32 or 64 bits. In the 64-bit mode the
;; operations on words, e.g., ADD4, use the whole registers, as the
;; processor does. The condition register is the eight fields CR0 to
;; CR7, the aliases of their bits, e.g., CR0LT, and the bits of XER are
;; the flags SO, OV, CA, OV32 and CA32. The disassembler names the base
;; register 0 of the addresses ZERO, whose value is zero, and divides the
;; branch displacements by four.

(defun low32 (x) (cast-low 32 x))
(defun sext (x) (cast-signed (word-width) x))
(defun zext (x) (cast-unsigned (word-width) x))
(defun ones64 () (cast-signed 64 1:1))

;; the record forms, e.g., ADD4_rec, compare the result with zero in CR0

(defun record (r)
  (set CR0LT (s< r 0))
  (set CR0GT (s> r 0))
  (set CR0EQ (is-zero r))
  (set CR0UN SO))

(defun set-field (crf lt gt eq)
  (set$ crf (concat lt gt eq SO)))

;; the overflow-enabled forms, e.g., ADD4O, set OV and OV32, and SO if
;; there was an overflow

(defun set-ov (ov ov32)
  (set OV ov)
  (set OV32 ov32)
  (set SO (logor SO ov)))

(defun set-ca (ca ca32)
  (set CA ca)
  (set CA32 ca32))

;;; ADDITION AND SUBTRACTION
;;
;; The additions and subtractions are X + Y + C, e.g., SUBF is
;; (lnot RA) + RB + 1, the carry and the overflow of the low halves are
;; CA32 and OV32.

(defun sum (x y c) (+ x y (zext c)))

(defun add-ca (rt x y c)
  (let ((r (sum x y c)))
    (set-ca (carry r x y) (carry (low32 r) (low32 x) (low32 y)))
    (set$ rt r)))

(defun add-ov (rt x y c)
  (let ((r (sum x y c)))
    (set-ov (overflow r x y) (overflow (low32 r) (low32 x) (low32 y)))
    (set$ rt r)))

(defun add-ca-ov (rt x y c)
  (let ((r (sum x y c)))
    (set-ca (carry r x y) (carry (low32 r) (low32 x) (low32 y)))
    (set-ov (overflow r x y) (overflow (low32 r) (low32 x) (low32 y)))
    (set$ rt r)))

;; the shifted immediates are sign-extended from 32 bits
(defun high-imm (imm) (sext (low32 (lshift imm 16))))

(defun ADD4 (rt ra rb) (set$ rt (+ ra rb)))
(defun ADD4O (rt ra rb) (add-ov rt ra rb 0:1))
(defun ADDI (rt ra imm) (set$ rt (+ ra imm)))
(defun ADDIS (rt ra imm) (set$ rt (+ ra (high-imm imm))))
(defun LI (rt imm) (set$ rt imm))
(defun LIS (rt imm) (set$ rt (high-imm imm)))
(defun ADDPCIS (rt imm) (set$ rt (+ (get-program-counter) 4 (high-imm imm))))
(defun ADDIC (rt ra imm) (add-ca rt ra imm 0:1))
(defun ADDC (rt ra rb) (add-ca rt ra rb 0:1))
(defun ADDCO (rt ra rb) (add-ca-ov rt ra rb 0:1))
(defun ADDE (rt ra rb) (add-ca rt ra rb CA))
(defun ADDEO (rt ra rb) (add-ca-ov rt ra rb CA))
(defun ADDME (rt ra) (add-ca rt ra (sext 1:1) CA))
(defun ADDMEO (rt ra) (add-ca-ov rt ra (sext 1:1) CA))
(defun ADDZE (rt ra) (add-ca rt ra 0 CA))
(defun ADDZEO (rt ra) (add-ca-ov rt ra 0 CA))
(defun SUBF (rt ra rb) (set$ rt (- rb ra)))
(defun SUBFO (rt ra rb) (add-ov rt (lnot ra) rb 1:1))
(defun SUBFIC (rt ra imm) (add-ca rt (lnot ra) imm 1:1))
(defun SUBFC (rt ra rb) (add-ca rt (lnot ra) rb 1:1))
(defun SUBFCO (rt ra rb) (add-ca-ov rt (lnot ra) rb 1:1))
(defun SUBFE (rt ra rb) (add-ca rt (lnot ra) rb CA))
(defun SUBFEO (rt ra rb) (add-ca-ov rt (lnot ra) rb CA))
(defun SUBFME (rt ra) (add-ca rt (lnot ra) (sext 1:1) CA))
(defun SUBFMEO (rt ra) (add-ca-ov rt (lnot ra) (sext 1:1) CA))
(defun SUBFZE (rt ra) (add-ca rt (lnot ra) 0 CA))
(defun SUBFZEO (rt ra) (add-ca-ov rt (lnot ra) 0 CA))
(defun NEG (rt ra) (set$ rt (neg ra)))
(defun NEGO (rt ra) (add-ov rt (lnot ra) 0 1:1))

(defun ADD4_rec (rt ra rb) (ADD4 rt ra rb) (record rt))
(defun ADD4O_rec (rt ra rb) (ADD4O rt ra rb) (record rt))
(defun ADDIC_rec (rt ra imm) (ADDIC rt ra imm) (record rt))
(defun ADDC_rec (rt ra rb) (ADDC rt ra rb) (record rt))
(defun ADDCO_rec (rt ra rb) (ADDCO rt ra rb) (record rt))
(defun ADDE_rec (rt ra rb) (ADDE rt ra rb) (record rt))
(defun ADDEO_rec (rt ra rb) (ADDEO rt ra rb) (record rt))
(defun ADDME_rec (rt ra) (ADDME rt ra) (record rt))
(defun ADDMEO_rec (rt ra) (ADDMEO rt ra) (record rt))
(defun ADDZE_rec (rt ra) (ADDZE rt ra) (record rt))
(defun ADDZEO_rec (rt ra) (ADDZEO rt ra) (record rt))
(defun SUBF_rec (rt ra rb) (SUBF rt ra rb) (record rt))
(defun SUBFO_rec (rt ra rb) (SUBFO rt ra rb) (record rt))
(defun SUBFC_rec (rt ra rb) (SUBFC rt ra rb) (record rt))
(defun SUBFCO_rec (rt ra rb) (SUBFCO rt ra rb) (record rt))
(defun SUBFE_rec (rt ra rb) (SUBFE rt ra rb) (record rt))
(defun SUBFEO_rec (rt ra rb) (SUBFEO rt ra rb) (record rt))
(defun SUBFME_rec (rt ra) (SUBFME rt ra) (record rt))
(defun SUBFMEO_rec (rt ra) (SUBFMEO rt ra) (record rt))
(defun SUBFZE_rec (rt ra) (SUBFZE rt ra) (record rt))
(defun SUBFZEO_rec (rt ra) (SUBFZEO rt ra) (record rt))
(defun NEG_rec (rt ra) (NEG rt ra) (record rt))
(defun NEGO_rec (rt ra) (NEGO rt ra) (record rt))

;;; MULTIPLICATION AND DIVISION
;;
;; The high words of the products of words are zero-extended, as the
;; ISA leaves the high half of the register undefined in the 64-bit
;; mode. The quotient of an invalid division, by zero or of the most
;; negative number by -1, is the dividend for DIVW and DIVD and zero for
;; the extended divisions, and the remainder is zero, as in QEMU.

(defmacro mul32 (cast ra rb) (* (cast 64 (low32 ra)) (cast 64 (low32 rb))))
(defmacro mul64 (cast ra rb) (* (cast 128 ra) (cast 128 rb)))

(defun MULLI (rt ra imm) (set$ rt (* ra imm)))
(defun MULLW (rt ra rb)
  (set$ rt (cast-low (word-width) (mul32 cast-signed ra rb))))
(defun MULLWO (rt ra rb)
  (let ((p (mul32 cast-signed ra rb))
        (ov (/= p (cast-signed 64 (low32 p)))))
    (set-ov ov ov)
    (set$ rt (cast-low (word-width) p))))
(defun MULHW (rt ra rb) (set$ rt (zext (cast-high 32 (mul32 cast-signed ra rb)))))
(defun MULHWU (rt ra rb) (set$ rt (zext (cast-high 32 (mul32 cast-unsigned ra rb)))))
(defun MULLD (rt ra rb) (set$ rt (* ra rb)))
(defun MULLDO (rt ra rb)
  (let ((p (mul64 cast-signed ra rb))
        (ov (/= p (cast-signed 128 (cast-low 64 p)))))
    (set-ov ov ov)
    (set$ rt (cast-low 64 p))))
(defun MULHD (rt ra rb) (set$ rt (cast-high 64 (mul64 cast-signed ra rb))))
(defun MULHDU (rt ra rb) (set$ rt (cast-high 64 (mul64 cast-unsigned ra rb))))

(defun MULLW_rec (rt ra rb) (MULLW rt ra rb) (record rt))
(defun MULLWO_rec (rt ra rb) (MULLWO rt ra rb) (record rt))
(defun MULHW_rec (rt ra rb) (MULHW rt ra rb) (record rt))
(defun MULHWU_rec (rt ra rb) (MULHWU rt ra rb) (record rt))
(defun MULLD_rec (rt ra rb) (MULLD rt ra rb) (record rt))
(defun MULLDO_rec (rt ra rb) (MULLDO rt ra rb) (record rt))
(defun MULHD_rec (rt ra rb) (MULHD rt ra rb) (record rt))
(defun MULHDU_rec (rt ra rb) (MULHDU rt ra rb) (record rt))

(defun most-negative (x) (lshift (cast-unsigned (word-width x) 1:1) (- (word-width x) 1)))

(defun invalid-sdiv (x y)
  (logor (is-zero y) (logand (= x (most-negative x)) (= y (lnot (cast-low (word-width y) 0))))))

;; the divisor of an invalid division is 1, so that nothing divides by zero
(defun one-like (x) (cast-unsigned (word-width x) 1:1))
(defun sdivisor (x y) (if (invalid-sdiv x y) (one-like y) y))
(defun udivisor (y) (if (is-zero y) (one-like y) y))

(defun sdiv (x y) (s/ x (sdivisor x y)))
(defun udiv (x y) (/ x (udivisor y)))
(defun smod (x y) (let ((d (sdivisor x y))) (- x (* (s/ x d) d))))
(defun umod (x y) (let ((d (udivisor y))) (- x (* (/ x d) d))))

(defun DIVW (rt ra rb) (set$ rt (zext (sdiv (low32 ra) (low32 rb)))))
(defun DIVWU (rt ra rb) (set$ rt (zext (udiv (low32 ra) (low32 rb)))))
(defun DIVWO (rt ra rb)
  (let ((ov (invalid-sdiv (low32 ra) (low32 rb))))
    (DIVW rt ra rb)
    (set-ov ov ov)))
(defun DIVWUO (rt ra rb)
  (let ((ov (is-zero (low32 rb))))
    (DIVWU rt ra rb)
    (set-ov ov ov)))

(defun DIVD (rt ra rb) (set$ rt (sdiv ra rb)))
(defun DIVDU (rt ra rb) (set$ rt (udiv ra rb)))
(defun DIVDO (rt ra rb)
  (let ((ov (invalid-sdiv ra rb)))
    (DIVD rt ra rb)
    (set-ov ov ov)))
(defun DIVDUO (rt ra rb)
  (let ((ov (is-zero rb)))
    (DIVDU rt ra rb)
    (set-ov ov ov)))

;; the extended divisions divide the low word of RA shifted by a word,
;; the quotient doesn't fit a word if they overflow, the quotients of the
;; signed divisions are sign-extended

(defun divwe-overflow (y q) (logor (is-zero y) (/= q (cast-signed 64 (low32 q)))))
(defun divweu-overflow (y q) (logor (is-zero y) (/= q (cast-unsigned 64 (low32 q)))))
(defun divde-overflow (y q) (logor (is-zero y) (/= q (cast-signed 128 (cast-low 64 q)))))
(defun divdeu-overflow (y q) (logor (is-zero y) (/= q (cast-unsigned 128 (cast-low 64 q)))))

(defmacro divide-extended (rt ov cast size div overflow ra rb)
  (let ((x (concat (cast-low size ra) (cast-low size 0)))
        (y (cast (* 2 size) (cast-low size rb)))
        (q (div x y)))
    (set ov (overflow y q))
    (set$ rt (if ov 0 (cast (word-width) (cast-low size q))))))

(defun DIVWE (rt ra rb)
  (let ((ov false)) (divide-extended rt ov cast-signed 32 sdiv divwe-overflow ra rb)))
(defun DIVWEU (rt ra rb)
  (let ((ov false)) (divide-extended rt ov cast-unsigned 32 udiv divweu-overflow ra rb)))
(defun DIVDE (rt ra rb)
  (let ((ov false)) (divide-extended rt ov cast-signed 64 sdiv divde-overflow ra rb)))
(defun DIVDEU (rt ra rb)
  (let ((ov false)) (divide-extended rt ov cast-unsigned 64 udiv divdeu-overflow ra rb)))
(defun DIVWEO (rt ra rb)
  (let ((ov false))
    (divide-extended rt ov cast-signed 32 sdiv divwe-overflow ra rb)
    (set-ov ov ov)))
(defun DIVWEUO (rt ra rb)
  (let ((ov false))
    (divide-extended rt ov cast-unsigned 32 udiv divweu-overflow ra rb)
    (set-ov ov ov)))
(defun DIVDEO (rt ra rb)
  (let ((ov false))
    (divide-extended rt ov cast-signed 64 sdiv divde-overflow ra rb)
    (set-ov ov ov)))
(defun DIVDEUO (rt ra rb)
  (let ((ov false))
    (divide-extended rt ov cast-unsigned 64 udiv divdeu-overflow ra rb)
    (set-ov ov ov)))

(defun MODSW (rt ra rb) (set$ rt (sext (smod (low32 ra) (low32 rb)))))
(defun MODUW (rt ra rb) (set$ rt (zext (umod (low32 ra) (low32 rb)))))
(defun MODSD (rt ra rb) (set$ rt (smod ra rb)))
(defun MODUD (rt ra rb) (set$ rt (umod ra rb)))

(defun DIVW_rec (rt ra rb) (DIVW rt ra rb) (record rt))
(defun DIVWU_rec (rt ra rb) (DIVWU rt ra rb) (record rt))
(defun DIVWO_rec (rt ra rb) (DIVWO rt ra rb) (record rt))
(defun DIVWUO_rec (rt ra rb) (DIVWUO rt ra rb) (record rt))
(defun DIVD_rec (rt ra rb) (DIVD rt ra rb) (record rt))
(defun DIVDU_rec (rt ra rb) (DIVDU rt ra rb) (record rt))
(defun DIVDO_rec (rt ra rb) (DIVDO rt ra rb) (record rt))
(defun DIVDUO_rec (rt ra rb) (DIVDUO rt ra rb) (record rt))
(defun DIVWE_rec (rt ra rb) (DIVWE rt ra rb) (record rt))
(defun DIVWEU_rec (rt ra rb) (DIVWEU rt ra rb) (record rt))
(defun DIVWEO_rec (rt ra rb) (DIVWEO rt ra rb) (record rt))
(defun DIVWEUO_rec (rt ra rb) (DIVWEUO rt ra rb) (record rt))
(defun DIVDE_rec (rt ra rb) (DIVDE rt ra rb) (record rt))
(defun DIVDEU_rec (rt ra rb) (DIVDEU rt ra rb) (record rt))
(defun DIVDEO_rec (rt ra rb) (DIVDEO rt ra rb) (record rt))
(defun DIVDEUO_rec (rt ra rb) (DIVDEUO rt ra rb) (record rt))

;;; LOGICAL OPERATIONS
;;
;; The immediates of the logical operations are zero-extended.

(defun uimm (imm) (zext (cast-low 16 imm)))
(defun high-uimm (imm) (zext (lshift (cast-unsigned 32 (cast-low 16 imm)) 16)))

(defun AND (ra rs rb) (set$ ra (logand rs rb)))
(defun ANDC (ra rs rb) (set$ ra (logand rs (lnot rb))))
(defun ANDI_rec (ra rs imm) (set$ ra (logand rs (uimm imm))) (record ra))
(defun ANDIS_rec (ra rs imm) (set$ ra (logand rs (high-uimm imm))) (record ra))
(defun OR (ra rs rb) (set$ ra (logor rs rb)))
(defun ORC (ra rs rb) (set$ ra (logor rs (lnot rb))))
(defun ORI (ra rs imm) (set$ ra (logor rs (uimm imm))))
(defun ORIS (ra rs imm) (set$ ra (logor rs (high-uimm imm))))
(defun XOR (ra rs rb) (set$ ra (logxor rs rb)))
(defun XORI (ra rs imm) (set$ ra (logxor rs (uimm imm))))
(defun XORIS (ra rs imm) (set$ ra (logxor rs (high-uimm imm))))
(defun NAND (ra rs rb) (set$ ra (lnot (logand rs rb))))
(defun NOR (ra rs rb) (set$ ra (lnot (logor rs rb))))
(defun EQV (ra rs rb) (set$ ra (lnot (logxor rs rb))))
(defun NOP () (empty))

(defun EXTSB (ra rs) (set$ ra (sext (cast-low 8 rs))))
(defun EXTSH (ra rs) (set$ ra (sext (cast-low 16 rs))))
(defun EXTSW (ra rs) (set$ ra (sext (low32 rs))))
(defun CNTLZW (ra rs) (set$ ra (zext (clz (low32 rs)))))
(defun CNTLZD (ra rs) (set$ ra (zext (clz rs))))
(defun CNTTZW (ra rs) (set$ ra (zext (clz (reverse-bits (low32 rs))))))
(defun CNTTZD (ra rs) (set$ ra (zext (clz (reverse-bits rs)))))

(defun popcount-of-words (x)
  (let ((y (cast-unsigned 64 x)))
    (cast-low (word-width)
              (concat (cast-unsigned 32 (popcount (cast-high 32 y)))
                      (cast-unsigned 32 (popcount (low32 y)))))))

(defun popcount-of-bytes (x)
  (let ((y (cast-unsigned 64 x)))
    (cast-low (word-width)
              (concat (cast-unsigned 8 (popcount (extract 63 56 y)))
                      (cast-unsigned 8 (popcount (extract 55 48 y)))
                      (cast-unsigned 8 (popcount (extract 47 40 y)))
                      (cast-unsigned 8 (popcount (extract 39 32 y)))
                      (cast-unsigned 8 (popcount (extract 31 24 y)))
                      (cast-unsigned 8 (popcount (extract 23 16 y)))
                      (cast-unsigned 8 (popcount (extract 15 8 y)))
                      (cast-unsigned 8 (popcount (extract 7 0 y)))))))

(defun POPCNTB (ra rs) (set$ ra (popcount-of-bytes rs)))
(defun POPCNTW (ra rs) (set$ ra (popcount-of-words rs)))
(defun POPCNTD (ra rs) (set$ ra (zext (popcount rs))))

(defun byte-mask (x y i)
  (if (= (extract (+ (* 8 i) 7) (* 8 i) x) (extract (+ (* 8 i) 7) (* 8 i) y))
      0xff:8 0:8))

(defun CMPB (ra rs rb)
  (let ((x (cast-unsigned 64 rs))
        (y (cast-unsigned 64 rb)))
    (set$ ra (cast-low (word-width)
                       (concat (byte-mask x y 7) (byte-mask x y 6)
                               (byte-mask x y 5) (byte-mask x y 4)
                               (byte-mask x y 3) (byte-mask x y 2)
                               (byte-mask x y 1) (byte-mask x y 0))))))

;; the bit I of the result is the bit of RB, in the big-endian numbering,
;; that the byte I of RS selects
(defun permuted-bit (rs rb i)
  (let ((k (cast-unsigned 64 (extract (- 63 (* 8 i)) (- 56 (* 8 i)) rs))))
    (if (< k 64) (cast-low 1 (rshift rb (- 63 k))) 0:1)))

(defun BPERMD (ra rs rb)
  (set$ ra (cast-unsigned 64
                         (concat (permuted-bit rs rb 0) (permuted-bit rs rb 1)
                                 (permuted-bit rs rb 2) (permuted-bit rs rb 3)
                                 (permuted-bit rs rb 4) (permuted-bit rs rb 5)
                                 (permuted-bit rs rb 6) (permuted-bit rs rb 7)))))

(defun AND_rec (ra rs rb) (AND ra rs rb) (record ra))
(defun ANDC_rec (ra rs rb) (ANDC ra rs rb) (record ra))
(defun OR_rec (ra rs rb) (OR ra rs rb) (record ra))
(defun ORC_rec (ra rs rb) (ORC ra rs rb) (record ra))
(defun XOR_rec (ra rs rb) (XOR ra rs rb) (record ra))
(defun NAND_rec (ra rs rb) (NAND ra rs rb) (record ra))
(defun NOR_rec (ra rs rb) (NOR ra rs rb) (record ra))
(defun EQV_rec (ra rs rb) (EQV ra rs rb) (record ra))
(defun EXTSB_rec (ra rs) (EXTSB ra rs) (record ra))
(defun EXTSH_rec (ra rs) (EXTSH ra rs) (record ra))
(defun EXTSW_rec (ra rs) (EXTSW ra rs) (record ra))
(defun CNTLZW_rec (ra rs) (CNTLZW ra rs) (record ra))
(defun CNTLZD_rec (ra rs) (CNTLZD ra rs) (record ra))
(defun CNTTZW_rec (ra rs) (CNTTZW ra rs) (record ra))
(defun CNTTZD_rec (ra rs) (CNTTZD ra rs) (record ra))

;;; ROTATIONS AND SHIFTS
;;
;; The rotations of words rotate the low word replicated in both halves
;; of a doubleword, and the masks MASK(B, E) have the ones from the bit B
;; to the bit E, in the big-endian numbering, wrapping around if B > E,
;; so a rotation of a word may set the high half of the register in the
;; 64-bit mode.

(defun rotl32 (x n)
  (let ((w (low32 x))) (rotate-left (concat w w) n)))

(defun mask (b e)
  (let ((hi (rshift (ones64) b))
        (lo (lshift (ones64) (- 63 e))))
    (if (<= b e) (logand hi lo) (logor hi lo))))

(defun rotated (r m) (cast-low (word-width) (logand r m)))
(defun inserted (ra r m)
  (cast-low (word-width)
            (logor (logand r m) (logand (cast-unsigned 64 ra) (lnot m)))))

(defun RLWINM (ra rs sh mb me)
  (set$ ra (rotated (rotl32 rs sh) (mask (+ mb 32) (+ me 32)))))
(defun RLWNM (ra rs rb mb me)
  (set$ ra (rotated (rotl32 rs (logand rb 31)) (mask (+ mb 32) (+ me 32)))))
(defun RLWIMI (ra _ rs sh mb me)
  (set$ ra (inserted ra (rotl32 rs sh) (mask (+ mb 32) (+ me 32)))))
(defun RLDICL (ra rs sh mb) (set$ ra (rotated (rotate-left rs sh) (mask mb 63))))
(defun RLDICR (ra rs sh me) (set$ ra (rotated (rotate-left rs sh) (mask 0 me))))
(defun RLDIC (ra rs sh mb) (set$ ra (rotated (rotate-left rs sh) (mask mb (- 63 sh)))))
(defun RLDCL (ra rs rb mb)
  (set$ ra (rotated (rotate-left rs (logand rb 63)) (mask mb 63))))
(defun RLDCR (ra rs rb me)
  (set$ ra (rotated (rotate-left rs (logand rb 63)) (mask 0 me))))
(defun RLDIMI (ra _ rs sh mb)
  (set$ ra (inserted ra (rotate-left rs sh) (mask mb (- 63 sh)))))

(defun RLWINM_rec (ra rs sh mb me) (RLWINM ra rs sh mb me) (record ra))
(defun RLWNM_rec (ra rs rb mb me) (RLWNM ra rs rb mb me) (record ra))
(defun RLWIMI_rec (ra ra' rs sh mb me) (RLWIMI ra ra' rs sh mb me) (record ra))
(defun RLDICL_rec (ra rs sh mb) (RLDICL ra rs sh mb) (record ra))
(defun RLDICR_rec (ra rs sh me) (RLDICR ra rs sh me) (record ra))
(defun RLDIC_rec (ra rs sh mb) (RLDIC ra rs sh mb) (record ra))
(defun RLDCL_rec (ra rs rb mb) (RLDCL ra rs rb mb) (record ra))
(defun RLDCR_rec (ra rs rb me) (RLDCR ra rs rb me) (record ra))
(defun RLDIMI_rec (ra ra' rs sh mb) (RLDIMI ra ra' rs sh mb) (record ra))

;; the shift amounts of words have 6 bits and of doublewords 7 bits, the
;; amounts that are not less than the size shift all bits out

(defun SLW (ra rs rb)
  (let ((n (logand rb 63)))
    (set$ ra (if (< n 32) (zext (lshift (low32 rs) n)) 0))))

(defun SRW (ra rs rb)
  (let ((n (logand rb 63)))
    (set$ ra (if (< n 32) (zext (rshift (low32 rs) n)) 0))))

(defun SLD (ra rs rb)
  (let ((n (logand rb 127)))
    (set$ ra (if (< n 64) (lshift rs n) 0))))

(defun SRD (ra rs rb)
  (let ((n (logand rb 127)))
    (set$ ra (if (< n 64) (rshift rs n) 0))))

;; the algebraic shifts set CA if the result is negative and ones were
;; shifted out, X is a doubleword and N is less than 64
(defun shift-right-algebraic (ra x n)
  (let ((lost (logand x (lnot (lshift (ones64) n))))
        (ca (logand (msb x) (non-zero lost))))
    (set-ca ca ca)
    (set$ ra (cast-low (word-width) (arshift x n)))))

(defun SRAWI (ra rs sh) (shift-right-algebraic ra (cast-signed 64 (low32 rs)) sh))
(defun SRAW (ra rs rb)
  (let ((n (logand rb 63)))
    (shift-right-algebraic ra (cast-signed 64 (low32 rs)) (if (< n 32) n 32))))
(defun SRADI (ra rs sh) (shift-right-algebraic ra rs sh))
(defun SRAD (ra rs rb)
  (let ((n (logand rb 127)))
    (if (< n 64)
        (shift-right-algebraic ra rs n)
      (prog
        (set-ca (msb rs) (msb rs))
        (set$ ra (arshift rs 63))))))

(defun EXTSWSLI (ra rs sh) (set$ ra (lshift (sext (low32 rs)) sh)))

(defun SLW_rec (ra rs rb) (SLW ra rs rb) (record ra))
(defun SRW_rec (ra rs rb) (SRW ra rs rb) (record ra))
(defun SLD_rec (ra rs rb) (SLD ra rs rb) (record ra))
(defun SRD_rec (ra rs rb) (SRD ra rs rb) (record ra))
(defun SRAWI_rec (ra rs sh) (SRAWI ra rs sh) (record ra))
(defun SRAW_rec (ra rs rb) (SRAW ra rs rb) (record ra))
(defun SRADI_rec (ra rs sh) (SRADI ra rs sh) (record ra))
(defun SRAD_rec (ra rs rb) (SRAD ra rs rb) (record ra))
(defun EXTSWSLI_rec (ra rs sh) (EXTSWSLI ra rs sh) (record ra))

;;; COMPARISONS AND THE CONDITION REGISTER

(defun compare-signed (crf x y) (set-field crf (s< x y) (s> x y) (= x y)))
(defun compare-unsigned (crf x y) (set-field crf (< x y) (> x y) (= x y)))

(defun CMPW (crf ra rb) (compare-signed crf (low32 ra) (low32 rb)))
(defun CMPWI (crf ra imm) (compare-signed crf (low32 ra) (low32 imm)))
(defun CMPLW (crf ra rb) (compare-unsigned crf (low32 ra) (low32 rb)))
(defun CMPLWI (crf ra imm) (compare-unsigned crf (low32 ra) (low32 imm)))
(defun CMPD (crf ra rb) (compare-signed crf ra rb))
(defun CMPDI (crf ra imm) (compare-signed crf ra imm))
(defun CMPLD (crf ra rb) (compare-unsigned crf ra rb))
(defun CMPLDI (crf ra imm) (compare-unsigned crf ra (uimm imm)))

(defun CRAND (bt ba bb) (set$ bt (logand ba bb)))
(defun CRNAND (bt ba bb) (set$ bt (lnot (logand ba bb))))
(defun CROR (bt ba bb) (set$ bt (logor ba bb)))
(defun CRXOR (bt ba bb) (set$ bt (logxor ba bb)))
(defun CRNOR (bt ba bb) (set$ bt (lnot (logor ba bb))))
(defun CREQV (bt ba bb) (set$ bt (lnot (logxor ba bb))))
(defun CRANDC (bt ba bb) (set$ bt (logand ba (lnot bb))))
(defun CRORC (bt ba bb) (set$ bt (logor ba (lnot bb))))
(defun MCRF (bf bfa) (set$ bf bfa))
(defun MCRXRX (bf) (set$ bf (concat OV OV32 CA CA32)))

(defun SETB (rt bfa)
  (set$ rt (if (msb bfa) (sext 1:1)
             (if (extract 2 2 bfa) 1 0))))

(defun ISEL (rt ra rb bc) (set$ rt (if bc ra rb)))

(defun cr ()
  (concat CR0 CR1 CR2 CR3 CR4 CR5 CR6 CR7))

(defun field-index (crf)
  (case (symbol crf)
    'CR0 0 'CR1 1 'CR2 2 'CR3 3 'CR4 4 'CR5 5 'CR6 6 'CR7 7))

(defun field-of (x i)
  (cast-low 4 (rshift x (* 4 (- 7 i)))))

(defun MFCR (rt) (set$ rt (zext (cr))))

;; the other fields of the result are zero, as in QEMU
(defun MFOCRF (rt crf)
  (set$ rt (lshift (zext crf) (* 4 (- 7 (field-index crf))))))

(defun MTOCRF (crf rs) (set$ crf (field-of rs (field-index crf))))

(defun move-to-field (fxm rs i crf)
  (when (non-zero (logand fxm (lshift 1 (- 7 i))))
    (set$ crf (field-of rs i))))

(defun MTCRF (fxm rs)
  (move-to-field fxm rs 0 'CR0)
  (move-to-field fxm rs 1 'CR1)
  (move-to-field fxm rs 2 'CR2)
  (move-to-field fxm rs 3 'CR3)
  (move-to-field fxm rs 4 'CR4)
  (move-to-field fxm rs 5 'CR5)
  (move-to-field fxm rs 6 'CR6)
  (move-to-field fxm rs 7 'CR7))

;;; SPECIAL PURPOSE REGISTERS
;;
;; The other special purpose registers are moved by the intrinsics.

(defun flag (x n) (lshift (zext x) n))

(defun xer ()
  (logor (flag SO 31) (flag OV 30) (flag CA 29) (flag OV32 19) (flag CA32 18)))

(defun set-xer (x)
  (set SO (extract 31 31 x))
  (set OV (extract 30 30 x))
  (set CA (extract 29 29 x))
  (set OV32 (extract 19 19 x))
  (set CA32 (extract 18 18 x)))

(defun MFSPR (rt spr)
  (case spr
    1 (set$ rt (xer))
    8 (set$ rt LR)
    9 (set$ rt CTR)
    815 (set$ rt TAR)
    (set$ rt (intrinsic 'move-from-special-register spr))))

(defun MTSPR (spr rs)
  (case spr
    1 (set-xer rs)
    8 (set LR rs)
    9 (set CTR rs)
    815 (set TAR rs)
    (intrinsic 'move-to-special-register spr rs)))

(defun MFLR (rt) (set$ rt LR))
(defun MFCTR (rt) (set$ rt CTR))
(defun MTLR (rs) (set LR rs))
(defun MTCTR (rs) (set CTR rs))

;;; LOADS AND STORES
;;
;; The update forms, e.g., LBZU, write the address to the base register,
;; which is their second operand, the byte-reversed forms access the
;; memory in the other byte order. The displacements are 16-bit.

(defun ea (ra d) (+ ra (sext (cast-low 16 d))))

(defun byte-reversed (x)
  (case (word-width x)
    16 (concat (extract 7 0 x) (extract 15 8 x))
    32 (concat (extract 7 0 x) (extract 15 8 x) (extract 23 16 x) (extract 31 24 x))
    64 (concat (extract 7 0 x) (extract 15 8 x) (extract 23 16 x) (extract 31 24 x)
               (extract 39 32 x) (extract 47 40 x) (extract 55 48 x) (extract 63 56 x))))

(defun load-size (size addr) (cast-low size (load-bits size addr)))

(defun load-zero (rt size addr) (set$ rt (zext (load-size size addr))))
(defun load-sign (rt size addr) (set$ rt (sext (load-size size addr))))
(defun load-reversed (rt size addr) (set$ rt (zext (byte-reversed (load-size size addr)))))

(defun load-update (rt ra size addr)
  (let ((ea addr))
    (load-zero rt size ea)
    (set$ ra ea)))

(defun load-sign-update (rt ra size addr)
  (let ((ea addr))
    (load-sign rt size ea)
    (set$ ra ea)))

(defun LBZ (rt d ra) (load-zero rt 8 (ea ra d)))
(defun LHZ (rt d ra) (load-zero rt 16 (ea ra d)))
(defun LWZ (rt d ra) (load-zero rt 32 (ea ra d)))
(defun LD (rt d ra) (load-zero rt 64 (ea ra d)))
(defun LHA (rt d ra) (load-sign rt 16 (ea ra d)))
(defun LWA (rt d ra) (load-sign rt 32 (ea ra d)))
(defun LBZX (rt ra rb) (load-zero rt 8 (+ ra rb)))
(defun LHZX (rt ra rb) (load-zero rt 16 (+ ra rb)))
(defun LWZX (rt ra rb) (load-zero rt 32 (+ ra rb)))
(defun LDX (rt ra rb) (load-zero rt 64 (+ ra rb)))
(defun LHAX (rt ra rb) (load-sign rt 16 (+ ra rb)))
(defun LWAX (rt ra rb) (load-sign rt 32 (+ ra rb)))
(defun LBZU (rt ra d _) (load-update rt ra 8 (ea ra d)))
(defun LHZU (rt ra d _) (load-update rt ra 16 (ea ra d)))
(defun LWZU (rt ra d _) (load-update rt ra 32 (ea ra d)))
(defun LDU (rt ra d _) (load-update rt ra 64 (ea ra d)))
(defun LHAU (rt ra d _) (load-sign-update rt ra 16 (ea ra d)))
(defun LBZUX (rt ra _ rb) (load-update rt ra 8 (+ ra rb)))
(defun LHZUX (rt ra _ rb) (load-update rt ra 16 (+ ra rb)))
(defun LWZUX (rt ra _ rb) (load-update rt ra 32 (+ ra rb)))
(defun LDUX (rt ra _ rb) (load-update rt ra 64 (+ ra rb)))
(defun LHAUX (rt ra _ rb) (load-sign-update rt ra 16 (+ ra rb)))
(defun LWAUX (rt ra _ rb) (load-sign-update rt ra 32 (+ ra rb)))
(defun LHBRX (rt ra rb) (load-reversed rt 16 (+ ra rb)))
(defun LWBRX (rt ra rb) (load-reversed rt 32 (+ ra rb)))
(defun LDBRX (rt ra rb) (load-reversed rt 64 (+ ra rb)))

;; the reservations of the atomic accesses are not modeled, the
;; conditional stores succeed
(defun LBARX (rt ra rb) (LBZX rt ra rb))
(defun LHARX (rt ra rb) (LHZX rt ra rb))
(defun LWARX (rt ra rb) (LWZX rt ra rb))
(defun LDARX (rt ra rb) (LDX rt ra rb))

(defun store-size (size rs addr) (store-word addr (cast-low size rs)))

(defun store-update (ra size rs addr)
  (let ((ea addr))
    (store-size size rs ea)
    (set$ ra ea)))

(defun STB (rs d ra) (store-size 8 rs (ea ra d)))
(defun STH (rs d ra) (store-size 16 rs (ea ra d)))
(defun STW (rs d ra) (store-size 32 rs (ea ra d)))
(defun STD (rs d ra) (store-size 64 rs (ea ra d)))
(defun STBX (rs ra rb) (store-size 8 rs (+ ra rb)))
(defun STHX (rs ra rb) (store-size 16 rs (+ ra rb)))
(defun STWX (rs ra rb) (store-size 32 rs (+ ra rb)))
(defun STDX (rs ra rb) (store-size 64 rs (+ ra rb)))
(defun STBU (ra rs d _) (store-update ra 8 rs (ea ra d)))
(defun STHU (ra rs d _) (store-update ra 16 rs (ea ra d)))
(defun STWU (ra rs d _) (store-update ra 32 rs (ea ra d)))
(defun STDU (ra rs d _) (store-update ra 64 rs (ea ra d)))
(defun STBUX (ra rs _ rb) (store-update ra 8 rs (+ ra rb)))
(defun STHUX (ra rs _ rb) (store-update ra 16 rs (+ ra rb)))
(defun STWUX (ra rs _ rb) (store-update ra 32 rs (+ ra rb)))
(defun STDUX (ra rs _ rb) (store-update ra 64 rs (+ ra rb)))
(defun STHBRX (rs ra rb) (store-word (+ ra rb) (byte-reversed (cast-low 16 rs))))
(defun STWBRX (rs ra rb) (store-word (+ ra rb) (byte-reversed (low32 rs))))
(defun STDBRX (rs ra rb) (store-word (+ ra rb) (byte-reversed (cast-low 64 rs))))

(defun store-conditional (size rs addr)
  (store-size size rs addr)
  (set-field 'CR0 false false true))

(defun STBCX (rs ra rb) (store-conditional 8 rs (+ ra rb)))
(defun STHCX (rs ra rb) (store-conditional 16 rs (+ ra rb)))
(defun STWCX (rs ra rb) (store-conditional 32 rs (+ ra rb)))
(defun STDCX (rs ra rb) (store-conditional 64 rs (+ ra rb)))

;;; BRANCHES
;;
;; The BO operand of the conditional branches: if BO_2, 4, is clear, CTR
;; is decremented and is tested to be zero if BO_3, 2, is set, nonzero
;; otherwise, and if BO_0, 16, is clear, the bit BI is tested to be BO_1,
;; 8. The other bits are hints. The link is the address of the next
;; instruction.

(defun link () (+ (get-program-counter) 4))
(defun relative (d) (+ (get-program-counter) (lshift d 2)))
(defun absolute (d) (lshift d 2))
(defun aligned (x) (logand x (lnot 3)))

(defun bit-set (bo n) (non-zero (logand bo n)))

(defun ctr-ok (bo)
  (if (bit-set bo 4) true
    (prog
      (set CTR (- CTR 1))
      (if (bit-set bo 2) (is-zero CTR) (non-zero CTR)))))

(defun cond-ok (bo bi)
  (if (bit-set bo 16) true
    (if (bit-set bo 8) bi (not bi))))

;; CTR is decremented before the condition is tested
(defun taken (bo bi)
  (let ((c (ctr-ok bo)))
    (logand c (cond-ok bo bi))))

(defun branch (bo bi dst)
  (when (taken bo bi) (exec-addr dst)))

;; the link is written whether the branch is taken or not
(defun branch-and-link (bo bi dst)
  (let ((d dst))
    (set LR (link))
    (branch bo bi d)))

(defun B (d) (exec-addr (relative d)))
(defun BA (d) (exec-addr (absolute d)))
(defun BL (d) (set LR (link)) (exec-addr (relative d)))
(defun BLA (d) (set LR (link)) (exec-addr (absolute d)))

(defun gBC (bo bi d) (branch bo bi (relative d)))
(defun gBCA (bo bi d) (branch bo bi (absolute d)))
(defun gBCL (bo bi d) (branch-and-link bo bi (relative d)))
(defun gBCLA (bo bi d) (branch-and-link bo bi (absolute d)))
(defun gBCLR (bo bi _) (branch bo bi (aligned LR)))
(defun gBCLRL (bo bi _) (branch-and-link bo bi (aligned LR)))
(defun gBCCTR (bo bi _) (branch bo bi (aligned CTR)))
(defun gBCCTRL (bo bi _) (branch-and-link bo bi (aligned CTR)))
(defun gBCTAR (bo bi _) (branch bo bi (aligned TAR)))
(defun gBCTARL (bo bi _) (branch-and-link bo bi (aligned TAR)))

(defun BLR () (exec-addr (aligned LR)))
(defun BLRL () (branch-and-link 20 false (aligned LR)))
(defun BCTR () (exec-addr (aligned CTR)))
(defun BCTRL () (branch-and-link 20 false (aligned CTR)))

;; the decrementing branches, BO is 16 for BDNZ and 18 for BDZ, and the
;; forms with the hints, e.g., BDNZm
(defun BDNZ (d) (gBC 16 false d))
(defun BDZ (d) (gBC 18 false d))
(defun BDNZA (d) (gBCA 16 false d))
(defun BDZA (d) (gBCA 18 false d))
(defun BDNZL (d) (gBCL 16 false d))
(defun BDZL (d) (gBCL 18 false d))
(defun BDNZLA (d) (gBCLA 16 false d))
(defun BDZLA (d) (gBCLA 18 false d))
(defun BDNZLR () (gBCLR 16 false 0))
(defun BDZLR () (gBCLR 18 false 0))
(defun BDNZLRL () (gBCLRL 16 false 0))
(defun BDZLRL () (gBCLRL 18 false 0))

(defun BDNZm (d) (BDNZ d))
(defun BDNZp (d) (BDNZ d))
(defun BDZm (d) (BDZ d))
(defun BDZp (d) (BDZ d))
(defun BDNZAm (d) (BDNZA d))
(defun BDNZAp (d) (BDNZA d))
(defun BDZAm (d) (BDZA d))
(defun BDZAp (d) (BDZA d))
(defun BDNZLm (d) (BDNZL d))
(defun BDNZLp (d) (BDNZL d))
(defun BDZLm (d) (BDZL d))
(defun BDZLp (d) (BDZL d))
(defun BDNZLAm (d) (BDNZLA d))
(defun BDNZLAp (d) (BDNZLA d))
(defun BDZLAm (d) (BDZLA d))
(defun BDZLAp (d) (BDZLA d))
(defun BDNZLRm () (BDNZLR))
(defun BDNZLRp () (BDNZLR))
(defun BDZLRm () (BDZLR))
(defun BDZLRp () (BDZLR))
(defun BDNZLRLm () (BDNZLRL))
(defun BDNZLRLp () (BDNZLRL))
(defun BDZLRLm () (BDZLRL))
(defun BDZLRLp () (BDZLRL))

;;; TRAPS, SYSTEM CALLS AND THE OTHER INSTRUCTIONS
;;
;; TO selects the comparisons of the trap: 16 signed less, 8 signed
;; greater, 4 equal, 2 unsigned less and 1 unsigned greater.

(defun trap-if (to x y)
  (when (logor (logand (bit-set to 16) (s< x y))
               (logand (bit-set to 8) (s> x y))
               (logand (bit-set to 4) (= x y))
               (logand (bit-set to 2) (< x y))
               (logand (bit-set to 1) (> x y)))
    (intrinsic 'trap :aborts)))

(defun TW (to ra rb) (trap-if to (low32 ra) (low32 rb)))
(defun TWI (to ra imm) (trap-if to (low32 ra) (low32 imm)))
(defun TD (to ra rb) (trap-if to ra rb))
(defun TDI (to ra imm) (trap-if to ra imm))
(defun TRAP () (intrinsic 'trap :aborts))
(defun SC (lev) (intrinsic 'syscall lev))

(defun SYNC (_) (empty))
(defun ISYNC () (empty))
(defun EnforceIEIO () (empty))
(defun DCBT (_ _ _) (empty))
(defun DCBTST (_ _ _) (empty))
(defun DCBF (_ _ _) (empty))
(defun DCBST (_ _) (empty))
(defun ICBI (_ _) (empty))
