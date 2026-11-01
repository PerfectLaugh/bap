(declare (context (target powerpc-family)))
(require powerpc)
(require powerpc-vector)

(in-package powerpc)

;;; VECTOR-SCALAR EXTENSION
;;
;; The 64 registers of VSX are the operands whose names are VSL0 to VSL31
;; and V0 to V31, which the target's aliases make of the first doublewords
;; F0 to F31, the second doublewords F0L to F31L, and the AltiVec
;; registers. The scalars are the first doublewords, whose names are F0
;; to F31 and VF0 to VF31, a symbol with the suffix L is the other
;; doubleword. As in powerpc.lisp, the elements are numbered from the most
;; significant one, the floating-point operations round to nearest and
;; the status bits of FPSCR are not modeled.
;;
;; The scalar operations set the second doubleword to zero, as the ISA 3.0
;; does, the older ones left it undefined.

(defun set-scalar (xt x)
  (set$ xt x)
  (set-symbol-value (symbol-concat (symbol xt) 'L) (u64 0)))

;;; LOGICAL OPERATIONS, ETC.

(defun XXLAND (xt xa xb) (set$ xt (logand xa xb)))
(defun XXLANDC (xt xa xb) (set$ xt (logand xa (lnot xb))))
(defun XXLEQV (xt xa xb) (set$ xt (lnot (logxor xa xb))))
(defun XXLNAND (xt xa xb) (set$ xt (lnot (logand xa xb))))
(defun XXLNOR (xt xa xb) (set$ xt (lnot (logor xa xb))))
(defun XXLOR (xt xa xb) (set$ xt (logor xa xb)))
(defun XXLORC (xt xa xb) (set$ xt (logor xa (lnot xb))))
(defun XXLXOR (xt xa xb) (set$ xt (logxor xa xb)))
(defun XXSEL (xt xa xb xc) (set$ xt (logor (logand xb xc) (logand xa (lnot xc)))))

;; the imm is indexed by the bits of A, B and C, from its most significant
;; bit, the result is the sum of the minterms that it has
(defun minterm (a b c k)
  (logand (if (non-zero (logand k 4)) a (lnot a))
          (if (non-zero (logand k 2)) b (lnot b))
          (if (non-zero (logand k 1)) c (lnot c))))
(defun xxeval-from (a b c imm k)
  (if (= k 8) (cast-unsigned 128 0:1)
    (logor (if (non-zero (logand imm (lshift 1 (- 7 k)))) (minterm a b c k) (cast-unsigned 128 0:1))
           (xxeval-from a b c imm (+ k 1)))))
(defun XXEVAL (xt xa xb xc imm) (set$ xt (xxeval-from xa xb xc imm 0)))

(defun blend (a b c) (pick (msb c) b a))
(defun XXBLENDVB (xt xa xb xc) (set$ xt (lanes8-3 blend xa xb xc)))
(defun XXBLENDVH (xt xa xb xc) (set$ xt (lanes16-3 blend xa xb xc)))
(defun XXBLENDVW (xt xa xb xc) (set$ xt (lanes32-3 blend xa xb xc)))
(defun XXBLENDVD (xt xa xb xc) (set$ xt (lanes64-3 blend xa xb xc)))

(defun XXMRGHW (xt xa xb)
  (set$ xt (concat (extract 127 96 xa) (extract 127 96 xb) (extract 95 64 xa) (extract 95 64 xb))))
(defun XXMRGLW (xt xa xb)
  (set$ xt (concat (extract 63 32 xa) (extract 63 32 xb) (extract 31 0 xa) (extract 31 0 xb))))

(defun XXPERMDI (xt xa xb dm)
  (set$ xt (concat (if (non-zero (logand dm 2)) (extract 63 0 xa) (extract 127 64 xa))
                   (if (non-zero (logand dm 1)) (extract 63 0 xb) (extract 127 64 xb)))))

(defun XXSLDWI (xt xa xb sh)
  (set$ xt (cast-low 128 (rshift (concat xa xb) (* 32 (- 4 (logand sh 3)))))))

(defun XXSPLTW (xt xb uim) (set$ xt (splat (element xb 32 (logand uim 3)))))
(defun XXSPLTIB (xt imm) (set$ xt (splat (cast-low 8 imm))))
(defun XXSPLTIW (xt imm) (set$ xt (splat (cast-low 32 imm))))
(defun XXSPLTIDP (xt imm)
  (let ((d (single-to-double (cast-low 32 imm))))
    (set$ xt (concat d d))))
(defun XXSPLTI32DX (xt _ ix imm)
  (let ((w (cast-low 32 imm)))
    (set$ xt (if (non-zero ix)
                 (concat (extract 127 96 xt) w (extract 63 32 xt) w)
               (concat w (extract 95 64 xt) w (extract 31 0 xt))))))

(defun XXPERM (xt xa _ xb)
  (let ((ab (concat xa xt)))
    (set$ xt (lanes8-e permuted-byte ab xb))))
(defun XXPERMR (xt xa _ xb)
  (let ((ab (concat xa xt)))
    (set$ xt (lanes8-e permuted-byte-r ab xb))))

;; the byte of the 32 of AB if the high bits of its index are UIM, or zero
(defun permx-byte (uim ab c)
  (pick (= (extract 7 5 c) uim) (permuted-byte ab c) 0:8))
(defun XXPERMX (xt xa xb xc imm)
  (let ((ab (concat xa xb))
        (uim (cast-low 3 imm)))
    (set$ xt (lanes8-e-with permx-byte uim ab xc))))
(defmacro lanes8-e-with (op e f x)
  (concat (op e f (extract 127 120 x))
          (op e f (extract 119 112 x))
          (op e f (extract 111 104 x))
          (op e f (extract 103 96 x))
          (op e f (extract 95 88 x))
          (op e f (extract 87 80 x))
          (op e f (extract 79 72 x))
          (op e f (extract 71 64 x))
          (op e f (extract 63 56 x))
          (op e f (extract 55 48 x))
          (op e f (extract 47 40 x))
          (op e f (extract 39 32 x))
          (op e f (extract 31 24 x))
          (op e f (extract 23 16 x))
          (op e f (extract 15 8 x))
          (op e f (extract 7 0 x))))

(defun XXBRH (xt xb) (set$ xt (lanes16-1 byte-reversed xb)))
(defun XXBRW (xt xb) (set$ xt (lanes32-1 byte-reversed xb)))
(defun XXBRD (xt xb) (set$ xt (lanes64-1 byte-reversed xb)))
(defun reversed-128 (x)
  (concat (byte-reversed (extract 63 0 x)) (byte-reversed (extract 127 64 x))))
(defun XXBRQ (xt xb) (set$ xt (reversed-128 xb)))

;; the offsets are in bytes from the most significant one, as for VEXTRACT
(defun XXEXTRACTUW (xt xb uim)
  (set-scalar xt (u64 (element-at xb 4 uim))))
(defun XXINSERTW (xt _ xb uim) (insert-at xt (extract 95 64 xb) 4 uim))

;; the integer operations on the elements, that only the registers
;; make different from those of AltiVec
(defun XVADDUHM (xt xa xb) (set$ xt (lanes16 add xa xb)))
(defun XVADDUWM (xt xa xb) (set$ xt (lanes32 add xa xb)))
(defun XVSUBUHM (xt xa xb) (set$ xt (lanes16 sub xa xb)))
(defun XVSUBUWM (xt xa xb) (set$ xt (lanes32 sub xa xb)))
(defun XVMULUHM (xt xa xb) (set$ xt (lanes16 mul-low xa xb)))
(defun XVMULUWM (xt xa xb) (set$ xt (lanes32 mul-low xa xb)))
(defun XVMULHUH (xt xa xb) (set$ xt (lanes16 mulh-u xa xb)))
(defun XVMULHUW (xt xa xb) (set$ xt (lanes32 mulh-u xa xb)))
(defun XVMULHSH (xt xa xb) (set$ xt (lanes16 mulh-s xa xb)))
(defun XVMULHSW (xt xa xb) (set$ xt (lanes32 mulh-s xa xb)))
(defun XVRLW (xt xa xb) (set$ xt (lanes32 rol xa xb)))

;; the LSB test: LT if all the bytes have it, EQ if none has
(defun XVTLSBB (bf xb)
  (let ((m (lanes8-1 byte-lsb xb)))
    (set$ bf (concat (= m 0xffff:16) 0:1 (is-zero m) 0:1))))

;; the constants of quad precision, from the table of the ISA 3.1
(defun quad-constant (uim)
  (case uim
    1 0x3fff0000000000000000000000000000:128
    2 0x40000000000000000000000000000000:128
    3 0x40008000000000000000000000000000:128
    4 0x40010000000000000000000000000000:128
    5 0x40014000000000000000000000000000:128
    6 0x40018000000000000000000000000000:128
    7 0x4001c000000000000000000000000000:128
    8 0x7fff0000000000000000000000000000:128
    9 0x7fff8000000000000000000000000000:128
    16 0x80000000000000000000000000000000:128
    17 0xbfff0000000000000000000000000000:128
    18 0xc0000000000000000000000000000000:128
    19 0xc0008000000000000000000000000000:128
    20 0xc0010000000000000000000000000000:128
    21 0xc0014000000000000000000000000000:128
    22 0xc0018000000000000000000000000000:128
    23 0xc001c000000000000000000000000000:128
    24 0xffff0000000000000000000000000000:128
    25 0xffff8000000000000000000000000000:128
    (intrinsic 'lxvkq-reserved uim :result 128)))
(defun LXVKQ (xt uim) (set$ xt (quad-constant uim)))

;; the masks for permutations, whose tables are of the intrinsics
(defun XXGENPCVBM (xt vb imm) (set$ xt (intrinsic 'xxgenpcvbm vb imm :result 128)))
(defun XXGENPCVHM (xt vb imm) (set$ xt (intrinsic 'xxgenpcvhm vb imm :result 128)))
(defun XXGENPCVWM (xt vb imm) (set$ xt (intrinsic 'xxgenpcvwm vb imm :result 128)))
(defun XXGENPCVDM (xt vb imm) (set$ xt (intrinsic 'xxgenpcvdm vb imm :result 128)))

;;; MOVES BETWEEN THE GENERAL AND THE VSX REGISTERS

(defun MFVSRD (ra xt) (set$ ra (zext xt)))
(defun MFVSRWZ (ra xt) (set$ ra (zext (low32 xt))))
(defun MFVSRLD (ra xt) (set$ ra (zext (cast-low 64 xt))))
(defun MTVSRD (xt ra) (set-scalar xt (u64 ra)))
(defun MTVSRWZ (xt ra) (set-scalar xt (u64 (low32 ra))))
(defun MTVSRWA (xt ra) (set-scalar xt (s64 (low32 ra))))
(defun MTVSRDD (xt ra rb) (set$ xt (concat (u64 ra) (u64 rb))))
(defun MTVSRWS (xt ra) (set$ xt (splat (low32 ra))))

;;; LOADS AND STORES
;;
;; LXV and the like access 16 bytes in the byte order of the mode, so that
;; the byte at the address is the first of the register in the big-endian
;; mode, and the last one in the little-endian one. The forms with the
;; elements in their names access the elements in the order of the
;; register, each in the byte order of the mode, so that a little-endian
;; LXVB16X has the first byte of the memory in the first byte of the
;; register.

(defun load-v (xt a) (set$ xt (load-bits 128 a)))
(defun store-v (xs a) (store-word a xs))

(defun LXV (xt d ra) (load-v xt (+ ra d)))
(defun LXVX (xt ra rb) (load-v xt (+ ra rb)))
(defun STXV (xs d ra) (store-v xs (+ ra d)))
(defun STXVX (xs ra rb) (store-v xs (+ ra rb)))

(defun at-offset (a n) (+ a (cast-unsigned (word-width) (cast-unsigned 16 n))))

(defun load-elems-2 (xt a)
  (set$ xt (concat (load-bits 64 a) (load-bits 64 (at-offset a 8)))))
(defun load-elems-4 (xt a)
  (set$ xt (concat (load-bits 32 a) (load-bits 32 (at-offset a 4))
                   (load-bits 32 (at-offset a 8)) (load-bits 32 (at-offset a 12)))))
(defun load-elems-8 (xt a)
  (set$ xt (concat (load-bits 16 a) (load-bits 16 (at-offset a 2))
                   (load-bits 16 (at-offset a 4)) (load-bits 16 (at-offset a 6))
                   (load-bits 16 (at-offset a 8)) (load-bits 16 (at-offset a 10))
                   (load-bits 16 (at-offset a 12)) (load-bits 16 (at-offset a 14)))))
(defun load-elems-16 (xt a)
  (set$ xt (concat (load-bits 8 a) (load-bits 8 (at-offset a 1))
                   (load-bits 8 (at-offset a 2)) (load-bits 8 (at-offset a 3))
                   (load-bits 8 (at-offset a 4)) (load-bits 8 (at-offset a 5))
                   (load-bits 8 (at-offset a 6)) (load-bits 8 (at-offset a 7))
                   (load-bits 8 (at-offset a 8)) (load-bits 8 (at-offset a 9))
                   (load-bits 8 (at-offset a 10)) (load-bits 8 (at-offset a 11))
                   (load-bits 8 (at-offset a 12)) (load-bits 8 (at-offset a 13))
                   (load-bits 8 (at-offset a 14)) (load-bits 8 (at-offset a 15)))))

(defun LXVD2X (xt ra rb) (let ((a (+ ra rb))) (load-elems-2 xt a)))
(defun LXVW4X (xt ra rb) (let ((a (+ ra rb))) (load-elems-4 xt a)))
(defun LXVH8X (xt ra rb) (let ((a (+ ra rb))) (load-elems-8 xt a)))
(defun LXVB16X (xt ra rb) (let ((a (+ ra rb))) (load-elems-16 xt a)))

(defun LXVDSX (xt ra rb)
  (let ((d (load-bits 64 (+ ra rb)))) (set$ xt (concat d d))))
(defun LXVWSX (xt ra rb) (set$ xt (splat (load-bits 32 (+ ra rb)))))

(defun store-elems (x a size i n)
  (when (< i n)
    (store-word (at-offset a (* (/ size 8) i))
                (cast-low size (rshift x (* size (- n 1 i)))))
    (store-elems x a size (+ i 1) n)))

(defun STXVD2X (xs ra rb) (let ((a (+ ra rb))) (store-elems xs a 64 0 2)))
(defun STXVW4X (xs ra rb) (let ((a (+ ra rb))) (store-elems xs a 32 0 4)))
(defun STXVH8X (xs ra rb) (let ((a (+ ra rb))) (store-elems xs a 16 0 8)))
(defun STXVB16X (xs ra rb) (let ((a (+ ra rb))) (store-elems xs a 8 0 16)))

;; the elements in the rightmost bits of the register, the others are zero
(defun LXVRBX (xt ra rb) (set$ xt (u128 (load-bits 8 (+ ra rb)))))
(defun LXVRHX (xt ra rb) (set$ xt (u128 (load-bits 16 (+ ra rb)))))
(defun LXVRWX (xt ra rb) (set$ xt (u128 (load-bits 32 (+ ra rb)))))
(defun LXVRDX (xt ra rb) (set$ xt (u128 (load-bits 64 (+ ra rb)))))
(defun STXVRBX (xs ra rb) (store-word (+ ra rb) (cast-low 8 xs)))
(defun STXVRHX (xs ra rb) (store-word (+ ra rb) (cast-low 16 xs)))
(defun STXVRWX (xs ra rb) (store-word (+ ra rb) (cast-low 32 xs)))
(defun STXVRDX (xs ra rb) (store-word (+ ra rb) (cast-low 64 xs)))

;; the scalars, in the first doubleword
(defun LXSD (xt d ra) (set-scalar xt (load-bits 64 (+ ra d))))
(defun LXSDX (xt ra rb) (set-scalar xt (load-bits 64 (+ ra rb))))
(defun LXSSP (xt d ra) (set-scalar xt (single-to-double (load-bits 32 (+ ra d)))))
(defun LXSSPX (xt ra rb) (set-scalar xt (single-to-double (load-bits 32 (+ ra rb)))))
(defun LXSIWAX (xt ra rb) (set-scalar xt (s64 (load-bits 32 (+ ra rb)))))
(defun LXSIWZX (xt ra rb) (set-scalar xt (u64 (load-bits 32 (+ ra rb)))))
(defun LXSIHZX (xt ra rb) (set-scalar xt (u64 (load-bits 16 (+ ra rb)))))
(defun LXSIBZX (xt ra rb) (set-scalar xt (u64 (load-bits 8 (+ ra rb)))))
(defun STXSD (xs d ra) (store-word (+ ra d) xs))
(defun STXSDX (xs ra rb) (store-word (+ ra rb) xs))
(defun STXSSP (xs d ra) (store-word (+ ra d) (double-to-single xs)))
(defun STXSSPX (xs ra rb) (store-word (+ ra rb) (double-to-single xs)))
(defun STXSIWX (xs ra rb) (store-word (+ ra rb) (low32 xs)))
(defun STXSIHX (xs ra rb) (store-word (+ ra rb) (cast-low 16 xs)))
(defun STXSIBX (xs ra rb) (store-word (+ ra rb) (cast-low 8 xs)))

;; the loads and stores with a length, in the eight high bits of RB, at
;; most 16 bytes, the bytes of the other forms of the register are zero.
;; The bytes that are out of the length aren't accessed, so each one is
;; conditional. I is the number of the byte in the memory, FROM-RIGHT says
;; that it counts from the right of the register, not from the left.

(defun access-length (rb)
  (let ((n (cast-high 8 (u64 rb))))
    (pick (> n 16:8) 16:8 n)))

(defun byte-shift (from-right i)
  (if (non-zero from-right) (* 8 i) (* 8 (- 15 i))))

(defun load-length-from (xt a n from-right i)
  (when (< i 16)
    (when (< (cast-unsigned 8 (cast-unsigned 16 i)) n)
      (set$ xt (logor xt (lshift (u128 (load-bits 8 (at-offset a i)))
                                 (u128 (cast-unsigned 16 (byte-shift from-right i)))))))
    (load-length-from xt a n from-right (+ i 1))))

(defun store-length-from (xs a n from-right i)
  (when (< i 16)
    (when (< (cast-unsigned 8 (cast-unsigned 16 i)) n)
      (store-word (at-offset a i)
                  (cast-low 8 (rshift xs (u128 (cast-unsigned 16 (byte-shift from-right i)))))))
    (store-length-from xs a n from-right (+ i 1))))

;; the byte I of the memory is the byte 15 - I of a little-endian register
(defun le-first ()
  (declare (context (endianness eb)))
  0)
(defun le-first ()
  (declare (context (endianness le)))
  1)

(defun load-length (xt ra rb from-right)
  (let ((a ra) (n (access-length rb)))
    (set$ xt (u128 0))
    (load-length-from xt a n from-right 0)))
(defun store-length (xs ra rb from-right)
  (let ((a ra) (n (access-length rb)))
    (store-length-from xs a n from-right 0)))

(defun LXVL (xt ra rb) (load-length xt ra rb (le-first)))
(defun LXVLL (xt ra rb) (load-length xt ra rb 0))
(defun STXVL (xs ra rb) (store-length xs ra rb (le-first)))
(defun STXVLL (xs ra rb) (store-length xs ra rb 0))

;; the pairs: the 32 bytes in the order of the mode, the first register
;; of the pair has the bytes at the address in the big-endian mode

(defun LXVP (xt d ra) (set$ xt (load-bits 256 (+ ra d))))
(defun LXVPX (xt ra rb) (set$ xt (load-bits 256 (+ ra rb))))
(defun STXVP (xs d ra) (store-word (+ ra d) xs))
(defun STXVPX (xs ra rb) (store-word (+ ra rb) xs))

;; the prefixed forms, see ea34 and pcrel
(defun PLXV (xt d ra) (load-v xt (ea34 ra d)))
(defun PLXVpc (xt d _) (load-v xt (pcrel d)))
(defun PSTXV (xs d ra) (store-v xs (ea34 ra d)))
(defun PSTXVpc (xs d _) (store-v xs (pcrel d)))
(defun PLXVP (xt d ra) (set$ xt (load-bits 256 (ea34 ra d))))
(defun PLXVPpc (xt d _) (set$ xt (load-bits 256 (pcrel d))))
(defun PSTXVP (xs d ra) (store-word (ea34 ra d) xs))
(defun PSTXVPpc (xs d _) (store-word (pcrel d) xs))
(defun PLXSD (xt d ra) (set-scalar xt (load-bits 64 (ea34 ra d))))
(defun PLXSDpc (xt d _) (set-scalar xt (load-bits 64 (pcrel d))))
(defun PLXSSP (xt d ra) (set-scalar xt (single-to-double (load-bits 32 (ea34 ra d)))))
(defun PLXSSPpc (xt d _) (set-scalar xt (single-to-double (load-bits 32 (pcrel d)))))
(defun PSTXSD (xs d ra) (store-word (ea34 ra d) xs))
(defun PSTXSDpc (xs d _) (store-word (pcrel d) xs))
(defun PSTXSSP (xs d ra) (store-word (ea34 ra d) (double-to-single xs)))
(defun PSTXSSPpc (xs d _) (store-word (pcrel d) (double-to-single xs)))

;;; FLOATING-POINT MOVES AND THE FIELDS

(defun with-sign-of (a b) (concat (msb a) (cast-low (- (word-width b) 1) b)))
(defun XSABSDP (xt xb) (set-scalar xt (fp-abs xb)))
(defun XSNABSDP (xt xb) (set-scalar xt (fp-nabs xb)))
(defun XSNEGDP (xt xb) (set-scalar xt (fp-neg xb)))
(defun XSCPSGNDP (xt xa xb) (set-scalar xt (with-sign-of xa xb)))
(defun XVABSDP (xt xb) (set$ xt (lanes64-1 fp-abs xb)))
(defun XVABSSP (xt xb) (set$ xt (lanes32-1 fp-abs xb)))
(defun XVNABSDP (xt xb) (set$ xt (lanes64-1 fp-nabs xb)))
(defun XVNABSSP (xt xb) (set$ xt (lanes32-1 fp-nabs xb)))
(defun XVNEGDP (xt xb) (set$ xt (lanes64-1 fp-neg xb)))
(defun XVNEGSP (xt xb) (set$ xt (lanes32-1 fp-neg xb)))
(defun XVCPSGNDP (xt xa xb) (set$ xt (lanes64 with-sign-of xa xb)))
(defun XVCPSGNSP (xt xa xb) (set$ xt (lanes32 with-sign-of xa xb)))
(defun XSABSQP (vt vb) (set$ vt (fp-abs vb)))
(defun XSNABSQP (vt vb) (set$ vt (fp-nabs vb)))
(defun XSNEGQP (vt vb) (set$ vt (fp-neg vb)))
(defun XSCPSGNQP (vt va vb) (set$ vt (with-sign-of va vb)))

;; the significand with its implicit bit, if the number is normal
(defun significand (x)
  (let ((e (fp-exponent x))
        (top (low-ones x (exponent-size x))))
    (logor (fp-fraction x)
           (pick (logand (non-zero e) (/= e top))
                 (lshift (one-like x) (fraction-size x))
                 (cast-unsigned (word-width x) 0:1)))))

(defun with-exponent (x e)
  (let ((f (fraction-size x)))
    (logor (logand x (lnot (fp-infinity x)))
           (logand (lshift e f) (fp-infinity x)))))

(defun XSXEXPDP (rt xb) (set$ rt (zext (fp-exponent xb))))
(defun XSXSIGDP (rt xb) (set$ rt (zext (significand xb))))
(defun XSIEXPDP (xt ra rb)
  (set$ xt (concat (with-exponent (u64 ra) (u64 rb)) (u64 0))))
(defun XVXEXPDP (xt xb) (set$ xt (lanes64-1 fp-exponent xb)))
(defun XVXEXPSP (xt xb) (set$ xt (lanes32-1 fp-exponent xb)))
(defun XVXSIGDP (xt xb) (set$ xt (lanes64-1 significand xb)))
(defun XVXSIGSP (xt xb) (set$ xt (lanes32-1 significand xb)))
(defun XVIEXPDP (xt xa xb) (set$ xt (lanes64 with-exponent xa xb)))
(defun XVIEXPSP (xt xa xb) (set$ xt (lanes32 with-exponent xa xb)))
(defun XSXEXPQP (vt vb) (set$ vt (concat (u64 (cast-low 64 (fp-exponent vb))) (u64 0))))
(defun XSXSIGQP (vt vb) (set$ vt (significand vb)))
;; the disassembler has the third operand in the class of F0 to VF31,
;; with a number that is of the AltiVec registers: F7 stands for VF7
(defun XSIEXPQP (vt va xb)
  (set$ vt (with-exponent va (u128 (unquote (symbol-concat 'V (symbol xb)))))))

;;; THE TESTS AND COMPARISONS, BY THE BITS OF THE NUMBERS

;; DCMX has the bits, from the most significant: NaN, +inf, -inf, +0, -0,
;; +denormal and -denormal
(defun class-match (dcmx x)
  (let ((s (msb x)))
    (logor (logand (non-zero (logand dcmx 0x40)) (fp-nan x))
           (logand (non-zero (logand dcmx 0x20)) (fp-inf x) (lnot s))
           (logand (non-zero (logand dcmx 0x10)) (fp-inf x) s)
           (logand (non-zero (logand dcmx 0x08)) (fp-zero x) (lnot s))
           (logand (non-zero (logand dcmx 0x04)) (fp-zero x) s)
           (logand (non-zero (logand dcmx 0x02)) (fp-denormal x) (lnot s))
           (logand (non-zero (logand dcmx 0x01)) (fp-denormal x) s))))

(defun test-class (bf dcmx x)
  (set$ bf (concat (msb x) 0:1 (class-match dcmx x) 0:1)))
(defun XSTSTDCDP (bf dcmx xb) (test-class bf dcmx xb))
(defun XSTSTDCQP (bf dcmx vb) (test-class bf dcmx vb))

;; the double as a single: its denormals are those of the single, whatever
;; is below the exponent of the smallest normal one, and the last bit of
;; the field says that the value is not exactly a single
(defun single-class (dcmx x)
  (let ((expn (fp-exponent x))
        (small (logor (fp-denormal x)
                      (logand (non-zero expn) (< expn (u64 0x381))))))
    (logor (class-match (logand dcmx 0x7c) x)
           (logand (non-zero (logand dcmx 2)) small (lnot (msb x)))
           (logand (non-zero (logand dcmx 1)) small (msb x)))))
(defun XSTSTDCSP (bf dcmx xb)
  (set$ bf (concat (msb xb) 0:1 (single-class dcmx xb)
                   (/= xb (single-to-double (double-to-single xb))))))
(defun class-mask (dcmx x) (cast-signed (word-width x) (class-match dcmx x)))
(defun XVTSTDCDP (xt dcmx xb) (set$ xt (lanes64-e class-mask dcmx xb)))
(defun XVTSTDCSP (xt dcmx xb) (set$ xt (lanes32-e class-mask dcmx xb)))

;; the four bits LT, GT, EQ and UN of the comparison of the numbers
(defun compare-bits (x y)
  (let ((un (logor (fp-nan x) (fp-nan y)))
        (lt (logand (not un) (fp-lt-bits x y)))
        (gt (logand (not un) (fp-lt-bits y x)))
        (eq (logand (not un) (fp-eq-bits x y))))
    (concat lt gt eq un)))

(defun set-compare (bf c)
  (set FL (select 3 c))
  (set FG (select 2 c))
  (set FE (select 1 c))
  (set FU (select 0 c))
  (set$ bf c))

(defun XSCMPUDP (bf xa xb) (let ((c (compare-bits xa xb))) (set-compare bf c)))
(defun XSCMPODP (bf xa xb) (let ((c (compare-bits xa xb))) (set-compare bf c)))
(defun XSCMPUQP (bf va vb) (let ((c (compare-bits va vb))) (set-compare bf c)))
(defun XSCMPOQP (bf va vb) (let ((c (compare-bits va vb))) (set-compare bf c)))

(defun compare-exponents (x y)
  (let ((un (logor (fp-nan x) (fp-nan y)))
        (ex (fp-exponent x))
        (ey (fp-exponent y)))
    (concat (logand (not un) (< ex ey)) (logand (not un) (> ex ey)) (logand (not un) (= ex ey)) un)))
(defun XSCMPEXPDP (bf xa xb) (let ((c (compare-exponents xa xb))) (set-compare bf c)))
(defun XSCMPEXPQP (bf va vb) (let ((c (compare-exponents va vb))) (set-compare bf c)))

(defun cmp-eq (x y) (select 1 (compare-bits x y)))
(defun cmp-gt (x y) (select 2 (compare-bits x y)))
(defun cmp-ge (x y) (logor (cmp-gt x y) (cmp-eq x y)))
(defun eq-of (x y) (cast-signed (word-width x) (cmp-eq x y)))
(defun gt-of (x y) (cast-signed (word-width x) (cmp-gt x y)))
(defun ge-of (x y) (cast-signed (word-width x) (cmp-ge x y)))

(defun XSCMPEQDP (xt xa xb) (set$ xt (concat (eq-of xa xb) (u64 0))))
(defun XSCMPGTDP (xt xa xb) (set$ xt (concat (gt-of xa xb) (u64 0))))
(defun XSCMPGEDP (xt xa xb) (set$ xt (concat (ge-of xa xb) (u64 0))))
(defun XSCMPEQQP (vt va vb) (set$ vt (eq-of va vb)))
(defun XSCMPGTQP (vt va vb) (set$ vt (gt-of va vb)))
(defun XSCMPGEQP (vt va vb) (set$ vt (ge-of va vb)))
(defun XVCMPEQDP (xt xa xb) (set$ xt (lanes64 eq-of xa xb)))
(defun XVCMPGTDP (xt xa xb) (set$ xt (lanes64 gt-of xa xb)))
(defun XVCMPGEDP (xt xa xb) (set$ xt (lanes64 ge-of xa xb)))
(defun XVCMPEQSP (xt xa xb) (set$ xt (lanes32 eq-of xa xb)))
(defun XVCMPGTSP (xt xa xb) (set$ xt (lanes32 gt-of xa xb)))
(defun XVCMPGESP (xt xa xb) (set$ xt (lanes32 ge-of xa xb)))
(defun XVCMPEQDP_rec (xt xa xb) (XVCMPEQDP xt xa xb) (record-vector xt))
(defun XVCMPGTDP_rec (xt xa xb) (XVCMPGTDP xt xa xb) (record-vector xt))
(defun XVCMPGEDP_rec (xt xa xb) (XVCMPGEDP xt xa xb) (record-vector xt))
(defun XVCMPEQSP_rec (xt xa xb) (XVCMPEQSP xt xa xb) (record-vector xt))
(defun XVCMPGTSP_rec (xt xa xb) (XVCMPGTSP xt xa xb) (record-vector xt))
(defun XVCMPGESP_rec (xt xa xb) (XVCMPGESP xt xa xb) (record-vector xt))

;; the maximum and minimum: of the ISA 2.06, a NaN loses to a number; of
;; the type C, a NaN operand or an equal one gives B; of the type J, a NaN
;; is the result, and the order of the zeros counts

;; of two NaNs the first one is the result, quiet if it is signaling, as in
;; QEMU, and a signaling NaN B is quiet, against a number
(defun fp-max (a b)
  (pick (fp-snan a) (fp-quiet a)
        (pick (fp-nan a) (pick (fp-nan b) a b)
              (pick (fp-snan b) (fp-quiet b)
                    (pick (fp-nan b) a
                          (pick (fp-lt-bits a b) b
                                (pick (fp-lt-bits b a) a (logand a b))))))))
(defun fp-min (a b)
  (pick (fp-snan a) (fp-quiet a)
        (pick (fp-nan a) (pick (fp-nan b) a b)
              (pick (fp-snan b) (fp-quiet b)
                    (pick (fp-nan b) a
                          (pick (fp-lt-bits a b) a
                                (pick (fp-lt-bits b a) b (logor a b))))))))
(defun fp-maxc (a b)
  (pick (logor (fp-nan a) (fp-nan b)) b (pick (fp-lt-bits b a) a b)))
(defun fp-minc (a b)
  (pick (logor (fp-nan a) (fp-nan b)) b (pick (fp-lt-bits a b) a b)))
(defun fp-maxj (a b)
  (pick (fp-nan a) a
        (pick (fp-nan b) b
              (pick (fp-lt-bits a b) b
                    (pick (fp-lt-bits b a) a (logand a b))))))
(defun fp-minj (a b)
  (pick (fp-nan a) a
        (pick (fp-nan b) b
              (pick (fp-lt-bits a b) a
                    (pick (fp-lt-bits b a) b (logor a b))))))

(defun XSMAXDP (xt xa xb) (set-scalar xt (fp-max xa xb)))
(defun XSMINDP (xt xa xb) (set-scalar xt (fp-min xa xb)))
(defun XSMAXCDP (xt xa xb) (set-scalar xt (fp-maxc xa xb)))
(defun XSMINCDP (xt xa xb) (set-scalar xt (fp-minc xa xb)))
(defun XSMAXJDP (xt xa xb) (set$ xt (concat (fp-maxj xa xb) (u64 0))))
(defun XSMINJDP (xt xa xb) (set$ xt (concat (fp-minj xa xb) (u64 0))))
(defun XVMAXDP (xt xa xb) (set$ xt (lanes64 fp-max xa xb)))
(defun XVMINDP (xt xa xb) (set$ xt (lanes64 fp-min xa xb)))
(defun XVMAXSP (xt xa xb) (set$ xt (lanes32 fp-max xa xb)))
(defun XVMINSP (xt xa xb) (set$ xt (lanes32 fp-min xa xb)))
(defun XSMAXCQP (vt va vb) (set$ vt (fp-maxc va vb)))
(defun XSMINCQP (vt va vb) (set$ vt (fp-minc va vb)))

;; the tests for software division and square root, see FTDIV
(defun XSTDIVDP (bf xa xb) (FTDIV bf xa xb))
(defun XSTSQRTDP (bf xb) (FTSQRT bf xb))
(defun set-tests (bf fg fe) (set$ bf (concat 1:1 fg fe 0:1)))
(defun XVTDIVDP (bf xa xb)
  (let ((a0 (extract 127 64 xa)) (a1 (extract 63 0 xa))
        (b0 (extract 127 64 xb)) (b1 (extract 63 0 xb)))
    (set-tests bf (logor (tdiv-fg a0 b0) (tdiv-fg a1 b1))
               (logor (tdiv-fe a0 b0) (tdiv-fe a1 b1)))))
(defun XVTSQRTDP (bf xb)
  (let ((b0 (extract 127 64 xb)) (b1 (extract 63 0 xb)))
    (set-tests bf (logor (tsqrt-fg b0) (tsqrt-fg b1))
               (logor (tsqrt-fe b0) (tsqrt-fe b1)))))
(defun XVTDIVSP (bf xa xb)
  (set-tests bf (non-zero (lanes32 tdiv-fg xa xb)) (non-zero (lanes32 tdiv-fe xa xb))))
(defun XVTSQRTSP (bf xb)
  (set-tests bf (non-zero (lanes32-1 tsqrt-fg xb)) (non-zero (lanes32-1 tsqrt-fe xb))))

;;; ARITHMETIC

;; the NaN result of the operations on singles, see nan-result
(defun nan-result32 (r a b c)
  (pick (fp-nan a) (quiet32 a)
        (pick (fp-nan b) (quiet32 b)
              (pick (fp-nan c) (quiet32 c)
                    (pick (fp-nan r) 0x7fc00000:32 r)))))

(defun sp-add (a b) (nan-result32 (+. :rne a b) a b a))
(defun sp-sub (a b) (nan-result32 (-. :rne a b) a b a))
(defun sp-mul (a b) (nan-result32 (*. :rne a b) a b a))
(defun sp-div (a b) (nan-result32 (/. :rne a b) a b a))
(defun sp-sqrt (b) (nan-result32 (fsqrt :rne b) b b b))
(defun sp-fma (a c b)
  (intrinsic (symbol-concat 'fmad 'rne 'ieee754_binary '32 :sep '_) a c b :result 32))
(defun sp-mad (a c b) (nan-result32 (sp-fma a c b) a b c))
(defun sp-msub (a c b) (nan-result32 (sp-fma a c (fp-neg b)) a b c))
(defun sp-nmad (a c b) (fp-negate32 (sp-mad a c b)))
(defun sp-nmsub (a c b) (fp-negate32 (sp-msub a c b)))
(defun dp-nmad (a c b) (fp-negate (fmad64 a c b)))
(defun dp-nmsub (a c b) (fp-negate (fmsub64 a c b)))
(defun dp-re (b) (fp-div 0x3ff0000000000000:64 b))
(defun dp-rsqrte (b) (fp-div 0x3ff0000000000000:64 (fp-sqrt b)))
(defun sp-re (b) (sp-div 0x3f800000:32 b))
(defun sp-rsqrte (b) (sp-div 0x3f800000:32 (sp-sqrt b)))

(defun XSADDDP (xt xa xb) (set-scalar xt (fp-add xa xb)))
(defun XSSUBDP (xt xa xb) (set-scalar xt (fp-sub xa xb)))
(defun XSMULDP (xt xa xb) (set-scalar xt (fp-mul xa xb)))
(defun XSDIVDP (xt xa xb) (set-scalar xt (fp-div xa xb)))
(defun XSSQRTDP (xt xb) (set-scalar xt (fp-sqrt xb)))
(defun XSREDP (xt xb) (set-scalar xt (dp-re xb)))
(defun XSRSQRTEDP (xt xb) (set-scalar xt (dp-rsqrte xb)))
(defun XSADDSP (xt xa xb) (set-scalar xt (fp-single (fp-add xa xb))))
(defun XSSUBSP (xt xa xb) (set-scalar xt (fp-single (fp-sub xa xb))))
(defun XSMULSP (xt xa xb) (set-scalar xt (fp-single (fp-mul xa xb))))
(defun XSDIVSP (xt xa xb) (set-scalar xt (fp-single (fp-div xa xb))))
(defun XSSQRTSP (xt xb) (set-scalar xt (fp-single (fp-sqrt xb))))
(defun XSRESP (xt xb) (set-scalar xt (fp-single (dp-re xb))))
(defun XSRSQRTESP (xt xb) (set-scalar xt (fp-single (dp-rsqrte xb))))
(defun XSRSP (xt xb) (set-scalar xt (fp-single xb)))

;; the forms A take T as the addend, the forms M as the multiplier
(defun XSMADDADP (xt _ xa xb) (set-scalar xt (fmad64 xa xb xt)))
(defun XSMADDMDP (xt _ xa xb) (set-scalar xt (fmad64 xa xt xb)))
(defun XSMSUBADP (xt _ xa xb) (set-scalar xt (fmsub64 xa xb xt)))
(defun XSMSUBMDP (xt _ xa xb) (set-scalar xt (fmsub64 xa xt xb)))
(defun XSNMADDADP (xt _ xa xb) (set-scalar xt (dp-nmad xa xb xt)))
(defun XSNMADDMDP (xt _ xa xb) (set-scalar xt (dp-nmad xa xt xb)))
(defun XSNMSUBADP (xt _ xa xb) (set-scalar xt (dp-nmsub xa xb xt)))
(defun XSNMSUBMDP (xt _ xa xb) (set-scalar xt (dp-nmsub xa xt xb)))
(defun XSMADDASP (xt _ xa xb) (set-scalar xt (fp-single (fmad64 xa xb xt))))
(defun XSMADDMSP (xt _ xa xb) (set-scalar xt (fp-single (fmad64 xa xt xb))))
(defun XSMSUBASP (xt _ xa xb) (set-scalar xt (fp-single (fmsub64 xa xb xt))))
(defun XSMSUBMSP (xt _ xa xb) (set-scalar xt (fp-single (fmsub64 xa xt xb))))
(defun XSNMADDASP (xt _ xa xb) (set-scalar xt (fp-negate (fp-single (fmad64 xa xb xt)))))
(defun XSNMADDMSP (xt _ xa xb) (set-scalar xt (fp-negate (fp-single (fmad64 xa xt xb)))))
(defun XSNMSUBASP (xt _ xa xb) (set-scalar xt (fp-negate (fp-single (fmsub64 xa xb xt)))))
(defun XSNMSUBMSP (xt _ xa xb) (set-scalar xt (fp-negate (fp-single (fmsub64 xa xt xb)))))

(defun XVADDDP (xt xa xb) (set$ xt (lanes64 fp-add xa xb)))
(defun XVSUBDP (xt xa xb) (set$ xt (lanes64 fp-sub xa xb)))
(defun XVMULDP (xt xa xb) (set$ xt (lanes64 fp-mul xa xb)))
(defun XVDIVDP (xt xa xb) (set$ xt (lanes64 fp-div xa xb)))
(defun XVSQRTDP (xt xb) (set$ xt (lanes64-1 fp-sqrt xb)))
(defun XVREDP (xt xb) (set$ xt (lanes64-1 dp-re xb)))
(defun XVRSQRTEDP (xt xb) (set$ xt (lanes64-1 dp-rsqrte xb)))
(defun XVADDSP (xt xa xb) (set$ xt (lanes32 sp-add xa xb)))
(defun XVSUBSP (xt xa xb) (set$ xt (lanes32 sp-sub xa xb)))
(defun XVMULSP (xt xa xb) (set$ xt (lanes32 sp-mul xa xb)))
(defun XVDIVSP (xt xa xb) (set$ xt (lanes32 sp-div xa xb)))
(defun XVSQRTSP (xt xb) (set$ xt (lanes32-1 sp-sqrt xb)))
(defun XVRESP (xt xb) (set$ xt (lanes32-1 sp-re xb)))
(defun XVRSQRTESP (xt xb) (set$ xt (lanes32-1 sp-rsqrte xb)))

(defun XVMADDADP (xt _ xa xb) (set$ xt (lanes64-3 fmad64 xa xb xt)))
(defun XVMADDMDP (xt _ xa xb) (set$ xt (lanes64-3 fmad64 xa xt xb)))
(defun XVMSUBADP (xt _ xa xb) (set$ xt (lanes64-3 fmsub64 xa xb xt)))
(defun XVMSUBMDP (xt _ xa xb) (set$ xt (lanes64-3 fmsub64 xa xt xb)))
(defun XVNMADDADP (xt _ xa xb) (set$ xt (lanes64-3 dp-nmad xa xb xt)))
(defun XVNMADDMDP (xt _ xa xb) (set$ xt (lanes64-3 dp-nmad xa xt xb)))
(defun XVNMSUBADP (xt _ xa xb) (set$ xt (lanes64-3 dp-nmsub xa xb xt)))
(defun XVNMSUBMDP (xt _ xa xb) (set$ xt (lanes64-3 dp-nmsub xa xt xb)))
(defun XVMADDASP (xt _ xa xb) (set$ xt (lanes32-3 sp-mad xa xb xt)))
(defun XVMADDMSP (xt _ xa xb) (set$ xt (lanes32-3 sp-mad xa xt xb)))
(defun XVMSUBASP (xt _ xa xb) (set$ xt (lanes32-3 sp-msub xa xb xt)))
(defun XVMSUBMSP (xt _ xa xb) (set$ xt (lanes32-3 sp-msub xa xt xb)))
(defun XVNMADDASP (xt _ xa xb) (set$ xt (lanes32-3 sp-nmad xa xb xt)))
(defun XVNMADDMSP (xt _ xa xb) (set$ xt (lanes32-3 sp-nmad xa xt xb)))
(defun XVNMSUBASP (xt _ xa xb) (set$ xt (lanes32-3 sp-nmsub xa xb xt)))
(defun XVNMSUBMSP (xt _ xa xb) (set$ xt (lanes32-3 sp-nmsub xa xt xb)))

;; the rounding to integral values, I is to the nearest with the ties
;; away from zero, C is by the mode, which is to the nearest with the
;; ties to even here

(defun round-a (x) (round-with-nan (fround :rna x) x))
(defun round-c (x) (round-with-nan (fround :rne x) x))
(defun round-m (x) (round-with-nan (fround :rtn x) x))
(defun round-p (x) (round-with-nan (fround :rtp x) x))
(defun round-z (x) (round-with-nan (fround :rtz x) x))
(defun round-with-nan32 (r x) (pick (fp-nan x) (quiet32 x) r))
(defun rounds-a (x) (round-with-nan32 (fround :rna x) x))
(defun rounds-c (x) (round-with-nan32 (fround :rne x) x))
(defun rounds-m (x) (round-with-nan32 (fround :rtn x) x))
(defun rounds-p (x) (round-with-nan32 (fround :rtp x) x))
(defun rounds-z (x) (round-with-nan32 (fround :rtz x) x))

(defun XSRDPI (xt xb) (set-scalar xt (round-a xb)))
(defun XSRDPIC (xt xb) (set-scalar xt (round-c xb)))
(defun XSRDPIM (xt xb) (set-scalar xt (round-m xb)))
(defun XSRDPIP (xt xb) (set-scalar xt (round-p xb)))
(defun XSRDPIZ (xt xb) (set-scalar xt (round-z xb)))
(defun XVRDPI (xt xb) (set$ xt (lanes64-1 round-a xb)))
(defun XVRDPIC (xt xb) (set$ xt (lanes64-1 round-c xb)))
(defun XVRDPIM (xt xb) (set$ xt (lanes64-1 round-m xb)))
(defun XVRDPIP (xt xb) (set$ xt (lanes64-1 round-p xb)))
(defun XVRDPIZ (xt xb) (set$ xt (lanes64-1 round-z xb)))
(defun XVRSPI (xt xb) (set$ xt (lanes32-1 rounds-a xb)))
(defun XVRSPIC (xt xb) (set$ xt (lanes32-1 rounds-c xb)))
(defun XVRSPIM (xt xb) (set$ xt (lanes32-1 rounds-m xb)))
(defun XVRSPIP (xt xb) (set$ xt (lanes32-1 rounds-p xb)))
(defun XVRSPIZ (xt xb) (set$ xt (lanes32-1 rounds-z xb)))

;;; CONVERSIONS
;;
;; The singles of the vectors are in the words 0 and 2 for the conversions
;; to and from doublewords, as the ISA 3.0 says, whose other words are
;; undefined and are copies here, as in QEMU.

(defun word0 (x) (extract 63 32 x))
(defun word1 (x) (extract 31 0 x))

;; a signaling NaN is quiet in the result
(defun sp-to-dp (w)
  (let ((d (single-to-double w)))
    (pick (fp-snan w) (fp-quiet d) d)))
(defun dp-to-sp (x)
  (pick (fp-nan x) (double-to-single (fp-quiet x)) (fconvert :rne 32 x)))
(defun dp-to-sp-copies (x) (let ((s (dp-to-sp x))) (concat s s)))

(defun XSCVDPSP (xt xb) (set-scalar xt (dp-to-sp-copies xb)))
(defun XSCVSPDP (xt xb) (set-scalar xt (sp-to-dp (word0 xb))))
;; ConvertDPtoSP_NS: it doesn't signal, a NaN stays what it is and the rest is truncated, in the two words of the first doubleword
(defun dp-to-sp-ns (x) (pick (fp-nan x) (double-to-single x) (fconvert :rtz 32 x)))
(defun XSCVDPSPN (xt xb) (let ((s (dp-to-sp-ns xb))) (set-scalar xt (concat s s))))
(defun XSCVSPDPN (xt xb) (set-scalar xt (single-to-double (extract 127 96 xb))))
(defun XVCVDPSP (xt xb) (set$ xt (lanes64-1 dp-to-sp-copies xb)))
(defun sp-to-dp-first (x) (sp-to-dp (word0 x)))
(defun XVCVSPDP (xt xb) (set$ xt (lanes64-1 sp-to-dp-first xb)))

(defun hp-to-dp (h) (fconvert :rne 64 h))
(defun dp-to-hp (x) (fconvert :rne 16 x))
(defun sp-to-hp (x) (fconvert :rne 16 x))
(defun hp-to-sp (h) (fconvert :rne 32 h))
(defun word-of-hp (x) (hp-to-sp (cast-low 16 x)))
(defun word-to-hp (x) (cast-unsigned 32 (sp-to-hp x)))
(defun XSCVHPDP (xt xb) (set-scalar xt (hp-to-dp (cast-low 16 xb))))
(defun XSCVDPHP (xt xb) (set-scalar xt (u64 (dp-to-hp xb))))
(defun XVCVHPSP (xt xb) (set$ xt (lanes32-1 word-of-hp xb)))
(defun XVCVSPHP (xt xb) (set$ xt (lanes32-1 word-to-hp xb)))

(defun bf16-to-sp (x) (intrinsic 'bfloat16-to-single x :result 32))
(defun sp-to-bf16 (x) (intrinsic 'single-to-bfloat16 x :result 32))
(defun XVCVBF16SPN (xt xb) (set$ xt (lanes32-1 bf16-to-sp xb)))
(defun XVCVSPBF16 (xt xb) (set$ xt (lanes32-1 sp-to-bf16 xb)))

;; to integers, toward zero, see fp-to-signed and fp-to-unsigned
(defun dp-to-sw (x) (fp-to-signed x 32 (lowest-word)))
(defun dp-to-uw (x) (fp-to-unsigned x 32 (u64 0)))
(defun word-pair (x) (let ((w (cast-low 32 x))) (concat w w)))
(defun dp-to-sw2 (x) (word-pair (dp-to-sw x)))
(defun dp-to-uw2 (x) (word-pair (dp-to-uw x)))
(defun sp-to-sd (x) (to-sd (single-to-double (word0 x))))
(defun sp-to-ud (x) (to-ud (single-to-double (word0 x))))
(defun sp-to-sw (x) (cast-low 32 (fp-to-signed (single-to-double x) 32 (lowest-word))))
(defun sp-to-uw (x) (cast-low 32 (fp-to-unsigned (single-to-double x) 32 (u64 0))))

(defun XSCVDPSXDS (xt xb) (set-scalar xt (to-sd xb)))
(defun XSCVDPUXDS (xt xb) (set-scalar xt (to-ud xb)))
;; the word is in the word 1, the word 0 is undefined and is a copy here,
;; as in QEMU
(defun XSCVDPSXWS (xt xb) (set-scalar xt (dp-to-sw2 xb)))
(defun XSCVDPUXWS (xt xb) (set-scalar xt (dp-to-uw2 xb)))
(defun XVCVDPSXDS (xt xb) (set$ xt (lanes64-1 to-sd xb)))
(defun XVCVDPUXDS (xt xb) (set$ xt (lanes64-1 to-ud xb)))
(defun XVCVDPSXWS (xt xb) (set$ xt (lanes64-1 dp-to-sw2 xb)))
(defun XVCVDPUXWS (xt xb) (set$ xt (lanes64-1 dp-to-uw2 xb)))
(defun XVCVSPSXDS (xt xb) (set$ xt (lanes64-1 sp-to-sd xb)))
(defun XVCVSPUXDS (xt xb) (set$ xt (lanes64-1 sp-to-ud xb)))
(defun XVCVSPSXWS (xt xb) (set$ xt (lanes32-1 sp-to-sw xb)))
(defun XVCVSPUXWS (xt xb) (set$ xt (lanes32-1 sp-to-uw xb)))

;; from integers
(defun sd-to-dp (x) (cast-sfloat :rne 64 x))
(defun ud-to-dp (x) (cast-float :rne 64 x))
(defun sd-to-sp2 (x) (let ((s (cast-sfloat :rne 32 x))) (concat s s)))
(defun ud-to-sp2 (x) (let ((s (cast-float :rne 32 x))) (concat s s)))
(defun sw-to-dp (x) (cast-sfloat :rne 64 (word0 x)))
(defun uw-to-dp (x) (cast-float :rne 64 (word0 x)))
(defun sw-to-sp (x) (cast-sfloat :rne 32 x))
(defun uw-to-sp (x) (cast-float :rne 32 x))

(defun XSCVSXDDP (xt xb) (set-scalar xt (sd-to-dp xb)))
(defun XSCVUXDDP (xt xb) (set-scalar xt (ud-to-dp xb)))
(defun XSCVSXDSP (xt xb) (set-scalar xt (fconvert :rne 64 (cast-sfloat :rne 32 xb))))
(defun XSCVUXDSP (xt xb) (set-scalar xt (fconvert :rne 64 (cast-float :rne 32 xb))))
(defun XVCVSXDDP (xt xb) (set$ xt (lanes64-1 sd-to-dp xb)))
(defun XVCVUXDDP (xt xb) (set$ xt (lanes64-1 ud-to-dp xb)))
(defun XVCVSXDSP (xt xb) (set$ xt (lanes64-1 sd-to-sp2 xb)))
(defun XVCVUXDSP (xt xb) (set$ xt (lanes64-1 ud-to-sp2 xb)))
(defun XVCVSXWDP (xt xb) (set$ xt (lanes64-1 sw-to-dp xb)))
(defun XVCVUXWDP (xt xb) (set$ xt (lanes64-1 uw-to-dp xb)))
(defun XVCVSXWSP (xt xb) (set$ xt (lanes32-1 sw-to-sp xb)))
(defun XVCVUXWSP (xt xb) (set$ xt (lanes32-1 uw-to-sp xb)))

;;; QUAD PRECISION
;;
;; The values are in the whole of a vector register. The arithmetic is of
;; binary128 and its intrinsics, what has no theory, i.e., the rounding to
;; odd of the forms with the O suffix, and the fused operations and the
;; conversions, is an intrinsic with the name of the instruction, whose
;; results are what the instruction writes.

(defun qp-nan-first (r a b)
  (pick (fp-nan a) (fp-quiet a)
        (pick (fp-nan b) (fp-quiet b)
              (pick (fp-nan r) 0x7fff8000000000000000000000000000:128 r))))

(defun XSADDQP (vt va vb) (set$ vt (qp-nan-first (+. :rne va vb) va vb)))
(defun XSSUBQP (vt va vb) (set$ vt (qp-nan-first (-. :rne va vb) va vb)))
(defun XSMULQP (vt va vb) (set$ vt (qp-nan-first (*. :rne va vb) va vb)))
(defun XSDIVQP (vt va vb) (set$ vt (qp-nan-first (/. :rne va vb) va vb)))
(defun XSSQRTQP (vt vb) (set$ vt (qp-nan-first (fsqrt :rne vb) vb vb)))
(defun XSADDQPO (vt va vb) (set$ vt (intrinsic 'xsaddqpo va vb :result 128)))
(defun XSSUBQPO (vt va vb) (set$ vt (intrinsic 'xssubqpo va vb :result 128)))
(defun XSMULQPO (vt va vb) (set$ vt (intrinsic 'xsmulqpo va vb :result 128)))
(defun XSDIVQPO (vt va vb) (set$ vt (intrinsic 'xsdivqpo va vb :result 128)))
(defun XSSQRTQPO (vt vb) (set$ vt (intrinsic 'xssqrtqpo vb :result 128)))

(defun XSMADDQP (vt _ va vb) (set$ vt (intrinsic 'xsmaddqp va vb vt :result 128)))
(defun XSMSUBQP (vt _ va vb) (set$ vt (intrinsic 'xsmsubqp va vb vt :result 128)))
(defun XSNMADDQP (vt _ va vb) (set$ vt (intrinsic 'xsnmaddqp va vb vt :result 128)))
(defun XSNMSUBQP (vt _ va vb) (set$ vt (intrinsic 'xsnmsubqp va vb vt :result 128)))
(defun XSMADDQPO (vt _ va vb) (set$ vt (intrinsic 'xsmaddqpo va vb vt :result 128)))
(defun XSMSUBQPO (vt _ va vb) (set$ vt (intrinsic 'xsmsubqpo va vb vt :result 128)))
(defun XSNMADDQPO (vt _ va vb) (set$ vt (intrinsic 'xsnmaddqpo va vb vt :result 128)))
(defun XSNMSUBQPO (vt _ va vb) (set$ vt (intrinsic 'xsnmsubqpo va vb vt :result 128)))

(defun XSCVDPQP (vt xb) (set$ vt (intrinsic 'xscvdpqp xb :result 128)))
(defun XSCVSDQP (vt xb) (set$ vt (intrinsic 'xscvsdqp xb :result 128)))
(defun XSCVUDQP (vt xb) (set$ vt (intrinsic 'xscvudqp xb :result 128)))
(defun XSCVSQQP (vt vb) (set$ vt (intrinsic 'xscvsqqp vb :result 128)))
(defun XSCVUQQP (vt vb) (set$ vt (intrinsic 'xscvuqqp vb :result 128)))
(defun XSCVQPDP (xt vb) (set-scalar xt (intrinsic 'xscvqpdp vb :result 64)))
(defun XSCVQPDPO (xt vb) (set-scalar xt (intrinsic 'xscvqpdpo vb :result 64)))
(defun XSCVQPSDZ (vt vb) (set$ vt (intrinsic 'xscvqpsdz vb :result 128)))
(defun XSCVQPUDZ (vt vb) (set$ vt (intrinsic 'xscvqpudz vb :result 128)))
(defun XSCVQPSWZ (vt vb) (set$ vt (intrinsic 'xscvqpswz vb :result 128)))
(defun XSCVQPUWZ (vt vb) (set$ vt (intrinsic 'xscvqpuwz vb :result 128)))
(defun XSCVQPSQZ (vt vb) (set$ vt (intrinsic 'xscvqpsqz vb :result 128)))
(defun XSCVQPUQZ (vt vb) (set$ vt (intrinsic 'xscvqpuqz vb :result 128)))
(defun XSRQPI (vt r vb rmc) (set$ vt (intrinsic 'xsrqpi r vb rmc :result 128)))
(defun XSRQPIX (vt r vb rmc) (set$ vt (intrinsic 'xsrqpix r vb rmc :result 128)))
(defun XSRQPXP (vt r vb rmc) (set$ vt (intrinsic 'xsrqpxp r vb rmc :result 128)))

;;; THE MATRIX-MULTIPLY ASSIST OF THE ISA 3.1
;;
;; The accumulators are the operands whose names are ACC0 to ACC7 and
;; UACC0 to UACC7, each made of four VSX registers by the target's aliases.
;; The moves in and out of the accumulator have thus no effect on the
;; values, that real hardware has only for the renaming. The products are
;; the intrinsics with the names of the instructions, which take the
;; accumulator in the forms that accumulate.

(defun XXMTACC (_ _) (empty))
(defun XXMFACC (_ _) (empty))
(defun XXSETACCZ (at) (set$ at (cast-unsigned 512 0:1)))

(defmacro ger (name at xa xb)
  (set$ at (intrinsic name xa xb :result 512)))
(defmacro ger-acc (name at xa xb)
  (set$ at (intrinsic name at xa xb :result 512)))
(defmacro pm-ger (name at xa xb xm ym)
  (set$ at (intrinsic name xa xb xm ym :result 512)))
(defmacro pm-ger-acc (name at xa xb xm ym)
  (set$ at (intrinsic name at xa xb xm ym :result 512)))
(defmacro pm-ger3 (name at xa xb xm ym pm)
  (set$ at (intrinsic name xa xb xm ym pm :result 512)))
(defmacro pm-ger3-acc (name at xa xb xm ym pm)
  (set$ at (intrinsic name at xa xb xm ym pm :result 512)))

(defun XVF32GER (at xa xb) (ger 'xvf32ger at xa xb))
(defun XVF64GER (at xa xb) (ger 'xvf64ger at xa xb))
(defun XVF16GER2 (at xa xb) (ger 'xvf16ger2 at xa xb))
(defun XVBF16GER2 (at xa xb) (ger 'xvbf16ger2 at xa xb))
(defun XVI4GER8 (at xa xb) (ger 'xvi4ger8 at xa xb))
(defun XVI8GER4 (at xa xb) (ger 'xvi8ger4 at xa xb))
(defun XVI16GER2 (at xa xb) (ger 'xvi16ger2 at xa xb))
(defun XVI16GER2S (at xa xb) (ger 'xvi16ger2s at xa xb))
(defun XVF32GERPP (at _ xa xb) (ger-acc 'xvf32gerpp at xa xb))
(defun XVF32GERPN (at _ xa xb) (ger-acc 'xvf32gerpn at xa xb))
(defun XVF32GERNP (at _ xa xb) (ger-acc 'xvf32gernp at xa xb))
(defun XVF32GERNN (at _ xa xb) (ger-acc 'xvf32gernn at xa xb))
(defun XVF64GERPP (at _ xa xb) (ger-acc 'xvf64gerpp at xa xb))
(defun XVF64GERPN (at _ xa xb) (ger-acc 'xvf64gerpn at xa xb))
(defun XVF64GERNP (at _ xa xb) (ger-acc 'xvf64gernp at xa xb))
(defun XVF64GERNN (at _ xa xb) (ger-acc 'xvf64gernn at xa xb))
(defun XVF16GER2PP (at _ xa xb) (ger-acc 'xvf16ger2pp at xa xb))
(defun XVF16GER2PN (at _ xa xb) (ger-acc 'xvf16ger2pn at xa xb))
(defun XVF16GER2NP (at _ xa xb) (ger-acc 'xvf16ger2np at xa xb))
(defun XVF16GER2NN (at _ xa xb) (ger-acc 'xvf16ger2nn at xa xb))
(defun XVBF16GER2PP (at _ xa xb) (ger-acc 'xvbf16ger2pp at xa xb))
(defun XVBF16GER2PN (at _ xa xb) (ger-acc 'xvbf16ger2pn at xa xb))
(defun XVBF16GER2NP (at _ xa xb) (ger-acc 'xvbf16ger2np at xa xb))
(defun XVBF16GER2NN (at _ xa xb) (ger-acc 'xvbf16ger2nn at xa xb))
(defun XVI4GER8PP (at _ xa xb) (ger-acc 'xvi4ger8pp at xa xb))
(defun XVI8GER4PP (at _ xa xb) (ger-acc 'xvi8ger4pp at xa xb))
(defun XVI8GER4SPP (at _ xa xb) (ger-acc 'xvi8ger4spp at xa xb))
(defun XVI16GER2PP (at _ xa xb) (ger-acc 'xvi16ger2pp at xa xb))
(defun XVI16GER2SPP (at _ xa xb) (ger-acc 'xvi16ger2spp at xa xb))

;; the prefixed forms have the masks as well
(defun PMXVF32GER (at xa xb xm ym) (pm-ger 'pmxvf32ger at xa xb xm ym))
(defun PMXVF32GERPP (at _ xa xb xm ym) (pm-ger-acc 'pmxvf32gerpp at xa xb xm ym))
(defun PMXVF32GERPN (at _ xa xb xm ym) (pm-ger-acc 'pmxvf32gerpn at xa xb xm ym))
(defun PMXVF32GERNP (at _ xa xb xm ym) (pm-ger-acc 'pmxvf32gernp at xa xb xm ym))
(defun PMXVF32GERNN (at _ xa xb xm ym) (pm-ger-acc 'pmxvf32gernn at xa xb xm ym))
(defun PMXVF64GER (at xa xb xm ym) (pm-ger 'pmxvf64ger at xa xb xm ym))
(defun PMXVF64GERPP (at _ xa xb xm ym) (pm-ger-acc 'pmxvf64gerpp at xa xb xm ym))
(defun PMXVF64GERPN (at _ xa xb xm ym) (pm-ger-acc 'pmxvf64gerpn at xa xb xm ym))
(defun PMXVF64GERNP (at _ xa xb xm ym) (pm-ger-acc 'pmxvf64gernp at xa xb xm ym))
(defun PMXVF64GERNN (at _ xa xb xm ym) (pm-ger-acc 'pmxvf64gernn at xa xb xm ym))
(defun PMXVF16GER2 (at xa xb xm ym pm) (pm-ger3 'pmxvf16ger2 at xa xb xm ym pm))
(defun PMXVF16GER2PP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvf16ger2pp at xa xb xm ym pm))
(defun PMXVF16GER2PN (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvf16ger2pn at xa xb xm ym pm))
(defun PMXVF16GER2NP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvf16ger2np at xa xb xm ym pm))
(defun PMXVF16GER2NN (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvf16ger2nn at xa xb xm ym pm))
(defun PMXVBF16GER2 (at xa xb xm ym pm) (pm-ger3 'pmxvbf16ger2 at xa xb xm ym pm))
(defun PMXVBF16GER2PP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvbf16ger2pp at xa xb xm ym pm))
(defun PMXVBF16GER2PN (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvbf16ger2pn at xa xb xm ym pm))
(defun PMXVBF16GER2NP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvbf16ger2np at xa xb xm ym pm))
(defun PMXVBF16GER2NN (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvbf16ger2nn at xa xb xm ym pm))
(defun PMXVI4GER8 (at xa xb xm ym pm) (pm-ger3 'pmxvi4ger8 at xa xb xm ym pm))
(defun PMXVI4GER8PP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvi4ger8pp at xa xb xm ym pm))
(defun PMXVI8GER4 (at xa xb xm ym pm) (pm-ger3 'pmxvi8ger4 at xa xb xm ym pm))
(defun PMXVI8GER4PP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvi8ger4pp at xa xb xm ym pm))
(defun PMXVI8GER4SPP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvi8ger4spp at xa xb xm ym pm))
(defun PMXVI16GER2 (at xa xb xm ym pm) (pm-ger3 'pmxvi16ger2 at xa xb xm ym pm))
(defun PMXVI16GER2PP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvi16ger2pp at xa xb xm ym pm))
(defun PMXVI16GER2S (at xa xb xm ym pm) (pm-ger3 'pmxvi16ger2s at xa xb xm ym pm))
(defun PMXVI16GER2SPP (at _ xa xb xm ym pm) (pm-ger3-acc 'pmxvi16ger2spp at xa xb xm ym pm))
