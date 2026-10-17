(declare (context (target arm-family)
                  (bits 32)))

(require thumb)
(require arm-a32)

(in-package thumb)

;;; THUMB-2 INSTRUCTIONS
;;
;; The 32-bit T32 instructions that are not recoded as A32 ones. The
;; last operand of a flag-setting instruction is CPSR when it sets the
;; flags. The shifted register operands encode the shift as in
;; i-shift, the type in the lowest three bits and the amount above. As
;; in arm-float, the values are computed without dynamic if.

(defun sets-flags (s) (= (symbol s) 'CPSR))

(defun bit-of (x n)
  "(bit-of X N) is the bit N of X as a boolean, N may be dynamic and
   is 0 if it is out of the range"
  (not (is-zero (logand (rshift x n) 1))))

(defun shift-amount (simm)
  "the amount of the encoded immediate shift, lsr and asr #0 are #32"
  (let ((typ (logand simm 7))
        (amt (rshift simm 3)))
    (if (and (= amt 0) (or (= typ 1) (= typ 3))) 32 amt)))

(defun shifted (x simm)
  "(shifted X SIMM) is X shifted by the static encoded shift SIMM"
  (let ((typ (logand simm 7))
        (amt (shift-amount simm)))
    (case typ
      1 (arshift x (if (= amt 32) 31 amt))
      2 (lshift x amt)
      3 (if (= amt 32) (cast-unsigned 32 0) (rshift x amt))
      4 (rotate-right x amt)
      5 (logor (rshift x 1) (lshift (cast-unsigned 32 CF) 31)))))

(defun shifter-carry (x simm)
  "(shifter-carry X SIMM) is the carry out of the static shift SIMM"
  (let ((typ (logand simm 7))
        (amt (shift-amount simm)))
    (case typ
      1 (bit-of x (- amt 1))
      2 (if (= amt 0) CF (bit-of x (- 32 amt)))
      3 (bit-of x (- amt 1))
      4 (if (= amt 0) CF (bit-of x (- amt 1)))
      5 (bit-of x 0))))

;; register-specified shifts, the amount is the lowest byte of n

(defun reg-shifted (typ x n)
  (let ((n (logand n 0xff)))
    (case typ
      'lsl (lshift x n)
      'lsr (rshift x n)
      'asr (arshift x (a32-mux (< n 32) n 31))
      'ror (rotate-right x n))))

(defun bool-mux (c x y)
  "(bool-mux C X Y) is the boolean X if C is true and Y otherwise"
  (logor (logand c x) (logand (not c) y)))

(defun reg-shifter-carry (typ x n)
  (let ((n (logand n 0xff))
        (m (logand n 31)))
    (bool-mux (is-zero n) CF
      (case typ
        'lsl (bit-of x (- 32 n))
        'lsr (bit-of x (- n 1))
        'asr (bool-mux (< n 32) (bit-of x (- n 1)) (msb x))
        'ror (bool-mux (is-zero m) (msb x) (bit-of x (- m 1)))))))

(defun set-nz (r)
  (set NF (msb r))
  (set ZF (is-zero r)))

(defmacro t2-logical (op rd rn y c cnd s)
  "sets rd to (op rn y) and the N, Z and C flags if s is CPSR, where c
   is the carry out of the shifter"
  (when (condition-holds cnd)
    (let ((carry c)
          (r (op rn y)))
      (set$ rd r)
      (when (sets-flags s)
        (set-nz r)
        (set CF carry)))))

(defmacro t2-test (op rn y c cnd)
  (when (condition-holds cnd)
    (let ((carry c)
          (r (op rn y)))
      (set-nz r)
      (set CF carry))))

(defmacro t2-arith (rd x y c cnd s)
  "sets rd to x + y + c, and the flags if s is CPSR"
  (when (condition-holds cnd)
    (let ((r (+ x y c)))
      (when (sets-flags s)
        (set-nzcv-from-registers r x y))
      (set$ rd r))))

(defmacro t2-compare (x y c cnd)
  (when (condition-holds cnd)
    (set-nzcv-from-registers (+ x y c) x y)))

(defun logornot (x y) (logor x (lnot y)))
(defun logandnot2 (x y) (logand x (lnot y)))
(defun second (_ y) y)
(defun second-not (_ y) (lnot y))

(defun t2ANDrs (rd rn rm sh cnd _ s)
  (t2-logical logand rd rn (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2ORRrs (rd rn rm sh cnd _ s)
  (t2-logical logor rd rn (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2EORrs (rd rn rm sh cnd _ s)
  (t2-logical logxor rd rn (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2BICrs (rd rn rm sh cnd _ s)
  (t2-logical logandnot2 rd rn (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2ORNrs (rd rn rm sh cnd _ s)
  (t2-logical logornot rd rn (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2ORNrr (rd rn rm cnd _ s) (t2-logical logornot rd rn rm CF cnd s))
(defun t2ORNri (rd rn imm cnd _ s) (t2-logical logornot rd rn imm CF cnd s))
(defun t2MVNs (rd rm sh cnd _ s)
  (t2-logical second-not rd rm (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2MOVsi (rd rm sh cnd _ s)
  (t2-logical second rd rm (shifted rm sh) (shifter-carry rm sh) cnd s))
(defun t2TSTrs (rn rm sh cnd _)
  (t2-test logand rn (shifted rm sh) (shifter-carry rm sh) cnd))
(defun t2TEQrs (rn rm sh cnd _)
  (t2-test logxor rn (shifted rm sh) (shifter-carry rm sh) cnd))

(defun t2ADDrs (rd rn rm sh cnd _ s)
  (t2-arith rd rn (shifted rm sh) (cast-unsigned 32 0) cnd s))
(defun t2SUBrs (rd rn rm sh cnd _ s)
  (t2-arith rd rn (lnot (shifted rm sh)) (cast-unsigned 32 1) cnd s))
(defun t2RSBrs (rd rn rm sh cnd _ s)
  (t2-arith rd (shifted rm sh) (lnot rn) (cast-unsigned 32 1) cnd s))
(defun t2ADCrs (rd rn rm sh cnd _ s)
  (t2-arith rd rn (shifted rm sh) (cast-unsigned 32 CF) cnd s))
(defun t2SBCrs (rd rn rm sh cnd _ s)
  (t2-arith rd rn (lnot (shifted rm sh)) (cast-unsigned 32 CF) cnd s))
(defun t2CMPrs (rn rm sh cnd _)
  (t2-compare rn (lnot (shifted rm sh)) (cast-unsigned 32 1) cnd))
(defun t2CMNzrs (rn rm sh cnd _)
  (t2-compare rn (shifted rm sh) (cast-unsigned 32 0) cnd))

;; the immediate shifts
(defmacro t2-shift-imm (typ rd rm imm cnd s)
  (let ((sh (logor typ (lshift (if (= imm 32) 0 imm) 3))))
    (t2-logical second rd rm (shifted rm sh) (shifter-carry rm sh) cnd s)))

(defun t2LSLri (rd rm imm cnd _ s) (t2-shift-imm 2 rd rm imm cnd s))
(defun t2LSRri (rd rm imm cnd _ s) (t2-shift-imm 3 rd rm imm cnd s))
(defun t2ASRri (rd rm imm cnd _ s) (t2-shift-imm 1 rd rm imm cnd s))
(defun t2RORri (rd rm imm cnd _ s) (t2-shift-imm 4 rd rm imm cnd s))
(defun t2RRX (rd rm cnd _ s) (t2-logical second rd rm (shifted rm 5) (shifter-carry rm 5) cnd s))

;; the register shifts
(defmacro t2-shift-reg (typ rd rn rm cnd s)
  (t2-logical second rd rn (reg-shifted typ rn rm) (reg-shifter-carry typ rn rm) cnd s))

(defun t2LSLrr (rd rn rm cnd _ s) (t2-shift-reg 'lsl rd rn rm cnd s))
(defun t2LSRrr (rd rn rm cnd _ s) (t2-shift-reg 'lsr rd rn rm cnd s))
(defun t2ASRrr (rd rn rm cnd _ s) (t2-shift-reg 'asr rd rn rm cnd s))
(defun t2RORrr (rd rn rm cnd _ s) (t2-shift-reg 'ror rd rn rm cnd s))

;; MISCELLANEOUS

(defun t2CLZ (rd rm cnd _) (when (condition-holds cnd) (set$ rd (clz rm))))
(defun tREVSH (rd rm cnd _) (when (condition-holds cnd) (set$ rd (a32-revsh rm))))
(defun t2REVSH (rd rm cnd _) (when (condition-holds cnd) (set$ rd (a32-revsh rm))))
(defun t2UDIV (rd rn rm cnd _) (when (condition-holds cnd) (a32-div / rd rn rm)))
(defun t2SDIV (rd rn rm cnd _) (when (condition-holds cnd) (a32-div s/ rd rn rm)))
(defun t2QADD (rd rm rn cnd _) (QADD rd rm rn cnd _))
(defun t2QSUB (rd rm rn cnd _) (QSUB rd rm rn cnd _))
(defun t2SSAT (rd n rn sh cnd _) (SSAT rd n rn sh cnd _))
(defun t2USAT (rd n rn sh cnd _) (USAT rd n rn sh cnd _))
(defun t2SMULBT (rd rn rm cnd _) (SMULBT rd rn rm cnd _))
(defun t2SMULTB (rd rn rm cnd _) (SMULTB rd rn rm cnd _))
(defun t2SMULTT (rd rn rm cnd _) (SMULTT rd rn rm cnd _))
(defun t2SMMUL (rd rn rm cnd _) (SMMUL rd rn rm cnd _))
(defun t2SMMLA (rd rn rm ra cnd _) (SMMLA rd rn rm ra cnd _))
(defun t2SMMLS (rd rn rm ra cnd _) (SMMLS rd rn rm ra cnd _))

;; the condition and the mask of IT apply to the following instructions,
;; which the decoder gives the condition operands
(defun t2IT (_ _) (empty))

(defun t2MRS_AR (rd cnd _)
  (when (condition-holds cnd)
    (set$ rd (concat NF ZF CF VF QF (cast-unsigned 27 0)))))

;; LOADS AND STORES

(defmacro t2-pre (load rt wb rn off)
  (let ((a (+ rn off))) (set$ rt (load a)) (set$ wb a)))
(defmacro t2-post (load rt wb rn off)
  (let ((a rn)) (set$ rt (load a)) (set$ wb (+ a off))))

(defun load-word32 (a) (load-word a))
(defun load-byte32 (a) (cast-unsigned 32 (load-byte a)))
(defun load-half32 (a) (cast-unsigned 32 (load-bits 16 a)))
(defun load-sbyte32 (a) (cast-signed 32 (load-byte a)))
(defun load-shalf32 (a) (cast-signed 32 (load-bits 16 a)))

(defun t2LDR_PRE (rt wb rn off cnd _) (when (condition-holds cnd) (t2-pre load-word32 rt wb rn off)))
(defun t2LDRB_POST (rt wb rn off cnd _) (when (condition-holds cnd) (t2-post load-byte32 rt wb rn off)))
(defun t2LDRH_PRE (rt wb rn off cnd _) (when (condition-holds cnd) (t2-pre load-half32 rt wb rn off)))
(defun t2LDRH_POST (rt wb rn off cnd _) (when (condition-holds cnd) (t2-post load-half32 rt wb rn off)))
(defun t2LDRSB_PRE (rt wb rn off cnd _) (when (condition-holds cnd) (t2-pre load-sbyte32 rt wb rn off)))
(defun t2LDRSB_POST (rt wb rn off cnd _) (when (condition-holds cnd) (t2-post load-sbyte32 rt wb rn off)))
(defun t2LDRSH_PRE (rt wb rn off cnd _) (when (condition-holds cnd) (t2-pre load-shalf32 rt wb rn off)))
(defun t2LDRSH_POST (rt wb rn off cnd _) (when (condition-holds cnd) (t2-post load-shalf32 rt wb rn off)))

(defun t2LDRD_POST (rt rt2 wb rn off cnd _)
  (when (condition-holds cnd)
    (let ((a rn))
      (set$ rt (load-word a))
      (set$ rt2 (load-word (+ a 4)))
      (set$ wb (+ a off)))))

(defun t2LDRD_PRE (rt rt2 wb rn off cnd _)
  (when (condition-holds cnd)
    (let ((a (+ rn off)))
      (set$ rt (load-word a))
      (set$ rt2 (load-word (+ a 4)))
      (set$ wb a))))

(defun t2STR_POST (wb rt rn off cnd _)
  (when (condition-holds cnd)
    (let ((a rn)) (store-word a rt) (set$ wb (+ a off)))))
(defun t2STRB_POST (wb rt rn off cnd _)
  (when (condition-holds cnd)
    (let ((a rn)) (store-byte a rt) (set$ wb (+ a off)))))
(defun t2STRH_POST (wb rt rn off cnd _)
  (when (condition-holds cnd)
    (let ((a rn)) (store-word a (cast-low 16 rt)) (set$ wb (+ a off)))))
(defun t2STRB_PRE (wb rt rn off cnd _)
  (when (condition-holds cnd)
    (let ((a (+ rn off))) (store-byte a rt) (set$ wb a))))
(defun t2STRH_PRE (wb rt rn off cnd _)
  (when (condition-holds cnd)
    (let ((a (+ rn off))) (store-word a (cast-low 16 rt)) (set$ wb a))))

(defun t2LDRBs (rt rn rm sh cnd _)
  (when (condition-holds cnd) (set$ rt (load-byte32 (+ rn (lshift rm sh))))))
(defun t2LDRHs (rt rn rm sh cnd _)
  (when (condition-holds cnd) (set$ rt (load-half32 (+ rn (lshift rm sh))))))
(defun t2LDRSBs (rt rn rm sh cnd _)
  (when (condition-holds cnd) (set$ rt (load-sbyte32 (+ rn (lshift rm sh))))))
(defun t2LDRSHs (rt rn rm sh cnd _)
  (when (condition-holds cnd) (set$ rt (load-shalf32 (+ rn (lshift rm sh))))))
(defun t2STRBs (rt rn rm sh cnd _)
  (when (condition-holds cnd) (store-byte (+ rn (lshift rm sh)) rt)))
(defun t2STRHs (rt rn rm sh cnd _)
  (when (condition-holds cnd) (store-word (+ rn (lshift rm sh)) (cast-low 16 rt))))

;; the exclusive monitor is not modeled, an exclusive store succeeds
(defun t2LDREX (rt rn off cnd _)
  (when (condition-holds cnd) (set$ rt (load-word (+ rn (lshift off 2))))))
(defun t2LDREXB (rt rn cnd _) (when (condition-holds cnd) (set$ rt (load-byte32 rn))))
(defun t2LDREXH (rt rn cnd _) (when (condition-holds cnd) (set$ rt (load-half32 rn))))
(defun t2STREX (rd rt rn off cnd _)
  (when (condition-holds cnd)
    (store-word (+ rn (lshift off 2)) rt)
    (set$ rd 0)))
(defun t2STREXB (rd rt rn cnd _)
  (when (condition-holds cnd) (store-byte rn rt) (set$ rd 0)))
(defun t2STREXH (rd rt rn cnd _)
  (when (condition-holds cnd) (store-word rn (cast-low 16 rt)) (set$ rd 0)))
(defun t2CLREX (_) (empty))

;; the 16-bit register shifts and CMN, the flags are set outside of an
;; IT block, where the second operand is CPSR
(defun tLSLrr (rd s rn rm cnd _) (t2-shift-reg 'lsl rd rn rm cnd s))
(defun tLSRrr (rd s rn rm cnd _) (t2-shift-reg 'lsr rd rn rm cnd s))
(defun tASRrr (rd s rn rm cnd _) (t2-shift-reg 'asr rd rn rm cnd s))
(defun tROR (rd s rn rm cnd _) (t2-shift-reg 'ror rd rn rm cnd s))
(defun tCMNz (rn rm cnd _) (t2-compare rn rm (cast-unsigned 32 0) cnd))
