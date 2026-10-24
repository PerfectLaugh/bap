(declare (context (target arm-family)
                  (bits 32)))

(in-package arm)

(require bits)
(require arm-bits)
(require arm-float)

;;; AARCH32 INTEGER OPERATIONS
;;
;; The operations shared by the A32 and T32 encodings, and the A32
;; data processing, bit field, multiplication, branch and system
;; instructions, the loads and stores are in arm-a32-mem. As in
;; arm-float, the values are computed without dynamic if.
;;
;; The last operand of a flag-setting instruction is CPSR when it sets
;; the flags. The shifted register operands encode the shift as in
;; i-shift, the type in the lowest three bits and the amount above.

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

(defun logornot (x y) (logor x (lnot y)))
(defun logandnot2 (x y) (logand x (lnot y)))
(defun second (_ y) y)
(defun second-not (_ y) (lnot y))

(defun load-word32 (a) (load-word a))
(defun load-byte32 (a) (cast-unsigned 32 (load-byte a)))
(defun load-half32 (a) (cast-unsigned 32 (load-bits 16 a)))
(defun load-sbyte32 (a) (cast-signed 32 (load-byte a)))
(defun load-shalf32 (a) (cast-signed 32 (load-bits 16 a)))

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

;; the supervisor call, as in AArch64
(defun SVC (imm cnd _) (a32-cond cnd (intrinsic 'svc imm)))

;;; THE A32 INSTRUCTIONS
;;
;; A register operand that is PC reads as the address of the
;; instruction plus 8, and a write to PC is a branch.

(defun a32-pc () (+ (get-program-counter) 8))
(defun a32-is-pc (r) (= (symbol r) 'PC))
(defun a32-is-nil (r) (= (symbol r) 'Nil))
(defun a32-reg (r) (if (a32-is-pc r) (a32-pc) r))

(defun a32-write-pc (x)
  "(a32-write-pc X) branches to X, the bit 0 of which selects the
   instruction set and is not a part of the address"
  (exec-addr (logand x 0xfffffffe)))

(defmacro a32-set (rd x)
  "(a32-set RD X) sets RD to X, or branches to X if RD is PC"
  (if (a32-is-pc rd) (a32-write-pc x) (set$ rd x)))

(defun a32-next () (+ (get-program-counter) 4))

;; the modified immediates are encoded, an 8-bit value rotated right by
;; twice the bits 11:8, the carry out is not changed if it is not rotated

(defun a32-imm (x)
  (rotate-right (logand x 0xff) (* 2 (logand (rshift x 8) 0xf))))

(defun a32-imm-carry (x)
  (if (= 0 (logand x 0xf00)) CF (msb (a32-imm x))))

;; the register shifts encode the type as in i-shift
(defun a32-shift-type (typ)
  (case typ 1 'asr 2 'lsl 3 'lsr 'ror))

(defun a32-reg-shifted (rm rs typ)
  (reg-shifted (a32-shift-type typ) rm rs))

(defun a32-reg-carry (rm rs typ)
  (reg-shifter-carry (a32-shift-type typ) rm rs))

;; data processing, rd and the operands are the values

(defmacro a32-logical (op rd x y c cnd s)
  "sets rd to (op x y) and the N, Z and C flags if s is CPSR, where c
   is the carry out of the shifter"
  (when (condition-holds cnd)
    (let ((carry c)
          (r (op x y)))
      (when (sets-flags s)
        (set-nz r)
        (set CF carry))
      (a32-set rd r))))

(defmacro a32-arith (rd x y c cnd s)
  "sets rd to x + y + c, and the flags if s is CPSR"
  (when (condition-holds cnd)
    (let ((r (+ x y c)))
      (when (sets-flags s)
        (set-nzcv-from-registers r x y))
      (a32-set rd r))))

(defmacro a32-test (op x y c cnd)
  (when (condition-holds cnd)
    (let ((carry c)
          (r (op x y)))
      (set-nz r)
      (set CF carry))))

(defmacro a32-compare (x y c cnd)
  (when (condition-holds cnd)
    (set-nzcv-from-registers (+ x y c) x y)))

(defun a32-zero () (cast-unsigned 32 0))
(defun a32-one () (cast-unsigned 32 1))
(defun a32-carry () (cast-unsigned 32 CF))

(defmacro a32-ADD (rd x y cnd s) (a32-arith rd x y (a32-zero) cnd s))
(defmacro a32-SUB (rd x y cnd s) (a32-arith rd x (lnot y) (a32-one) cnd s))
(defmacro a32-RSB (rd x y cnd s) (a32-arith rd y (lnot x) (a32-one) cnd s))
(defmacro a32-ADC (rd x y cnd s) (a32-arith rd x y (a32-carry) cnd s))
(defmacro a32-SBC (rd x y cnd s) (a32-arith rd x (lnot y) (a32-carry) cnd s))
(defmacro a32-RSC (rd x y cnd s) (a32-arith rd y (lnot x) (a32-carry) cnd s))
(defmacro a32-CMP (x y cnd) (a32-compare x (lnot y) (a32-one) cnd))
(defmacro a32-CMN (x y cnd) (a32-compare x y (a32-zero) cnd))

;; the second operand of a data processing instruction, the immediate
;; ri, the register rr, the shifted by an immediate rsi and the shifted
;; by a register rsr forms

(defmacro a32-op2-ri (imm) (a32-imm imm))
(defmacro a32-op2-rr (rm) (a32-reg rm))
(defmacro a32-op2-rsi (rm sh) (shifted (a32-reg rm) sh))
(defmacro a32-op2-rsr (rm rs typ) (a32-reg-shifted rm rs typ))

(defun ANDri (rd rn imm cnd _ s) (a32-logical logand rd (a32-reg rn) (a32-imm imm) (a32-imm-carry imm) cnd s))
(defun ANDrr (rd rn rm cnd _ s) (a32-logical logand rd (a32-reg rn) (a32-reg rm) CF cnd s))
(defun ANDrsi (rd rn rm sh cnd _ s) (a32-logical logand rd (a32-reg rn) (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd s))
(defun ANDrsr (rd rn rm rs typ cnd _ s) (a32-logical logand rd rn (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd s))
(defun EORri (rd rn imm cnd _ s) (a32-logical logxor rd (a32-reg rn) (a32-imm imm) (a32-imm-carry imm) cnd s))
(defun EORrr (rd rn rm cnd _ s) (a32-logical logxor rd (a32-reg rn) (a32-reg rm) CF cnd s))
(defun EORrsi (rd rn rm sh cnd _ s) (a32-logical logxor rd (a32-reg rn) (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd s))
(defun EORrsr (rd rn rm rs typ cnd _ s) (a32-logical logxor rd rn (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd s))
(defun ORRri (rd rn imm cnd _ s) (a32-logical logor rd (a32-reg rn) (a32-imm imm) (a32-imm-carry imm) cnd s))
(defun ORRrr (rd rn rm cnd _ s) (a32-logical logor rd (a32-reg rn) (a32-reg rm) CF cnd s))
(defun ORRrsi (rd rn rm sh cnd _ s) (a32-logical logor rd (a32-reg rn) (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd s))
(defun ORRrsr (rd rn rm rs typ cnd _ s) (a32-logical logor rd rn (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd s))
(defun BICri (rd rn imm cnd _ s) (a32-logical logandnot2 rd (a32-reg rn) (a32-imm imm) (a32-imm-carry imm) cnd s))
(defun BICrr (rd rn rm cnd _ s) (a32-logical logandnot2 rd (a32-reg rn) (a32-reg rm) CF cnd s))
(defun BICrsi (rd rn rm sh cnd _ s) (a32-logical logandnot2 rd (a32-reg rn) (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd s))
(defun BICrsr (rd rn rm rs typ cnd _ s) (a32-logical logandnot2 rd rn (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd s))

(defun MOVi (rd imm cnd _ s) (a32-logical second rd 0 (a32-imm imm) (a32-imm-carry imm) cnd s))
(defun MOVr (rd rm cnd _ s) (a32-logical second rd 0 (a32-reg rm) CF cnd s))
(defun MOVsi (rd rm sh cnd _ s) (a32-logical second rd 0 (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd s))
(defun MOVsr (rd rm rs typ cnd _ s) (a32-logical second rd 0 (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd s))
(defun MVNi (rd imm cnd _ s) (a32-logical second-not rd 0 (a32-imm imm) (a32-imm-carry imm) cnd s))
(defun MVNr (rd rm cnd _ s) (a32-logical second-not rd 0 (a32-reg rm) CF cnd s))
(defun MVNsi (rd rm sh cnd _ s) (a32-logical second-not rd 0 (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd s))
(defun MVNsr (rd rm rs typ cnd _ s) (a32-logical second-not rd 0 (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd s))
(defun MOVPCLR (cnd _) (when (condition-holds cnd) (a32-write-pc LR)))
(defun MOVi16 (rd imm cnd _) (when (condition-holds cnd) (set$ rd imm)))

(defun cp15-reg (cop opc1 crn crm opc2)
  "the register of the system control coprocessor, p15, by its crn, crm,
   and opc2, as a number crn:crm:opc2, or -1, if it isn't of p15"
  (declare (visibility :private))
  (if (and (= cop 15) (= opc1 0))
      (logor (lshift crn 8) (lshift crm 4) opc2)
    -1))

(defun read-coprocessor (rt cop opc1 crn crm opc2 cnd)
  "reads the thread ID registers of the user, that the user mode reads,
   TPIDRURW (c13, c0, 2), and TPIDRURO (c13, c0, 3), e.g., the thread
   pointer of Linux, the other registers are not modeled"
  (when (condition-holds cnd)
    (case (cp15-reg cop opc1 crn crm opc2)
      0xd02 (set$ rt TPIDRURW)
      0xd03 (set$ rt TPIDRURO)
      (intrinsic 'undefined-instruction :aborts))))

(defun write-coprocessor (cop opc1 rt crn crm opc2 cnd)
  "writes the thread ID registers of the user, TPIDRURW (c13, c0, 2),
   and TPIDRURO (c13, c0, 3), which Unicorn writes, as it runs in a
   privileged mode, the other moves to p15, that the user mode runs, are
   the barriers of ARMv6, ISB (c7, c5, 4), DSB (c7, c10, 4), and DMB
   (c7, c10, 5), which have no effect, and the other registers are not
   modeled"
  (when (condition-holds cnd)
    (case (cp15-reg cop opc1 crn crm opc2)
      0xd02 (set TPIDRURW rt)
      0xd03 (set TPIDRURO rt)
      0x754 (empty)
      0x7a4 (empty)
      0x7a5 (empty)
      (intrinsic 'undefined-instruction :aborts))))

(defun MRC (rt cop opc1 crn crm opc2 cnd _)
  (read-coprocessor rt cop opc1 crn crm opc2 cnd))

(defun t2MRC (rt cop opc1 crn crm opc2 cnd _)
  (read-coprocessor rt cop opc1 crn crm opc2 cnd))
(defun MOVTi16 (rd rn imm cnd _)
  (when (condition-holds cnd)
    (set$ rd (logor (logand rn 0xffff) (lshift imm 16)))))

(defun TSTri (rn imm cnd _) (a32-test logand (a32-reg rn) (a32-imm imm) (a32-imm-carry imm) cnd))
(defun TSTrr (rn rm cnd _) (a32-test logand (a32-reg rn) (a32-reg rm) CF cnd))
(defun TSTrsi (rn rm sh cnd _) (a32-test logand (a32-reg rn) (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd))
(defun TSTrsr (rn rm rs typ cnd _) (a32-test logand rn (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd))
(defun TEQri (rn imm cnd _) (a32-test logxor (a32-reg rn) (a32-imm imm) (a32-imm-carry imm) cnd))
(defun TEQrr (rn rm cnd _) (a32-test logxor (a32-reg rn) (a32-reg rm) CF cnd))
(defun TEQrsi (rn rm sh cnd _) (a32-test logxor (a32-reg rn) (a32-op2-rsi rm sh) (shifter-carry (a32-reg rm) sh) cnd))
(defun TEQrsr (rn rm rs typ cnd _) (a32-test logxor rn (a32-op2-rsr rm rs typ) (a32-reg-carry rm rs typ) cnd))

(defun ADDri (rd rn imm cnd _ s) (a32-ADD rd (a32-reg rn) (a32-op2-ri imm) cnd s))
(defun ADDrr (rd rn rm cnd _ s) (a32-ADD rd (a32-reg rn) (a32-op2-rr rm) cnd s))
(defun ADDrsi (rd rn rm sh cnd _ s) (a32-ADD rd (a32-reg rn) (a32-op2-rsi rm sh) cnd s))
(defun ADDrsr (rd rn rm rs typ cnd _ s) (a32-ADD rd rn (a32-op2-rsr rm rs typ) cnd s))
(defun SUBri (rd rn imm cnd _ s) (a32-SUB rd (a32-reg rn) (a32-op2-ri imm) cnd s))
(defun SUBrr (rd rn rm cnd _ s) (a32-SUB rd (a32-reg rn) (a32-op2-rr rm) cnd s))
(defun SUBrsi (rd rn rm sh cnd _ s) (a32-SUB rd (a32-reg rn) (a32-op2-rsi rm sh) cnd s))
(defun SUBrsr (rd rn rm rs typ cnd _ s) (a32-SUB rd rn (a32-op2-rsr rm rs typ) cnd s))
(defun RSBri (rd rn imm cnd _ s) (a32-RSB rd (a32-reg rn) (a32-op2-ri imm) cnd s))
(defun RSBrr (rd rn rm cnd _ s) (a32-RSB rd (a32-reg rn) (a32-op2-rr rm) cnd s))
(defun RSBrsi (rd rn rm sh cnd _ s) (a32-RSB rd (a32-reg rn) (a32-op2-rsi rm sh) cnd s))
(defun RSBrsr (rd rn rm rs typ cnd _ s) (a32-RSB rd rn (a32-op2-rsr rm rs typ) cnd s))
(defun ADCri (rd rn imm cnd _ s) (a32-ADC rd (a32-reg rn) (a32-op2-ri imm) cnd s))
(defun ADCrr (rd rn rm cnd _ s) (a32-ADC rd (a32-reg rn) (a32-op2-rr rm) cnd s))
(defun ADCrsi (rd rn rm sh cnd _ s) (a32-ADC rd (a32-reg rn) (a32-op2-rsi rm sh) cnd s))
(defun ADCrsr (rd rn rm rs typ cnd _ s) (a32-ADC rd rn (a32-op2-rsr rm rs typ) cnd s))
(defun SBCri (rd rn imm cnd _ s) (a32-SBC rd (a32-reg rn) (a32-op2-ri imm) cnd s))
(defun SBCrr (rd rn rm cnd _ s) (a32-SBC rd (a32-reg rn) (a32-op2-rr rm) cnd s))
(defun SBCrsi (rd rn rm sh cnd _ s) (a32-SBC rd (a32-reg rn) (a32-op2-rsi rm sh) cnd s))
(defun SBCrsr (rd rn rm rs typ cnd _ s) (a32-SBC rd rn (a32-op2-rsr rm rs typ) cnd s))
(defun RSCri (rd rn imm cnd _ s) (a32-RSC rd (a32-reg rn) (a32-op2-ri imm) cnd s))
(defun RSCrr (rd rn rm cnd _ s) (a32-RSC rd (a32-reg rn) (a32-op2-rr rm) cnd s))
(defun RSCrsi (rd rn rm sh cnd _ s) (a32-RSC rd (a32-reg rn) (a32-op2-rsi rm sh) cnd s))
(defun RSCrsr (rd rn rm rs typ cnd _ s) (a32-RSC rd rn (a32-op2-rsr rm rs typ) cnd s))
(defun CMPri (rn imm cnd _) (a32-CMP (a32-reg rn) (a32-op2-ri imm) cnd))
(defun CMPrr (rn rm cnd _) (a32-CMP (a32-reg rn) (a32-op2-rr rm) cnd))
(defun CMPrsi (rn rm sh cnd _) (a32-CMP (a32-reg rn) (a32-op2-rsi rm sh) cnd))
(defun CMPrsr (rn rm rs typ cnd _) (a32-CMP rn (a32-op2-rsr rm rs typ) cnd))
(defun CMNri (rn imm cnd _) (a32-CMN (a32-reg rn) (a32-op2-ri imm) cnd))
(defun CMNzrr (rn rm cnd _) (a32-CMN (a32-reg rn) (a32-op2-rr rm) cnd))
(defun CMNzrsi (rn rm sh cnd _) (a32-CMN (a32-reg rn) (a32-op2-rsi rm sh) cnd))
(defun CMNzrsr (rn rm rs typ cnd _) (a32-CMN rn (a32-op2-rsr rm rs typ) cnd))
;; LLVM 23 names the register forms of CMN without z
(defun CMNrr (rn rm cnd _) (CMNzrr rn rm cnd _))
(defun CMNrsi (rn rm sh cnd _) (CMNzrsi rn rm sh cnd _))
(defun CMNrsr (rn rm rs typ cnd _) (CMNzrsr rn rm rs typ cnd _))

;; bit fields, extensions and reversals

(defun a32-bfi (rd x mask)
  "inserts the low bits of X into the bits of RD that the inverted MASK clears"
  (let ((field (lnot mask)))
    (logor (logand rd mask) (logand (* x (logand field (- 0 field))) field))))

(defun a32-ror (x rot) (rotate-right x (* 8 rot)))
(defun a32-uxtb (x rot) (cast-unsigned 32 (cast-low 8 (a32-ror x rot))))
(defun a32-uxth (x rot) (cast-unsigned 32 (cast-low 16 (a32-ror x rot))))
(defun a32-sxtb (x rot) (cast-signed 32 (cast-low 8 (a32-ror x rot))))
(defun a32-sxth (x rot) (cast-signed 32 (cast-low 16 (a32-ror x rot))))

(defun a32-rev (x)
  (concat (extract 7 0 x) (extract 15 8 x) (extract 23 16 x) (extract 31 24 x)))
(defun a32-rev16 (x)
  (concat (extract 23 16 x) (extract 31 24 x) (extract 7 0 x) (extract 15 8 x)))

(defun a32-pkhtb (x y sh)
  "the top half of X and the bottom half of Y asr SH, asr #0 is asr #32"
  (concat (extract 31 16 x) (extract 15 0 (arshift y (if (= sh 0) 31 sh)))))
(defun a32-pkhbt (x y sh)
  (concat (extract 31 16 (lshift y sh)) (extract 15 0 x)))

(defun BFC (rd rn mask cnd _) (a32-cond cnd (set$ rd (logand rn mask))))
(defun BFI (rd rd0 rn mask cnd _) (a32-cond cnd (set$ rd (a32-bfi rd0 rn mask))))
(defun UBFX (rd rn lsb w cnd _)
  (a32-cond cnd (set$ rd (cast-unsigned 32 (extract (+ lsb w) lsb rn)))))
(defun SBFX (rd rn lsb w cnd _)
  (a32-cond cnd (set$ rd (cast-signed 32 (extract (+ lsb w) lsb rn)))))
(defun RBIT (rd rm cnd _) (a32-cond cnd (set$ rd (reverse-bits rm))))
(defun REV (rd rm cnd _) (a32-cond cnd (set$ rd (a32-rev rm))))
(defun REV16 (rd rm cnd _) (a32-cond cnd (set$ rd (a32-rev16 rm))))
(defun PKHTB (rd rn rm sh cnd _) (a32-cond cnd (set$ rd (a32-pkhtb rn rm sh))))
(defun PKHBT (rd rn rm sh cnd _) (a32-cond cnd (set$ rd (a32-pkhbt rn rm sh))))
(defun UXTB (rd rm rot cnd _) (a32-cond cnd (set$ rd (a32-uxtb rm rot))))
(defun UXTH (rd rm rot cnd _) (a32-cond cnd (set$ rd (a32-uxth rm rot))))
(defun SXTB (rd rm rot cnd _) (a32-cond cnd (set$ rd (a32-sxtb rm rot))))
(defun SXTH (rd rm rot cnd _) (a32-cond cnd (set$ rd (a32-sxth rm rot))))
(defun UXTAB (rd rn rm rot cnd _) (a32-cond cnd (set$ rd (+ rn (a32-uxtb rm rot)))))
(defun UXTAH (rd rn rm rot cnd _) (a32-cond cnd (set$ rd (+ rn (a32-uxth rm rot)))))
(defun SXTAB (rd rn rm rot cnd _) (a32-cond cnd (set$ rd (+ rn (a32-sxtb rm rot)))))
(defun SXTAH (rd rn rm rot cnd _) (a32-cond cnd (set$ rd (+ rn (a32-sxth rm rot)))))

;; multiplications, the flag-setting ones set only N and Z

(defun a32-add-q (x y)
  "(a32-add-q X Y) is the sum of the signed X and Y, it sets the Q flag
   if the sum overflows"
  (let ((r (+ x y))
        (ov (logand (= (msb x) (msb y)) (/= (msb r) (msb x)))))
    (set QF (logor QF ov))
    r))

(defun a32-sum-q (s)
  "(a32-sum-q S) is the lower word of the 64-bit sum S, it sets the Q
   flag if S doesn't fit into the signed word"
  (let ((r (cast-low 32 s)))
    (set QF (logor QF (/= s (cast-signed 64 r))))
    r))

(defun a32-s64 (x) (cast-signed 64 x))
(defun a32-u64 (x) (cast-unsigned 64 x))

(defmacro a32-mul (rd r s)
  (let ((v r))
    (when (sets-flags s) (set-nz v))
    (set$ rd v)))

(defmacro a32-mul64 (lo hi r s)
  (let ((v r))
    (when (sets-flags s)
      (set NF (msb v))
      (set ZF (is-zero v)))
    (set$ lo (cast-low 32 v))
    (set$ hi (cast-high 32 v))))

(defun MUL (rd rn rm cnd _ s) (a32-cond cnd (a32-mul rd (* rn rm) s)))
(defun MLA (rd rn rm ra cnd _ s) (a32-cond cnd (a32-mul rd (+ ra (* rn rm)) s)))
(defun MLS (rd rn rm ra cnd _) (a32-cond cnd (set$ rd (- ra (* rn rm)))))
(defun UMULL (lo hi rn rm cnd _ s)
  (a32-cond cnd (a32-mul64 lo hi (* (a32-u64 rn) (a32-u64 rm)) s)))
(defun SMULL (lo hi rn rm cnd _ s)
  (a32-cond cnd (a32-mul64 lo hi (* (a32-s64 rn) (a32-s64 rm)) s)))
(defun UMLAL (lo hi rn rm lo0 hi0 cnd _ s)
  (a32-cond cnd (a32-mul64 lo hi (+ (concat hi0 lo0) (* (a32-u64 rn) (a32-u64 rm))) s)))
(defun SMLAL (lo hi rn rm lo0 hi0 cnd _ s)
  (a32-cond cnd (a32-mul64 lo hi (+ (concat hi0 lo0) (* (a32-s64 rn) (a32-s64 rm))) s)))
(defun SMULBB (rd rn rm cnd _)
  (a32-cond cnd (set$ rd (* (a32-half rn false) (a32-half rm false)))))
(defun SMLABB (rd rn rm ra cnd _)
  (a32-cond cnd (set$ rd (a32-add-q (* (a32-half rn false) (a32-half rm false)) ra))))
(defun SMLAWB (rd rn rm ra cnd _)
  (a32-cond cnd
    (set$ rd (a32-add-q (extract 47 16 (* (a32-s64 rn) (a32-s64 (a32-half rm false)))) ra))))
(defun SMUAD (rd rn rm cnd _)
  (a32-cond cnd
    (set$ rd (a32-sum-q (+ (a32-s64 (* (a32-half rn false) (a32-half rm false)))
                           (a32-s64 (* (a32-half rn true) (a32-half rm true))))))))
(defun SMLAD (rd rn rm ra cnd _)
  (a32-cond cnd
    (set$ rd (a32-sum-q (+ (a32-s64 (* (a32-half rn false) (a32-half rm false)))
                           (a32-s64 (* (a32-half rn true) (a32-half rm true)))
                           (a32-s64 ra))))))
(defmacro a32-set64 (lo hi x)
  (let ((v x))
    (set$ lo (cast-low 32 v))
    (set$ hi (cast-high 32 v))))

(defun SMLALBT (lo hi rn rm lo0 hi0 cnd _)
  (a32-cond cnd
    (a32-set64 lo hi (+ (concat hi0 lo0)
                        (a32-s64 (* (a32-half rn false) (a32-half rm true)))))))

;; the parallel saturating and halving additions and subtractions of
;; the halfwords and the bytes, the GE flags are not modeled, so the
;; ones that set them, e.g., SADD16, are not defined

(defun a32-lane-qadds (x y)
  (let ((e (word-width x))
        (r (+ (cast-signed (+ e 1) x) (cast-signed (+ e 1) y)))
        (hi (cast-unsigned (+ e 1) (- (lshift (cast-unsigned 32 1) (- e 1)) 1)))
        (lo (lnot hi)))
    (cast-low e (a32-mux (s> r hi) hi (a32-mux (s< r lo) lo r)))))

(defun a32-lane-qsubs (x y)
  (let ((e (word-width x))
        (r (- (cast-signed (+ e 1) x) (cast-signed (+ e 1) y)))
        (hi (cast-unsigned (+ e 1) (- (lshift (cast-unsigned 32 1) (- e 1)) 1)))
        (lo (lnot hi)))
    (cast-low e (a32-mux (s> r hi) hi (a32-mux (s< r lo) lo r)))))

(defun a32-lane-qaddu (x y)
  (let ((e (word-width x))
        (r (+ (cast-unsigned (+ e 1) x) (cast-unsigned (+ e 1) y))))
    (a32-mux (msb r) (lnot (cast-unsigned e 0)) (cast-low e r))))

(defun a32-lane-qsubu (x y)
  (let ((e (word-width x))
        (r (- (cast-unsigned (+ e 1) x) (cast-unsigned (+ e 1) y))))
    (a32-mux (msb r) (cast-unsigned e 0) (cast-low e r))))

(defun a32-lane-hadds (x y)
  (let ((e (word-width x)))
    (cast-high e (+ (cast-signed (+ e 1) x) (cast-signed (+ e 1) y)))))
(defun a32-lane-hsubs (x y)
  (let ((e (word-width x)))
    (cast-high e (- (cast-signed (+ e 1) x) (cast-signed (+ e 1) y)))))
(defun a32-lane-haddu (x y)
  (let ((e (word-width x)))
    (cast-high e (+ (cast-unsigned (+ e 1) x) (cast-unsigned (+ e 1) y)))))
(defun a32-lane-hsubu (x y)
  (let ((e (word-width x)))
    (cast-high e (- (cast-unsigned (+ e 1) x) (cast-unsigned (+ e 1) y)))))

(defmacro a32-par16 (f x y)
  (concat (f (cast-high 16 x) (cast-high 16 y))
          (f (cast-low 16 x) (cast-low 16 y))))

(defmacro a32-par8 (f x y)
  (concat (f (extract 31 24 x) (extract 31 24 y))
          (f (extract 23 16 x) (extract 23 16 y))
          (f (extract 15 8 x) (extract 15 8 y))
          (f (extract 7 0 x) (extract 7 0 y))))

(defmacro a32-asx (add sub x y)
  "the sum of the top half of X and the bottom one of Y, and the
   difference of the bottom half of X and the top one of Y"
  (concat (add (cast-high 16 x) (cast-low 16 y))
          (sub (cast-low 16 x) (cast-high 16 y))))

(defmacro a32-sax (add sub x y)
  (concat (sub (cast-high 16 x) (cast-low 16 y))
          (add (cast-low 16 x) (cast-high 16 y))))

(defmacro a32-par (rd x cnd)
  (a32-cond cnd (set$ rd x)))

(defun QADD16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-qadds rn rm) cnd))
(defun QSUB16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-qsubs rn rm) cnd))
(defun QADD8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-qadds rn rm) cnd))
(defun QSUB8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-qsubs rn rm) cnd))
(defun QASX (rd rn rm cnd _) (a32-par rd (a32-asx a32-lane-qadds a32-lane-qsubs rn rm) cnd))
(defun QSAX (rd rn rm cnd _) (a32-par rd (a32-sax a32-lane-qadds a32-lane-qsubs rn rm) cnd))
(defun UQADD16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-qaddu rn rm) cnd))
(defun UQSUB16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-qsubu rn rm) cnd))
(defun UQADD8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-qaddu rn rm) cnd))
(defun UQSUB8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-qsubu rn rm) cnd))
(defun UQASX (rd rn rm cnd _) (a32-par rd (a32-asx a32-lane-qaddu a32-lane-qsubu rn rm) cnd))
(defun UQSAX (rd rn rm cnd _) (a32-par rd (a32-sax a32-lane-qaddu a32-lane-qsubu rn rm) cnd))
(defun SHADD16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-hadds rn rm) cnd))
(defun SHSUB16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-hsubs rn rm) cnd))
(defun SHADD8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-hadds rn rm) cnd))
(defun SHSUB8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-hsubs rn rm) cnd))
(defun SHASX (rd rn rm cnd _) (a32-par rd (a32-asx a32-lane-hadds a32-lane-hsubs rn rm) cnd))
(defun SHSAX (rd rn rm cnd _) (a32-par rd (a32-sax a32-lane-hadds a32-lane-hsubs rn rm) cnd))
(defun UHADD16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-haddu rn rm) cnd))
(defun UHSUB16 (rd rn rm cnd _) (a32-par rd (a32-par16 a32-lane-hsubu rn rm) cnd))
(defun UHADD8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-haddu rn rm) cnd))
(defun UHSUB8 (rd rn rm cnd _) (a32-par rd (a32-par8 a32-lane-hsubu rn rm) cnd))
(defun UHASX (rd rn rm cnd _) (a32-par rd (a32-asx a32-lane-haddu a32-lane-hsubu rn rm) cnd))
(defun UHSAX (rd rn rm cnd _) (a32-par rd (a32-sax a32-lane-haddu a32-lane-hsubu rn rm) cnd))

;; branches, BX and BLX may change the instruction set, which is
;; chosen by the label of the destination, the bit 0 of the register
;; is not a part of the address, as in the writes to PC

(defun a32-branch (off) (exec-addr (+ (a32-pc) off)))
(defun a32-link () (set LR (a32-next)))

(defun Bcc (off cnd _) (a32-cond cnd (a32-branch off)))
(defun BL (off) (a32-link) (a32-branch off))
(defun BL_pred (off cnd _) (a32-cond cnd (prog (a32-link) (a32-branch off))))
(defun BLXi (off) (a32-link) (a32-branch off))
(defun BX (rm) (a32-write-pc rm))
(defun BX_pred (rm cnd _) (a32-cond cnd (a32-write-pc rm)))
(defun BX_RET (cnd _) (a32-cond cnd (a32-write-pc LR)))
(defun BLX (rm) (let ((dst rm)) (a32-link) (a32-write-pc dst)))
(defun BLX_pred (rm cnd _)
  (a32-cond cnd (let ((dst rm)) (a32-link) (a32-write-pc dst))))

;; the status register, the GE flags are not modeled and the mode bits
;; read as the user mode

(defun a32-apsr () (concat NF ZF CF VF QF (cast-unsigned 27 0x10)))

(defun a32-msr (mask x)
  (when (/= 0 (logand mask 8))
    (set NF (select 31 x))
    (set ZF (select 30 x))
    (set CF (select 29 x))
    (set VF (select 28 x))
    (set QF (select 27 x))))

(defun MRS (rd cnd _) (a32-cond cnd (set$ rd (a32-apsr))))
(defun MSR (mask rn cnd _) (a32-cond cnd (a32-msr mask rn)))
(defun MSRi (mask imm cnd _) (a32-cond cnd (a32-msr mask (a32-imm imm))))

;; the hints, the barriers and the instructions that have no effect in
;; the user mode
(defun CPS1p (_) (empty))
(defun CPS2p (_ _) (empty))
(defun CPS3p (_ _ _) (empty))
(defun DMB (_) (empty))
(defun DSB (_) (empty))
(defun ISB (_) (empty))
(defun HINT (_ _ _) (empty))
(defun PLDi12 (_ _) (empty))
(defun PLDrs (_ _ _) (empty))
(defun PLIi12 (_ _) (empty))
(defun PLIrs (_ _ _) (empty))
(defun CLREX () (empty))

;; the moves to the coprocessors, see [write-coprocessor], and MCR2,
;; whose coprocessors are not modeled
(defun MCR (cop opc1 rt crn crm opc2 cnd _)
  (write-coprocessor cop opc1 rt crn crm opc2 cnd))
(defun MCR2 (_ _ _ _ _ _) (intrinsic 'undefined-instruction :aborts))
