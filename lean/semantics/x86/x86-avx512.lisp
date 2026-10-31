(declare (context (target x86)))
(require x86-common)

(in-package x86-common)

;;; AVX-512: THE EVEX INSTRUCTIONS AND THE MASK REGISTERS
;;
;; LLVM has thousands of EVEX opcodes, each family in up to 27 forms. A
;; family is one definition here, `evex:NAME` for the opcodes that are
;; NAME and a form, which `Bap.Target.LLVMLift` finds by the name of the
;; opcode. Its one argument O is the list of what the name says, and the
;; operands of the instruction: (W MEM M I OPERANDS...)
;;
;; W is the size of the vector, 128, 256 or 512.
;; MEM is how the last source is given: 0 a register, 1 memory, 2 the
;; broadcast of an element of memory, 3 the instruction stores to
;; memory, 4 a register, and a static rounding mode as the last operand.
;; M is the masking: 0 none, 1 merging with {k}, 2 zeroing with {k}{z}.
;; I is 1 if the last operand is an immediate, as forms with it and
;; without it have the same shape.
;;
;; OPERANDS are those of LLVM, the masked forms have the destination
;; twice for merging, and then the mask: (RD PASS K SOURCES...) and
;; (RD K SOURCES...) for {z}.
;;
;; A lane of a masked source in memory is loaded only if its bit of the
;; mask is set, as a lane that is masked out doesn't fault, and each
;; lane of a masked store is stored only if its bit is set. All these
;; instructions clear the bits of the ZMM register above the result.
;;
;; The list operations and lambda can't be compiled and an instruction
;; has up to 64 lanes, so what happens for each lane has no lists and is
;; compiled: what a lane needs are the arguments A ... L of a definition
;; (F A ... L I), and a source is a mode and a value:
;; 0 the lanes of the value, 1 the lanes of memory at the value,
;; 2 the value is each lane, 3 each lane is the memory at the value.
;; What reads the list has no let, as the evaluator takes long for it.

;; what the name says, and the operands

(defun evex-w (o) (car o))
(defun evex-mem (o) (car (cdr o)))
(defun evex-m (o) (car (cdr (cdr o))))
(defun evex-i (o) (car (cdr (cdr (cdr o)))))
(defun evex-ops (o) (cdr (cdr (cdr (cdr o)))))
(defun evex-rd (o) (car (evex-ops o)))

(defun evex-drop (n l)
  (case n
    0 l
    1 (cdr l)
    2 (cdr (cdr l))
    3 (cdr (cdr (cdr l)))
    (evex-drop (- n 4) (cdr (cdr (cdr (cdr l)))))))

(defun evex-nth (n l) (car (evex-drop n l)))

(defun evex-last (l)
  (if (null? (cdr l)) (car l) (evex-last (cdr l))))

(defun evex-imm (o) (evex-last (evex-ops o)))
(defun evex-imm-form (o) (= (evex-i o) 1))

;; what follows the destination and the mask, in the three layouts of
;; the operands: with the destination twice if merging, as most are,
;; once, as the comparisons have, and twice always, as the instructions
;; that have the destination as a source have
(defun evex-sources (o)
  (evex-drop (if (= (evex-m o) 1) 3 (if (= (evex-m o) 2) 2 1)) (evex-ops o)))
(defun evex-sources-once (o)
  (evex-drop (if (= (evex-m o) 0) 1 2) (evex-ops o)))
(defun evex-sources-tied (o)
  (evex-drop (if (= (evex-m o) 0) 2 3) (evex-ops o)))

(defun evex-k (o)
  (if (= (evex-m o) 0) 0 (evex-nth (if (= (evex-m o) 1) 2 1) (evex-ops o))))
(defun evex-k-once (o) (if (= (evex-m o) 0) 0 (evex-nth 1 (evex-ops o))))
(defun evex-k-tied (o) (if (= (evex-m o) 0) 0 (evex-nth 2 (evex-ops o))))
(defun evex-pass (o) (evex-nth 1 (evex-ops o)))
(defun evex-merged (o) (if (= (evex-m o) 1) (evex-pass o) 0))

(defun evex-count (o e) (/ (evex-w o) e))

;; the lanes

(defun evex-freeze (x)
  "(evex-freeze X) is X, computed once and here"
  (let ((v x)) v))

(defun evex-lane (e x i)
  "(evex-lane E X I) is the E-bit lane I of X"
  (extract (- (* e (+ i 1)) 1) (* e i) x))

(defun evex-address (e a i)
  "(evex-address E A I) is the address of the E-bit lane I of memory at A"
  (+ a (* (/ e 8) i)))

(defun evex-y (mode e y i)
  "(evex-y MODE E Y I) is the E-bit lane I of the source"
  (case mode
    0 (evex-lane e y i)
    1 (load-n e (evex-address e y i))
    2 y
    (load-n e y)))

(defun evex-mask (m k pass e i lane)
  "(evex-mask M K PASS E I LANE) is the lane I of the result"
  (case m
    0 lane
    1 (if (select i k) lane (evex-lane e pass i))
    (if (select i k) lane (zeros e))))

(defun evex-lanes (m k pass e f a b c d h j l i n)
  "the N lanes from I up of (F A ... L INDEX), under the mask"
  (if (= n 1)
      (evex-mask m k pass e i (f a b c d h j l i))
    (concat (evex-lanes m k pass e f a b c d h j l (+ i (/ n 2)) (/ n 2))
            (evex-lanes m k pass e f a b c d h j l i (/ n 2)))))

(defun evex-bits (m k f a b c d h j l i n)
  "the N bits from I up of (F A ... L INDEX), a bit masked out is clear"
  (if (= n 1)
      (case m
        0 (f a b c d h j l i)
        (if (select i k) (f a b c d h j l i) 0:1))
    (concat (evex-bits m k f a b c d h j l (+ i (/ n 2)) (/ n 2))
            (evex-bits m k f a b c d h j l i (/ n 2)))))

(defun evex-each (f a b c d h j l i n)
  "(F A ... L INDEX) for the N indices from I up, the highest first"
  (if (= n 1)
      (f a b c d h j l i)
    (prog
       (evex-each f a b c d h j l (+ i (/ n 2)) (/ n 2))
       (evex-each f a b c d h j l i (/ n 2)))))

(defun evex-put-n (o e n f a b c d h j l)
  "sets the destination to N E-bit lanes, of the operands (RD PASS K ...) or (RD K ...)"
  (set-vex (evex-rd o)
           (evex-lanes (evex-m o) (evex-k o) (evex-merged o) e f a b c d h j l 0 n)))

(defun evex-put (o e f a b c d h j l) (evex-put-n o e (evex-count o e) f a b c d h j l))

(defun evex-put-tied (o e f a b c d h j l)
  "the same, of the operands (RD PASS [K] ...)"
  (set-vex (evex-rd o)
           (evex-lanes (evex-m o) (evex-k-tied o) (evex-pass o) e f a b c d h j l 0 (evex-count o e))))

(defun evex-put-mask (o e f a b c d h j l)
  "sets the mask destination to the bits, of the operands (KD [K] ...)"
  (set$ (evex-rd o)
        (cast-unsigned 64 (evex-bits (evex-m o) (evex-k-once o) f a b c d h j l 0 (evex-count o e)))))

;; the sources

(defun evex-rounding () (error "evex: a static rounding mode"))

(defun evex-ea (s)
  (evex-freeze (ea (car s) (evex-nth 1 s) (evex-nth 2 s) (evex-nth 3 s) (evex-nth 4 s))))

(defun evex-mode (o)
  (case (evex-mem o)
    0 0
    1 (if (= (evex-m o) 0) 0 1)
    2 (if (= (evex-m o) 0) 2 3)
    (evex-rounding)))

(defun evex-value (o e total s)
  "the value of the source at the head of S, of TOTAL bits, whose mode
   is (evex-mode O). A masked one has the address: each lane is loaded
   only if its bit is set"
  (case (evex-mem o)
    0 (car s)
    1 (if (= (evex-m o) 0) (evex-freeze (load-n total (evex-ea s))) (evex-ea s))
    (if (= (evex-m o) 0) (evex-freeze (load-n e (evex-ea s))) (evex-ea s))))

(defun evex-src (o e s) (evex-value o e (evex-w o) s))

(defun evex-replicate (v n) (replicate v n))

(defun evex-full (o e s)
  "(evex-full O E S) is the whole of the source at the head of S, as for
   a permutation, which doesn't suppress faults by the mask"
  (case (evex-mem o)
    0 (car s)
    1 (evex-freeze (load-n (evex-w o) (evex-ea s)))
    2 (evex-replicate (evex-freeze (load-n e (evex-ea s))) (evex-count o e))
    (evex-rounding)))

;; the shapes of the instructions

(defun evex-lane-binary (f e x mode y _ _ i)
  (f (evex-lane e x i) (evex-y mode e y i)))

(defun evex-binary-of (f e o s)
  (evex-put o e evex-lane-binary f e (car s) (evex-mode o) (evex-src o e (cdr s)) 0 0))
(defun evex-binary (f e o)
  "(RD X Y) is (F XI YI) in each lane"
  (evex-binary-of f e o (evex-sources o)))

(defun evex-lane-unary (f e mode y _ _ _ i) (f (evex-y mode e y i)))

(defun evex-unary (f e o)
  "(RD Y) is (F YI) in each lane"
  (evex-put o e evex-lane-unary f e (evex-mode o) (evex-src o e (evex-sources o)) 0 0 0))

(defun evex-lane-with (f e mode y v _ _ i) (f (evex-y mode e y i) v))

(defun evex-lane-ternary (f e x y mode z _ i)
  (f (evex-lane e x i) (evex-lane e y i) (evex-y mode e z i)))

(defun evex-ternary-of (f e o s)
  (evex-put-tied o e evex-lane-ternary f e (evex-pass o) (car s) (evex-mode o) (evex-src o e (cdr s)) 0))
(defun evex-ternary (f e o)
  "(RD X Y Z), with RD = X, is (F XI YI ZI) in each lane"
  (evex-ternary-of f e o (evex-sources-tied o)))

(defun evex-lane-ternary-imm (f e x y mode z imm i)
  (f (evex-lane e x i) (evex-lane e y i) (evex-y mode e z i) imm))

(defun evex-ternary-imm-of (f e o s)
  (evex-put-tied o e evex-lane-ternary-imm f e (evex-pass o) (car s) (evex-mode o) (evex-src o e (cdr s)) (evex-imm o)))
(defun evex-ternary-imm (f e o)
  "the same with an immediate as the last argument of F"
  (evex-ternary-imm-of f e o (evex-sources-tied o)))

(defun evex-test-of (f e o s)
  (evex-put-mask o e evex-lane-binary f e (car s) (evex-mode o) (evex-src o e (cdr s)) 0 0))
(defun evex-test (f e o)
  "(KD X Y) sets the bit of KD to (F XI YI)"
  (evex-test-of f e o (evex-sources-once o)))

(defun evex-lane-binary-imm (f e x mode y imm _ i)
  (f (evex-lane e x i) (evex-y mode e y i) imm))

(defun evex-test-imm-of (f e o s)
  (evex-put-mask o e evex-lane-binary-imm f e (car s) (evex-mode o) (evex-src o e (cdr s)) (evex-imm o) 0))
(defun evex-test-imm (f e o)
  "(KD X Y IMM) sets the bit of KD to (F XI YI IMM)"
  (evex-test-imm-of f e o (evex-sources-once o)))

;; the moves

(defun evex-store-lane (a e k x _ _ _ i)
  (when (select i k)
    (store-n e (evex-address e a i) (evex-lane e x i))))

(defun evex-store-lanes (a e k x n)
  (evex-each evex-store-lane a e k x 0 0 0 0 n))

(defun evex-store-of (o e ops)
  (if (= (evex-m o) 0)
      (store-n (evex-w o) (evex-ea ops) (evex-nth 5 ops))
    (evex-store-lanes (evex-ea ops) e (evex-nth 5 ops) (evex-nth 6 ops) (evex-count o e))))

(defun evex-store (o e)
  "(BASE SCALE INDEX OFF SEG [K] X) stores X"
  (evex-store-of o e (evex-ops o)))

(defun evex-lane-move (e mode y _ _ _ _ i) (evex-y mode e y i))

(defun evex-move (e o)
  (if (= (evex-mem o) 3) (evex-store o e)
    (evex-put o e evex-lane-move e (evex-mode o) (evex-src o e (evex-sources o)) 0 0 0 0)))

(defun evex:VMOVDQA32 (o) (evex-move 32 o))
(defun evex:VMOVDQA64 (o) (evex-move 64 o))
(defun evex:VMOVDQU8 (o) (evex-move 8 o))
(defun evex:VMOVDQU16 (o) (evex-move 16 o))
(defun evex:VMOVDQU32 (o) (evex-move 32 o))
(defun evex:VMOVDQU64 (o) (evex-move 64 o))
(defun evex:VMOVAPS (o) (evex-move 32 o))
(defun evex:VMOVAPD (o) (evex-move 64 o))
(defun evex:VMOVUPS (o) (evex-move 32 o))
(defun evex:VMOVUPD (o) (evex-move 64 o))
(defun evex:VMOVNTDQ (o) (evex-move 64 o))
(defun evex:VMOVNTPS (o) (evex-move 32 o))
(defun evex:VMOVNTPD (o) (evex-move 64 o))
(defun evex:VMOVNTDQA (o) (evex-move 64 o))

;; the scalar moves, whose upper lanes come from the first source, or
;; are cleared if there is none

(defun evex-scalar-set (o e x lane)
  (set-vex (evex-rd o)
           (concat (extract 127 e x)
                   (evex-mask (evex-m o) (evex-k o) (evex-merged o) e 0 lane))))

(defun evex-scalar-of (f e o s)
  (evex-scalar-set o e (car s) (f (evex-lane e (car s) 0)
                                  (evex-y (evex-mode o) e (evex-value o e e (cdr s)) 0))))
(defun evex-scalar2 (e o f)
  "(RD X Y) is the lane (F X0 Y0) under the mask, with the upper bits of X"
  (evex-scalar-of f e o (evex-sources o)))

(defun evex-second (x y) y)

(defun evex-scalar-store (o e ops)
  (if (= (evex-m o) 0)
      (store-n e (evex-ea ops) (evex-nth 5 ops))
    (when (select 0 (evex-nth 5 ops))
      (store-n e (evex-ea ops) (evex-nth 6 ops)))))

(defun evex-scalar-move (e o)
  (case (evex-mem o)
    3 (evex-scalar-store o e (evex-ops o))
    0 (evex-scalar2 e o evex-second)
    (set-vex (evex-rd o)
             (evex-mask (evex-m o) (evex-k o) (evex-merged o) e 0
                        (evex-y (evex-mode o) e (evex-value o e e (evex-sources o)) 0)))))

(defun evex:VMOVSS (o) (evex-scalar-move 32 o))
(defun evex:VMOVSD (o) (evex-scalar-move 64 o))

;; the broadcasts: of the low lane of a register, or of an element of
;; memory, or of a group of lanes

(defun evex-lane-value (v _ _ _ _ _ _ i) v)
(defun evex-lane-element (e a _ _ _ _ _ i) (load-n e a))

(defun evex-broadcast-of (e o s)
  (case (evex-mem o)
    0 (evex-put o e evex-lane-value (evex-freeze (cast-low e (car s))) 0 0 0 0 0 0)
    (if (= (evex-m o) 0)
        (evex-put o e evex-lane-value (evex-freeze (load-n e (evex-ea s))) 0 0 0 0 0 0)
      (evex-put o e evex-lane-element e (evex-ea s) 0 0 0 0 0))))
(defun evex-broadcast (e o) (evex-broadcast-of e o (evex-sources o)))

(defun evex:VPBROADCASTB (o) (evex-broadcast 8 o))
(defun evex:VPBROADCASTW (o) (evex-broadcast 16 o))
(defun evex:VPBROADCASTD (o) (evex-broadcast 32 o))
(defun evex:VPBROADCASTQ (o) (evex-broadcast 64 o))
(defun evex:VPBROADCASTBr (o) (evex-broadcast 8 o))
(defun evex:VPBROADCASTWr (o) (evex-broadcast 16 o))
(defun evex:VPBROADCASTDr (o) (evex-broadcast 32 o))
(defun evex:VPBROADCASTQr (o) (evex-broadcast 64 o))
(defun evex:VBROADCASTSS (o) (evex-broadcast 32 o))
(defun evex:VBROADCASTSD (o) (evex-broadcast 64 o))

(defun evex-lane-group (e n mode y _ _ _ i) (evex-y mode e y (mod i n)))

(defun evex-broadcast-group-of (e t o s)
  (evex-put o e evex-lane-group e (/ t e) (evex-mode o) (evex-value o e t s) 0 0 0))
(defun evex-broadcast-group (e t o)
  "the broadcast of a group of T bits, of lanes of E bits"
  (evex-broadcast-group-of e t o (evex-sources o)))

(defun evex:VBROADCASTI32X2 (o) (evex-broadcast-group 32 64 o))
(defun evex:VBROADCASTF32X2 (o) (evex-broadcast-group 32 64 o))
(defun evex:VBROADCASTI32X4 (o) (evex-broadcast-group 32 128 o))
(defun evex:VBROADCASTF32X4 (o) (evex-broadcast-group 32 128 o))
(defun evex:VBROADCASTI32X8 (o) (evex-broadcast-group 32 256 o))
(defun evex:VBROADCASTF32X8 (o) (evex-broadcast-group 32 256 o))
(defun evex:VBROADCASTI64X2 (o) (evex-broadcast-group 64 128 o))
(defun evex:VBROADCASTF64X2 (o) (evex-broadcast-group 64 128 o))
(defun evex:VBROADCASTI64X4 (o) (evex-broadcast-group 64 256 o))
(defun evex:VBROADCASTF64X4 (o) (evex-broadcast-group 64 256 o))

(defun evex-mask-low (e o n)
  (evex-put o e evex-lane-value (evex-freeze (cast-unsigned e (cast-low n (car (evex-sources o))))) 0 0 0 0 0 0))

(defun evex:VPBROADCASTMB2Q (o) (evex-mask-low 64 o 8))
(defun evex:VPBROADCASTMW2D (o) (evex-mask-low 32 o 16))

;; the arithmetic and the logic of the lanes

(defun lane-and (x y) (logand x y))
(defun lane-or (x y) (logor x y))
(defun lane-xor (x y) (logxor x y))
(defun lane-andn (x y) (logand (lnot x) y))

(defun evex:VPADDB (o) (evex-binary lane-add 8 o))
(defun evex:VPADDW (o) (evex-binary lane-add 16 o))
(defun evex:VPADDD (o) (evex-binary lane-add 32 o))
(defun evex:VPADDQ (o) (evex-binary lane-add 64 o))
(defun evex:VPSUBB (o) (evex-binary lane-sub 8 o))
(defun evex:VPSUBW (o) (evex-binary lane-sub 16 o))
(defun evex:VPSUBD (o) (evex-binary lane-sub 32 o))
(defun evex:VPSUBQ (o) (evex-binary lane-sub 64 o))
(defun evex:VPADDSB (o) (evex-binary add-ssat 8 o))
(defun evex:VPADDSW (o) (evex-binary add-ssat 16 o))
(defun evex:VPADDUSB (o) (evex-binary add-usat 8 o))
(defun evex:VPADDUSW (o) (evex-binary add-usat 16 o))
(defun evex:VPSUBSB (o) (evex-binary sub-ssat 8 o))
(defun evex:VPSUBSW (o) (evex-binary sub-ssat 16 o))
(defun evex:VPSUBUSB (o) (evex-binary sub-usat 8 o))
(defun evex:VPSUBUSW (o) (evex-binary sub-usat 16 o))
(defun evex:VPMULLW (o) (evex-binary mul-low 16 o))
(defun evex:VPMULLD (o) (evex-binary mul-low 32 o))
(defun evex:VPMULLQ (o) (evex-binary mul-low 64 o))
(defun evex:VPMULHW (o) (evex-binary mul-high-signed 16 o))
(defun evex:VPMULHUW (o) (evex-binary mul-high-unsigned 16 o))
(defun evex:VPMULHRSW (o) (evex-binary mul-high-round 16 o))
(defun evex:VPAVGB (o) (evex-binary lane-avg 8 o))
(defun evex:VPAVGW (o) (evex-binary lane-avg 16 o))
(defun evex:VPMINUB (o) (evex-binary lane-minu 8 o))
(defun evex:VPMINUW (o) (evex-binary lane-minu 16 o))
(defun evex:VPMINUD (o) (evex-binary lane-minu 32 o))
(defun evex:VPMINUQ (o) (evex-binary lane-minu 64 o))
(defun evex:VPMINSB (o) (evex-binary lane-mins 8 o))
(defun evex:VPMINSW (o) (evex-binary lane-mins 16 o))
(defun evex:VPMINSD (o) (evex-binary lane-mins 32 o))
(defun evex:VPMINSQ (o) (evex-binary lane-mins 64 o))
(defun evex:VPMAXUB (o) (evex-binary lane-maxu 8 o))
(defun evex:VPMAXUW (o) (evex-binary lane-maxu 16 o))
(defun evex:VPMAXUD (o) (evex-binary lane-maxu 32 o))
(defun evex:VPMAXUQ (o) (evex-binary lane-maxu 64 o))
(defun evex:VPMAXSB (o) (evex-binary lane-maxs 8 o))
(defun evex:VPMAXSW (o) (evex-binary lane-maxs 16 o))
(defun evex:VPMAXSD (o) (evex-binary lane-maxs 32 o))
(defun evex:VPMAXSQ (o) (evex-binary lane-maxs 64 o))
(defun evex:VPANDD (o) (evex-binary lane-and 32 o))
(defun evex:VPANDQ (o) (evex-binary lane-and 64 o))
(defun evex:VPANDND (o) (evex-binary lane-andn 32 o))
(defun evex:VPANDNQ (o) (evex-binary lane-andn 64 o))
(defun evex:VPORD (o) (evex-binary lane-or 32 o))
(defun evex:VPORQ (o) (evex-binary lane-or 64 o))
(defun evex:VPXORD (o) (evex-binary lane-xor 32 o))
(defun evex:VPXORQ (o) (evex-binary lane-xor 64 o))
(defun evex:VANDPS (o) (evex-binary lane-and 32 o))
(defun evex:VANDPD (o) (evex-binary lane-and 64 o))
(defun evex:VANDNPS (o) (evex-binary lane-andn 32 o))
(defun evex:VANDNPD (o) (evex-binary lane-andn 64 o))
(defun evex:VORPS (o) (evex-binary lane-or 32 o))
(defun evex:VORPD (o) (evex-binary lane-or 64 o))
(defun evex:VXORPS (o) (evex-binary lane-xor 32 o))
(defun evex:VXORPD (o) (evex-binary lane-xor 64 o))
(defun evex:VPMADDWD (o) (evex-binary madd-words 32 o))
(defun evex:VPMADDUBSW (o) (evex-binary madd-ubsw 16 o))
(defun evex:VPSADBW (o) (evex-binary sad-bytes 64 o))

(defun lane-mul-signed (x y)
  (* (cast-signed 64 (cast-low 32 x)) (cast-signed 64 (cast-low 32 y))))
(defun lane-mul-unsigned (x y)
  (* (cast-unsigned 64 (cast-low 32 x)) (cast-unsigned 64 (cast-low 32 y))))

(defun evex:VPMULDQ (o) (evex-binary lane-mul-signed 64 o))
(defun evex:VPMULUDQ (o) (evex-binary lane-mul-unsigned 64 o))

(defun lane-abs1 (x) (if (msb x) (neg x) x))

(defun evex:VPABSB (o) (evex-unary lane-abs1 8 o))
(defun evex:VPABSW (o) (evex-unary lane-abs1 16 o))
(defun evex:VPABSD (o) (evex-unary lane-abs1 32 o))
(defun evex:VPABSQ (o) (evex-unary lane-abs1 64 o))

(defun evex-popcount-from (x i)
  (if (= i 0) (cast-unsigned (word-width x) (select 0 x))
    (+ (cast-unsigned (word-width x) (select i x)) (evex-popcount-from x (- i 1)))))
(defun lane-popcount (x) (evex-popcount-from x (- (word-width x) 1)))

(defun lane-clz (x) (cast-low (word-width x) (clz x)))

(defun evex:VPOPCNTB (o) (evex-unary lane-popcount 8 o))
(defun evex:VPOPCNTW (o) (evex-unary lane-popcount 16 o))
(defun evex:VPOPCNTD (o) (evex-unary lane-popcount 32 o))
(defun evex:VPOPCNTQ (o) (evex-unary lane-popcount 64 o))
(defun evex:VPLZCNTD (o) (evex-unary lane-clz 32 o))
(defun evex:VPLZCNTQ (o) (evex-unary lane-clz 64 o))

;; the shifts: by the counts of the lanes of a source, by the one count
;; in the low quadword of a source, and by an immediate, of a source
;; that can be memory

(defun lane-rol (x c)
  (let ((w (word-width x))
        (n (logand c (- (cast-unsigned w (resize 8 w)) 1:1))))
    (logor (lshift x n) (rshift x (- (cast-unsigned w (resize 8 w)) n)))))
(defun lane-ror (x c)
  (let ((w (word-width x))
        (n (logand c (- (cast-unsigned w (resize 8 w)) 1:1))))
    (logor (rshift x n) (lshift x (- (cast-unsigned w (resize 8 w)) n)))))

(defun evex:VPSLLVW (o) (evex-binary lane-sll 16 o))
(defun evex:VPSLLVD (o) (evex-binary lane-sll 32 o))
(defun evex:VPSLLVQ (o) (evex-binary lane-sll 64 o))
(defun evex:VPSRLVW (o) (evex-binary lane-srl 16 o))
(defun evex:VPSRLVD (o) (evex-binary lane-srl 32 o))
(defun evex:VPSRLVQ (o) (evex-binary lane-srl 64 o))
(defun evex:VPSRAVW (o) (evex-binary lane-sra 16 o))
(defun evex:VPSRAVD (o) (evex-binary lane-sra 32 o))
(defun evex:VPSRAVQ (o) (evex-binary lane-sra 64 o))
(defun evex:VPROLVD (o) (evex-binary lane-rol 32 o))
(defun evex:VPROLVQ (o) (evex-binary lane-rol 64 o))
(defun evex:VPRORVD (o) (evex-binary lane-ror 32 o))
(defun evex:VPRORVQ (o) (evex-binary lane-ror 64 o))

(defun evex-imm-count (e imm)
  (cast-unsigned e (cast-low 8 imm)))

(defun evex-shift-imm (f e o)
  (evex-put o e evex-lane-with f e (evex-mode o) (evex-src o e (evex-sources o))
            (evex-imm-count e (evex-imm o)) 0 0))

(defun evex-lane-count (f e x c _ _ _ i) (f (evex-lane e x i) c))

(defun evex-count-source (o s)
  (if (= (evex-mem o) 0) (cast-low 64 (car s))
    (evex-freeze (load-n 64 (evex-ea s)))))

(defun evex-shift-count-of (f e o s)
  (evex-put o e evex-lane-count f e (car s)
            (evex-freeze (clamped-count e (evex-count-source o (cdr s)))) 0 0 0))
(defun evex-shift-count (f e o) (evex-shift-count-of f e o (evex-sources o)))

(defun evex-shift (f e o)
  "(RD Y IMM), or (RD X C) with the count in a register or memory"
  (if (evex-imm-form o) (evex-shift-imm f e o) (evex-shift-count f e o)))

(defun evex:VPSLLW (o) (evex-shift lane-sll 16 o))
(defun evex:VPSLLD (o) (evex-shift lane-sll 32 o))
(defun evex:VPSLLQ (o) (evex-shift lane-sll 64 o))
(defun evex:VPSRLW (o) (evex-shift lane-srl 16 o))
(defun evex:VPSRLD (o) (evex-shift lane-srl 32 o))
(defun evex:VPSRLQ (o) (evex-shift lane-srl 64 o))
(defun evex:VPSRAW (o) (evex-shift lane-sra 16 o))
(defun evex:VPSRAD (o) (evex-shift lane-sra 32 o))
(defun evex:VPSRAQ (o) (evex-shift lane-sra 64 o))
(defun evex:VPROLD (o) (evex-shift-imm lane-rol 32 o))
(defun evex:VPROLQ (o) (evex-shift-imm lane-rol 64 o))
(defun evex:VPRORD (o) (evex-shift-imm lane-ror 32 o))
(defun evex:VPRORQ (o) (evex-shift-imm lane-ror 64 o))

(defun evex-byte-shift (f o)
  (evex-put o 128 evex-lane-with f 128 (evex-mode o) (evex-src o 128 (evex-sources o))
            (cast-low 8 (evex-imm o)) 0 0))

(defun evex:VPSLLDQ (o) (evex-byte-shift pslldq-lane o))
(defun evex:VPSRLDQ (o) (evex-byte-shift psrldq-lane o))

;; the concatenated shifts

(defun lane-shld (x y c)
  (let ((w (word-width x))
        (n (logand (cast-unsigned w c) (- (cast-unsigned w (resize 8 w)) 1:1))))
    (cast-high w (lshift (concat x y) (cast-unsigned (* 2 w) n)))))
(defun lane-shrd (x y c)
  (let ((w (word-width x))
        (n (logand (cast-unsigned w c) (- (cast-unsigned w (resize 8 w)) 1:1))))
    (cast-low w (rshift (concat y x) (cast-unsigned (* 2 w) n)))))

(defun evex-concat-imm-of (f e o s)
  (evex-put o e evex-lane-binary-imm f e (car s) (evex-mode o) (evex-src o e (cdr s))
            (cast-low 8 (evex-imm o)) 0))
(defun evex-concat-imm (f e o) (evex-concat-imm-of f e o (evex-sources o)))

(defun evex:VPSHLDW (o) (evex-concat-imm lane-shld 16 o))
(defun evex:VPSHLDD (o) (evex-concat-imm lane-shld 32 o))
(defun evex:VPSHLDQ (o) (evex-concat-imm lane-shld 64 o))
(defun evex:VPSHRDW (o) (evex-concat-imm lane-shrd 16 o))
(defun evex:VPSHRDD (o) (evex-concat-imm lane-shrd 32 o))
(defun evex:VPSHRDQ (o) (evex-concat-imm lane-shrd 64 o))
(defun evex:VPSHLDVW (o) (evex-ternary lane-shld 16 o))
(defun evex:VPSHLDVD (o) (evex-ternary lane-shld 32 o))
(defun evex:VPSHLDVQ (o) (evex-ternary lane-shld 64 o))
(defun evex:VPSHRDVW (o) (evex-ternary lane-shrd 16 o))
(defun evex:VPSHRDVD (o) (evex-ternary lane-shrd 32 o))
(defun evex:VPSHRDVQ (o) (evex-ternary lane-shrd 64 o))

;; VPTERNLOG: each bit of the result is the bit of the immediate whose
;; index is the bits of the three sources

(defun evex-spread (w bit) (cast-signed w bit))

(defun lane-ternlog (x y z imm)
  (let ((t (cast-low 8 imm))
        (w (word-width x)))
    (logor (logand (evex-spread w (select 7 t)) x y z)
           (logand (evex-spread w (select 6 t)) x y (lnot z))
           (logand (evex-spread w (select 5 t)) x (lnot y) z)
           (logand (evex-spread w (select 4 t)) x (lnot y) (lnot z))
           (logand (evex-spread w (select 3 t)) (lnot x) y z)
           (logand (evex-spread w (select 2 t)) (lnot x) y (lnot z))
           (logand (evex-spread w (select 1 t)) (lnot x) (lnot y) z)
           (logand (evex-spread w (select 0 t)) (lnot x) (lnot y) (lnot z)))))

(defun evex:VPTERNLOGD (o) (evex-ternary-imm lane-ternlog 32 o))
(defun evex:VPTERNLOGQ (o) (evex-ternary-imm lane-ternlog 64 o))

;; the comparisons, whose results are the bits of a mask register

(defun lane-eq1 (x y) (= x y))
(defun lane-gt1 (x y) (s> x y))
(defun lane-test (x y) (non-zero (logand x y)))
(defun lane-testn (x y) (is-zero (logand x y)))

(defun lane-compare-signed (x y imm)
  (case (logand imm 7)
    0 (= x y)
    1 (s< x y)
    2 (s<= x y)
    3 0:1
    4 (/= x y)
    5 (s>= x y)
    6 (s> x y)
    1:1))

(defun lane-compare-unsigned (x y imm)
  (case (logand imm 7)
    0 (= x y)
    1 (< x y)
    2 (<= x y)
    3 0:1
    4 (/= x y)
    5 (>= x y)
    6 (> x y)
    1:1))

(defun evex:VPCMPEQB (o) (evex-test lane-eq1 8 o))
(defun evex:VPCMPEQW (o) (evex-test lane-eq1 16 o))
(defun evex:VPCMPEQD (o) (evex-test lane-eq1 32 o))
(defun evex:VPCMPEQQ (o) (evex-test lane-eq1 64 o))
(defun evex:VPCMPGTB (o) (evex-test lane-gt1 8 o))
(defun evex:VPCMPGTW (o) (evex-test lane-gt1 16 o))
(defun evex:VPCMPGTD (o) (evex-test lane-gt1 32 o))
(defun evex:VPCMPGTQ (o) (evex-test lane-gt1 64 o))
(defun evex:VPCMPB (o) (evex-test-imm lane-compare-signed 8 o))
(defun evex:VPCMPW (o) (evex-test-imm lane-compare-signed 16 o))
(defun evex:VPCMPD (o) (evex-test-imm lane-compare-signed 32 o))
(defun evex:VPCMPQ (o) (evex-test-imm lane-compare-signed 64 o))
(defun evex:VPCMPUB (o) (evex-test-imm lane-compare-unsigned 8 o))
(defun evex:VPCMPUW (o) (evex-test-imm lane-compare-unsigned 16 o))
(defun evex:VPCMPUD (o) (evex-test-imm lane-compare-unsigned 32 o))
(defun evex:VPCMPUQ (o) (evex-test-imm lane-compare-unsigned 64 o))
(defun evex:VPTESTMB (o) (evex-test lane-test 8 o))
(defun evex:VPTESTMW (o) (evex-test lane-test 16 o))
(defun evex:VPTESTMD (o) (evex-test lane-test 32 o))
(defun evex:VPTESTMQ (o) (evex-test lane-test 64 o))
(defun evex:VPTESTNMB (o) (evex-test lane-testn 8 o))
(defun evex:VPTESTNMW (o) (evex-test lane-testn 16 o))
(defun evex:VPTESTNMD (o) (evex-test lane-testn 32 o))
(defun evex:VPTESTNMQ (o) (evex-test lane-testn 64 o))

;; between the vectors and the masks

(defun evex-lane-sign (e x _ _ _ _ _ i) (msb (evex-lane e x i)))
(defun evex-lane-of-bit (e k _ _ _ _ _ i) (cast-signed e (select i k)))

(defun evex-to-mask (e o)
  (set$ (evex-rd o)
        (cast-unsigned 64 (evex-bits 0 0 evex-lane-sign e (evex-nth 1 (evex-ops o)) 0 0 0 0 0 0 (evex-count o e)))))

(defun evex-from-mask (e o)
  (set-vex (evex-rd o)
           (evex-lanes 0 0 0 e evex-lane-of-bit e (evex-nth 1 (evex-ops o)) 0 0 0 0 0 0 (evex-count o e))))

(defun evex:VPMOVB2M (o) (evex-to-mask 8 o))
(defun evex:VPMOVW2M (o) (evex-to-mask 16 o))
(defun evex:VPMOVD2M (o) (evex-to-mask 32 o))
(defun evex:VPMOVQ2M (o) (evex-to-mask 64 o))
(defun evex:VPMOVM2B (o) (evex-from-mask 8 o))
(defun evex:VPMOVM2W (o) (evex-from-mask 16 o))
(defun evex:VPMOVM2D (o) (evex-from-mask 32 o))
(defun evex:VPMOVM2Q (o) (evex-from-mask 64 o))

;; the blends by a mask: their operands have the destination once, the
;; first source is what merging keeps

(defun evex-blend-of (e o s)
  (set-vex (evex-rd o)
           (evex-lanes (evex-m o) (evex-k-once o) (car s) e
                       evex-lane-move e (evex-mode o) (evex-src o e (cdr s)) 0 0 0 0
                       0 (evex-count o e))))
(defun evex-blend (e o) (evex-blend-of e o (evex-sources-once o)))

(defun evex:VPBLENDMB (o) (evex-blend 8 o))
(defun evex:VPBLENDMW (o) (evex-blend 16 o))
(defun evex:VPBLENDMD (o) (evex-blend 32 o))
(defun evex:VPBLENDMQ (o) (evex-blend 64 o))
(defun evex:VBLENDMPS (o) (evex-blend 32 o))
(defun evex:VBLENDMPD (o) (evex-blend 64 o))

;; the extensions, of the lanes of a shorter source

(defun evex-extend-signed (n x) (cast-signed n x))
(defun evex-extend-unsigned (n x) (cast-unsigned n x))
(defun evex-lane-extended (cast es ed mode y _ _ i) (cast ed (evex-y mode es y i)))

(defun evex-extend (cast es ed o)
  (evex-put o ed evex-lane-extended cast es ed (evex-mode o)
            (evex-value o es (* (evex-count o ed) es) (evex-sources o)) 0 0))

(defun evex:VPMOVZXBW (o) (evex-extend evex-extend-unsigned 8 16 o))
(defun evex:VPMOVZXBD (o) (evex-extend evex-extend-unsigned 8 32 o))
(defun evex:VPMOVZXBQ (o) (evex-extend evex-extend-unsigned 8 64 o))
(defun evex:VPMOVZXWD (o) (evex-extend evex-extend-unsigned 16 32 o))
(defun evex:VPMOVZXWQ (o) (evex-extend evex-extend-unsigned 16 64 o))
(defun evex:VPMOVZXDQ (o) (evex-extend evex-extend-unsigned 32 64 o))
(defun evex:VPMOVSXBW (o) (evex-extend evex-extend-signed 8 16 o))
(defun evex:VPMOVSXBD (o) (evex-extend evex-extend-signed 8 32 o))
(defun evex:VPMOVSXBQ (o) (evex-extend evex-extend-signed 8 64 o))
(defun evex:VPMOVSXWD (o) (evex-extend evex-extend-signed 16 32 o))
(defun evex:VPMOVSXWQ (o) (evex-extend evex-extend-signed 16 64 o))
(defun evex:VPMOVSXDQ (o) (evex-extend evex-extend-signed 32 64 o))

;; the truncations, to a register whose upper bits are cleared, or to
;; memory

(defun lane-truncate (e x) (cast-low e x))
(defun lane-saturate-signed (e x) (cast-saturate :signed e x))
(defun lane-saturate-unsigned (e x)
  (if (non-zero (rshift x (cast-unsigned (word-width x) e)))
      (ones e)
    (cast-low e x)))

(defun evex-narrow-store-lane (f es ed a k m x i)
  (when (if (= m 0) 1:1 (select i k))
    (store-n ed (evex-address ed a i) (f ed (evex-lane es x i)))))

(defun evex-narrow-lane (f es ed x _ _ _ i) (f ed (evex-lane es x i)))

(defun evex-narrow-store-of (f es ed o ops)
  (evex-each evex-narrow-store-lane f es ed (evex-ea ops)
             (if (= (evex-m o) 0) 0 (evex-nth 5 ops)) (evex-m o) (evex-last ops)
             0 (evex-count o es)))

(defun evex-narrow (f es ed o)
  (if (= (evex-mem o) 3)
      (evex-narrow-store-of f es ed o (evex-ops o))
    (evex-put-n o ed (evex-count o es) evex-narrow-lane f es ed (car (evex-sources o)) 0 0 0)))

(defun evex:VPMOVWB (o) (evex-narrow lane-truncate 16 8 o))
(defun evex:VPMOVDB (o) (evex-narrow lane-truncate 32 8 o))
(defun evex:VPMOVDW (o) (evex-narrow lane-truncate 32 16 o))
(defun evex:VPMOVQB (o) (evex-narrow lane-truncate 64 8 o))
(defun evex:VPMOVQW (o) (evex-narrow lane-truncate 64 16 o))
(defun evex:VPMOVQD (o) (evex-narrow lane-truncate 64 32 o))
(defun evex:VPMOVSWB (o) (evex-narrow lane-saturate-signed 16 8 o))
(defun evex:VPMOVSDB (o) (evex-narrow lane-saturate-signed 32 8 o))
(defun evex:VPMOVSDW (o) (evex-narrow lane-saturate-signed 32 16 o))
(defun evex:VPMOVSQB (o) (evex-narrow lane-saturate-signed 64 8 o))
(defun evex:VPMOVSQW (o) (evex-narrow lane-saturate-signed 64 16 o))
(defun evex:VPMOVSQD (o) (evex-narrow lane-saturate-signed 64 32 o))
(defun evex:VPMOVUSWB (o) (evex-narrow lane-saturate-unsigned 16 8 o))
(defun evex:VPMOVUSDB (o) (evex-narrow lane-saturate-unsigned 32 8 o))
(defun evex:VPMOVUSDW (o) (evex-narrow lane-saturate-unsigned 32 16 o))
(defun evex:VPMOVUSQB (o) (evex-narrow lane-saturate-unsigned 64 8 o))
(defun evex:VPMOVUSQW (o) (evex-narrow lane-saturate-unsigned 64 16 o))
(defun evex:VPMOVUSQD (o) (evex-narrow lane-saturate-unsigned 64 32 o))

;; the shuffles in each group of 128 bits. A lane has an index in its
;; group, and an index by which the group starts.

(defun evex-group-start (n i) (* n (/ i n)))

(defun evex-select-imm (bits n imm i)
  "the field of BITS bits of IMM for the lane I, of N lanes of a group"
  (logand (rshift imm (* bits (mod i n))) (- (lshift 1 bits) 1)))

(defun evex-lane-shuffled (e n bits imm mode y _ i)
  (evex-y mode e y (+ (evex-group-start n i) (evex-select-imm bits n imm i))))

(defun evex-shuffle-imm (e bits o)
  "(RD Y IMM): the lanes of a group of Y by the fields of the immediate"
  (evex-put o e evex-lane-shuffled e (/ 128 e) bits (evex-imm o) (evex-mode o)
            (evex-src o e (evex-sources o)) 0))

(defun evex:VPSHUFD (o) (evex-shuffle-imm 32 2 o))

(defun evex-lane-shufw-low (imm mode y _ _ _ _ i)
  (if (< (mod i 8) 4)
      (evex-y mode 16 y (+ (evex-group-start 8 i) (evex-select-imm 2 4 imm i)))
    (evex-y mode 16 y i)))

(defun evex-lane-shufw-high (imm mode y _ _ _ _ i)
  (if (< (mod i 8) 4)
      (evex-y mode 16 y i)
    (evex-y mode 16 y (+ (evex-group-start 8 i) 4 (evex-select-imm 2 4 imm i)))))

(defun evex-shufw-low (o)
  (evex-put o 16 evex-lane-shufw-low (evex-imm o) (evex-mode o) (evex-src o 16 (evex-sources o)) 0 0 0 0))

(defun evex-shufw-high (o)
  (evex-put o 16 evex-lane-shufw-high (evex-imm o) (evex-mode o) (evex-src o 16 (evex-sources o)) 0 0 0 0))

(defun evex:VPSHUFLW (o) (evex-shufw-low o))
(defun evex:VPSHUFHW (o) (evex-shufw-high o))

(defun evex-lane-shuffle-byte (x mode y _ _ _ _ i)
  (shuffle-byte (evex-lane 128 x (/ i 16)) (evex-y mode 8 y i)))

(defun evex-bytes-of-group-of (o s)
  (evex-put o 8 evex-lane-shuffle-byte (car s) (evex-mode o) (evex-src o 8 (cdr s)) 0 0 0 0))
(defun evex-bytes-of-group (o) (evex-bytes-of-group-of o (evex-sources o)))

(defun evex:VPSHUFB (o) (evex-bytes-of-group o))

(defun evex-lane-permil-pd (x mode c _ _ _ _ i)
  (select-lane 64 (evex-lane 128 x (/ i 2))
               (cast-unsigned 128 (select 1 (evex-y mode 64 c i)))))

(defun evex-permil-pd-control-of (o s)
  (evex-put o 64 evex-lane-permil-pd (car s) (evex-mode o) (evex-src o 64 (cdr s)) 0 0 0 0))
(defun evex-permil-pd-control (o)
  "(RD X C): the lane of each group by the bit 1 of the lane of C"
  (evex-permil-pd-control-of o (evex-sources o)))

(defun evex-lane-permil-ps (x mode c _ _ _ _ i)
  (select-lane 32 (evex-lane 128 x (/ i 4))
               (cast-unsigned 128 (logand (evex-y mode 32 c i) 3:32))))

(defun evex-permil-ps-control-of (o s)
  (evex-put o 32 evex-lane-permil-ps (car s) (evex-mode o) (evex-src o 32 (cdr s)) 0 0 0 0))
(defun evex-permil-ps-control (o) (evex-permil-ps-control-of o (evex-sources o)))

(defun evex-lane-permil-pd-imm (imm mode y _ _ _ _ i)
  (evex-y mode 64 y (+ (evex-group-start 2 i) (logand (rshift imm i) 1))))

(defun evex-permil-pd-imm (o)
  (evex-put o 64 evex-lane-permil-pd-imm (evex-imm o) (evex-mode o) (evex-src o 64 (evex-sources o)) 0 0 0 0))

(defun evex:VPERMILPS (o) (if (evex-imm-form o) (evex-shuffle-imm 32 2 o) (evex-permil-ps-control o)))
(defun evex:VPERMILPD (o) (if (evex-imm-form o) (evex-permil-pd-imm o) (evex-permil-pd-control o)))

(defun evex-lane-shufps (x mode y imm _ _ _ i)
  (let ((j (+ (evex-group-start 4 i) (evex-select-imm 2 4 imm i))))
    (if (< (mod i 4) 2) (evex-lane 32 x j) (evex-y mode 32 y j))))

(defun evex-shufps-of (o s)
  (evex-put o 32 evex-lane-shufps (car s) (evex-mode o) (evex-src o 32 (cdr s)) (evex-imm o) 0 0 0))
(defun evex-shufps (o) (evex-shufps-of o (evex-sources o)))

(defun evex-lane-shufpd (x mode y imm _ _ _ i)
  (let ((j (+ (evex-group-start 2 i) (logand (rshift imm i) 1))))
    (if (= (mod i 2) 0) (evex-lane 64 x j) (evex-y mode 64 y j))))

(defun evex-shufpd-of (o s)
  (evex-put o 64 evex-lane-shufpd (car s) (evex-mode o) (evex-src o 64 (cdr s)) (evex-imm o) 0 0 0))
(defun evex-shufpd (o) (evex-shufpd-of o (evex-sources o)))

(defun evex:VSHUFPS (o) (evex-shufps o))
(defun evex:VSHUFPD (o) (evex-shufpd o))

(defun evex-lane-unpack (high e n x mode y _ i)
  (let ((j (+ (evex-group-start n i) (/ (mod i n) 2) (if high (/ n 2) 0))))
    (if (= (mod i 2) 0) (evex-lane e x j) (evex-y mode e y j))))

(defun evex-unpack-of (high e o s)
  (evex-put o e evex-lane-unpack high e (/ 128 e) (car s) (evex-mode o) (evex-src o e (cdr s)) 0))
(defun evex-unpack (high e o)
  "the lanes of the low or high half of each group, of X and Y in turn"
  (evex-unpack-of high e o (evex-sources o)))

(defun evex:VPUNPCKLBW (o) (evex-unpack false 8 o))
(defun evex:VPUNPCKLWD (o) (evex-unpack false 16 o))
(defun evex:VPUNPCKLDQ (o) (evex-unpack false 32 o))
(defun evex:VPUNPCKLQDQ (o) (evex-unpack false 64 o))
(defun evex:VPUNPCKHBW (o) (evex-unpack true 8 o))
(defun evex:VPUNPCKHWD (o) (evex-unpack true 16 o))
(defun evex:VPUNPCKHDQ (o) (evex-unpack true 32 o))
(defun evex:VPUNPCKHQDQ (o) (evex-unpack true 64 o))
(defun evex:VUNPCKLPS (o) (evex-unpack false 32 o))
(defun evex:VUNPCKLPD (o) (evex-unpack false 64 o))
(defun evex:VUNPCKHPS (o) (evex-unpack true 32 o))
(defun evex:VUNPCKHPD (o) (evex-unpack true 64 o))

(defun evex-lane-pack (kind es ed x mode y _ i)
  (let ((n (/ 128 ed))
        (half (/ n 2))
        (j (+ (* half (/ i n)) (mod (mod i n) half))))
    (cast-saturate kind ed (if (< (mod i n) half) (evex-lane es x j) (evex-y mode es y j)))))

(defun evex-pack-of (kind es ed o s)
  (evex-put o ed evex-lane-pack kind es ed (car s) (evex-mode o) (evex-src o es (cdr s)) 0))
(defun evex-pack (kind es ed o)
  "the saturated lanes of X in the low half of each group, of Y in the high"
  (evex-pack-of kind es ed o (evex-sources o)))

(defun evex:VPACKSSWB (o) (evex-pack :signed 16 8 o))
(defun evex:VPACKSSDW (o) (evex-pack :signed 32 16 o))
(defun evex:VPACKUSWB (o) (evex-pack :unsigned 16 8 o))
(defun evex:VPACKUSDW (o) (evex-pack :unsigned 32 16 o))

(defun evex-lane-palignr (x y c _ _ _ _ i)
  (evex-lane 8
             (cast-low 128 (rshift (concat (evex-lane 128 x (/ i 16)) (evex-lane 128 y (/ i 16))) c))
             (mod i 16)))

(defun evex-palignr-of (o s)
  (evex-put o 8 evex-lane-palignr (car s) (evex-full o 8 (cdr s))
            (cast-unsigned 256 (* 8 (cast-unsigned 16 (cast-low 8 (evex-imm o))))) 0 0 0 0))
(defun evex-palignr (o) (evex-palignr-of o (evex-sources o)))

(defun evex:VPALIGNR (o) (evex-palignr o))

(defun evex-aligned (o e x y)
  (evex-freeze
   (cast-low (evex-w o)
             (rshift (concat x y)
                     (cast-unsigned (* 2 (evex-w o))
                                    (* e (logand (evex-imm o) (- (evex-count o e) 1))))))))

(defun evex-align-of (e o s)
  (evex-put o e evex-lane-move e 0 (evex-aligned o e (car s) (evex-full o e (cdr s))) 0 0 0 0))
(defun evex-align (e o) (evex-align-of e o (evex-sources o)))

(defun evex:VALIGND (o) (evex-align 32 o))
(defun evex:VALIGNQ (o) (evex-align 64 o))

;; the permutations of all the lanes

(defun evex-dyn (e x idx)
  "(evex-dyn E X IDX) is the lane of X at the unknown index IDX"
  (let ((w (word-width x)))
    (cast-low e (rshift x (* (cast-unsigned w idx) (cast-unsigned w (resize 16 e)))))))

(defun evex-lane-perm (e n c y _ _ _ i)
  (evex-dyn e y (logand (evex-lane e c i) (resize e (- n 1)))))

(defun evex-perm-of (e o s)
  (evex-put o e evex-lane-perm e (evex-count o e) (car s) (evex-full o e (cdr s)) 0 0 0))
(defun evex-perm (e o)
  "(RD C Y): the lanes of Y by the lanes of C"
  (evex-perm-of e o (evex-sources o)))

(defun evex-perm-imm (o)
  "(RD Y IMM): the 64-bit lanes of each group of 256 bits by the immediate"
  (evex-put o 64 evex-lane-shuffled 64 4 2 (evex-imm o) (evex-mode o)
            (evex-src o 64 (evex-sources o)) 0))

(defun evex-perm64 (o)
  (if (evex-imm-form o) (evex-perm-imm o) (evex-perm 64 o)))

(defun evex:VPERMB (o) (evex-perm 8 o))
(defun evex:VPERMW (o) (evex-perm 16 o))
(defun evex:VPERMD (o) (evex-perm 32 o))
(defun evex:VPERMPS (o) (evex-perm 32 o))
(defun evex:VPERMQ (o) (evex-perm64 o))
(defun evex:VPERMPD (o) (evex-perm64 o))

(defun evex-two-tables (e n a b idx)
  "the lane of the two tables A and B, of N lanes each, at the index IDX"
  (let ((j (logand idx (resize e (- n 1)))))
    (if (non-zero (logand idx (resize e n)))
        (evex-dyn e b j)
      (evex-dyn e a j))))

(defun evex-lane-two-tables (e n a b c _ _ i)
  (evex-two-tables e n a b (evex-lane e c i)))

(defun evex-permi2-of (e o s)
  (evex-put-tied o e evex-lane-two-tables e (evex-count o e) (car s) (evex-full o e (cdr s)) (evex-pass o) 0 0))
(defun evex-permi2 (e o)
  "(RD C A B), with C = RD: the lanes of the tables A and B by C"
  (evex-permi2-of e o (evex-sources-tied o)))

(defun evex-permt2-of (e o s)
  (evex-put-tied o e evex-lane-two-tables e (evex-count o e) (evex-pass o) (evex-full o e (cdr s)) (car s) 0 0))
(defun evex-permt2 (e o)
  "(RD A C B), with A = RD: the lanes of the tables A and B by C"
  (evex-permt2-of e o (evex-sources-tied o)))

(defun evex:VPERMI2B (o) (evex-permi2 8 o))
(defun evex:VPERMI2W (o) (evex-permi2 16 o))
(defun evex:VPERMI2D (o) (evex-permi2 32 o))
(defun evex:VPERMI2Q (o) (evex-permi2 64 o))
(defun evex:VPERMI2PS (o) (evex-permi2 32 o))
(defun evex:VPERMI2PD (o) (evex-permi2 64 o))
(defun evex:VPERMT2B (o) (evex-permt2 8 o))
(defun evex:VPERMT2W (o) (evex-permt2 16 o))
(defun evex:VPERMT2D (o) (evex-permt2 32 o))
(defun evex:VPERMT2Q (o) (evex-permt2 64 o))
(defun evex:VPERMT2PS (o) (evex-permt2 32 o))
(defun evex:VPERMT2PD (o) (evex-permt2 64 o))

;; the groups as a whole

(defun evex-lane-shuf-group (e t w x mode y imm i)
  (let ((n (/ t e))
        (groups (/ w t))
        (bits (if (= groups 4) 2 1))
        (g (/ i n))
        (j (+ (* n (logand (rshift imm (* bits g)) (- (lshift 1 bits) 1)))
              (mod i n))))
    (if (< g (/ groups 2)) (evex-lane e x j) (evex-y mode e y j))))

(defun evex-shuf-group-of (e t o s)
  (evex-put o e evex-lane-shuf-group e t (evex-w o) (car s) (evex-mode o) (evex-src o e (cdr s)) (evex-imm o)))
(defun evex-shuf-group (e t o)
  "(RD X Y IMM): the low half of the groups of T bits are of X, the high
   half of Y, by the fields of the immediate"
  (evex-shuf-group-of e t o (evex-sources o)))

(defun evex:VSHUFI32X4 (o) (evex-shuf-group 32 128 o))
(defun evex:VSHUFF32X4 (o) (evex-shuf-group 32 128 o))
(defun evex:VSHUFI64X2 (o) (evex-shuf-group 64 128 o))
(defun evex:VSHUFF64X2 (o) (evex-shuf-group 64 128 o))

(defun evex-group-index (o t) (logand (evex-imm o) (- (/ (evex-w o) t) 1)))

(defun evex-extract-store-of (e t o ops)
  (if (= (evex-m o) 0)
      (store-n t (evex-ea ops) (evex-lane t (evex-nth 5 ops) (evex-group-index o t)))
    (evex-store-lanes (evex-ea ops) e (evex-nth 5 ops)
                      (evex-lane t (evex-nth 6 ops) (evex-group-index o t)) (/ t e))))

(defun evex-extract (e t o)
  "(RD X IMM), or a store: a group of T bits of X, of E-bit lanes"
  (if (= (evex-mem o) 3)
      (evex-extract-store-of e t o (evex-ops o))
    (evex-put-n o e (/ t e) evex-lane-move e 0
                (evex-lane t (car (evex-sources o)) (evex-group-index o t)) 0 0 0 0)))

(defun evex:VEXTRACTI32X4 (o) (evex-extract 32 128 o))
(defun evex:VEXTRACTF32X4 (o) (evex-extract 32 128 o))
(defun evex:VEXTRACTI32X8 (o) (evex-extract 32 256 o))
(defun evex:VEXTRACTF32X8 (o) (evex-extract 32 256 o))
(defun evex:VEXTRACTI64X2 (o) (evex-extract 64 128 o))
(defun evex:VEXTRACTF64X2 (o) (evex-extract 64 128 o))
(defun evex:VEXTRACTI64X4 (o) (evex-extract 64 256 o))
(defun evex:VEXTRACTF64X4 (o) (evex-extract 64 256 o))

(defun evex-lane-insert (e n g x mode y _ i)
  (if (= (/ i n) g) (evex-y mode e y (mod i n)) (evex-lane e x i)))

(defun evex-insert-of (e t o s)
  (evex-put o e evex-lane-insert e (/ t e) (evex-group-index o t) (car s) (evex-mode o)
            (evex-value o e t (cdr s)) 0))
(defun evex-insert (e t o)
  "(RD X Y IMM): X with a group of T bits, of E-bit lanes, replaced by Y"
  (evex-insert-of e t o (evex-sources o)))

(defun evex:VINSERTI32X4 (o) (evex-insert 32 128 o))
(defun evex:VINSERTF32X4 (o) (evex-insert 32 128 o))
(defun evex:VINSERTI32X8 (o) (evex-insert 32 256 o))
(defun evex:VINSERTF32X8 (o) (evex-insert 32 256 o))
(defun evex:VINSERTI64X2 (o) (evex-insert 64 128 o))
(defun evex:VINSERTF64X2 (o) (evex-insert 64 128 o))
(defun evex:VINSERTI64X4 (o) (evex-insert 64 256 o))
(defun evex:VINSERTF64X4 (o) (evex-insert 64 256 o))

;; compressing and expanding by a mask, which have an unknown position
;; for each lane

(defun evex-count-below (k i)
  "(evex-count-below K I) is the number of the set bits of K below I"
  (if (= i 0) 0:8
    (+ (evex-count-below k (- i 1)) (cast-unsigned 8 (select (- i 1) k)))))

(defun evex-select-nth-set (e x k n j i)
  "the lane of X of the first set bit from I, with J set bits below it"
  (if (= i n) (zeros e)
    (if (logand (select i k) (= j (evex-count-below k i)))
        (evex-lane e x i)
      (evex-select-nth-set e x k n j (+ i 1)))))

(defun evex-unsupported () (error "evex: a compressing store"))

(defun evex-lane-compress (e n m k pass y _ i)
  (if (< (resize 8 i) (evex-count-below k n))
      (evex-select-nth-set e y k n (resize 8 i) 0)
    (if (= m 1) (evex-lane e pass i) (zeros e))))

(defun evex-compress (e o)
  "(RD K Y): the lanes of Y whose bits are set, at the bottom"
  (if (= (evex-m o) 0) (evex-move e o)
    (if (= (evex-mem o) 3) (evex-unsupported)
      (set-vex (evex-rd o)
               (evex-lanes 0 0 0 e evex-lane-compress e (evex-count o e) (evex-m o) (evex-k o)
                           (evex-merged o) (car (evex-sources o)) 0 0 (evex-count o e))))))

(defun evex-lane-expand (e m k pass mem y a i)
  (if (select i k)
      (if (= mem 0)
          (evex-dyn e y (cast-unsigned e (evex-count-below k i)))
        (load-n e (+ a (* (/ e 8) (cast-unsigned (word-width a) (evex-count-below k i))))))
    (if (= m 1) (evex-lane e pass i) (zeros e))))

(defun evex-expand-of (e o s)
  (set-vex (evex-rd o)
           (evex-lanes 0 0 0 e evex-lane-expand e (evex-m o) (evex-k o) (evex-merged o) (evex-mem o)
                       (if (= (evex-mem o) 0) (car s) 0)
                       (if (= (evex-mem o) 0) 0 (evex-ea s))
                       0 (evex-count o e))))

(defun evex-expand (e o)
  "(RD K Y): the lanes of Y at the bottom go to the lanes whose bits are
   set, only those of memory are loaded"
  (if (= (evex-m o) 0) (evex-move e o) (evex-expand-of e o (evex-sources o))))

(defun evex:VPCOMPRESSB (o) (evex-compress 8 o))
(defun evex:VPCOMPRESSW (o) (evex-compress 16 o))
(defun evex:VPCOMPRESSD (o) (evex-compress 32 o))
(defun evex:VPCOMPRESSQ (o) (evex-compress 64 o))
(defun evex:VCOMPRESSPS (o) (evex-compress 32 o))
(defun evex:VCOMPRESSPD (o) (evex-compress 64 o))
(defun evex:VPEXPANDB (o) (evex-expand 8 o))
(defun evex:VPEXPANDW (o) (evex-expand 16 o))
(defun evex:VPEXPANDD (o) (evex-expand 32 o))
(defun evex:VPEXPANDQ (o) (evex-expand 64 o))
(defun evex:VEXPANDPS (o) (evex-expand 32 o))
(defun evex:VEXPANDPD (o) (evex-expand 64 o))

;; the floating point lanes, which are intrinsics as those of SSE are

(defun evex-lane-fp2 (f e x mode y _ _ i) (f e (evex-lane e x i) (evex-y mode e y i)))
(defun evex-lane-fp1 (f e mode y _ _ _ i) (f e (evex-y mode e y i)))
(defun evex-lane-fp-compare (e x mode y imm _ _ i)
  (fp-predicate e (evex-lane e x i) (evex-y mode e y i) imm))

(defun evex-fp-binary-of (f e o s)
  (evex-put o e evex-lane-fp2 f e (car s) (evex-mode o) (evex-src o e (cdr s)) 0 0))
(defun evex-fp-binary (f e o) (evex-fp-binary-of f e o (evex-sources o)))

(defun evex-fp-unary (f e o)
  (evex-put o e evex-lane-fp1 f e (evex-mode o) (evex-src o e (evex-sources o)) 0 0 0))

(defun evex-fp-compare-of (e o s)
  (evex-put-mask o e evex-lane-fp-compare e (car s) (evex-mode o) (evex-src o e (cdr s)) (evex-imm o) 0 0))
(defun evex-fp-compare (e o) (evex-fp-compare-of e o (evex-sources-once o)))

(defun evex:VADDPS (o) (evex-fp-binary fp-add 32 o))
(defun evex:VADDPD (o) (evex-fp-binary fp-add 64 o))
(defun evex:VSUBPS (o) (evex-fp-binary fp-sub 32 o))
(defun evex:VSUBPD (o) (evex-fp-binary fp-sub 64 o))
(defun evex:VMULPS (o) (evex-fp-binary fp-mul 32 o))
(defun evex:VMULPD (o) (evex-fp-binary fp-mul 64 o))
(defun evex:VDIVPS (o) (evex-fp-binary fp-div 32 o))
(defun evex:VDIVPD (o) (evex-fp-binary fp-div 64 o))
(defun evex:VMINPS (o) (evex-fp-binary fp-min 32 o))
(defun evex:VMINPD (o) (evex-fp-binary fp-min 64 o))
(defun evex:VMAXPS (o) (evex-fp-binary fp-max 32 o))
(defun evex:VMAXPD (o) (evex-fp-binary fp-max 64 o))
(defun evex:VSQRTPS (o) (evex-fp-unary fp-sqrt 32 o))
(defun evex:VSQRTPD (o) (evex-fp-unary fp-sqrt 64 o))
(defun evex:VCMPPS (o) (evex-fp-compare 32 o))
(defun evex:VCMPPD (o) (evex-fp-compare 64 o))
(defun evex:VCVTDQ2PS (o) (evex-fp-unary fp-sint-to-float 32 o))
(defun evex:VCVTPS2DQ (o) (evex-fp-unary fp-float-to-sint 32 o))
(defun evex:VCVTTPS2DQ (o) (evex-fp-unary fp-float-to-sint-rtz 32 o))

;; the fused operations: (RD X Y Z) with RD = X, the number says which
;; are the factors and which is the term

(defun evex-fma-of (f order e x y z)
  (case order
    132 (f e x z y)
    213 (f e y x z)
    (f e y z x)))

(defun evex-lane-fma (f order e x y mode z i)
  (evex-fma-of f order e (evex-lane e x i) (evex-lane e y i) (evex-y mode e z i)))

(defun evex-fma-packed-of (f order e o s)
  (evex-put-tied o e evex-lane-fma f order e (evex-pass o) (car s) (evex-mode o) (evex-src o e (cdr s))))
(defun evex-fma (f order e o) (evex-fma-packed-of f order e o (evex-sources-tied o)))

(defun evex-lane-fma-alternate (sub-even order e x y mode z i)
  (evex-fma-of (if (= (= (mod i 2) 0) sub-even) fma-msub fma-madd)
               order e (evex-lane e x i) (evex-lane e y i) (evex-y mode e z i)))

(defun evex-fmaddsub-of (even order e o s)
  (evex-put-tied o e evex-lane-fma-alternate even order e (evex-pass o) (car s) (evex-mode o) (evex-src o e (cdr s))))
(defun evex-fmaddsub (even order e o) (evex-fmaddsub-of even order e o (evex-sources-tied o)))

(defun evex-fma-scalar-of (f order e o s)
  (set-vex (evex-rd o)
           (concat (extract 127 e (evex-pass o))
                   (evex-mask (evex-m o) (evex-k-tied o) (evex-pass o) e 0
                              (evex-fma-of f order e (evex-lane e (evex-pass o) 0) (evex-lane e (car s) 0)
                                           (evex-y (evex-mode o) e (evex-value o e e (cdr s)) 0))))))
(defun evex-fma-scalar (f order e o) (evex-fma-scalar-of f order e o (evex-sources-tied o)))

(defun evex:VFMADD132PS (o) (evex-fma fma-madd 132 32 o))
(defun evex:VFMADD132PD (o) (evex-fma fma-madd 132 64 o))
(defun evex:VFMADD132SS (o) (evex-fma-scalar fma-madd 132 32 o))
(defun evex:VFMADD132SD (o) (evex-fma-scalar fma-madd 132 64 o))
(defun evex:VFMADD213PS (o) (evex-fma fma-madd 213 32 o))
(defun evex:VFMADD213PD (o) (evex-fma fma-madd 213 64 o))
(defun evex:VFMADD213SS (o) (evex-fma-scalar fma-madd 213 32 o))
(defun evex:VFMADD213SD (o) (evex-fma-scalar fma-madd 213 64 o))
(defun evex:VFMADD231PS (o) (evex-fma fma-madd 231 32 o))
(defun evex:VFMADD231PD (o) (evex-fma fma-madd 231 64 o))
(defun evex:VFMADD231SS (o) (evex-fma-scalar fma-madd 231 32 o))
(defun evex:VFMADD231SD (o) (evex-fma-scalar fma-madd 231 64 o))
(defun evex:VFMSUB132PS (o) (evex-fma fma-msub 132 32 o))
(defun evex:VFMSUB132PD (o) (evex-fma fma-msub 132 64 o))
(defun evex:VFMSUB132SS (o) (evex-fma-scalar fma-msub 132 32 o))
(defun evex:VFMSUB132SD (o) (evex-fma-scalar fma-msub 132 64 o))
(defun evex:VFMSUB213PS (o) (evex-fma fma-msub 213 32 o))
(defun evex:VFMSUB213PD (o) (evex-fma fma-msub 213 64 o))
(defun evex:VFMSUB213SS (o) (evex-fma-scalar fma-msub 213 32 o))
(defun evex:VFMSUB213SD (o) (evex-fma-scalar fma-msub 213 64 o))
(defun evex:VFMSUB231PS (o) (evex-fma fma-msub 231 32 o))
(defun evex:VFMSUB231PD (o) (evex-fma fma-msub 231 64 o))
(defun evex:VFMSUB231SS (o) (evex-fma-scalar fma-msub 231 32 o))
(defun evex:VFMSUB231SD (o) (evex-fma-scalar fma-msub 231 64 o))
(defun evex:VFNMADD132PS (o) (evex-fma fma-nmadd 132 32 o))
(defun evex:VFNMADD132PD (o) (evex-fma fma-nmadd 132 64 o))
(defun evex:VFNMADD132SS (o) (evex-fma-scalar fma-nmadd 132 32 o))
(defun evex:VFNMADD132SD (o) (evex-fma-scalar fma-nmadd 132 64 o))
(defun evex:VFNMADD213PS (o) (evex-fma fma-nmadd 213 32 o))
(defun evex:VFNMADD213PD (o) (evex-fma fma-nmadd 213 64 o))
(defun evex:VFNMADD213SS (o) (evex-fma-scalar fma-nmadd 213 32 o))
(defun evex:VFNMADD213SD (o) (evex-fma-scalar fma-nmadd 213 64 o))
(defun evex:VFNMADD231PS (o) (evex-fma fma-nmadd 231 32 o))
(defun evex:VFNMADD231PD (o) (evex-fma fma-nmadd 231 64 o))
(defun evex:VFNMADD231SS (o) (evex-fma-scalar fma-nmadd 231 32 o))
(defun evex:VFNMADD231SD (o) (evex-fma-scalar fma-nmadd 231 64 o))
(defun evex:VFNMSUB132PS (o) (evex-fma fma-nmsub 132 32 o))
(defun evex:VFNMSUB132PD (o) (evex-fma fma-nmsub 132 64 o))
(defun evex:VFNMSUB132SS (o) (evex-fma-scalar fma-nmsub 132 32 o))
(defun evex:VFNMSUB132SD (o) (evex-fma-scalar fma-nmsub 132 64 o))
(defun evex:VFNMSUB213PS (o) (evex-fma fma-nmsub 213 32 o))
(defun evex:VFNMSUB213PD (o) (evex-fma fma-nmsub 213 64 o))
(defun evex:VFNMSUB213SS (o) (evex-fma-scalar fma-nmsub 213 32 o))
(defun evex:VFNMSUB213SD (o) (evex-fma-scalar fma-nmsub 213 64 o))
(defun evex:VFNMSUB231PS (o) (evex-fma fma-nmsub 231 32 o))
(defun evex:VFNMSUB231PD (o) (evex-fma fma-nmsub 231 64 o))
(defun evex:VFNMSUB231SS (o) (evex-fma-scalar fma-nmsub 231 32 o))
(defun evex:VFNMSUB231SD (o) (evex-fma-scalar fma-nmsub 231 64 o))
(defun evex:VFMADDSUB132PS (o) (evex-fmaddsub true 132 32 o))
(defun evex:VFMADDSUB132PD (o) (evex-fmaddsub true 132 64 o))
(defun evex:VFMADDSUB213PS (o) (evex-fmaddsub true 213 32 o))
(defun evex:VFMADDSUB213PD (o) (evex-fmaddsub true 213 64 o))
(defun evex:VFMADDSUB231PS (o) (evex-fmaddsub true 231 32 o))
(defun evex:VFMADDSUB231PD (o) (evex-fmaddsub true 231 64 o))
(defun evex:VFMSUBADD132PS (o) (evex-fmaddsub false 132 32 o))
(defun evex:VFMSUBADD132PD (o) (evex-fmaddsub false 132 64 o))
(defun evex:VFMSUBADD213PS (o) (evex-fmaddsub false 213 32 o))
(defun evex:VFMSUBADD213PD (o) (evex-fmaddsub false 213 64 o))
(defun evex:VFMSUBADD231PS (o) (evex-fmaddsub false 231 32 o))
(defun evex:VFMSUBADD231PD (o) (evex-fmaddsub false 231 64 o))

;; the conversions, whose vector size is that of the longer lanes

(defun evex-lane-convert (f es mode y _ _ _ i) (f (evex-y mode es y i)))

(defun evex-convert-n (f es ed n o)
  (evex-put-n o ed n evex-lane-convert f es (evex-mode o)
              (evex-value o es (* n es) (evex-sources o)) 0 0 0))
(defun evex-widen (f es ed o) (evex-convert-n f es ed (evex-count o ed) o))
(defun evex-shorten (f es ed o) (evex-convert-n f es ed (evex-count o es) o))

(defun fp-sint32-to-double (x) (sse-convert 'cast_sfloat *sse-rmode* 32 64 x))
(defun fp-sint64-to-double (x) (sse-convert 'cast_sfloat *sse-rmode* 64 64 x))
(defun fp-sint64-to-float (x) (sse-convert 'cast_sfloat *sse-rmode* 64 32 x))
(defun fp-uint32-to-float (x) (sse-convert 'cast_ufloat *sse-rmode* 32 32 x))
(defun fp-uint32-to-double (x) (sse-convert 'cast_ufloat *sse-rmode* 32 64 x))
(defun fp-uint64-to-double (x) (sse-convert 'cast_ufloat *sse-rmode* 64 64 x))
(defun fp-uint64-to-float (x) (sse-convert 'cast_ufloat *sse-rmode* 64 32 x))
(defun fp-float-to-int64 (x) (sse-to-int *sse-rmode* 32 64 x))
(defun fp-double-to-int64 (x) (sse-to-int *sse-rmode* 64 64 x))
(defun fp-float-to-int64-rtz (x) (sse-to-int 'rtz 32 64 x))
(defun fp-double-to-int64-rtz (x) (sse-to-int 'rtz 64 64 x))

(defun evex:VCVTDQ2PD (o) (evex-widen fp-int32-to-double 32 64 o))
(defun evex:VCVTPS2PD (o) (evex-widen fp-float-to-double 32 64 o))
(defun evex:VCVTPD2PS (o) (evex-shorten fp-double-to-float 64 32 o))
(defun evex:VCVTPD2DQ (o) (evex-shorten fp-double-to-int32 64 32 o))
(defun evex:VCVTTPD2DQ (o) (evex-shorten fp-double-to-int32-rtz 64 32 o))
(defun evex:VCVTQQ2PD (o) (evex-widen fp-sint64-to-double 64 64 o))
(defun evex:VCVTQQ2PS (o) (evex-shorten fp-sint64-to-float 64 32 o))
(defun evex:VCVTUDQ2PS (o) (evex-widen fp-uint32-to-float 32 32 o))
(defun evex:VCVTUDQ2PD (o) (evex-widen fp-uint32-to-double 32 64 o))
(defun evex:VCVTUQQ2PD (o) (evex-widen fp-uint64-to-double 64 64 o))
(defun evex:VCVTUQQ2PS (o) (evex-shorten fp-uint64-to-float 64 32 o))
(defun evex:VCVTPS2QQ (o) (evex-widen fp-float-to-int64 32 64 o))
(defun evex:VCVTPD2QQ (o) (evex-widen fp-double-to-int64 64 64 o))
(defun evex:VCVTTPS2QQ (o) (evex-widen fp-float-to-int64-rtz 32 64 o))
(defun evex:VCVTTPD2QQ (o) (evex-widen fp-double-to-int64-rtz 64 64 o))

;; the operations that have no theory here, as intrinsics of each lane,
;; with the immediate as an argument if there is one

(defun fp-getexp (rt x) (sse-unary 'fgetexp rt x))
(defun fp-rcp14 (rt x) (sse-unary 'frcp14 rt x))
(defun fp-rsqrt14 (rt x) (sse-unary 'frsqrt14 rt x))
(defun fp-rcp28 (rt x) (sse-unary 'frcp28 rt x))
(defun fp-rsqrt28 (rt x) (sse-unary 'frsqrt28 rt x))
(defun fp-exp2 (rt x) (sse-unary 'fexp2 rt x))
(defun fp-scalef (rt x y) (sse-binary 'fscalef rt x y))

(defun fp-with-imm (name rt x imm)
  (intrinsic (symbol-concat name *sse-rmode* *sse-format* (symbol-of-size rt) :sep '_)
             (cast-low rt x) (cast-low 8 imm) :result rt))
(defun fp2-with-imm (name rt x y imm)
  (intrinsic (symbol-concat name *sse-rmode* *sse-format* (symbol-of-size rt) :sep '_)
             (cast-low rt x) (cast-low rt y) (cast-low 8 imm) :result rt))

(defun evex-lane-fp-imm (name e mode y imm _ _ i) (fp-with-imm name e (evex-y mode e y i) imm))
(defun evex-lane-fp2-imm (name e x mode y imm _ i) (fp2-with-imm name e (evex-lane e x i) (evex-y mode e y i) imm))
(defun evex-lane-fp-class (e mode y imm _ _ _ i) (cast-low 1 (fp-with-imm 'fpclass e (evex-y mode e y i) imm)))

(defun evex-fp-imm (name e o)
  (evex-put o e evex-lane-fp-imm name e (evex-mode o) (evex-src o e (evex-sources o)) (evex-imm o) 0 0))
(defun evex-fp2-imm-of (name e o s)
  (evex-put o e evex-lane-fp2-imm name e (car s) (evex-mode o) (evex-src o e (cdr s)) (evex-imm o) 0))
(defun evex-fp2-imm (name e o) (evex-fp2-imm-of name e o (evex-sources o)))
(defun evex-fp-class (e o)
  (evex-put-mask o e evex-lane-fp-class e (evex-mode o) (evex-src o e (evex-sources-once o)) (evex-imm o) 0 0 0))

(defun evex:VGETEXPPS (o) (evex-fp-unary fp-getexp 32 o))
(defun evex:VGETEXPPD (o) (evex-fp-unary fp-getexp 64 o))
(defun evex:VRCP14PS (o) (evex-fp-unary fp-rcp14 32 o))
(defun evex:VRCP14PD (o) (evex-fp-unary fp-rcp14 64 o))
(defun evex:VRSQRT14PS (o) (evex-fp-unary fp-rsqrt14 32 o))
(defun evex:VRSQRT14PD (o) (evex-fp-unary fp-rsqrt14 64 o))
(defun evex:VRCP28PS (o) (evex-fp-unary fp-rcp28 32 o))
(defun evex:VRCP28PD (o) (evex-fp-unary fp-rcp28 64 o))
(defun evex:VRSQRT28PS (o) (evex-fp-unary fp-rsqrt28 32 o))
(defun evex:VRSQRT28PD (o) (evex-fp-unary fp-rsqrt28 64 o))
(defun evex:VEXP2PS (o) (evex-fp-unary fp-exp2 32 o))
(defun evex:VEXP2PD (o) (evex-fp-unary fp-exp2 64 o))
(defun evex:VSCALEFPS (o) (evex-fp-binary fp-scalef 32 o))
(defun evex:VSCALEFPD (o) (evex-fp-binary fp-scalef 64 o))
(defun evex:VGETMANTPS (o) (evex-fp-imm 'fgetmant 32 o))
(defun evex:VGETMANTPD (o) (evex-fp-imm 'fgetmant 64 o))
(defun evex:VREDUCEPS (o) (evex-fp-imm 'freduce 32 o))
(defun evex:VREDUCEPD (o) (evex-fp-imm 'freduce 64 o))
(defun evex:VRNDSCALEPS (o) (evex-fp-imm 'frndscale 32 o))
(defun evex:VRNDSCALEPD (o) (evex-fp-imm 'frndscale 64 o))
(defun evex:VRANGEPS (o) (evex-fp2-imm 'frange 32 o))
(defun evex:VRANGEPD (o) (evex-fp2-imm 'frange 64 o))
(defun evex:VFPCLASSPS (o) (evex-fp-class 32 o))
(defun evex:VFPCLASSPD (o) (evex-fp-class 64 o))

;; the duplicating moves

(defun evex-lane-dup-low (e mode y _ _ _ _ i) (evex-y mode e y (* 2 (/ i 2))))
(defun evex-lane-dup-high (e mode y _ _ _ _ i) (evex-y mode e y (+ 1 (* 2 (/ i 2)))))

(defun evex-dup (f e o)
  (evex-put o e f e (evex-mode o) (evex-src o e (evex-sources o)) 0 0 0 0))

(defun evex:VMOVDDUP (o)
  (if (= (evex-w o) 128)
      (evex-dup128 o)
    (evex-dup evex-lane-dup-low 64 o)))
(defun evex-dup128 (o)
  (evex-put o 64 evex-lane-value (evex-freeze (cast-low 64 (evex-dup128-source o (evex-sources o)))) 0 0 0 0 0 0))
(defun evex-dup128-source (o s)
  (if (= (evex-mem o) 0) (car s) (load-n 64 (evex-ea s))))
(defun evex:VMOVSLDUP (o) (evex-dup evex-lane-dup-low 32 o))
(defun evex:VMOVSHDUP (o) (evex-dup evex-lane-dup-high 32 o))

;; the instructions on the bytes and words of the lanes

(defun lane-madd52-low (x y z)
  (+ x (cast-unsigned 64 (cast-low 52 (* (cast-unsigned 104 (cast-low 52 y)) (cast-unsigned 104 (cast-low 52 z)))))))
(defun lane-madd52-high (x y z)
  (+ x (cast-unsigned 64 (cast-high 52 (* (cast-unsigned 104 (cast-low 52 y)) (cast-unsigned 104 (cast-low 52 z)))))))

(defun evex:VPMADD52LUQ (o) (evex-ternary lane-madd52-low 64 o))
(defun evex:VPMADD52HUQ (o) (evex-ternary lane-madd52-high 64 o))

;; the sum of the products of the unsigned bytes of the first source and
;; the signed ones of the second, or of the signed words of both
(defun evex-dot-byte (y z i)
  (* (cast-unsigned 32 (evex-lane 8 y i)) (cast-signed 32 (evex-lane 8 z i))))
(defun evex-dot-word (y z i)
  (* (cast-signed 64 (evex-lane 16 y i)) (cast-signed 64 (evex-lane 16 z i))))
(defun evex-dot-bytes (y z)
  (+ (evex-dot-byte y z 0) (evex-dot-byte y z 1) (evex-dot-byte y z 2) (evex-dot-byte y z 3)))
(defun evex-dot-words (y z) (+ (evex-dot-word y z 0) (evex-dot-word y z 1)))
(defun lane-dpbusd (x y z) (+ x (evex-dot-bytes y z)))
(defun lane-dpbusds (x y z)
  (cast-saturate :signed 32 (+ (cast-signed 64 x) (cast-signed 64 (evex-dot-bytes y z)))))
(defun lane-dpwssd (x y z) (+ x (cast-low 32 (evex-dot-words y z))))
(defun lane-dpwssds (x y z)
  (cast-saturate :signed 32 (+ (cast-signed 64 x) (evex-dot-words y z))))

(defun evex:VPDPBUSD (o) (evex-ternary lane-dpbusd 32 o))
(defun evex:VPDPBUSDS (o) (evex-ternary lane-dpbusds 32 o))
(defun evex:VPDPWSSD (o) (evex-ternary lane-dpwssd 32 o))
(defun evex:VPDPWSSDS (o) (evex-ternary lane-dpwssds 32 o))

;; VPCONFLICT: the bits of a lane say which of the lanes below are equal

(defun evex-conflict-bits (e x i j)
  (if (= j 0) (zeros e)
    (logor (evex-conflict-bits e x i (- j 1))
           (if (= (evex-lane e x i) (evex-lane e x (- j 1)))
               (lshift (cast-unsigned e 1:1) (cast-unsigned e (- j 1)))
             (zeros e)))))

(defun evex-lane-conflict (e x _ _ _ _ _ i) (evex-conflict-bits e x i i))

(defun evex-conflict (e o)
  (evex-put o e evex-lane-conflict e (evex-full o e (evex-sources o)) 0 0 0 0 0))

(defun evex:VPCONFLICTD (o) (evex-conflict 32 o))
(defun evex:VPCONFLICTQ (o) (evex-conflict 64 o))

;; VPSHUFBITQMB: a bit of the mask is the bit of the quadword of X that
;; the byte of Y selects

(defun evex-lane-bitqmb (x mode y _ _ _ _ i)
  (cast-low 1 (rshift (evex-lane 64 x (/ i 8))
                      (cast-unsigned 64 (logand (evex-y mode 8 y i) 63:8)))))

(defun evex-shufbitqmb-of (o s)
  (evex-put-mask o 8 evex-lane-bitqmb (car s) (evex-mode o) (evex-src o 8 (cdr s)) 0 0 0 0))
(defun evex:VPSHUFBITQMB (o) (evex-shufbitqmb-of o (evex-sources-once o)))

;; VPMULTISHIFTQB: a byte is 8 bits of the quadword rotated by the byte
;; of the control

(defun evex-lane-multishift (c mode y _ _ _ _ i)
  (let ((q (evex-y mode 64 y (/ i 8))))
    (cast-low 8 (rshift (concat q q)
                        (cast-unsigned 128 (logand (evex-lane 8 c i) 63:8))))))

(defun evex-multishift-of (o s)
  (evex-put o 8 evex-lane-multishift (car s) 0 (evex-full o 64 (cdr s)) 0 0 0 0))
(defun evex:VPMULTISHIFTQB (o) (evex-multishift-of o (evex-sources o)))

;; the scalar compare to a mask

(defun evex-scalar-compare-of (e o s)
  (set$ (evex-rd o)
        (cast-unsigned 64
          (if (= (evex-m o) 0)
              (fp-predicate e (evex-lane e (car s) 0)
                            (evex-y (evex-mode o) e (evex-value o e e (cdr s)) 0) (evex-imm o))
            (if (select 0 (evex-k-once o))
                (fp-predicate e (evex-lane e (car s) 0)
                              (evex-y (evex-mode o) e (evex-value o e e (cdr s)) 0) (evex-imm o))
              0:1)))))
(defun evex:VCMPSS (o) (evex-scalar-compare-of 32 o (evex-sources-once o)))
(defun evex:VCMPSD (o) (evex-scalar-compare-of 64 o (evex-sources-once o)))

;; what has no family

(defun VMOVPQIto64Zmr (b s i off seg x) (store-n 64 (ea b s i off seg) x))

;; the scalar lanes

(defun evex-fp-scalar-of (f e o s)
  (evex-scalar-set o e (car s) (f e (evex-lane e (car s) 0)
                                  (evex-y (evex-mode o) e (evex-value o e e (cdr s)) 0))))
(defun evex-fp-scalar (f e o) (evex-fp-scalar-of f e o (evex-sources o)))

(defun evex-fp-scalar1-of (f e o s)
  (evex-scalar-set o e (car s) (f e (evex-y (evex-mode o) e (evex-value o e e (cdr s)) 0))))
(defun evex-fp-scalar1 (f e o) (evex-fp-scalar1-of f e o (evex-sources o)))

(defun evex:VADDSS (o) (evex-fp-scalar fp-add 32 o))
(defun evex:VADDSD (o) (evex-fp-scalar fp-add 64 o))
(defun evex:VSUBSS (o) (evex-fp-scalar fp-sub 32 o))
(defun evex:VSUBSD (o) (evex-fp-scalar fp-sub 64 o))
(defun evex:VMULSS (o) (evex-fp-scalar fp-mul 32 o))
(defun evex:VMULSD (o) (evex-fp-scalar fp-mul 64 o))
(defun evex:VDIVSS (o) (evex-fp-scalar fp-div 32 o))
(defun evex:VDIVSD (o) (evex-fp-scalar fp-div 64 o))
(defun evex:VMINSS (o) (evex-fp-scalar fp-min 32 o))
(defun evex:VMINSD (o) (evex-fp-scalar fp-min 64 o))
(defun evex:VMAXSS (o) (evex-fp-scalar fp-max 32 o))
(defun evex:VMAXSD (o) (evex-fp-scalar fp-max 64 o))
(defun evex:VSQRTSS (o) (evex-fp-scalar1 fp-sqrt 32 o))
(defun evex:VSQRTSD (o) (evex-fp-scalar1 fp-sqrt 64 o))

;;; THE MASK REGISTERS
;;
;; They have 64 bits, and an instruction writes the bits of its size and
;; clears the others.

(defun k-set (rd x) (set$ rd (cast-unsigned 64 x)))

(defun k-binary (f n rd x y) (k-set rd (f (cast-low n x) (cast-low n y))))
(defun k-unary (f n rd x) (k-set rd (f (cast-low n x))))

(defun KMOVBkk (rd x) (k-set rd (cast-low 8 x)))
(defun KMOVWkk (rd x) (k-set rd (cast-low 16 x)))
(defun KMOVDkk (rd x) (k-set rd (cast-low 32 x)))
(defun KMOVQkk (rd x) (k-set rd x))
(defun KMOVBkk_EVEX (rd x) (k-set rd (cast-low 8 x)))
(defun KMOVWkk_EVEX (rd x) (k-set rd (cast-low 16 x)))
(defun KMOVDkk_EVEX (rd x) (k-set rd (cast-low 32 x)))
(defun KMOVQkk_EVEX (rd x) (k-set rd x))
(defun KMOVBkr (rd x) (k-set rd (cast-low 8 x)))
(defun KMOVWkr (rd x) (k-set rd (cast-low 16 x)))
(defun KMOVDkr (rd x) (k-set rd (cast-low 32 x)))
(defun KMOVQkr (rd x) (k-set rd (cast-low 64 x)))
(defun KMOVBkr_EVEX (rd x) (k-set rd (cast-low 8 x)))
(defun KMOVWkr_EVEX (rd x) (k-set rd (cast-low 16 x)))
(defun KMOVDkr_EVEX (rd x) (k-set rd (cast-low 32 x)))
(defun KMOVQkr_EVEX (rd x) (k-set rd (cast-low 64 x)))
(defun KMOVBrk (rd x) (set-gpr rd (cast-unsigned 32 (cast-low 8 x))))
(defun KMOVWrk (rd x) (set-gpr rd (cast-unsigned 32 (cast-low 16 x))))
(defun KMOVDrk (rd x) (set-gpr rd (cast-low 32 x)))
(defun KMOVQrk (rd x) (set-gpr rd x))
(defun KMOVBrk_EVEX (rd x) (set-gpr rd (cast-unsigned 32 (cast-low 8 x))))
(defun KMOVWrk_EVEX (rd x) (set-gpr rd (cast-unsigned 32 (cast-low 16 x))))
(defun KMOVDrk_EVEX (rd x) (set-gpr rd (cast-low 32 x)))
(defun KMOVQrk_EVEX (rd x) (set-gpr rd x))
(defun KMOVBkm (rd b s i off seg) (k-set rd (load-n 8 (ea b s i off seg))))
(defun KMOVWkm (rd b s i off seg) (k-set rd (load-n 16 (ea b s i off seg))))
(defun KMOVDkm (rd b s i off seg) (k-set rd (load-n 32 (ea b s i off seg))))
(defun KMOVQkm (rd b s i off seg) (k-set rd (load-n 64 (ea b s i off seg))))
(defun KMOVBkm_EVEX (rd b s i off seg) (k-set rd (load-n 8 (ea b s i off seg))))
(defun KMOVWkm_EVEX (rd b s i off seg) (k-set rd (load-n 16 (ea b s i off seg))))
(defun KMOVDkm_EVEX (rd b s i off seg) (k-set rd (load-n 32 (ea b s i off seg))))
(defun KMOVQkm_EVEX (rd b s i off seg) (k-set rd (load-n 64 (ea b s i off seg))))
(defun KMOVBmk (b s i off seg x) (store-n 8 (ea b s i off seg) x))
(defun KMOVWmk (b s i off seg x) (store-n 16 (ea b s i off seg) x))
(defun KMOVDmk (b s i off seg x) (store-n 32 (ea b s i off seg) x))
(defun KMOVQmk (b s i off seg x) (store-n 64 (ea b s i off seg) x))
(defun KMOVBmk_EVEX (b s i off seg x) (store-n 8 (ea b s i off seg) x))
(defun KMOVWmk_EVEX (b s i off seg x) (store-n 16 (ea b s i off seg) x))
(defun KMOVDmk_EVEX (b s i off seg x) (store-n 32 (ea b s i off seg) x))
(defun KMOVQmk_EVEX (b s i off seg x) (store-n 64 (ea b s i off seg) x))

(defun k-add (x y) (+ x y))

(defun KADDBkk (rd x y) (k-binary k-add 8 rd x y))
(defun KADDWkk (rd x y) (k-binary k-add 16 rd x y))
(defun KADDDkk (rd x y) (k-binary k-add 32 rd x y))
(defun KADDQkk (rd x y) (k-binary k-add 64 rd x y))
(defun KANDBkk (rd x y) (k-binary lane-and 8 rd x y))
(defun KANDWkk (rd x y) (k-binary lane-and 16 rd x y))
(defun KANDDkk (rd x y) (k-binary lane-and 32 rd x y))
(defun KANDQkk (rd x y) (k-binary lane-and 64 rd x y))
(defun KANDNBkk (rd x y) (k-binary lane-andn 8 rd x y))
(defun KANDNWkk (rd x y) (k-binary lane-andn 16 rd x y))
(defun KANDNDkk (rd x y) (k-binary lane-andn 32 rd x y))
(defun KANDNQkk (rd x y) (k-binary lane-andn 64 rd x y))
(defun KORBkk (rd x y) (k-binary lane-or 8 rd x y))
(defun KORWkk (rd x y) (k-binary lane-or 16 rd x y))
(defun KORDkk (rd x y) (k-binary lane-or 32 rd x y))
(defun KORQkk (rd x y) (k-binary lane-or 64 rd x y))
(defun KXORBkk (rd x y) (k-binary lane-xor 8 rd x y))
(defun KXORWkk (rd x y) (k-binary lane-xor 16 rd x y))
(defun KXORDkk (rd x y) (k-binary lane-xor 32 rd x y))
(defun KXORQkk (rd x y) (k-binary lane-xor 64 rd x y))

(defun k-xnor (x y) (lnot (logxor x y)))

(defun KXNORBkk (rd x y) (k-binary k-xnor 8 rd x y))
(defun KXNORWkk (rd x y) (k-binary k-xnor 16 rd x y))
(defun KXNORDkk (rd x y) (k-binary k-xnor 32 rd x y))
(defun KXNORQkk (rd x y) (k-binary k-xnor 64 rd x y))

(defun k-not (x) (lnot x))

(defun KNOTBkk (rd x) (k-unary k-not 8 rd x))
(defun KNOTWkk (rd x) (k-unary k-not 16 rd x))
(defun KNOTDkk (rd x) (k-unary k-not 32 rd x))
(defun KNOTQkk (rd x) (k-unary k-not 64 rd x))

;; the unpacks concatenate the low halves, of the first source the high
(defun KUNPCKBWkk (rd x y) (k-set rd (concat (cast-low 8 x) (cast-low 8 y))))
(defun KUNPCKWDkk (rd x y) (k-set rd (concat (cast-low 16 x) (cast-low 16 y))))
(defun KUNPCKDQkk (rd x y) (k-set rd (concat (cast-low 32 x) (cast-low 32 y))))

;; the count of a shift is not reduced: all the bits go if it isn't
;; less than the size
(defun k-shift-left (n rd x imm)
  (let ((c (cast-low 8 imm)))
    (k-set rd (if (>= c (resize 8 n)) (zeros n)
                (lshift (cast-low n x) (cast-unsigned n c))))))
(defun k-shift-right (n rd x imm)
  (let ((c (cast-low 8 imm)))
    (k-set rd (if (>= c (resize 8 n)) (zeros n)
                (rshift (cast-low n x) (cast-unsigned n c))))))

(defun KSHIFTLBki (rd x imm) (k-shift-left 8 rd x imm))
(defun KSHIFTLWki (rd x imm) (k-shift-left 16 rd x imm))
(defun KSHIFTLDki (rd x imm) (k-shift-left 32 rd x imm))
(defun KSHIFTLQki (rd x imm) (k-shift-left 64 rd x imm))
(defun KSHIFTRBki (rd x imm) (k-shift-right 8 rd x imm))
(defun KSHIFTRWki (rd x imm) (k-shift-right 16 rd x imm))
(defun KSHIFTRDki (rd x imm) (k-shift-right 32 rd x imm))
(defun KSHIFTRQki (rd x imm) (k-shift-right 64 rd x imm))

;; ZF is whether the OR is zero, CF is whether it is all ones
(defun k-ortest (n x y)
  (let ((v (logor (cast-low n x) (cast-low n y))))
    (set ZF (is-zero v))
    (set CF (is-zero (lnot v)))
    (set AF 0:1)
    (set OF 0:1)
    (set PF 0:1)
    (set SF 0:1)))

(defun KORTESTBkk (x y) (k-ortest 8 x y))
(defun KORTESTWkk (x y) (k-ortest 16 x y))
(defun KORTESTDkk (x y) (k-ortest 32 x y))
(defun KORTESTQkk (x y) (k-ortest 64 x y))

(defun KTESTBkk (x y) (ptest (cast-low 8 x) (cast-low 8 y)))
(defun KTESTWkk (x y) (ptest (cast-low 16 x) (cast-low 16 y)))
(defun KTESTDkk (x y) (ptest (cast-low 32 x) (cast-low 32 y)))
(defun KTESTQkk (x y) (ptest (cast-low 64 x) (cast-low 64 y)))
