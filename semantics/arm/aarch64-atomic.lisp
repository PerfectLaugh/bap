(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; ATOMIC OPERATIONS

;; The compare and swap instructions compare the N lowest bits of rs with
;; the memory at rn, and store rt there if they are equal, and set rs to
;; the old value of the memory. The acquire and release orderings have
;; no effect on a single thread.

(defmacro CASord* (set load store n rs rt rn)
  "(CASord* set load store n rs rt rn) implements a generic
   compare-and-swap instruction on N bits. set is the function to
   assign to the size of rs and rt. load and store are functions to
   load/store to/from the size of rs and rt."
   (let ((data (load rn)))
    (when (= data (cast-low n rs))
      (store rn rt))
    (set rs data)))

(defmacro store-hword (dst src) (store-word dst (cast-low 32 src)))
(defmacro load-quarter-word (addr) (load-bits 16 addr))
(defmacro store-quarter-word (dst src) (store-word dst (cast-low 16 src)))

(defmacro CASordX (rs rt rn _ _)
  "Specialisation of CASord* for X registers."
  (CASord* set$ load-word store-word 64 rs rt rn))

(defmacro CASordW (rs rt rn _ _)
  "Specialisation of CASord* for W registers."
  (CASord* setw load-hword store-hword 32 rs rt rn))

(defmacro CASordB (rs rt rn _ _)
  "Specialisation of CASord* operating on individual bytes."
  (CASord* setw memory-read store-byte 8 rs rt rn))

(defmacro CASordH (rs rt rn _ _)
  "Specialisation of CASord* for 16-bit values."
  (CASord* setw load-quarter-word store-quarter-word 16 rs rt rn))

;; not sure why llvm returns 4 arguments.
;; when i've tested it, the first and second arguments are always the same value
;; so i'm just assuming they're the same and ignoring the second.
(defun CASX   (rs _ rt rn) (CASordX rs rt rn false false))
(defun CASAX  (rs _ rt rn) (CASordX rs rt rn true  false))
(defun CASLX  (rs _ rt rn) (CASordX rs rt rn false true))
(defun CASALX (rs _ rt rn) (CASordX rs rt rn true  true))

(defun CASW   (rs _ rt rn) (CASordW rs rt rn false false))
(defun CASAW  (rs _ rt rn) (CASordW rs rt rn true  false))
(defun CASLW  (rs _ rt rn) (CASordW rs rt rn false true))
(defun CASALW (rs _ rt rn) (CASordW rs rt rn true  true))

(defun CASB   (rs _ rt rn) (CASordB rs rt rn false false))
(defun CASAB  (rs _ rt rn) (CASordB rs rt rn true  false))
(defun CASLB  (rs _ rt rn) (CASordB rs rt rn false true))
(defun CASALB (rs _ rt rn) (CASordB rs rt rn true  true))

(defun CASH   (rs _ rt rn) (CASordH rs rt rn false false))
(defun CASAH  (rs _ rt rn) (CASordH rs rt rn true  false))
(defun CASLH  (rs _ rt rn) (CASordH rs rt rn false true))
(defun CASALH (rs _ rt rn) (CASordH rs rt rn true  true))


;; The atomic memory operations of LSE, of ARMv8.1, load the old value,
;; store the operation on it and the operand, and write the old value to
;; the destination, which is ignored, if it is the zero register, e.g., of
;; stadd. The operands are (rt rs rn), the destination, the operand, and
;; the address. The ordering has no effect on a single thread.

(defmacro LDOP* (set load store n op rt rs rn)
  "(LDOP* set load store n op rt rs rn) implements the atomic operation
   op on n bits of memory, at rn, and rs, setting rt to the old value."
  (let ((data (load rn))
        (operand (cast-low n rs)))
    (store rn (op data operand))
    (set rt data)))

(defmacro LDOP*X (op rt rs rn) (LDOP* set$ load-word store-word 64 op rt rs rn))
(defmacro LDOP*W (op rt rs rn) (LDOP* setw load-hword store-hword 32 op rt rs rn))
(defmacro LDOP*H (op rt rs rn)
  (LDOP* setw load-quarter-word store-quarter-word 16 op rt rs rn))
(defmacro LDOP*B (op rt rs rn) (LDOP* setw memory-read store-byte 8 op rt rs rn))

(defmacro ld-add (x y) (+ x y))
(defmacro ld-clr (x y) (logand x (lnot y)))
(defmacro ld-eor (x y) (logxor x y))
(defmacro ld-set (x y) (logor x y))
(defmacro ld-smax (x y) (if (s> x y) x y))
(defmacro ld-smin (x y) (if (s< x y) x y))
(defmacro ld-umax (x y) (if (> x y) x y))
(defmacro ld-umin (x y) (if (< x y) x y))
(defmacro ld-swp (_ y) y)


(defun LDADDX (rt rs rn) (LDOP*X ld-add rt rs rn))
(defun LDADDW (rt rs rn) (LDOP*W ld-add rt rs rn))
(defun LDADDH (rt rs rn) (LDOP*H ld-add rt rs rn))
(defun LDADDB (rt rs rn) (LDOP*B ld-add rt rs rn))
(defun LDADDAX (rt rs rn) (LDOP*X ld-add rt rs rn))
(defun LDADDAW (rt rs rn) (LDOP*W ld-add rt rs rn))
(defun LDADDAH (rt rs rn) (LDOP*H ld-add rt rs rn))
(defun LDADDAB (rt rs rn) (LDOP*B ld-add rt rs rn))
(defun LDADDALX (rt rs rn) (LDOP*X ld-add rt rs rn))
(defun LDADDALW (rt rs rn) (LDOP*W ld-add rt rs rn))
(defun LDADDALH (rt rs rn) (LDOP*H ld-add rt rs rn))
(defun LDADDALB (rt rs rn) (LDOP*B ld-add rt rs rn))
(defun LDADDLX (rt rs rn) (LDOP*X ld-add rt rs rn))
(defun LDADDLW (rt rs rn) (LDOP*W ld-add rt rs rn))
(defun LDADDLH (rt rs rn) (LDOP*H ld-add rt rs rn))
(defun LDADDLB (rt rs rn) (LDOP*B ld-add rt rs rn))

(defun LDCLRX (rt rs rn) (LDOP*X ld-clr rt rs rn))
(defun LDCLRW (rt rs rn) (LDOP*W ld-clr rt rs rn))
(defun LDCLRH (rt rs rn) (LDOP*H ld-clr rt rs rn))
(defun LDCLRB (rt rs rn) (LDOP*B ld-clr rt rs rn))
(defun LDCLRAX (rt rs rn) (LDOP*X ld-clr rt rs rn))
(defun LDCLRAW (rt rs rn) (LDOP*W ld-clr rt rs rn))
(defun LDCLRAH (rt rs rn) (LDOP*H ld-clr rt rs rn))
(defun LDCLRAB (rt rs rn) (LDOP*B ld-clr rt rs rn))
(defun LDCLRALX (rt rs rn) (LDOP*X ld-clr rt rs rn))
(defun LDCLRALW (rt rs rn) (LDOP*W ld-clr rt rs rn))
(defun LDCLRALH (rt rs rn) (LDOP*H ld-clr rt rs rn))
(defun LDCLRALB (rt rs rn) (LDOP*B ld-clr rt rs rn))
(defun LDCLRLX (rt rs rn) (LDOP*X ld-clr rt rs rn))
(defun LDCLRLW (rt rs rn) (LDOP*W ld-clr rt rs rn))
(defun LDCLRLH (rt rs rn) (LDOP*H ld-clr rt rs rn))
(defun LDCLRLB (rt rs rn) (LDOP*B ld-clr rt rs rn))

(defun LDEORX (rt rs rn) (LDOP*X ld-eor rt rs rn))
(defun LDEORW (rt rs rn) (LDOP*W ld-eor rt rs rn))
(defun LDEORH (rt rs rn) (LDOP*H ld-eor rt rs rn))
(defun LDEORB (rt rs rn) (LDOP*B ld-eor rt rs rn))
(defun LDEORAX (rt rs rn) (LDOP*X ld-eor rt rs rn))
(defun LDEORAW (rt rs rn) (LDOP*W ld-eor rt rs rn))
(defun LDEORAH (rt rs rn) (LDOP*H ld-eor rt rs rn))
(defun LDEORAB (rt rs rn) (LDOP*B ld-eor rt rs rn))
(defun LDEORALX (rt rs rn) (LDOP*X ld-eor rt rs rn))
(defun LDEORALW (rt rs rn) (LDOP*W ld-eor rt rs rn))
(defun LDEORALH (rt rs rn) (LDOP*H ld-eor rt rs rn))
(defun LDEORALB (rt rs rn) (LDOP*B ld-eor rt rs rn))
(defun LDEORLX (rt rs rn) (LDOP*X ld-eor rt rs rn))
(defun LDEORLW (rt rs rn) (LDOP*W ld-eor rt rs rn))
(defun LDEORLH (rt rs rn) (LDOP*H ld-eor rt rs rn))
(defun LDEORLB (rt rs rn) (LDOP*B ld-eor rt rs rn))

(defun LDSETX (rt rs rn) (LDOP*X ld-set rt rs rn))
(defun LDSETW (rt rs rn) (LDOP*W ld-set rt rs rn))
(defun LDSETH (rt rs rn) (LDOP*H ld-set rt rs rn))
(defun LDSETB (rt rs rn) (LDOP*B ld-set rt rs rn))
(defun LDSETAX (rt rs rn) (LDOP*X ld-set rt rs rn))
(defun LDSETAW (rt rs rn) (LDOP*W ld-set rt rs rn))
(defun LDSETAH (rt rs rn) (LDOP*H ld-set rt rs rn))
(defun LDSETAB (rt rs rn) (LDOP*B ld-set rt rs rn))
(defun LDSETALX (rt rs rn) (LDOP*X ld-set rt rs rn))
(defun LDSETALW (rt rs rn) (LDOP*W ld-set rt rs rn))
(defun LDSETALH (rt rs rn) (LDOP*H ld-set rt rs rn))
(defun LDSETALB (rt rs rn) (LDOP*B ld-set rt rs rn))
(defun LDSETLX (rt rs rn) (LDOP*X ld-set rt rs rn))
(defun LDSETLW (rt rs rn) (LDOP*W ld-set rt rs rn))
(defun LDSETLH (rt rs rn) (LDOP*H ld-set rt rs rn))
(defun LDSETLB (rt rs rn) (LDOP*B ld-set rt rs rn))

(defun LDSMAXX (rt rs rn) (LDOP*X ld-smax rt rs rn))
(defun LDSMAXW (rt rs rn) (LDOP*W ld-smax rt rs rn))
(defun LDSMAXH (rt rs rn) (LDOP*H ld-smax rt rs rn))
(defun LDSMAXB (rt rs rn) (LDOP*B ld-smax rt rs rn))
(defun LDSMAXAX (rt rs rn) (LDOP*X ld-smax rt rs rn))
(defun LDSMAXAW (rt rs rn) (LDOP*W ld-smax rt rs rn))
(defun LDSMAXAH (rt rs rn) (LDOP*H ld-smax rt rs rn))
(defun LDSMAXAB (rt rs rn) (LDOP*B ld-smax rt rs rn))
(defun LDSMAXALX (rt rs rn) (LDOP*X ld-smax rt rs rn))
(defun LDSMAXALW (rt rs rn) (LDOP*W ld-smax rt rs rn))
(defun LDSMAXALH (rt rs rn) (LDOP*H ld-smax rt rs rn))
(defun LDSMAXALB (rt rs rn) (LDOP*B ld-smax rt rs rn))
(defun LDSMAXLX (rt rs rn) (LDOP*X ld-smax rt rs rn))
(defun LDSMAXLW (rt rs rn) (LDOP*W ld-smax rt rs rn))
(defun LDSMAXLH (rt rs rn) (LDOP*H ld-smax rt rs rn))
(defun LDSMAXLB (rt rs rn) (LDOP*B ld-smax rt rs rn))

(defun LDSMINX (rt rs rn) (LDOP*X ld-smin rt rs rn))
(defun LDSMINW (rt rs rn) (LDOP*W ld-smin rt rs rn))
(defun LDSMINH (rt rs rn) (LDOP*H ld-smin rt rs rn))
(defun LDSMINB (rt rs rn) (LDOP*B ld-smin rt rs rn))
(defun LDSMINAX (rt rs rn) (LDOP*X ld-smin rt rs rn))
(defun LDSMINAW (rt rs rn) (LDOP*W ld-smin rt rs rn))
(defun LDSMINAH (rt rs rn) (LDOP*H ld-smin rt rs rn))
(defun LDSMINAB (rt rs rn) (LDOP*B ld-smin rt rs rn))
(defun LDSMINALX (rt rs rn) (LDOP*X ld-smin rt rs rn))
(defun LDSMINALW (rt rs rn) (LDOP*W ld-smin rt rs rn))
(defun LDSMINALH (rt rs rn) (LDOP*H ld-smin rt rs rn))
(defun LDSMINALB (rt rs rn) (LDOP*B ld-smin rt rs rn))
(defun LDSMINLX (rt rs rn) (LDOP*X ld-smin rt rs rn))
(defun LDSMINLW (rt rs rn) (LDOP*W ld-smin rt rs rn))
(defun LDSMINLH (rt rs rn) (LDOP*H ld-smin rt rs rn))
(defun LDSMINLB (rt rs rn) (LDOP*B ld-smin rt rs rn))

(defun LDUMAXX (rt rs rn) (LDOP*X ld-umax rt rs rn))
(defun LDUMAXW (rt rs rn) (LDOP*W ld-umax rt rs rn))
(defun LDUMAXH (rt rs rn) (LDOP*H ld-umax rt rs rn))
(defun LDUMAXB (rt rs rn) (LDOP*B ld-umax rt rs rn))
(defun LDUMAXAX (rt rs rn) (LDOP*X ld-umax rt rs rn))
(defun LDUMAXAW (rt rs rn) (LDOP*W ld-umax rt rs rn))
(defun LDUMAXAH (rt rs rn) (LDOP*H ld-umax rt rs rn))
(defun LDUMAXAB (rt rs rn) (LDOP*B ld-umax rt rs rn))
(defun LDUMAXALX (rt rs rn) (LDOP*X ld-umax rt rs rn))
(defun LDUMAXALW (rt rs rn) (LDOP*W ld-umax rt rs rn))
(defun LDUMAXALH (rt rs rn) (LDOP*H ld-umax rt rs rn))
(defun LDUMAXALB (rt rs rn) (LDOP*B ld-umax rt rs rn))
(defun LDUMAXLX (rt rs rn) (LDOP*X ld-umax rt rs rn))
(defun LDUMAXLW (rt rs rn) (LDOP*W ld-umax rt rs rn))
(defun LDUMAXLH (rt rs rn) (LDOP*H ld-umax rt rs rn))
(defun LDUMAXLB (rt rs rn) (LDOP*B ld-umax rt rs rn))

(defun LDUMINX (rt rs rn) (LDOP*X ld-umin rt rs rn))
(defun LDUMINW (rt rs rn) (LDOP*W ld-umin rt rs rn))
(defun LDUMINH (rt rs rn) (LDOP*H ld-umin rt rs rn))
(defun LDUMINB (rt rs rn) (LDOP*B ld-umin rt rs rn))
(defun LDUMINAX (rt rs rn) (LDOP*X ld-umin rt rs rn))
(defun LDUMINAW (rt rs rn) (LDOP*W ld-umin rt rs rn))
(defun LDUMINAH (rt rs rn) (LDOP*H ld-umin rt rs rn))
(defun LDUMINAB (rt rs rn) (LDOP*B ld-umin rt rs rn))
(defun LDUMINALX (rt rs rn) (LDOP*X ld-umin rt rs rn))
(defun LDUMINALW (rt rs rn) (LDOP*W ld-umin rt rs rn))
(defun LDUMINALH (rt rs rn) (LDOP*H ld-umin rt rs rn))
(defun LDUMINALB (rt rs rn) (LDOP*B ld-umin rt rs rn))
(defun LDUMINLX (rt rs rn) (LDOP*X ld-umin rt rs rn))
(defun LDUMINLW (rt rs rn) (LDOP*W ld-umin rt rs rn))
(defun LDUMINLH (rt rs rn) (LDOP*H ld-umin rt rs rn))
(defun LDUMINLB (rt rs rn) (LDOP*B ld-umin rt rs rn))

(defun SWPX (rt rs rn) (LDOP*X ld-swp rt rs rn))
(defun SWPW (rt rs rn) (LDOP*W ld-swp rt rs rn))
(defun SWPH (rt rs rn) (LDOP*H ld-swp rt rs rn))
(defun SWPB (rt rs rn) (LDOP*B ld-swp rt rs rn))
(defun SWPAX (rt rs rn) (LDOP*X ld-swp rt rs rn))
(defun SWPAW (rt rs rn) (LDOP*W ld-swp rt rs rn))
(defun SWPAH (rt rs rn) (LDOP*H ld-swp rt rs rn))
(defun SWPAB (rt rs rn) (LDOP*B ld-swp rt rs rn))
(defun SWPALX (rt rs rn) (LDOP*X ld-swp rt rs rn))
(defun SWPALW (rt rs rn) (LDOP*W ld-swp rt rs rn))
(defun SWPALH (rt rs rn) (LDOP*H ld-swp rt rs rn))
(defun SWPALB (rt rs rn) (LDOP*B ld-swp rt rs rn))
(defun SWPLX (rt rs rn) (LDOP*X ld-swp rt rs rn))
(defun SWPLW (rt rs rn) (LDOP*W ld-swp rt rs rn))
(defun SWPLH (rt rs rn) (LDOP*H ld-swp rt rs rn))
(defun SWPLB (rt rs rn) (LDOP*B ld-swp rt rs rn))

(defmacro CSop*r (set op rd rn rm cnd)
  "(CSop*r set op rd rn rm cnd) implements the conditional select
   instruction on W or X registers, with op being applied to rm
   when cnd is false."
  (if (condition-holds cnd)
    (set rd rn)
    (set rd (op rm))))

(defun id (arg) "identity function" (declare (visibility :private)) arg)

(defun CSELWr  (rd rn rm cnd) (CSop*r setw id   rd rn rm cnd))
(defun CSELXr  (rd rn rm cnd) (CSop*r set$ id   rd rn rm cnd))
(defun CSINCWr (rd rn rm cnd)
  (if (condition-holds cnd) (setw rd rn) (setw rd (+ rm 1))))
(defun CSINCXr (rd rn rm cnd)
  (if (condition-holds cnd) (set$ rd rn) (set$ rd (+ rm 1))))
(defun CSINVWr (rd rn rm cnd) (CSop*r setw lnot rd rn rm cnd))
(defun CSINVXr (rd rn rm cnd) (CSop*r set$ lnot rd rn rm cnd))
(defun CSNEGWr (rd rn rm cnd) (CSop*r setw neg  rd rn rm cnd))  ;; 2's complement negation
(defun CSNEGXr (rd rn rm cnd) (CSop*r set$ neg  rd rn rm cnd))  ;; 2's complement negation

;;; EXCLUSIVE AND ACQUIRE-RELEASE LOADS AND STORES
;;
;; The exclusive monitor is not modeled, an exclusive store always
;; succeeds and writes 0 to its status register. The memory ordering
;; has no effect on a single thread.

(defun LDXRX (rt rn) (ld-x rt rn))
(defun LDXRW (rt rn) (ld-w rt rn))
(defun LDXRH (rt rn) (ld-h rt rn))
(defun LDXRB (rt rn) (ld-b rt rn))
(defun LDAXRX (rt rn) (ld-x rt rn))
(defun LDAXRW (rt rn) (ld-w rt rn))
(defun LDAXRH (rt rn) (ld-h rt rn))
(defun LDAXRB (rt rn) (ld-b rt rn))
(defun LDARX (rt rn) (ld-x rt rn))
(defun LDARW (rt rn) (ld-w rt rn))
(defun LDARH (rt rn) (ld-h rt rn))
(defun LDARB (rt rn) (ld-b rt rn))
(defun LDAPRX (rt rn) (ld-x rt rn))
(defun LDAPRW (rt rn) (ld-w rt rn))
(defun LDAPRH (rt rn) (ld-h rt rn))
(defun LDAPRB (rt rn) (ld-b rt rn))

(defun STLRX (rt rn) (st-x rt rn))
(defun STLRW (rt rn) (st-w rt rn))
(defun STLRH (rt rn) (st-h rt rn))
(defun STLRB (rt rn) (st-b rt rn))

(defmacro STXR* (st rs rt rn) (prog (st rt rn) (setw rs 0)))
(defun STXRX (rs rt rn) (STXR* st-x rs rt rn))
(defun STXRW (rs rt rn) (STXR* st-w rs rt rn))
(defun STXRH (rs rt rn) (STXR* st-h rs rt rn))
(defun STXRB (rs rt rn) (STXR* st-b rs rt rn))
(defun STLXRX (rs rt rn) (STXR* st-x rs rt rn))
(defun STLXRW (rs rt rn) (STXR* st-w rs rt rn))
(defun STLXRH (rs rt rn) (STXR* st-h rs rt rn))
(defun STLXRB (rs rt rn) (STXR* st-b rs rt rn))

(defun LDXPX (r1 r2 rn) (LDST*pair ld-x r1 r2 rn 8))
(defun LDXPW (r1 r2 rn) (LDST*pair ld-w r1 r2 rn 4))
(defun LDAXPX (r1 r2 rn) (LDST*pair ld-x r1 r2 rn 8))
(defun LDAXPW (r1 r2 rn) (LDST*pair ld-w r1 r2 rn 4))
(defun STXPX (rs r1 r2 rn) (prog (LDST*pair st-x r1 r2 rn 8) (setw rs 0)))
(defun STXPW (rs r1 r2 rn) (prog (LDST*pair st-w r1 r2 rn 4) (setw rs 0)))
(defun STLXPX (rs r1 r2 rn) (prog (LDST*pair st-x r1 r2 rn 8) (setw rs 0)))
(defun STLXPW (rs r1 r2 rn) (prog (LDST*pair st-w r1 r2 rn 4) (setw rs 0)))

(defun CLREX (_) (empty))

;; The compare and swap of a pair, CASP, of ARMv8.1. The pairs are lists
;; of an even register and the next one, which the semantics take by
;; their names; the first register of a pair is the lower half of the
;; memory, which is little endian here. The pair of X30 ends with the
;; zero register, whose write is dropped. The W registers are written
;; zero extended. The ordering has no effect on a single thread.

(defun a64-pair-first (p)
  (case (symbol p)
    'X0_X1 'X0 'X2_X3 'X2 'X4_X5 'X4 'X6_X7 'X6
    'X8_X9 'X8 'X10_X11 'X10 'X12_X13 'X12 'X14_X15 'X14
    'X16_X17 'X16 'X18_X19 'X18 'X20_X21 'X20 'X22_X23 'X22
    'X24_X25 'X24 'X26_X27 'X26 'X28_FP 'X28 'LR_XZR 'X30
    'W0_W1 'X0 'W2_W3 'X2 'W4_W5 'X4 'W6_W7 'X6
    'W8_W9 'X8 'W10_W11 'X10 'W12_W13 'X12 'W14_W15 'X14
    'W16_W17 'X16 'W18_W19 'X18 'W20_W21 'X20 'W22_W23 'X22
    'W24_W25 'X24 'W26_W27 'X26 'W28_W29 'X28 'W30_WZR 'X30
    (symbol p)))

(defun a64-pair-second (p)
  (case (symbol p)
    'X0_X1 'X1 'X2_X3 'X3 'X4_X5 'X5 'X6_X7 'X7
    'X8_X9 'X9 'X10_X11 'X11 'X12_X13 'X13 'X14_X15 'X15
    'X16_X17 'X17 'X18_X19 'X19 'X20_X21 'X21 'X22_X23 'X23
    'X24_X25 'X25 'X26_X27 'X27 'X28_FP 'X29 'LR_XZR 'XZR
    'W0_W1 'X1 'W2_W3 'X3 'W4_W5 'X5 'W6_W7 'X7
    'W8_W9 'X9 'W10_W11 'X11 'W12_W13 'X13 'W14_W15 'X15
    'W16_W17 'X17 'W18_W19 'X19 'W20_W21 'X21 'W22_W23 'X23
    'W24_W25 'X25 'W26_W27 'X27 'W28_W29 'X29 'W30_WZR 'XZR
    (symbol p)))

(defun a64-pair-value (p n)
  "the N bits of the two registers of the pair P, the first one is the lowest"
  (concat (cast-low n (unquote (a64-pair-second p)))
          (cast-low n (unquote (a64-pair-first p)))))

(defun a64-casp (rs rt rn n)
  (let ((a rn)
        (data (load-bits (* 2 n) a)))
    (when (= data (a64-pair-value rs n))
      (store-word a (a64-pair-value rt n)))
    (set-symbol-value (a64-pair-first rs) (cast-unsigned 64 (cast-low n data)))
    (set-symbol-value (a64-pair-second rs) (cast-unsigned 64 (cast-high n data)))))

(defun CASPX (rs _ rt rn) (a64-casp rs rt rn 64))
(defun CASPAX (rs _ rt rn) (a64-casp rs rt rn 64))
(defun CASPLX (rs _ rt rn) (a64-casp rs rt rn 64))
(defun CASPALX (rs _ rt rn) (a64-casp rs rt rn 64))
(defun CASPW (rs _ rt rn) (a64-casp rs rt rn 32))
(defun CASPAW (rs _ rt rn) (a64-casp rs rt rn 32))
(defun CASPLW (rs _ rt rn) (a64-casp rs rt rn 32))
(defun CASPALW (rs _ rt rn) (a64-casp rs rt rn 32))

;; The loads and the stores of LORegions and with the unscaled offsets
;; of RCpc, whose orderings have no effect on a single thread.

(defun LDLARX (rt rn) (ld-x rt rn))
(defun LDLARW (rt rn) (ld-w rt rn))
(defun LDLARH (rt rn) (ld-h rt rn))
(defun LDLARB (rt rn) (ld-b rt rn))
(defun STLLRX (rt rn) (st-x rt rn))
(defun STLLRW (rt rn) (st-w rt rn))
(defun STLLRH (rt rn) (st-h rt rn))
(defun STLLRB (rt rn) (st-b rt rn))
(defun LDAPURXi (rt rn off) (ld-x rt (+ rn off)))
(defun LDAPURi (rt rn off) (ld-w rt (+ rn off)))
(defun LDAPURHi (rt rn off) (ld-h rt (+ rn off)))
(defun LDAPURBi (rt rn off) (ld-b rt (+ rn off)))
(defun LDAPURSWi (rt rn off) (ld-sw rt (+ rn off)))
(defun LDAPURSHXi (rt rn off) (ld-shx rt (+ rn off)))
(defun LDAPURSHWi (rt rn off) (ld-shw rt (+ rn off)))
(defun LDAPURSBXi (rt rn off) (ld-sbx rt (+ rn off)))
(defun LDAPURSBWi (rt rn off) (ld-sbw rt (+ rn off)))
(defun STLURXi (rt rn off) (st-x rt (+ rn off)))
(defun STLURWi (rt rn off) (st-w rt (+ rn off)))
(defun STLURHi (rt rn off) (st-h rt (+ rn off)))
(defun STLURBi (rt rn off) (st-b rt (+ rn off)))
