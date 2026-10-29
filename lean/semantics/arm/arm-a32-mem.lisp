(declare (context (target arm-family)
                  (bits 32)))

(in-package arm)

(require bits)
(require arm-bits)
(require arm-a32)

;;; A32 LOADS AND STORES
;;
;; The offsets of the addressing modes are encoded:
;;
;; - the mode 2 of the word and byte accesses has the immediate in the
;;   bits 11:0, or the shift amount if there is an offset register, the
;;   subtraction in the bit 12 and the shift type, as in i-shift, in
;;   the bits 15:13;
;; - the mode 3 of the halfword, signed and doubleword accesses has the
;;   immediate in the bits 7:0, used if the offset register is Nil, and
;;   the subtraction in the bit 8;
;; - the unprivileged halfword and signed accesses, which are the same
;;   in the user mode, have the addition in the bit 8 of the immediate,
;;   or in the bit 0 if there is an offset register.
;;
;; A base that is PC reads as the address of the instruction plus 8. A
;; load to PC is a branch, which is taken after the base is written back.

(defun a32-negate-if (c x) (if c (- 0 x) x))

(defun a32-am2-imm (am)
  (a32-negate-if (/= 0 (logand am 0x1000)) (logand am 0xfff)))

(defun a32-am2-reg (rm am)
  (let ((typ (logand (rshift am 13) 7))
        (sh (logor (if (= typ 0) 2 typ) (lshift (logand am 0x1f) 3))))
    (a32-negate-if (/= 0 (logand am 0x1000)) (shifted rm sh))))

(defun a32-am3 (rm am)
  (a32-negate-if (/= 0 (logand am 0x100))
                 (if (a32-is-nil rm) (logand am 0xff) rm)))

(defun a32-amt-imm (x) (a32-negate-if (= 0 (logand x 0x100)) (logand x 0xff)))
(defun a32-amt-reg (rm add) (a32-negate-if (= 0 add) rm))

(defun store-half32 (a x) (store-word a (cast-low 16 x)))

;; the accesses by their offset, pre-indexed and post-indexed addresses

(defmacro a32-load (load rt a)
  (let ((v (load a))) (a32-set rt v)))

(defmacro a32-load-pre (load rt wb a)
  (let ((addr a) (v (load addr))) (set$ wb addr) (a32-set rt v)))

(defmacro a32-load-post (load rt wb rn off)
  (let ((addr rn) (v (load addr))) (set$ wb (+ addr off)) (a32-set rt v)))

(defmacro a32-store (store rt a) (store a (a32-reg rt)))

(defmacro a32-store-pre (store rt wb a)
  (let ((addr a)) (store addr (a32-reg rt)) (set$ wb addr)))

(defmacro a32-store-post (store rt wb rn off)
  (let ((addr rn)) (store addr (a32-reg rt)) (set$ wb (+ addr off))))

;; the word and byte accesses

(defun LDRi12 (rt rn off cnd _) (a32-cond cnd (a32-load load-word32 rt (+ (a32-reg rn) off))))
(defun LDRBi12 (rt rn off cnd _) (a32-cond cnd (a32-load load-byte32 rt (+ (a32-reg rn) off))))
(defun STRi12 (rt rn off cnd _) (a32-cond cnd (a32-store store-word rt (+ (a32-reg rn) off))))
(defun STRBi12 (rt rn off cnd _) (a32-cond cnd (a32-store store-byte rt (+ (a32-reg rn) off))))
(defun LDRrs (rt rn rm am cnd _) (a32-cond cnd (a32-load load-word32 rt (+ (a32-reg rn) (a32-am2-reg rm am)))))
(defun LDRBrs (rt rn rm am cnd _) (a32-cond cnd (a32-load load-byte32 rt (+ (a32-reg rn) (a32-am2-reg rm am)))))
(defun STRrs (rt rn rm am cnd _) (a32-cond cnd (a32-store store-word rt (+ (a32-reg rn) (a32-am2-reg rm am)))))
(defun STRBrs (rt rn rm am cnd _) (a32-cond cnd (a32-store store-byte rt (+ (a32-reg rn) (a32-am2-reg rm am)))))

(defun LDR_PRE_IMM (rt wb rn off cnd _) (a32-cond cnd (a32-load-pre load-word32 rt wb (+ rn off))))
(defun LDRB_PRE_IMM (rt wb rn off cnd _) (a32-cond cnd (a32-load-pre load-byte32 rt wb (+ rn off))))
(defun STR_PRE_IMM (wb rt rn off cnd _) (a32-cond cnd (a32-store-pre store-word rt wb (+ rn off))))
(defun STRB_PRE_IMM (wb rt rn off cnd _) (a32-cond cnd (a32-store-pre store-byte rt wb (+ rn off))))
(defun LDR_PRE_REG (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-pre load-word32 rt wb (+ rn (a32-am2-reg rm am)))))
(defun LDRB_PRE_REG (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-pre load-byte32 rt wb (+ rn (a32-am2-reg rm am)))))
(defun STR_PRE_REG (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-pre store-word rt wb (+ rn (a32-am2-reg rm am)))))
(defun STRB_PRE_REG (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-pre store-byte rt wb (+ rn (a32-am2-reg rm am)))))

(defun LDR_POST_IMM (rt wb rn _ am cnd _) (a32-cond cnd (a32-load-post load-word32 rt wb rn (a32-am2-imm am))))
(defun LDRB_POST_IMM (rt wb rn _ am cnd _) (a32-cond cnd (a32-load-post load-byte32 rt wb rn (a32-am2-imm am))))
(defun LDRT_POST_IMM (rt wb rn _ am cnd _) (a32-cond cnd (a32-load-post load-word32 rt wb rn (a32-am2-imm am))))
(defun LDRBT_POST_IMM (rt wb rn _ am cnd _) (a32-cond cnd (a32-load-post load-byte32 rt wb rn (a32-am2-imm am))))
(defun STR_POST_IMM (wb rt rn _ am cnd _) (a32-cond cnd (a32-store-post store-word rt wb rn (a32-am2-imm am))))
(defun STRB_POST_IMM (wb rt rn _ am cnd _) (a32-cond cnd (a32-store-post store-byte rt wb rn (a32-am2-imm am))))
(defun STRT_POST_IMM (wb rt rn _ am cnd _) (a32-cond cnd (a32-store-post store-word rt wb rn (a32-am2-imm am))))
(defun STRBT_POST_IMM (wb rt rn _ am cnd _) (a32-cond cnd (a32-store-post store-byte rt wb rn (a32-am2-imm am))))
(defun LDR_POST_REG (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-word32 rt wb rn (a32-am2-reg rm am))))
(defun LDRB_POST_REG (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-byte32 rt wb rn (a32-am2-reg rm am))))
(defun LDRT_POST_REG (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-word32 rt wb rn (a32-am2-reg rm am))))
(defun LDRBT_POST_REG (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-byte32 rt wb rn (a32-am2-reg rm am))))
(defun STR_POST_REG (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-post store-word rt wb rn (a32-am2-reg rm am))))
(defun STRB_POST_REG (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-post store-byte rt wb rn (a32-am2-reg rm am))))
(defun STRT_POST_REG (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-post store-word rt wb rn (a32-am2-reg rm am))))
(defun STRBT_POST_REG (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-post store-byte rt wb rn (a32-am2-reg rm am))))

;; the halfword and signed accesses

(defun LDRH (rt rn rm am cnd _) (a32-cond cnd (a32-load load-half32 rt (+ (a32-reg rn) (a32-am3 rm am)))))
(defun LDRSH (rt rn rm am cnd _) (a32-cond cnd (a32-load load-shalf32 rt (+ (a32-reg rn) (a32-am3 rm am)))))
(defun LDRSB (rt rn rm am cnd _) (a32-cond cnd (a32-load load-sbyte32 rt (+ (a32-reg rn) (a32-am3 rm am)))))
(defun STRH (rt rn rm am cnd _) (a32-cond cnd (a32-store store-half32 rt (+ (a32-reg rn) (a32-am3 rm am)))))
(defun LDRH_PRE (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-pre load-half32 rt wb (+ rn (a32-am3 rm am)))))
(defun LDRSH_PRE (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-pre load-shalf32 rt wb (+ rn (a32-am3 rm am)))))
(defun LDRSB_PRE (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-pre load-sbyte32 rt wb (+ rn (a32-am3 rm am)))))
(defun STRH_PRE (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-pre store-half32 rt wb (+ rn (a32-am3 rm am)))))
(defun LDRH_POST (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-half32 rt wb rn (a32-am3 rm am))))
(defun LDRSH_POST (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-shalf32 rt wb rn (a32-am3 rm am))))
(defun LDRSB_POST (rt wb rn rm am cnd _) (a32-cond cnd (a32-load-post load-sbyte32 rt wb rn (a32-am3 rm am))))
(defun STRH_POST (wb rt rn rm am cnd _) (a32-cond cnd (a32-store-post store-half32 rt wb rn (a32-am3 rm am))))

(defun LDRHTi (rt wb rn off cnd _) (a32-cond cnd (a32-load-post load-half32 rt wb rn (a32-amt-imm off))))
(defun LDRSHTi (rt wb rn off cnd _) (a32-cond cnd (a32-load-post load-shalf32 rt wb rn (a32-amt-imm off))))
(defun LDRSBTi (rt wb rn off cnd _) (a32-cond cnd (a32-load-post load-sbyte32 rt wb rn (a32-amt-imm off))))
(defun STRHTi (wb rt rn off cnd _) (a32-cond cnd (a32-store-post store-half32 rt wb rn (a32-amt-imm off))))
(defun LDRHTr (rt wb rn rm add cnd _) (a32-cond cnd (a32-load-post load-half32 rt wb rn (a32-amt-reg rm add))))
(defun LDRSHTr (rt wb rn rm add cnd _) (a32-cond cnd (a32-load-post load-shalf32 rt wb rn (a32-amt-reg rm add))))
(defun LDRSBTr (rt wb rn rm add cnd _) (a32-cond cnd (a32-load-post load-sbyte32 rt wb rn (a32-amt-reg rm add))))
(defun STRHTr (wb rt rn rm add cnd _) (a32-cond cnd (a32-store-post store-half32 rt wb rn (a32-amt-reg rm add))))

;; the doubleword accesses, the first register is at the lower address

(defmacro a32-load-pair (rt rt2 a)
  (let ((addr a))
    (set$ rt (load-word addr))
    (set$ rt2 (load-word (+ addr 4)))))

(defmacro a32-load-named-pair (lo hi a)
  "loads the registers LO and HI that are named, not operands"
  (let ((addr a))
    (set lo (load-word addr))
    (set hi (load-word (+ addr 4)))))

(defmacro a32-store-pair (rt rt2 a)
  (let ((addr a))
    (store-word addr rt)
    (store-word (+ addr 4) rt2)))

(defun LDRD (rt rt2 rn rm am cnd _)
  (a32-cond cnd (a32-load-pair rt rt2 (+ (a32-reg rn) (a32-am3 rm am)))))
(defun STRD (rt rt2 rn rm am cnd _)
  (a32-cond cnd (a32-store-pair rt rt2 (+ rn (a32-am3 rm am)))))
(defun LDRD_PRE (rt rt2 wb rn rm am cnd _)
  (a32-cond cnd
    (let ((addr (+ rn (a32-am3 rm am))))
      (a32-load-pair rt rt2 addr)
      (set$ wb addr))))
(defun LDRD_POST (rt rt2 wb rn rm am cnd _)
  (a32-cond cnd
    (let ((addr rn))
      (a32-load-pair rt rt2 addr)
      (set$ wb (+ addr (a32-am3 rm am))))))
(defun STRD_PRE (wb rt rt2 rn rm am cnd _)
  (a32-cond cnd
    (let ((addr (+ rn (a32-am3 rm am))))
      (a32-store-pair rt rt2 addr)
      (set$ wb addr))))
(defun STRD_POST (wb rt rt2 rn rm am cnd _)
  (a32-cond cnd
    (let ((addr rn))
      (a32-store-pair rt rt2 addr)
      (set$ wb (+ addr (a32-am3 rm am))))))

;; the exclusive accesses, the monitor is not modeled and an exclusive
;; store succeeds, as in T32. The doubleword ones take a register pair,
;; e.g., R2_R3

(defun LDREX (rt rn cnd _) (a32-cond cnd (set$ rt (load-word32 rn))))
(defun LDREXB (rt rn cnd _) (a32-cond cnd (set$ rt (load-byte32 rn))))
(defun LDREXH (rt rn cnd _) (a32-cond cnd (set$ rt (load-half32 rn))))
(defun STREX (rd rt rn cnd _) (a32-cond cnd (prog (store-word rn rt) (set$ rd 0))))
(defun STREXB (rd rt rn cnd _) (a32-cond cnd (prog (store-byte rn rt) (set$ rd 0))))
(defun STREXH (rd rt rn cnd _) (a32-cond cnd (prog (store-half32 rn rt) (set$ rd 0))))

(defun LDREXD (p rn cnd _)
  (a32-cond cnd
    (let ((addr rn))
      (case (symbol p)
        'R0_R1 (a32-load-named-pair R0 R1 addr)
        'R2_R3 (a32-load-named-pair R2 R3 addr)
        'R4_R5 (a32-load-named-pair R4 R5 addr)
        'R6_R7 (a32-load-named-pair R6 R7 addr)
        'R8_R9 (a32-load-named-pair R8 R9 addr)
        'R10_R11 (a32-load-named-pair R10 R11 addr)))))

(defun STREXD (rd p rn cnd _)
  (a32-cond cnd
    (let ((addr rn))
      (case (symbol p)
        'R0_R1 (a32-store-pair R0 R1 addr)
        'R2_R3 (a32-store-pair R2 R3 addr)
        'R4_R5 (a32-store-pair R4 R5 addr)
        'R6_R7 (a32-store-pair R6 R7 addr)
        'R8_R9 (a32-store-pair R8 R9 addr)
        'R10_R11 (a32-store-pair R10 R11 addr))
      (set$ rd 0))))

;; the deprecated swap
(defun SWPB (rt rt2 rn cnd _)
  (a32-cond cnd
    (let ((addr rn) (v (load-byte32 addr)))
      (store-byte addr rt2)
      (set$ rt v))))
