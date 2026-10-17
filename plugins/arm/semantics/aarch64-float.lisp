(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

(require arm-float)

;;; SCALAR FLOATING-POINT INSTRUCTIONS
;;
;; The operations round to nearest with ties to even, which is the
;; rounding mode FPCR resets to; FPCR itself is not modeled, so the
;; FZ, DN and AHP controls and the exception flags are ignored. The
;; helpers are in arm-float.lisp.

(defun fp-compare (x y) (set-nzcv (fp-nzcv x y)))

;; ARITHMETIC

(defun FADDSrr (rd rn rm) (setd rd (+. :rne rn rm)))
(defun FADDDrr (rd rn rm) (setd rd (+. :rne rn rm)))
(defun FSUBSrr (rd rn rm) (setd rd (-. :rne rn rm)))
(defun FSUBDrr (rd rn rm) (setd rd (-. :rne rn rm)))
(defun FMULSrr (rd rn rm) (setd rd (*. :rne rn rm)))
(defun FMULDrr (rd rn rm) (setd rd (*. :rne rn rm)))
(defun FDIVSrr (rd rn rm) (setd rd (/. :rne rn rm)))
(defun FDIVDrr (rd rn rm) (setd rd (/. :rne rn rm)))
(defun FNMULSrr (rd rn rm) (setd rd (fp-neg (*. :rne rn rm))))
(defun FNMULDrr (rd rn rm) (setd rd (fp-neg (*. :rne rn rm))))

;; The multiply-add instructions are fused, i.e., they round only
;; once, but the semantics below rounds the product first, so the
;; result may differ from the hardware in the last bit.
(defun FMADDSrrr (rd rn rm ra) (setd rd (+. :rne ra (*. :rne rn rm))))
(defun FMADDDrrr (rd rn rm ra) (setd rd (+. :rne ra (*. :rne rn rm))))
(defun FMSUBSrrr (rd rn rm ra) (setd rd (-. :rne ra (*. :rne rn rm))))
(defun FMSUBDrrr (rd rn rm ra) (setd rd (-. :rne ra (*. :rne rn rm))))
(defun FNMADDSrrr (rd rn rm ra) (setd rd (fp-neg (+. :rne ra (*. :rne rn rm)))))
(defun FNMADDDrrr (rd rn rm ra) (setd rd (fp-neg (+. :rne ra (*. :rne rn rm)))))
(defun FNMSUBSrrr (rd rn rm ra) (setd rd (-. :rne (*. :rne rn rm) ra)))
(defun FNMSUBDrrr (rd rn rm ra) (setd rd (-. :rne (*. :rne rn rm) ra)))

(defun FSQRTSr (rd rn) (setd rd (fsqrt :rne rn)))
(defun FSQRTDr (rd rn) (setd rd (fsqrt :rne rn)))
(defun FABSSr (rd rn) (setd rd (fp-abs rn)))
(defun FABSDr (rd rn) (setd rd (fp-abs rn)))
(defun FNEGSr (rd rn) (setd rd (fp-neg rn)))
(defun FNEGDr (rd rn) (setd rd (fp-neg rn)))

(defun FMINSrr (rd rn rm) (setd rd (fp-min rn rm 23)))
(defun FMINDrr (rd rn rm) (setd rd (fp-min rn rm 52)))
(defun FMAXSrr (rd rn rm) (setd rd (fp-max rn rm 23)))
(defun FMAXDrr (rd rn rm) (setd rd (fp-max rn rm 52)))
(defun FMINNMSrr (rd rn rm) (setd rd (fp-minnm rn rm 23)))
(defun FMINNMDrr (rd rn rm) (setd rd (fp-minnm rn rm 52)))
(defun FMAXNMSrr (rd rn rm) (setd rd (fp-maxnm rn rm 23)))
(defun FMAXNMDrr (rd rn rm) (setd rd (fp-maxnm rn rm 52)))

;; ROUNDING TO INTEGRAL. FRINTX and FRINTI use the FPCR rounding
;; mode, which is assumed to be to nearest.

(defmacro FRINT*Sr (mode rd rn)
  (setd rd (fp-round-integral mode rn
                              (cast-low 32 0x3f800000)
                              (cast-low 32 0x3f000000)
                              8 23)))

(defmacro FRINT*Dr (mode rd rn)
  (setd rd (fp-round-integral mode rn
                              0x3ff0000000000000
                              0x3fe0000000000000
                              11 52)))

(defun FRINTNSr (rd rn) (FRINT*Sr 'n rd rn))
(defun FRINTNDr (rd rn) (FRINT*Dr 'n rd rn))
(defun FRINTASr (rd rn) (FRINT*Sr 'a rd rn))
(defun FRINTADr (rd rn) (FRINT*Dr 'a rd rn))
(defun FRINTPSr (rd rn) (FRINT*Sr 'p rd rn))
(defun FRINTPDr (rd rn) (FRINT*Dr 'p rd rn))
(defun FRINTMSr (rd rn) (FRINT*Sr 'm rd rn))
(defun FRINTMDr (rd rn) (FRINT*Dr 'm rd rn))
(defun FRINTZSr (rd rn) (FRINT*Sr 'z rd rn))
(defun FRINTZDr (rd rn) (FRINT*Dr 'z rd rn))
(defun FRINTXSr (rd rn) (FRINT*Sr 'n rd rn))
(defun FRINTXDr (rd rn) (FRINT*Dr 'n rd rn))
(defun FRINTISr (rd rn) (FRINT*Sr 'n rd rn))
(defun FRINTIDr (rd rn) (FRINT*Dr 'n rd rn))

;; COMPARISON AND SELECTION

(defun FCMPSrr (rn rm) (fp-compare rn rm))
(defun FCMPDrr (rn rm) (fp-compare rn rm))
(defun FCMPSri (rn) (fp-compare rn (fp-zero rn)))
(defun FCMPDri (rn) (fp-compare rn (fp-zero rn)))
(defun FCMPESrr (rn rm) (fp-compare rn rm))
(defun FCMPEDrr (rn rm) (fp-compare rn rm))
(defun FCMPESri (rn) (fp-compare rn (fp-zero rn)))
(defun FCMPEDri (rn) (fp-compare rn (fp-zero rn)))

(defmacro FCCMP** (rn rm nzcv cnd)
  (if (condition-holds cnd)
      (fp-compare rn rm)
    (set-nzcv nzcv)))

(defun FCCMPSrr (rn rm nzcv cnd) (FCCMP** rn rm nzcv cnd))
(defun FCCMPDrr (rn rm nzcv cnd) (FCCMP** rn rm nzcv cnd))
(defun FCCMPESrr (rn rm nzcv cnd) (FCCMP** rn rm nzcv cnd))
(defun FCCMPEDrr (rn rm nzcv cnd) (FCCMP** rn rm nzcv cnd))

(defun FCSELSrrr (rd rn rm cnd) (setd rd (if (condition-holds cnd) rn rm)))
(defun FCSELDrrr (rd rn rm cnd) (setd rd (if (condition-holds cnd) rn rm)))

;; MOVES

(defun FMOVSr (rd rn) (setd rd rn))
(defun FMOVDr (rd rn) (setd rd rn))
(defun FMOVWSr (rd rn) (setd rd (cast-low 32 rn)))
(defun FMOVXDr (rd rn) (setd rd (cast-low 64 rn)))
(defun FMOVSWr (rd rn) (setw rd (cast-unsigned (word) (cast-low 32 rn))))
(defun FMOVDXr (rd rn) (set$ rd (cast-low 64 rn)))
(defun FMOVSi (rd imm) (setd rd (vfp-expand-imm imm 8 23)))
(defun FMOVDi (rd imm) (setd rd (vfp-expand-imm imm 11 52)))

(defun MOVID (rd imm)
  "movi Dd, #imm sets each byte of Dd to the replicated bit of imm"
  (setd rd (concat (replicate-to-fill (select 7 imm) 8)
                   (replicate-to-fill (select 6 imm) 8)
                   (replicate-to-fill (select 5 imm) 8)
                   (replicate-to-fill (select 4 imm) 8)
                   (replicate-to-fill (select 3 imm) 8)
                   (replicate-to-fill (select 2 imm) 8)
                   (replicate-to-fill (select 1 imm) 8)
                   (replicate-to-fill (select 0 imm) 8))))

;; CONVERSIONS

(defun SCVTFUWSri (rd rn) (setd rd (cast-sfloat :rne 32 (cast-low 32 rn))))
(defun SCVTFUWDri (rd rn) (setd rd (cast-sfloat :rne 64 (cast-low 32 rn))))
(defun SCVTFUXSri (rd rn) (setd rd (cast-sfloat :rne 32 (cast-low 64 rn))))
(defun SCVTFUXDri (rd rn) (setd rd (cast-sfloat :rne 64 (cast-low 64 rn))))
(defun UCVTFUWSri (rd rn) (setd rd (cast-float :rne 32 (cast-low 32 rn))))
(defun UCVTFUWDri (rd rn) (setd rd (cast-float :rne 64 (cast-low 32 rn))))
(defun UCVTFUXSri (rd rn) (setd rd (cast-float :rne 32 (cast-low 64 rn))))
(defun UCVTFUXDri (rd rn) (setd rd (cast-float :rne 64 (cast-low 64 rn))))

(defun FCVTZSUWSr (rd rn) (setw rd (cast-unsigned (word) (fp-to-int true 32 rn 8 23))))
(defun FCVTZSUWDr (rd rn) (setw rd (cast-unsigned (word) (fp-to-int true 32 rn 11 52))))
(defun FCVTZSUXSr (rd rn) (set$ rd (fp-to-int true 64 rn 8 23)))
(defun FCVTZSUXDr (rd rn) (set$ rd (fp-to-int true 64 rn 11 52)))
(defun FCVTZUUWSr (rd rn) (setw rd (cast-unsigned (word) (fp-to-int false 32 rn 8 23))))
(defun FCVTZUUWDr (rd rn) (setw rd (cast-unsigned (word) (fp-to-int false 32 rn 11 52))))
(defun FCVTZUUXSr (rd rn) (set$ rd (fp-to-int false 64 rn 8 23)))
(defun FCVTZUUXDr (rd rn) (set$ rd (fp-to-int false 64 rn 11 52)))

(defun FCVTDSr (rd rn) (setd rd (fconvert :rne 64 rn)))
(defun FCVTSDr (rd rn) (setd rd (fconvert :rne 32 rn)))

;; LOADS AND STORES

(defun LDRSui (rt rn off) (setd rt (load-hword (+ rn (lshift off 2)))))
(defun STRSui (rt rn off) (store-word (+ rn (lshift off 2)) (cast-low 32 rt)))

(defun LDURSi (rt rn off) (setd rt (load-hword (+ rn off))))
(defun LDURDi (rt rn off) (setd rt (load-word (+ rn off))))
(defun LDURQi (rt rn off) (set$ rt (load-bits 128 (+ rn off))))
(defun STURSi (rt rn off) (store-word (+ rn off) (cast-low 32 rt)))
(defun STURDi (rt rn off) (store-word (+ rn off) (cast-low 64 rt)))
(defun STURQi (rt rn off) (store-word (+ rn off) (cast-low 128 rt)))

(defun LDRSl (rt off) (setd rt (load-hword (+ (get-program-counter) (lshift off 2)))))
(defun LDRDl (rt off) (setd rt (load-word (+ (get-program-counter) (lshift off 2)))))
(defun LDRQl (rt off) (set$ rt (load-bits 128 (+ (get-program-counter) (lshift off 2)))))

;; the pre- and post-indexed forms write the address back to the
;; first (tied) operand, which is the base register.

(defun LDRSpost (wb rt rn off)
  (setd rt (load-hword rn))
  (set$ wb (+ rn off)))

(defun LDRDpost (wb rt rn off)
  (setd rt (load-word rn))
  (set$ wb (+ rn off)))

(defun LDRQpost (wb rt rn off)
  (set$ rt (load-bits 128 rn))
  (set$ wb (+ rn off)))

(defun LDRSpre (wb rt rn off)
  (let ((addr (+ rn off)))
    (setd rt (load-hword addr))
    (set$ wb addr)))

(defun LDRDpre (wb rt rn off)
  (let ((addr (+ rn off)))
    (setd rt (load-word addr))
    (set$ wb addr)))

(defun LDRQpre (wb rt rn off)
  (let ((addr (+ rn off)))
    (set$ rt (load-bits 128 addr))
    (set$ wb addr)))

(defun STRSpost (wb rt rn off)
  (store-word rn (cast-low 32 rt))
  (set$ wb (+ rn off)))

(defun STRDpost (wb rt rn off)
  (store-word rn (cast-low 64 rt))
  (set$ wb (+ rn off)))

(defun STRQpost (wb rt rn off)
  (store-word rn (cast-low 128 rt))
  (set$ wb (+ rn off)))

(defun STRSpre (wb rt rn off)
  (let ((addr (+ rn off)))
    (store-word addr (cast-low 32 rt))
    (set$ wb addr)))

(defun STRDpre (wb rt rn off)
  (let ((addr (+ rn off)))
    (store-word addr (cast-low 64 rt))
    (set$ wb addr)))

(defun STRQpre (wb rt rn off)
  (let ((addr (+ rn off)))
    (store-word addr (cast-low 128 rt))
    (set$ wb addr)))

;; register pairs, the offset is scaled by the size of the register

(defmacro LDP*S (r1 r2 addr)
  (let ((a addr))
    (setd r1 (load-hword a))
    (setd r2 (load-hword (+ a 4)))))

(defmacro LDP*D (r1 r2 addr)
  (let ((a addr))
    (setd r1 (load-word a))
    (setd r2 (load-word (+ a 8)))))

(defmacro LDP*Q (r1 r2 addr)
  (let ((a addr))
    (set$ r1 (load-bits 128 a))
    (set$ r2 (load-bits 128 (+ a 16)))))

(defmacro STP*S (r1 r2 addr)
  (let ((a addr))
    (store-word a (cast-low 32 r1))
    (store-word (+ a 4) (cast-low 32 r2))))

(defmacro STP*D (r1 r2 addr)
  (let ((a addr))
    (store-word a (cast-low 64 r1))
    (store-word (+ a 8) (cast-low 64 r2))))

(defmacro STP*Q (r1 r2 addr)
  (let ((a addr))
    (store-word a (cast-low 128 r1))
    (store-word (+ a 16) (cast-low 128 r2))))

(defun LDPSi (r1 r2 rn off) (LDP*S r1 r2 (+ rn (lshift off 2))))
(defun LDPDi (r1 r2 rn off) (LDP*D r1 r2 (+ rn (lshift off 3))))
(defun LDPQi (r1 r2 rn off) (LDP*Q r1 r2 (+ rn (lshift off 4))))
(defun STPSi (r1 r2 rn off) (STP*S r1 r2 (+ rn (lshift off 2))))
(defun STPDi (r1 r2 rn off) (STP*D r1 r2 (+ rn (lshift off 3))))
(defun STPQi (r1 r2 rn off) (STP*Q r1 r2 (+ rn (lshift off 4))))

(defun LDPSpost (wb r1 r2 rn off)
  (let ((a rn)) (LDP*S r1 r2 a) (set$ wb (+ a (lshift off 2)))))
(defun LDPDpost (wb r1 r2 rn off)
  (let ((a rn)) (LDP*D r1 r2 a) (set$ wb (+ a (lshift off 3)))))
(defun LDPQpost (wb r1 r2 rn off)
  (let ((a rn)) (LDP*Q r1 r2 a) (set$ wb (+ a (lshift off 4)))))
(defun STPSpost (wb r1 r2 rn off)
  (let ((a rn)) (STP*S r1 r2 a) (set$ wb (+ a (lshift off 2)))))
(defun STPDpost (wb r1 r2 rn off)
  (let ((a rn)) (STP*D r1 r2 a) (set$ wb (+ a (lshift off 3)))))
(defun STPQpost (wb r1 r2 rn off)
  (let ((a rn)) (STP*Q r1 r2 a) (set$ wb (+ a (lshift off 4)))))

(defun LDPSpre (wb r1 r2 rn off)
  (let ((a (+ rn (lshift off 2)))) (LDP*S r1 r2 a) (set$ wb a)))
(defun LDPDpre (wb r1 r2 rn off)
  (let ((a (+ rn (lshift off 3)))) (LDP*D r1 r2 a) (set$ wb a)))
(defun LDPQpre (wb r1 r2 rn off)
  (let ((a (+ rn (lshift off 4)))) (LDP*Q r1 r2 a) (set$ wb a)))
(defun STPSpre (wb r1 r2 rn off)
  (let ((a (+ rn (lshift off 2)))) (STP*S r1 r2 a) (set$ wb a)))
(defun STPDpre (wb r1 r2 rn off)
  (let ((a (+ rn (lshift off 3)))) (STP*D r1 r2 a) (set$ wb a)))
(defun STPQpre (wb r1 r2 rn off)
  (let ((a (+ rn (lshift off 4)))) (STP*Q r1 r2 a) (set$ wb a)))
