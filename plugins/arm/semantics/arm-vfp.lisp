(declare (context (target armv7-a+fp)
                  (bits 32)))

(in-package arm)

(require bits)
(require arm-bits)
(require arm-float)

;;; VFP INSTRUCTIONS
;;
;; The operations round to nearest with ties to even, which is the
;; rounding mode FPSCR resets to; only the NZCV bits of FPSCR are
;; modeled, so the FZ and DN controls, the rounding mode and the
;; exception flags are ignored. The helpers are in arm-float.lisp.

(defmacro vfp (cnd body)
  "(vfp CND BODY) evaluates BODY if the condition CND holds"
  (when (condition-holds cnd) body))

(defun vfp-compare (x y)
  "(vfp-compare X Y) sets the NZCV bits of FPSCR"
  (set FPSCR (concat (fp-nzcv x y) (cast-low 28 FPSCR))))

;; ARITHMETIC

(defun VADDD (rd rn rm cnd _) (vfp cnd (set$ rd (+. :rne rn rm))))
(defun VADDS (rd rn rm cnd _) (vfp cnd (set$ rd (+. :rne rn rm))))
(defun VSUBD (rd rn rm cnd _) (vfp cnd (set$ rd (-. :rne rn rm))))
(defun VSUBS (rd rn rm cnd _) (vfp cnd (set$ rd (-. :rne rn rm))))
(defun VMULD (rd rn rm cnd _) (vfp cnd (set$ rd (*. :rne rn rm))))
(defun VMULS (rd rn rm cnd _) (vfp cnd (set$ rd (*. :rne rn rm))))
(defun VDIVD (rd rn rm cnd _) (vfp cnd (set$ rd (/. :rne rn rm))))
(defun VDIVS (rd rn rm cnd _) (vfp cnd (set$ rd (/. :rne rn rm))))
(defun VNMULD (rd rn rm cnd _) (vfp cnd (set$ rd (fp-neg (*. :rne rn rm)))))
(defun VNMULS (rd rn rm cnd _) (vfp cnd (set$ rd (fp-neg (*. :rne rn rm)))))

;; the multiply-accumulate instructions round the product, the second
;; operand is the accumulator, which is tied to the destination
(defun VMLAD (rd ra rn rm cnd _) (vfp cnd (set$ rd (+. :rne ra (*. :rne rn rm)))))
(defun VMLAS (rd ra rn rm cnd _) (vfp cnd (set$ rd (+. :rne ra (*. :rne rn rm)))))
(defun VMLSD (rd ra rn rm cnd _) (vfp cnd (set$ rd (-. :rne ra (*. :rne rn rm)))))
(defun VMLSS (rd ra rn rm cnd _) (vfp cnd (set$ rd (-. :rne ra (*. :rne rn rm)))))
(defun VNMLAD (rd ra rn rm cnd _) (vfp cnd (set$ rd (fp-neg (+. :rne ra (*. :rne rn rm))))))
(defun VNMLAS (rd ra rn rm cnd _) (vfp cnd (set$ rd (fp-neg (+. :rne ra (*. :rne rn rm))))))
(defun VNMLSD (rd ra rn rm cnd _) (vfp cnd (set$ rd (-. :rne (*. :rne rn rm) ra))))
(defun VNMLSS (rd ra rn rm cnd _) (vfp cnd (set$ rd (-. :rne (*. :rne rn rm) ra))))

(defun VNEGD (rd rn cnd _) (vfp cnd (set$ rd (fp-neg rn))))
(defun VNEGS (rd rn cnd _) (vfp cnd (set$ rd (fp-neg rn))))
(defun VABSD (rd rn cnd _) (vfp cnd (set$ rd (fp-abs rn))))
(defun VABSS (rd rn cnd _) (vfp cnd (set$ rd (fp-abs rn))))
(defun VSQRTD (rd rn cnd _) (vfp cnd (set$ rd (fsqrt :rne rn))))
(defun VSQRTS (rd rn cnd _) (vfp cnd (set$ rd (fsqrt :rne rn))))

;; MOVES

(defun VMOVD (rd rn cnd _) (vfp cnd (set$ rd rn)))
(defun VMOVS (rd rn cnd _) (vfp cnd (set$ rd rn)))
(defun VMOVRS (rt sn cnd _) (vfp cnd (set$ rt sn)))
(defun VMOVSR (sn rt cnd _) (vfp cnd (set$ sn rt)))

(defun VMOVRRD (rt rt2 dm cnd _)
  (vfp cnd (prog (set$ rt (cast-low 32 dm))
                 (set$ rt2 (cast-high 32 dm)))))

(defun VMOVDRR (dm rt rt2 cnd _) (vfp cnd (set$ dm (concat rt2 rt))))

(defun VMOVSRR (sm sm1 rt rt2 cnd _)
  (vfp cnd (prog (set$ sm rt) (set$ sm1 rt2))))

(defun VMOVRRS (rt rt2 sm sm1 cnd _)
  (vfp cnd (prog (set$ rt sm) (set$ rt2 sm1))))

(defun FCONSTD (rd imm cnd _) (vfp cnd (set$ rd (vfp-expand-imm imm 11 52))))
(defun FCONSTS (rd imm cnd _) (vfp cnd (set$ rd (vfp-expand-imm imm 8 23))))

(defun FMSTAT (cnd _) (vfp cnd (set-nzcv (cast-high 4 FPSCR))))
(defun VMRS (rt cnd _) (vfp cnd (set$ rt FPSCR)))
(defun VMSR (rt cnd _) (vfp cnd (set FPSCR rt)))

;; CONVERSIONS

(defun VCVTDS (dd sm cnd _) (vfp cnd (set$ dd (fconvert :rne 64 sm))))
(defun VCVTSD (sd dm cnd _) (vfp cnd (set$ sd (fconvert :rne 32 dm))))
(defun VSITOD (dd sm cnd _) (vfp cnd (set$ dd (cast-sfloat :rne 64 sm))))
(defun VUITOD (dd sm cnd _) (vfp cnd (set$ dd (cast-float :rne 64 sm))))
(defun VSITOS (sd sm cnd _) (vfp cnd (set$ sd (cast-sfloat :rne 32 sm))))
(defun VUITOS (sd sm cnd _) (vfp cnd (set$ sd (cast-float :rne 32 sm))))

;; the Z forms round toward zero, the R forms use the FPSCR rounding
;; mode, which is assumed to be to nearest
(defun VTOSIZD (sd dm cnd _) (vfp cnd (set$ sd (fp-to-int true 32 dm 11 52))))
(defun VTOUIZD (sd dm cnd _) (vfp cnd (set$ sd (fp-to-int false 32 dm 11 52))))
(defun VTOSIZS (sd sm cnd _) (vfp cnd (set$ sd (fp-to-int true 32 sm 8 23))))
(defun VTOUIZS (sd sm cnd _) (vfp cnd (set$ sd (fp-to-int false 32 sm 8 23))))

(defmacro VTO*IR (signed sd x one half e f cnd)
  (vfp cnd (set$ sd (fp-to-int signed 32
                               (fp-round-integral 'n x one half e f)
                               e f))))

(defun VTOSIRD (sd dm cnd _)
  (VTO*IR true sd dm 0x3ff0000000000000 0x3fe0000000000000 11 52 cnd))
(defun VTOUIRD (sd dm cnd _)
  (VTO*IR false sd dm 0x3ff0000000000000 0x3fe0000000000000 11 52 cnd))
(defun VTOSIRS (sd sm cnd _)
  (VTO*IR true sd sm (cast-low 32 0x3f800000) (cast-low 32 0x3f000000) 8 23 cnd))
(defun VTOUIRS (sd sm cnd _)
  (VTO*IR false sd sm (cast-low 32 0x3f800000) (cast-low 32 0x3f000000) 8 23 cnd))

;; COMPARISON

(defun VCMPD (dd dm cnd _) (vfp cnd (vfp-compare dd dm)))
(defun VCMPS (sd sm cnd _) (vfp cnd (vfp-compare sd sm)))
(defun VCMPED (dd dm cnd _) (vfp cnd (vfp-compare dd dm)))
(defun VCMPES (sd sm cnd _) (vfp cnd (vfp-compare sd sm)))
(defun VCMPZD (dd cnd _) (vfp cnd (vfp-compare dd (fp-zero dd))))
(defun VCMPZS (sd cnd _) (vfp cnd (vfp-compare sd (fp-zero sd))))
(defun VCMPEZD (dd cnd _) (vfp cnd (vfp-compare dd (fp-zero dd))))
(defun VCMPEZS (sd cnd _) (vfp cnd (vfp-compare sd (fp-zero sd))))

;; LOADS AND STORES

(defun vfp-base (pc rn)
  "(vfp-base PC RN) is the value of the base register RN, PC reads as
   the word-aligned address of the instruction plus PC, which is 8 in
   the A32 and 4 in the T32 encoding"
  (if (= (symbol rn) 'PC)
      (logand (+ (get-program-counter) pc) (lnot 3))
    rn))

(defun vfp-address (pc rn off)
  "(vfp-address PC RN OFF) is the address of the addressing mode 5
   with the base RN and the encoded offset OFF, which is the number of
   words in the low byte and the subtraction flag in the bit 8"
  (let ((base (vfp-base pc rn))
        (disp (lshift (extract 7 0 off) 2)))
    (if (= 1 (select 8 off))
        (- base (cast-unsigned (word-width) disp))
      (+ base (cast-unsigned (word-width) disp)))))

(defun VSTRD (dd rn off cnd _) (vfp cnd (store-word (vfp-address 8 rn off) dd)))
(defun VSTRS (sd rn off cnd _) (vfp cnd (store-word (vfp-address 8 rn off) sd)))

;; The load and store multiple instructions take the registers as the
;; trailing operands. As a function has a fixed number of parameters,
;; each instruction is defined for each number of registers, up to 16.
;; The registers are transferred from the lowest address upward; the
;; DB forms start below the base and write the lowest address back,
;; the IA forms write back the address after the last register.

(defmacro vldm-regs (addr r) (set$ r (load-bits (word-width r) addr)))
(defmacro vldm-regs (addr r rs)
  (prog (set$ r (load-bits (word-width r) addr))
        (vldm-regs (+ addr (/ (word-width r) 8)) rs)))

(defmacro vstm-regs (addr r) (store-word addr r))
(defmacro vstm-regs (addr r rs)
  (prog (store-word addr r)
        (vstm-regs (+ addr (/ (word-width r) 8)) rs)))

(defmacro vfp-regs-size (r) (/ (word-width r) 8))
(defmacro vfp-regs-size (r rs) (+ (/ (word-width r) 8) (vfp-regs-size rs)))

(defmacro VLDM*IA (rn cnd regs)
  (vfp cnd (let ((a rn)) (vldm-regs a regs))))
(defmacro VLDM*IA_UPD (wb rn cnd regs)
  (vfp cnd (let ((a rn))
             (vldm-regs a regs)
             (set$ wb (+ a (vfp-regs-size regs))))))
(defmacro VLDM*DB_UPD (wb rn cnd regs)
  (vfp cnd (let ((a (- rn (vfp-regs-size regs))))
             (vldm-regs a regs)
             (set$ wb a))))
(defmacro VSTM*IA (rn cnd regs)
  (vfp cnd (let ((a rn)) (vstm-regs a regs))))
(defmacro VSTM*IA_UPD (wb rn cnd regs)
  (vfp cnd (let ((a rn))
             (vstm-regs a regs)
             (set$ wb (+ a (vfp-regs-size regs))))))
(defmacro VSTM*DB_UPD (wb rn cnd regs)
  (vfp cnd (let ((a (- rn (vfp-regs-size regs))))
             (vstm-regs a regs)
             (set$ wb a))))

(defun VLDMDIA (rn cnd _ r1) (VLDM*IA rn cnd r1))
(defun VLDMDIA (rn cnd _ r1 r2) (VLDM*IA rn cnd r1 r2))
(defun VLDMDIA (rn cnd _ r1 r2 r3) (VLDM*IA rn cnd r1 r2 r3))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4) (VLDM*IA rn cnd r1 r2 r3 r4))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5) (VLDM*IA rn cnd r1 r2 r3 r4 r5))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VLDMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VLDMSIA (rn cnd _ r1) (VLDM*IA rn cnd r1))
(defun VLDMSIA (rn cnd _ r1 r2) (VLDM*IA rn cnd r1 r2))
(defun VLDMSIA (rn cnd _ r1 r2 r3) (VLDM*IA rn cnd r1 r2 r3))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4) (VLDM*IA rn cnd r1 r2 r3 r4))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5) (VLDM*IA rn cnd r1 r2 r3 r4 r5))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VLDMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VLDM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VSTMDIA (rn cnd _ r1) (VSTM*IA rn cnd r1))
(defun VSTMDIA (rn cnd _ r1 r2) (VSTM*IA rn cnd r1 r2))
(defun VSTMDIA (rn cnd _ r1 r2 r3) (VSTM*IA rn cnd r1 r2 r3))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4) (VSTM*IA rn cnd r1 r2 r3 r4))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5) (VSTM*IA rn cnd r1 r2 r3 r4 r5))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VSTMDIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VSTMSIA (rn cnd _ r1) (VSTM*IA rn cnd r1))
(defun VSTMSIA (rn cnd _ r1 r2) (VSTM*IA rn cnd r1 r2))
(defun VSTMSIA (rn cnd _ r1 r2 r3) (VSTM*IA rn cnd r1 r2 r3))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4) (VSTM*IA rn cnd r1 r2 r3 r4))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5) (VSTM*IA rn cnd r1 r2 r3 r4 r5))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VSTMSIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VSTM*IA rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VLDMDIA_UPD (wb rn cnd _ r1) (VLDM*IA_UPD wb rn cnd r1))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2) (VLDM*IA_UPD wb rn cnd r1 r2))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3) (VLDM*IA_UPD wb rn cnd r1 r2 r3))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VLDMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VLDMSIA_UPD (wb rn cnd _ r1) (VLDM*IA_UPD wb rn cnd r1))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2) (VLDM*IA_UPD wb rn cnd r1 r2))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3) (VLDM*IA_UPD wb rn cnd r1 r2 r3))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VLDMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VLDM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VLDMDDB_UPD (wb rn cnd _ r1) (VLDM*DB_UPD wb rn cnd r1))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2) (VLDM*DB_UPD wb rn cnd r1 r2))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3) (VLDM*DB_UPD wb rn cnd r1 r2 r3))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VLDMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VLDMSDB_UPD (wb rn cnd _ r1) (VLDM*DB_UPD wb rn cnd r1))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2) (VLDM*DB_UPD wb rn cnd r1 r2))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3) (VLDM*DB_UPD wb rn cnd r1 r2 r3))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VLDMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VLDM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VSTMDIA_UPD (wb rn cnd _ r1) (VSTM*IA_UPD wb rn cnd r1))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2) (VSTM*IA_UPD wb rn cnd r1 r2))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3) (VSTM*IA_UPD wb rn cnd r1 r2 r3))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VSTMDIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VSTMSIA_UPD (wb rn cnd _ r1) (VSTM*IA_UPD wb rn cnd r1))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2) (VSTM*IA_UPD wb rn cnd r1 r2))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3) (VSTM*IA_UPD wb rn cnd r1 r2 r3))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VSTMSIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VSTM*IA_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VSTMDDB_UPD (wb rn cnd _ r1) (VSTM*DB_UPD wb rn cnd r1))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2) (VSTM*DB_UPD wb rn cnd r1 r2))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3) (VSTM*DB_UPD wb rn cnd r1 r2 r3))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VSTMDDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

(defun VSTMSDB_UPD (wb rn cnd _ r1) (VSTM*DB_UPD wb rn cnd r1))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2) (VSTM*DB_UPD wb rn cnd r1 r2))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3) (VSTM*DB_UPD wb rn cnd r1 r2 r3))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15))
(defun VSTMSDB_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16) (VSTM*DB_UPD wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16))

;; The loads can have the PC base, which reads differently in the A32
;; and T32 encodings, so they are defined for each encoding, the T32
;; ones are in thumb-vfp.lisp. The stores with the PC base are
;; unpredictable.

(in-package llvm-armv7)

(defun VLDRD (dd rn off cnd _) (vfp cnd (set$ dd (load-bits 64 (vfp-address 8 rn off)))))
(defun VLDRS (sd rn off cnd _) (vfp cnd (set$ sd (load-bits 32 (vfp-address 8 rn off)))))
