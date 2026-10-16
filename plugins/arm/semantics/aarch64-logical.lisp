(declare (context (target arm-family)
                  (bits 64)))

(in-package aarch64)

;;; LOGICAL/BITFIELD OPERATIONS

;; Logical

(defmacro ORN*rs (set rd rn rm is)
  "(ORN*rs set rd rn rm is) implements the OR NOT instruction
   accepting either a W or X register."
  (set rd (logor rn (lnot (lshift rm is)))))

(defun ORNWrs (rd rn rm is) (ORN*rs setw rd rn rm is))
(defun ORNXrs (rd rn rm is) (ORN*rs set$ rd rn rm is))

(defmacro BIC*rs (set rd rn rm is)
  "(BIC*rs set rd rn rm is) implements AND NOT (bit clear) of a shifted
   register, accepting either a W or X register."
  (set rd (logand rn (lnot (shift-encoded rm is)))))

(defun BICWrs (rd rn rm is) (BIC*rs setw rd rn rm is))
(defun BICXrs (rd rn rm is) (BIC*rs set$ rd rn rm is))

(defun set-nz-clear-cv (r)
  "Sets N and Z from the result r of a logical operation and clears C and V,
   as the flag-setting logical instructions (ANDS, BICS) do."
  (set NF (msb r))
  (set ZF (is-zero r))
  (set CF 0:1)
  (set VF 0:1))

(defmacro BICS*rs (set rd rn rm is)
  (let ((r (logand rn (lnot (shift-encoded rm is)))))
    (set rd r)
    (set-nz-clear-cv r)))

(defun BICSWrs (rd rn rm is) (BICS*rs setw rd rn rm is))
(defun BICSXrs (rd rn rm is) (BICS*rs set$ rd rn rm is))

(defmacro ANDS*ri (set op rd rn imm register-width)
  (let ((r (op rn (immediate-from-bitmask imm register-width))))
    (set rd r)
    (set-nz-clear-cv r)))

(defun ANDSWri (rd rn imm) (ANDS*ri setw logand rd rn imm 32))
(defun ANDSXri (rd rn imm) (ANDS*ri set$ logand rd rn imm 64))

(defmacro ANDS*rs (set rd rn rm is)
  (let ((r (logand rn (shift-encoded rm is))))
    (set rd r)
    (set-nz-clear-cv r)))

(defun ANDSWrs (rd rn rm is) (ANDS*rs setw rd rn rm is))
(defun ANDSXrs (rd rn rm is) (ANDS*rs set$ rd rn rm is))

(defmacro log*rs (set op rd rn rm is)
  "(log*rs set op rd rn is) implements the logical operation (shift) instruction
   accepting either a W or X register. op is the binary logical operation."
  (set rd (op rn (shift-encoded rm is))))

(defun ORRWrs (rd rn rm is) (log*rs setw logor  rd rn rm is))
(defun EORWrs (rd rn rm is) (log*rs setw logxor rd rn rm is))
(defun ANDWrs (rd rn rm is) (log*rs setw logand rd rn rm is))
(defun ORRXrs (rd rn rm is) (log*rs set$ logor  rd rn rm is))
(defun EORXrs (rd rn rm is) (log*rs set$ logxor rd rn rm is))
(defun ANDXrs (rd rn rm is) (log*rs set$ logand rd rn rm is))

(defmacro log*ri (set op rd rn imm register-width)
  "(log*ri set op rd rn imm register-width) implements the logical operation (immediate) instruction
   accepting either a W or X register. op is the binary logical operation, and register-width
   is the width of the given registers."
  (set rd (op rn (immediate-from-bitmask imm register-width))))

(defun ANDWri (rd rn imm) (log*ri setw logand rd rn imm 32))
(defun ANDXri (rd rn imm) (log*ri set$ logand rd rn imm 64))
(defun EORWri (rd rn imm) (log*ri setw logxor rd rn imm 32))
(defun EORXri (rd rn imm) (log*ri set$ logxor rd rn imm 64))
(defun ORRWri (rd rn imm) (log*ri setw logor  rd rn imm 32))
(defun ORRXri (rd rn imm) (log*ri set$ logor  rd rn imm 64))

;; UBFM and SBFM
;; (bitfield moves)

(defmacro make-eBFM (set cast xd xr ir is)
  "(make-BFM  cast xd xr ir is) implements bitfield move instructions
   accepting either a W or X register, with cast being an unsigned or signed cast."
  (let ((rs (word-width xd)))
    (if (< is ir)
        (set xd (lshift
                 (cast rs (cast-low (+1 is) xr))
                 (- rs ir)))
      (set xd (cast rs (extract is ir xr))))))

(defun UBFMXri (xd xr ir is)
  (make-eBFM set$ cast-unsigned xd xr ir is))

(defun UBFMWri (xd xr ir is)
  (make-eBFM setw cast-unsigned xd xr ir is))

(defun SBFMXri (xd xr ir is)
  (make-eBFM set$ cast-signed xd xr ir is))

(defun SBFMWri (xd xr ir is)
  (make-eBFM setw cast-signed xd xr ir is))

(defmacro BFM (set rd rn r s)
  (let ((size (word-width rd)))
    (if (>= s r)
      (set rd (concat 
               (cast-high (- size (+1 (- s r))) rd)
               (if (= r 0)
                 (cast-low (+1 s) rn) 
                 (extract s r rn))))
      (set rd (concat
               (cast-high (- r s) rd)
               (cast-low (+1 s) rn)
               (cast-low (-1 (- size r)) rd))))))

(defun BFMXri (_ xd xr ir is)
  (BFM set$ xd xr ir is))

(defun BFMWri (_ xd xr ir is)
  (BFM setw xd xr ir is))
