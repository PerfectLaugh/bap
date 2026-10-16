(declare (context (target arm-family)
                  (bits 64)))


(in-package aarch64)

;;; INTEGER ARITHMETIC OPERATIONS

(defmacro ADD*r* (set shift-function rd rn imm-or-rm off)
  "Implements ADD*ri and ADD*rs by specifying the shift function."
  (set rd (+ rn (shift-function imm-or-rm off))))

;; ADD*ri only uses lshift since the shift arg only zero-extends
;; and doesn't actually change from lshift
(defun ADDWri (rd rn imm off) (ADD*r* setw lshift rd rn imm off))
(defun ADDXri (rd rn imm off) (ADD*r* set$ lshift rd rn imm off))
;; shift-encoded decodes the shift type and shifts
(defun ADDWrs (rd rn rm off) (ADD*r* setw shift-encoded rd rn rm off))
(defun ADDXrs (rd rn rm off) (ADD*r* set$ shift-encoded rd rn rm off))

(defun ADRP (dst imm)
  (set$ dst (+
             (logand (get-program-counter) (lshift -1 12))
             (cast-signed (word) (lshift imm 12)))))

;; the immediate of ADR is the byte offset from the instruction
(defun ADR (dst imm)
  (set$ dst (+ (get-program-counter) (cast-signed (word) imm))))

(defmacro SUB*r* (set shift-function rd rn imm-or-rm off)
  "Implements SUB*ri and SUB*rs by specifying the shift function."
  (set rd (- rn (shift-function imm-or-rm off))))

;; see ADD*ri vs ADD*rs
(defun SUBWri (rd rn rm off) (SUB*r* setw lshift rd rn rm off))
(defun SUBXri (rd rn rm off) (SUB*r* set$ lshift rd rn rm off))
(defun SUBWrs (rd rn rm off) (SUB*r* setw shift-encoded rd rn rm off))
(defun SUBXrs (rd rn rm off) (SUB*r* set$ shift-encoded rd rn rm off))

(defun SUBXrx64 (rd rn rm off)
  (set$ rd (- rn (extended rm off))))

(defun ADDWrx (rd rn rm off)
  (setw rd (cast-low 32 (+ rn (extended rm off)))))

(defun ADDXrx (rd rn rm off)
  (set$ rd (+ rn (extended rm off))))

(defun ADDXrx64 (rd rn rm off)
  (set$ rd (+ rn (extended rm off))))

;; ADDS/SUBS set the NZCV flags from the result. The W-forms go through
;; add-with-carry/clear-base, which computes at 32-bit width.
(defun ADDSWri (rd rn imm off)
  (add-with-carry/clear-base rd rn (lshift imm off) 0))

(defun ADDSXri (rd rn imm off)
  (add-with-carry rd rn (lshift imm off) 0))

(defun ADDSWrs (rd rn rm off)
  (add-with-carry/clear-base rd rn (shift-encoded rm off) 0))

(defun ADDSXrs (rd rn rm off)
  (add-with-carry rd rn (shift-encoded rm off) 0))

(defun SUBSWrs (rd rn rm off)
  (add-with-carry/clear-base rd rn (lnot (shift-encoded rm off)) 1))

(defun SUBSXrs (rd rn rm off)
  (add-with-carry rd rn (lnot (shift-encoded rm off)) 1))

(defun SUBSWri (rd rn imm off)
  (add-with-carry/clear-base rd rn (lnot (lshift imm off)) 1))

(defun SUBSXri (rd rn imm off)
  (add-with-carry rd rn (lnot (lshift imm off)) 1))

(defmacro Mop*rrr (set op rd rn rm ra)
  "(Mop*rrr set op rd rn rm ra) implements multiply-add, multiply-subtract
   etc with W or X registers. op is the binary operation used after *."
  (set rd (op ra (* rn rm))))

(defun MADDWrrr (rd rn rm ra) (Mop*rrr setw + rd rn rm ra))
(defun MADDXrrr (rd rn rm ra) (Mop*rrr set$ + rd rn rm ra))
(defun MSUBWrrr (rd rn rm ra) (Mop*rrr setw - rd rn rm ra))
(defun MSUBXrrr (rd rn rm ra) (Mop*rrr set$ - rd rn rm ra))

(defmacro *DIV*r (set div rd rn rm)
  "(*DIV*r set div rd rn rm) implements the SDIV or UDIV instructions
   on W or X registers, with div set to s/ or / respectively."
  (if (= rm 0)
    (set rd 0)
    (set rd (div rn rm))))

(defun SDIVWr (rd rn rm) (*DIV*r setw s/ rd rn rm))
(defun SDIVXr (rd rn rm) (*DIV*r set$ s/ rd rn rm))
(defun UDIVWr (rd rn rm) (*DIV*r setw /  rd rn rm))
(defun UDIVXr (rd rn rm) (*DIV*r set$ /  rd rn rm))

;;; VARIABLE SHIFTS

(defmacro *SHIFT*r (set shift width rd rn rm)
  "Variable shift of rn by rm mod datasize. width is the datasize (32 or 64),
   so the shift amount is taken from the low 5 (W) or 6 (X) bits of rm."
  (set rd (shift rn (cast-unsigned width (cast-low (if (= width 64) 6 5) rm)))))

(defun LSLVWr (rd rn rm) (*SHIFT*r setw lshift  32 rd rn rm))
(defun LSLVXr (rd rn rm) (*SHIFT*r set$ lshift  64 rd rn rm))
(defun LSRVWr (rd rn rm) (*SHIFT*r setw rshift  32 rd rn rm))
(defun LSRVXr (rd rn rm) (*SHIFT*r set$ rshift  64 rd rn rm))
(defun ASRVWr (rd rn rm) (*SHIFT*r setw arshift 32 rd rn rm))
(defun ASRVXr (rd rn rm) (*SHIFT*r set$ arshift 64 rd rn rm))
(defun RORVWr (rd rn rm) (setw rd (rotate-right rn (cast-unsigned 32 (cast-low 5 rm)))))
(defun RORVXr (rd rn rm) (set$ rd (rotate-right rn (cast-unsigned 64 (cast-low 6 rm)))))

;;; BIT COUNTING AND REVERSAL

(defun CLZWr (rd rn) (setw rd (cast-unsigned (word) (clz (cast-low 32 rn)))))
(defun CLZXr (rd rn) (set$ rd (cast-unsigned (word) (clz rn))))

(defun RBITWr (rd rn) (setw rd (reverse-bits (cast-low 32 rn))))
(defun RBITXr (rd rn) (set$ rd (reverse-bits rn)))
