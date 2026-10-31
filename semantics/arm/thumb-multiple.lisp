(require thumb)
(require arm-a32-multiple)

(declare (context (target arm-family)
                  (bits 32)))

(in-package thumb)

;;; THE NARROW MULTIPLE LOADS AND STORES
;;
;; `armMultiple` of the lifter does these too: both are here for a test
;; to tell them apart. As in `arm-a32-multiple`, the base is written back
;; before the registers are loaded, which is what makes a narrow LDM that
;; loads its base not write it back, and after they are stored.

(defun tPOP (cnd _ r1) (a32-ldm-upd 'ia SP SP cnd r1))
(defun tPOP (cnd _ r1 r2) (a32-ldm-upd 'ia SP SP cnd r1 r2))
(defun tPOP (cnd _ r1 r2 r3) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3))
(defun tPOP (cnd _ r1 r2 r3 r4) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3 r4))
(defun tPOP (cnd _ r1 r2 r3 r4 r5) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3 r4 r5))
(defun tPOP (cnd _ r1 r2 r3 r4 r5 r6) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3 r4 r5 r6))
(defun tPOP (cnd _ r1 r2 r3 r4 r5 r6 r7) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3 r4 r5 r6 r7))
(defun tPOP (cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun tPOP (cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (a32-ldm-upd 'ia SP SP cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))

(defun tPUSH (cnd _ r1) (a32-stm-upd 'db SP SP cnd r1))
(defun tPUSH (cnd _ r1 r2) (a32-stm-upd 'db SP SP cnd r1 r2))
(defun tPUSH (cnd _ r1 r2 r3) (a32-stm-upd 'db SP SP cnd r1 r2 r3))
(defun tPUSH (cnd _ r1 r2 r3 r4) (a32-stm-upd 'db SP SP cnd r1 r2 r3 r4))
(defun tPUSH (cnd _ r1 r2 r3 r4 r5) (a32-stm-upd 'db SP SP cnd r1 r2 r3 r4 r5))
(defun tPUSH (cnd _ r1 r2 r3 r4 r5 r6) (a32-stm-upd 'db SP SP cnd r1 r2 r3 r4 r5 r6))
(defun tPUSH (cnd _ r1 r2 r3 r4 r5 r6 r7) (a32-stm-upd 'db SP SP cnd r1 r2 r3 r4 r5 r6 r7))
(defun tPUSH (cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (a32-stm-upd 'db SP SP cnd r1 r2 r3 r4 r5 r6 r7 r8))
(defun tPUSH (cnd _ r1 r2 r3 r4 r5 r6 r7 r8 r9) (a32-stm-upd 'db SP SP cnd r1 r2 r3 r4 r5 r6 r7 r8 r9))

(defun tLDMIA (rn cnd _ r1) (a32-ldm-upd 'ia rn rn cnd r1))
(defun tLDMIA (rn cnd _ r1 r2) (a32-ldm-upd 'ia rn rn cnd r1 r2))
(defun tLDMIA (rn cnd _ r1 r2 r3) (a32-ldm-upd 'ia rn rn cnd r1 r2 r3))
(defun tLDMIA (rn cnd _ r1 r2 r3 r4) (a32-ldm-upd 'ia rn rn cnd r1 r2 r3 r4))
(defun tLDMIA (rn cnd _ r1 r2 r3 r4 r5) (a32-ldm-upd 'ia rn rn cnd r1 r2 r3 r4 r5))
(defun tLDMIA (rn cnd _ r1 r2 r3 r4 r5 r6) (a32-ldm-upd 'ia rn rn cnd r1 r2 r3 r4 r5 r6))
(defun tLDMIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7) (a32-ldm-upd 'ia rn rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun tLDMIA (rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (a32-ldm-upd 'ia rn rn cnd r1 r2 r3 r4 r5 r6 r7 r8))

(defun tSTMIA_UPD (wb rn cnd _ r1) (a32-stm-upd 'ia wb rn cnd r1))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2) (a32-stm-upd 'ia wb rn cnd r1 r2))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2 r3) (a32-stm-upd 'ia wb rn cnd r1 r2 r3))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2 r3 r4) (a32-stm-upd 'ia wb rn cnd r1 r2 r3 r4))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5) (a32-stm-upd 'ia wb rn cnd r1 r2 r3 r4 r5))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6) (a32-stm-upd 'ia wb rn cnd r1 r2 r3 r4 r5 r6))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7) (a32-stm-upd 'ia wb rn cnd r1 r2 r3 r4 r5 r6 r7))
(defun tSTMIA_UPD (wb rn cnd _ r1 r2 r3 r4 r5 r6 r7 r8) (a32-stm-upd 'ia wb rn cnd r1 r2 r3 r4 r5 r6 r7 r8))
