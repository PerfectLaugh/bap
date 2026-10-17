(declare (context (target armv7-a+fp)
                  (bits 32)))

(require thumb)
(require arm-vfp)

(in-package llvm-thumb)

;; In the T32 encoding PC reads as the address of the instruction
;; plus 4, see the A32 loads in arm-vfp.lisp.

(defun VLDRD (dd rn off cnd _) (vfp cnd (set$ dd (load-bits 64 (vfp-address 4 rn off)))))
(defun VLDRS (sd rn off cnd _) (vfp cnd (set$ sd (load-bits 32 (vfp-address 4 rn off)))))
