(require stdio)
(defun svc ()
  (declare (external "intrinsic:svc"))
  (set R0 (if (= R8 64) (write R0 R1 R2) -1)))
