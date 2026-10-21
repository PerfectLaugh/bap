(defun debug (dst src)
  (declare (advice :before strcpy))
  (bap-exit 7))
