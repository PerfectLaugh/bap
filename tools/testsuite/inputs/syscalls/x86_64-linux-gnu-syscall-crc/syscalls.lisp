(require stdio)
(defun syscall ()
  (declare (external "intrinsic:syscall"))
  (set RAX (if (= RAX 1) (write RDI RSI RDX) -1)))
