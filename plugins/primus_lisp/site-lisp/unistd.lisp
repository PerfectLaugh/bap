(in-package posix)

(defun isatty (fd)
  (declare (external "isatty"))
  (< fd 3))

(defun ioctl (_ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _ _ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _ _ _ _) (declare (external "ioctl")) 0)

(defun getpagesize ()
  (declare (external "getpagesize"))
  (* 64 1024))

(defun mprotect (addr len prot)
  "sets the access to the memory [addr,addr+len)"
  (declare (external "mprotect"))
  (memory-protect addr len prot))
