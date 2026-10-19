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

(defparameter *mmap/next* nil
  "the address of the next anonymous mapping, above the stack")

(defun mmap/round (len)
  (declare (visibility :private))
  (logand (+ len 0xfff) (lnot 0xfff)))

(defun mmap (addr len prot flags fd off)
  "maps the anonymous memory, which is the memory of a file descriptor
   -1, filled with zeros, at addr, if flags has MAP_FIXED (0x10), or
   above the stack, otherwise the files are not mapped"
  (declare (external "mmap"))
  (if (not (is-negative fd)) -1
    (let ((len (mmap/round len))
          (ptr (if (/= 0 (logand flags 0x10)) addr
                 (or *mmap/next*
                     (if (= (word-width) 64) 0x7f0000000000 0x60000000)))))
      (when (= 0 (logand flags 0x10))
        (set *mmap/next* (+ ptr len)))
      (memory-allocate ptr len 0)
      (memory-protect ptr len prot)
      ptr)))

(defun munmap (addr len)
  "denies the access to the memory, which stays mapped"
  (declare (external "munmap"))
  (memory-protect addr (mmap/round len) 0))
