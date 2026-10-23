(in-package posix)

(defun isatty (fd)
  (declare (external "isatty"))
  (< fd 3))

(defun ioctl (_ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _ _ _) (declare (external "ioctl")) 0)
(defun ioctl (_ _ _ _ _ _) (declare (external "ioctl")) 0)

(defparameter *page-size* 4096
  "the size of a page, which is 4096 on Linux on the most targets")

(defun getpagesize ()
  (declare (external "getpagesize"))
  *page-size*)

(defun mman/fail (code)
  "sets errno to the code and returns -1"
  (declare (visibility :private))
  (write-word int (errno-location) code)
  -1)

(defun mman/einval ()
  (declare (visibility :private))
  (mman/fail 22))

(defun mman/is-aligned (addr)
  (declare (visibility :private))
  (= 0 (logand addr (- *page-size* 1))))

(defun mman/round (len)
  "rounds the length up to the pages"
  (declare (visibility :private))
  (logand (+ len (- *page-size* 1)) (lnot (- *page-size* 1))))

(defun mprotect (addr len prot)
  "sets the access to the pages of [addr,addr+len), addr is aligned
   to a page"
  (declare (external "mprotect"))
  (if (not (mman/is-aligned addr)) (mman/einval)
    (memory-protect addr (mman/round len) prot)))

(defparameter *mmap/next* nil
  "the address of the next anonymous mapping, above the stack")

(defun mmap (addr len prot flags fd off)
  "maps the anonymous pages, which are of the file descriptor -1,
   filled with zeros, at addr, if flags has MAP_FIXED (0x10), which is
   aligned to a page, or above the stack, the files are not mapped"
  (declare (external "mmap"))
  (let ((fixed (/= 0 (logand flags 0x10))))
    (if (not (is-negative fd)) (mman/fail 19) ; ENODEV
      (if (or (= len 0) (and fixed (not (mman/is-aligned addr))))
          (mman/einval)
      (let ((len (mman/round len))
            (ptr (if fixed addr
                   (or *mmap/next*
                       (if (= (word-width) 64) 0x7f0000000000 0x60000000)))))
        ;; the length, that wraps around, when it is rounded, or that is
        ;; larger than the user space of Linux, and the mapping, that
        ;; wraps around the address space, are ENOMEM
        (if (or (= len 0)
                (> len (if (= (word-width) 64) 0x800000000000 0xC0000000))
                (< (+ ptr len) ptr))
            (mman/fail 12)
          (when (not fixed)
            (set *mmap/next* (+ ptr len)))
          (memory-allocate ptr len 0)
          (memory-protect ptr len prot)
          ptr))))))

(defun munmap (addr len)
  "denies the access to the pages of [addr,addr+len), which stay
   mapped, as Primus doesn't unmap the memory, addr is aligned to a page"
  (declare (external "munmap"))
  (if (or (= len 0) (not (mman/is-aligned addr))) (mman/einval)
    (memory-protect addr (mman/round len) 0)))
