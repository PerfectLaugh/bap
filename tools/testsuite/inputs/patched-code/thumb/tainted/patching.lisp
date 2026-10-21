(defparameter *patched* nil)

(defmethod call (name c)
  (when (and (= name 'putchar) (not *patched*))
    (set *patched* true)
    (taint-introduce-indirectly 'stack (- SP 64) 128)
    (memory-protect 0x202d0 2 7)
    (memory-write 0x202d0 0x2b:8)
    (memory-protect 0x202d0 2 5)))

(defmethod jumping (c dst) (msg "interpreted jump to $0" dst))
