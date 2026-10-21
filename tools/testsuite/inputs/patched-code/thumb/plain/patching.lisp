(defparameter *patched* nil)

(defmethod call (name c)
  (when (and (= name 'putchar) (not *patched*))
    (set *patched* true)
    (memory-protect 0x202d0 2 7)
    (memory-write 0x202d0 0x2b:8)
    (memory-protect 0x202d0 2 5)))
