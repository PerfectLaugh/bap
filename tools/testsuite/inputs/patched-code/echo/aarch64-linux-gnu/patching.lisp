(defparameter *patched* nil)

(defmethod call-return (name s n)
  (when (and (= name 'strlen) (not *patched*))
    (set *patched* true)
    (memory-protect 0xaa0 4 7)
    (memory-write (memory-write (memory-write (memory-write 0xaa0 0x60:8) 0x05:8) 0x80:8) 0x52:8)
    (memory-protect 0xaa0 4 5)))
