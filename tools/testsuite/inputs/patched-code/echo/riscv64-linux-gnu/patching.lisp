(defparameter *patched* nil)

(defmethod call-return (name s n)
  (when (and (= name 'strlen) (not *patched*))
    (set *patched* true)
    (memory-protect 0x10734 4 7)
    (memory-write (memory-write 0x10734 0x25:8) 0x45:8)
    (memory-protect 0x10734 4 5)))
