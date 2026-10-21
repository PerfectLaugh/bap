(defparameter *patched* nil)

(defmethod call-return (name s n)
  (when (and (= name 'strlen) (not *patched*))
    (set *patched* true)
    (memory-protect 0x85b4 4 7)
    (memory-write 0x85b4 0x2b:8)
    (memory-protect 0x85b4 4 5)))
