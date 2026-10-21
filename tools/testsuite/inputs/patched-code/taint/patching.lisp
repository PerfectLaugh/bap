(defparameter *patched* nil)

(defmethod call-return (name buf n _ ret)
  (when (= name 'fgets)
    (taint-introduce-indirectly 'input buf n)))

(defmethod jumping (c dst)
  (when (taint-get-direct 'input c)
    (msg "tainted jump to $0" dst)
    (unless *patched*
      (set *patched* true)
      (memory-protect 0x7B6 1 7)
      (memory-write 0x7B6 0x74:8)
      (memory-protect 0x7B6 1 5))))
