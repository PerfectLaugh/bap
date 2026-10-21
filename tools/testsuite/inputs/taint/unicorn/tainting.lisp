(defparameter *tainted* 0)

(defmethod call-return (name buf n _ ret)
  (when (= name 'fgets)
    (taint-introduce-indirectly 'input buf n)))

(defmethod jumping (c dst)
  (when (taint-get-direct 'input c)
    (msg "tainted jump to $0" dst)
    (incr *tainted*)))

(defmethod fini () (msg "tainted $0 jumps" *tainted*))
