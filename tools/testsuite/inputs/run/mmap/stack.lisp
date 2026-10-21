(defmethod call-return (name p n prot ret)
  (when (= name 'mprotect)
    (taint-introduce-indirectly 'stack (- RSP 64) 128)))
