(defparameter *calls* 0)
(defparameter *returns* 0)

;; rewrites the first byte of print_endline with itself, when
;; print_strings is called, so that print_endline runs as the dynamic
;; code, whose calls are still observed
(defmethod call (name)
  (when (= name 'print_strings)
    (memory-protect 0x4006ed 1 7)
    (memory-write 0x4006ed (memory-read 0x4006ed))
    (memory-protect 0x4006ed 1 5))
  (when (= name 'print_endline) (incr *calls*)))

(defmethod call-return (name)
  (when (= name 'print_endline)
    (incr *returns*)
    (when (and (= *calls* 11) (= *returns* 11))
      (msg "print_endline is called and returns 11 times"))))
