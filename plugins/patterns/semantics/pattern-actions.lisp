(in-package bap)

(declare (context (patterns enabled)))

(defmethod bap:patterns-action (action addr attrs)
  ;; the `after' attribute constrains the match to locations that are
  ;; not inside the body of an already discovered function, which we
  ;; can't check at this stage, so such patterns (e.g., SUB RSP, C)
  ;; would otherwise split functions right after their prologues
  (unless (patterns-attribute attrs :after)
    (when (is-in action 'funcstart 'possiblefuncstart)
      (promise-function-start addr))))
