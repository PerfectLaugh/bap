;;; The core macros of Primus Lisp, as in `plugins/primus_lisp/lisp/init.lisp`.

(defmacro += (x y)
  "(+= X Y) assigns a sum of X and Y to variable X"
  (set x (+ x y)))

(defmacro incr (x)
  "(incr X Y ...) increments the value bound with the variables X, Y, ..."
  (set x (+ x 1)))
(defmacro incr (x xs)
  (prog (incr x) (incr xs)))

(defmacro decr (x)
  "(decr X Y ...) decrements the value bound with the variables X, Y, ..."
  (set x (- x 1)))
(defmacro decr (x xs)
  (prog (decr x) (decr xs)))

(defmacro and (x)
  "(and X Y ...) evaluates expressions X,Y,... until the first expression
   that returns false. The value of the whole form is the value of the
   last evaluated expression."
  x)
(defmacro and (x xs)
  (let ((r x)) (if r (and xs) r)))

(defmacro or (x)
  "(or X Y ...) evaluates expressions X,Y,... until the first expression
   that returns true, which is the value of the whole form."
  x)
(defmacro or (x xs)
  (let ((r x)) (if r r (or xs))))

(defmacro dolist (f x)
  "(dolist F X Y ...) applies F to each of the following arguments."
  (f x))
(defmacro dolist (f x xs)
  (prog (f x) (dolist f xs)))

(defun memory-read (address)
  "(memory-read ADDRESS) is the byte at ADDRESS"
  (load-byte address))

(defun ident (x)
  "(ident X) is X"
  x)
