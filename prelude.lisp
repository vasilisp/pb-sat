;; function operators

(defun dot (&rest functions)
  "function composition operator"
  (if functions
      (let* ((functions (reverse functions))
             (first-function (car functions)))
        ;; last function can have an arbitrary number of arguments,
        ;; the rest only one
        #'(lambda (&rest arguments)
            (reduce #'(lambda (x f) (funcall f x))
                    (cdr functions)
                    :initial-value (apply first-function arguments))))
      #'identity))

(defmacro curry (fun &rest args)
  "function currying operator"
  (let ((more (gensym)))
    `(lambda (&rest ,more) (apply ,fun ,@args ,more))))

;; list utilities

(defun for-all (predicate list)
  "predicate is true for all elements of the list"
  (not (find-if-not predicate list)))

(defun in (element list &key (test #'eql))
  "membership predicate for lists"
  (find-if (curry test element) list))

(defun partition (predicate list)
  "partition list in two according to a predicate"
  (loop
     for element in list
     when (funcall predicate element)
     collect element into l1
     else
     collect element into l2
     finally (return (values l1 l2))))

;; various utilities

(defun time-evaluation (f &rest arguments)
  "apply arguments to f, and return time taken as the first value"
  (let ((t1 (get-internal-run-time))
        (l (multiple-value-list (apply f arguments)))
        (t2 (get-internal-run-time)))
    (values-list (append l (list (- t2 t1))))))
