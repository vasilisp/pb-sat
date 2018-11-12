(defvar *definitions*)
(defvar *clauses* nil)
;; store clauses we generate
(defparameter *store-clauses* nil)

(defun compare-clauses (c1 c2)
  "total order for clauses"
  (cond ((endp c1) t)
        ((< (length c1)
            (length c2)) t)
        ((> (length c1)
            (length c2)) nil)
        ((< (car c1)
            (car c2)) t)
        ((> (car c1)
            (car c2)) nil)
        (t (compare-clauses (cdr c1) (cdr c2)))))

(defun sort-clauses (clauses)
  "sort clauses"
  (sort (mapcar (lambda (clause)
                  (sort clause #'<))
                clauses)
        #'compare-clauses))

(defun ~ (x)
  (cond
    ((equal x t) nil)
    (x (- x))
    (t t)))

(defun get-variable ()
  (setf *last-variable*
        (1+ *last-variable*)))

(defun cl (&rest args)
  ;; clauses can contain variables and t/nil constants
  #+assert (assert (for-all (lambda (a)
                              (or (not a)
                                  (integerp a)
                                  (eql a t)))
                            args))
  (or (in t args) (remove-if-not #'identity args)))

(defun print-clause (st clause)
  "print clause to stream st"
  (format st "~{~a~^ ~} 0~%" clause))

(defun print-clauses (filename &optional (clauses *clauses*))
  "print generated clauses to file"
  (with-open-file (st filename
                      :direction :output
                      :if-exists :supersede
                      :if-does-not-exist :create)
    (format st "p cnf ~A ~A~%"
            *last-variable*
            (length clauses))
    (dolist (clause clauses)
      (print-clause st clause))))

(defun add-clause (clause)
  "add clause to SAT solver"
  (unless (eql clause t)
    (assert (> (length clause) 0))
    (if *store-clauses*
        (push (remove-if (curry #'eq t) clause) *clauses*))
    (picosat:add-clause clause)))

(defun or-var (literals)
  "CNF variable for the disjunction of literals"
  (let* ((v (get-variable)))
    (add-clause (cons (~ v) literals))
    (dolist (literal literals)
      (add-clause (cl (~ literal) v)))
    v))

(defun and-var (literals)
  "CNF variable for the conjunction of literals"
  (let* ((v (get-variable)))
    (add-clause (cons v (mapcar #'- literals)))
    (dolist (literal literals)
      (add-clause (cl (~ v) literal)))
    v))

(defun normalize-expr (op literals &optional (commutative t))
  (cons op
        (if commutative
            (sort (copy-list literals)
                  (lambda (x y)
                    (cond ((and (numberp x) (numberp y))
                           (< x y))
                          ((numberp x) t)
                          ((numberp y) t)
                          ((not x) nil)
                          ((not y) t)
                          (t t))))
            literals)))

(defun get-op (op literals commutative &optional (gen-f nil))
  (let* ((e (normalize-expr op literals commutative))
         (literals (cdr e)))
    (multiple-value-bind (v defined)
        (gethash e *definitions*)
      (cond (defined v)
            (gen-f (setf (gethash e *definitions*)
                         (funcall gen-f literals)))
            (t nil)))))

(defun get-and (&rest literals)
  (get-op :and literals t #'and-var))

(defun get-or (&rest literals)
  (get-op :or literals t #'or-var))

(defun get-xor2 (a b)
  "generate clauses for XOR(a, b)"
  (get-op
   :xor2 (list a b) t
   (lambda (literals)
     (let* ((x (get-variable))
            (a (car literals))
            (b (cadr literals)))
       (mapcar #'add-clause
               (list (cl (~ a) b x)
                     (cl a (~ b) x)
                     (cl (~ a) (~ b) (~ x))
                     (cl a b (~ x))))
       x))))

(defun get-xor3 (a b c)
  "generate clauses for XOR(a, b, c)"
  (get-op
   :xor3 (list a b c) t
   (lambda (literals)
     (let* ((x (get-variable))
            (a (car literals))
            (b (cadr literals))
            (c (caddr literals)))
       (mapcar #'add-clause
               (list (cl a b c (~ x))
                     (cl a (~ b) (~ c) (~ x))
                     (cl (~ a) b (~ c) (~ x))
                     (cl (~ a) (~ b) c (~ x))
                     (cl (~ a) (~ b) (~ c) x)
                     (cl (~ a) b c x)
                     (cl a (~ b) c x)
                     (cl a b (~ c) x)))
       (if *extra-clauses*
           (let ((carry (get-op :maj3 literals t)))
             (if carry
                 (mapcar #'add-clause
                         (list (cl (~ carry) (~ x) a)
                               (cl (~ carry) (~ x) b)
                               (cl (~ carry) (~ x) c)
                               (cl carry x (~ a))
                               (cl carry x (~ b))
                               (cl carry x (~ c)))))))
       x))))

(defun get-maj3 (a b c)
  "generate clauses for MAJ(a, b, c)"
  (let ((l (list a b c)))
    (get-op
     :maj3 l t
     (lambda (literals)
       (let* ((a (car literals))
              (b (cadr literals))
              (c (caddr literals))
              (x (get-variable)))
         (mapcar #'add-clause
                 (list (cl (~ a) (~ b) x)
                       (cl (~ a) (~ c) x)
                       (cl (~ b) (~ c) x)
                       (cl a b (~ x))
                       (cl a c (~ x))
                       (cl b c (~ x))))
         (if *extra-clauses*
             (let ((sum (get-op :xor3 literals t)))
               (if sum
                   (mapcar #'add-clause
                           (list (cl (~ sum) (~ x) a)
                                 (cl (~ sum) (~ x) b)
                                 (cl (~ sum) (~ x) c)
                                 (cl sum x (~ a))
                                 (cl sum x (~ b))
                                 (cl sum x (~ c)))))))
         x)))))

(defun get-ite+ (a b c)
  "generate positive polarity clauses for ITE node"
  (let ((l (list a b c)))
    (get-op
     :iteplus l nil
     (lambda (literals)
       (let ((a (car literals))
             (b (cadr literals))
             (c (caddr literals))
             (x (get-variable)))
         (mapcar #'add-clause
                 (list ;; (cl (~ a) (~ b) x)
                       (cl (~ a) b (~ x))
                       ;; (cl a (~ c) x)
                       (cl a c (~ x))
                       ;; (cl (~ b) (~ c) x)
                       (cl b c (~ x))))
         x)))))

(defun get-ite+-monotonic (a b c)
  "generate positive polarity clauses for ITE, assuming c => b"
  (let ((l (list a b c)))
    (get-op
     :iteplusmonotonic l nil
     (lambda (literals)
       (let ((s (car literals))
             (tr (cadr literals))
             (f (caddr literals))
             (x (get-variable)))
         (add-clause (cl s f (~ x)))
         (add-clause (cl tr (~ x)))
         x)))))
