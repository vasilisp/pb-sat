(defvar *ite-hash* nil)

(defun triple-eq (l1 l2)
  "triple equality predicate (all elements eq)"
  (or (eq l1 l2)
      (and (cddr l1)
           (cddr l2)
           (eq (first l1) (first l2))
           (eq (second l1) (second l2))
           (eq (third l1) (third l2)))))

(sb-ext:define-hash-table-test triple-eq sxhash)

(defun get-ite-node (&rest args)
  args)

(defun build-bdd (constraint &optional limit)
  "construct a BDD for constraint (does not convert to CNF)"
  (let ((memo (make-hash-table :test 'equal))
        (rhs (rhs constraint))
        (lhs (lhs constraint))
        (rel (rel constraint))
        (count 0))
    (block recursion
      (labels
          ((bb-aux (terms size sum max depth)
             (cond
               ((> sum rhs) (if (eql rel '>=) t nil))
               ((and (or (eql rel '>=)
                         (endp terms))
                     (= sum rhs)))
               ((< (+ sum max) rhs) nil)
               ((not (nth-value 1 (gethash (cons size sum) memo)))
                #+assert (assert terms)
                (setf count (1+ count))
                (if (and limit
                         (or (> depth 5000)
                             (> count limit)))
                    (return-from recursion :fail)
                    (let* ((term (car terms))
                           (var (tvar term))
                           (coef (let ((coef (tcoef term)))
                                   #+assert (assert (> coef 0))
                                   coef))
                           (max (- max coef))
                           (key (cons size sum))
                           (size (1- size))
                           (depth (1+ depth))
                           (hi (bb-aux (cdr terms) size (+ sum coef)
                                       max depth))
                           (lo (bb-aux (cdr terms) size sum
                                       max depth)))
                      (setf (gethash key memo)
                            (if (eq hi lo)
                                hi
                                (get-ite-node var hi lo))))))
               (t (gethash (cons size sum) memo)))))
        (let* ((s (apply #'+ (mapcar #'tcoef lhs)))
               (bdd (bb-aux lhs (length lhs) 0 s 0)))
          (values bdd count))))))

(defun sort-constraints-sum (constraints)
  "sort terms in constraints (largest coefficient sum first)"
  (let* ((llhs (mapcar
                (dot
                 (lambda (l)
                   (sort (copy-list l)
                         (lambda (x1 x2)
                           (< (abs (tvar x1))
                              (abs (tvar x2))))))
                 #'lhs)
                constraints))
         (f (lambda (&rest terms)
              (let* ((coefs (mapcar #'tcoef terms))
                     (sum (apply #'+ coefs))
                     (var (abs (tvar (car terms)))))
                (cons var sum))))
         (l (apply #'mapcar (cons f llhs)))
         (l (sort l (lambda (x1 x2) (> (cdr x1) (cdr x2)))))
         (h (make-hash-table)))
    (loop
       for i from 1
       for pair in l
       do (setf (gethash (car pair) h) i))
    (mapcar (lambda (c)
              (make-constraint
               (rel c)
               (sort (copy-list (lhs c))
                     (lambda (x1 x2)
                       (< (gethash (abs (tvar x1)) h)
                          (gethash (abs (tvar x2)) h))))
               (rhs c)))
            constraints)))

(defun always-falsified (terms rel rhs max)
  #+assert (assert (for-all (dot #'> #'tcoef) terms))
  #-assert (declare (ignorable terms))
  (or (< max rhs)
      (and (eql rel '=) (< rhs 0))))

(defun exists-falsified (largs)
  (find-if (curry #'apply #'always-falsified) largs))

(defun always-satisfied (terms rel rhs max)
  (declare (ignorable max))
  #+assert (assert (for-all (dot #'> #'tcoef) terms))
  (if (eql rel '>=)
      (<= rhs 0)
      (and (endp terms)
           (= rhs 0))))

(defun recursion-args (pos terms rel rhs max)
  (let* ((term (car terms))
         (var (tvar term))
         (coef (let ((coef (tcoef term)))
                 #+assert (assert (> coef 0))
                 coef))
         (rhs (if (if pos (> var 0) (< var 0))
                  (- rhs coef)
                  rhs))
         (max (- max coef)))
    (list (cdr terms) rel rhs max)))

(defun build-big-bdd (constraints &optional limit)

  (let* ((length (length constraints))
         (constraints (sort-constraints-sum constraints))
         (memo (make-hash-table :test 'equal))
         (count 0))

    (format t "c building big BDD (~A constraints)~%" length)

    (block blow-up
      (labels

          ((initial-arguments (constraint)
             (let* ((lhs (lhs constraint))
                    (max (apply #'+ (mapcar #'tcoef lhs))))
               (list lhs (rel constraint)
                     (rhs constraint) max)))

           (check-too-big (depth)
             (setf count (1+ count))
             (if (and limit
                      (or (> depth 5000)
                          (> count (* 1.2 limit))))
                 (return-from blow-up :fail)))

           (largs-hi (largs)
             (loop for args in largs
                collect (apply #'recursion-args (cons t args))))

           (largs-lo (largs)
             (loop for args in largs
                collect (apply #'recursion-args (cons nil args))))

           (bb-aux (vars largs size depth)
             (unless (exists-falsified largs)
               (or (for-all (curry #'apply #'always-satisfied) largs)
                   (let* ((rhss (mapcar #'cddr largs))
                          (key (list rhss size)))
                     (multiple-value-bind (v found)
                         (gethash key memo)
                       (if found v
                           (progn
                             (check-too-big depth)
                             (let* ((var (abs (car vars)))
                                    (size (1- size))
                                    (depth (1+ depth))
                                    (largs-hi (largs-hi largs))
                                    (largs-lo (largs-lo largs))
                                    (hi (bb-aux (cdr vars) largs-hi
                                                size depth))
                                    (lo (bb-aux (cdr vars) largs-lo
                                                size depth)))
                               (setf (gethash key memo)
                                     (if (eq hi lo)
                                         hi
                                         (get-ite-node
                                          var hi lo))))))))))))

      (let ((lvars (mapcar (dot (lambda (l) (sort l #'<))
                                (curry #'mapcar
                                       (dot #'abs #'tvar))
                                #'lhs)
                           constraints)))
        (assert (not (cdr (remove-duplicates lvars :test 'equal)))))

      (let ((bdd  (bb-aux (mapcar (dot #'abs #'tvar)
                                  (lhs (car constraints)))
                          (mapcar #'initial-arguments constraints)
                          (length (lhs (car constraints)))
                          0)))
        (values bdd count))))))

(defun convert-bdd (node &optional (monotonic nil))
  "convert BDD into CNF"
  (declare (ignorable monotonic))
  (labels
      ((cb-aux (node)
         (cond
           ((equal node t) t)
           ((not node) nil)
           ((cdddr node) (cdddr node))
           (t (let* ((v (car node))
                     (hi (cb-aux (cadr node)))
                     (lo (cb-aux (caddr node))))
                (setf
                 (cdddr node)
                 (cond
                   ((eql hi lo) hi)
                   ;; hi is nil cases
                   ((and (not hi) (not lo)) nil)
                   ((and (not hi) (eql lo t)) (- v))
                   ((not hi) (get-and (- v) lo))
                   ;; hi is t cases
                   ((and (eql hi t) (not lo)) v)
                   ((and (eql hi t) (eql lo t)) t)
                   ;; hi is unknown
                   (monotonic (get-ite+-monotonic v hi lo))
                   (t (get-ite+ v hi lo)))))))))
    (let ((v (cb-aux node)))
      #+assert (assert v)
      (add-clause (cl v))
      v)))

(defun add-0-terms (constraints)
  (let* ((all-variables
          (loop for constraint in constraints
             append (loop for term in (lhs constraint)
                       collect (abs (tvar term)))))
         (all-variables (remove-duplicates all-variables)))
    (mapcar
     (lambda (constraint)
       (let* ((lhs (lhs constraint))
              (aux-terms
               (loop
                  for v in all-variables
                  unless (find-if (dot (curry #'eql v)
                                       #'abs #'tvar)
                                  lhs)
                  collect (cons v 0))))
         (make-constraint (rel constraint)
                          (append lhs aux-terms)
                          (rhs constraint))))
     constraints)))

(defun all-bdds-aux (triples)
  (let* ((merged-constraints (list (first (car triples))))
         (remaining-triples nil)
         (bdd (second (car triples)))
         (size (third (car triples))))
    (loop
       for triple in (cdr triples)
       for c = (first triple)
       for s = (third triple)
       for l = (multiple-value-list
                (build-big-bdd
                 (add-0-terms
                  (cons c merged-constraints))))
       for new-bdd = (first l)
       for new-size = (second l)
       when (<= new-size (+ size s))
       do (progn
            (setf bdd new-bdd size new-size)
            (push c merged-constraints))
       else do (push triple remaining-triples)
       finally (return
                 (values
                  (list bdd size (length merged-constraints))
                  remaining-triples)))))

(defun all-bdds (triples acc)
  (if (endp triples)
      (progn
        (format t "sizes: ~A~%" (mapcar #'third acc))
        (mapcar #'car acc))
      (multiple-value-bind (bdd triples)
          (all-bdds-aux triples)
        (all-bdds triples (cons bdd acc)))))

(defun add-bdd (constraint)
  "build BDD and produce CNF for it"
  (let ((m (equal (rel constraint) '>=))
        (b (build-bdd constraint)))
    (convert-bdd b m)))
