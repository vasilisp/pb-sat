(defvar *clauses* nil)
(defvar *pb-constraints* nil)

(defun assignment (l &key (dl0 nil))
  "get the value of literal l under current assignment"
  (if dl0
      (picosat:deref-toplevel l)
      (picosat:deref l)))

(defun evaluate-lhs (lhs)
  "sum up the activated terms in the LHS of a constraint"
  (loop
     for term in lhs
     when
       (if (consp (tvar term))
           (for-all (dot (curry #'< 0) #'assignment)
                    (tvar term))
           (> (assignment (tvar term)) 0))
     sum (tcoef term)))

(defun evaluate-pb-constraint (pb-constraint)
  "evaluate PB constraint to true or false"
  (let* ((rhs (rhs pb-constraint))
         (rel (rel pb-constraint))
         (lhs (evaluate-lhs (lhs pb-constraint))))
    (funcall rel lhs rhs)))

(defun falsified-pb-constraints (&optional (c *pb-constraints*))
  "evaluate PB constraints, and return the falsified ones"
  (remove-if #'evaluate-pb-constraint c))

(defun set-more-important-variables ()
  "set PB variables to be more important than others"
  (loop
     for i from 1 to *pb-variables*
     do (picosat:set-more-important-lit i)))

(defun init ()
  "initialize data structures and SAT solver"
  (setf *definitions* (make-hash-table :test 'equal)
        *ite-hash* (make-hash-table :test 'triple-eq :size 10000000))
  (picosat:init)
  (if *important-variables* (set-more-important-variables)))

(defun count-known-units (&key (only-pb t))
  "count the units the SAT solver knows"
  (loop
     for i from 1 to (if only-pb *pb-variables* *last-variable*)
     unless (eql (assignment i :dl0 t) 0)
     count i))

(defun answer-sat ()
  "print message for SAT/OPT, and provide statistics"
  (assert (not (falsified-pb-constraints)))
  (format t "s SATISFIABLE~%")
  (format t "c ~A variables, ~A clauses, ~A PB units, ~A units~%"
          (picosat:variables)
          (picosat:added-original-clauses)
          (count-known-units)
          (count-known-units :only-pb nil))
  (format t "c PicoSAT time: ~$ sec~%" (picosat:seconds))
  (sb-ext:quit))

(defun answer-opt (objective-value)
  (format t "s OPTIMUM FOUND: ~A~%" objective-value)
  (format t "c ~A variables, ~A clauses _ PB units, _ units~%"
          (picosat:variables)
          (picosat:added-original-clauses))
  (format t "c PicoSAT time: ~$ sec~%" (picosat:seconds))
  (sb-ext:quit))

(defun answer-unsat ()
  "print message for UNSAT, and provide statistics"
  (format t "c ~A variables, ~A clauses _ PB units, _ units~%"
          (picosat:variables)
          (picosat:added-original-clauses))
  (format t "s UNSATISFIABLE~%")
  (format t "c PicoSAT time: ~$ sec~%" (picosat:seconds))
  (sb-ext:quit))

(defun solve-and-answer ()
  (if (eql (picosat:sat -1) 10)
      (answer-sat)
      (answer-unsat)))

;; standard preprocessing steps

(defun no-negative-coefficients (pb-constraint)
  "true iff LHS has no negative coefficients"
  (for-all (dot (curry #'< 0) #'tvar)
           (lhs pb-constraint)))

(defun remove-multiple-occurrences (pb-constraint)
  "remove multiple occurrences of same variable in constraint"
  #+assert (assert (no-negative-coefficients pb-constraint))
  (let ((h (make-hash-table :test 'equal)))
    (dolist (term (lhs pb-constraint))
      (let ((var (tvar term))
            (coef (tcoef term)))
        (push coef (gethash var h))))
    (make-constraint
     (rel pb-constraint)
     (loop
        for k being the hash-keys of h
        using (hash-value v)
        collect (cons k (apply #'+ v)))
     (rhs pb-constraint))))

(defun remove-<= (pb-constraint)
  "turn <= into >="
  #+assert (assert (no-negative-coefficients pb-constraint))
  (if (eql (rel pb-constraint) '<=)
      (make-constraint 
       '>=
       (mapcar (lambda (term)
                 (let ((var (tvar term))
                       (coef (tcoef term)))
                   (cons var (- coef))))
               (lhs pb-constraint))
       (- (rhs pb-constraint)))
      pb-constraint))

(defun remove-negative-coefficients (pb-constraint)
  "remove negative coefficients by negating literals and updating RHS"
  (let ((lhs (lhs pb-constraint))
        (rel (rel pb-constraint))
        (rhs (rhs pb-constraint)))
    (loop
       for (var . coef) in lhs
       when (< coef 0)
       collect (cons (- var) (- coef)) into new-lhs and
       sum (- coef) into s
       else collect (cons var coef) into new-lhs
       finally
         (progn
           #+assert (assert (>= (+ rhs s) 0))
           (return (make-constraint rel new-lhs (+ rhs s)))))))

(defun trim-coefficients (pb-constraint)
  "trim coefficients greater than the RHS"
  (let ((rhs (rhs pb-constraint))
        (rel (rel pb-constraint)))
    (if (eql rel #'>=)
        (progn
          #+assert (assert (>= rhs 0))
          (make-constraint
           (rel pb-constraint)
           (mapcar (lambda (term)
                     (if (> (tcoef term) rhs)
                         (cons (tvar term) rhs)
                         term))
                   (lhs pb-constraint))
           rhs))
        pb-constraint)))

(defun sort-coefficients (pb-constraint)
  "sort terms of constraint (largest coefficients first)"
  (make-constraint
   (rel pb-constraint)
   (sort (copy-list (lhs pb-constraint))
         (lambda (x y)
           (> (tcoef x) (tcoef y))))
   (rhs pb-constraint)))

(defun gcd-reduction (c)
  "divide LHS and RHS by the GCD"
  (if (eql (rhs c) '=)
      (let* ((gcd (apply #'gcd (cons (rhs c) (lhs-c c))))
             (coefs (mapcar (lambda (x) (/ x gcd)) (lhs-c c)))
             (lhs (make-lhs coefs (lhs-v c))))
        (make-constraint (rel c) lhs (/ (rhs c) gcd)))
      (let* ((gcd (apply #'gcd (lhs-c c)))
             (rhs (ceiling (/ (rhs c) gcd)))
             (rhs (if (equal (rhs c) '<=) 
                      (floor rhs)
                      (ceiling rhs)))
             (coefs (mapcar (lambda (x) (/ x gcd)) (lhs-c c)))
             (lhs (make-lhs coefs (lhs-v c))))
        (make-constraint (rel c) lhs rhs))))

(defun linearize (pb-constraint)
  "turn non-linear constraint into linear"
  (make-constraint
   (rel pb-constraint)
   (mapcar (lambda (term)
             (let ((var (tvar term))
                   (coef (tcoef term)))
               (if (consp var)
                   (cons (apply #'get-and var) coef)
                   term)))
           (lhs pb-constraint))
   (rhs pb-constraint)))

(defun normalize-1st (pb-constraint)
  "perform 1st set of normalization steps"
  (remove-negative-coefficients
   (remove-<=
    (remove-multiple-occurrences
     (linearize
      pb-constraint)))))

(defun normalize-2nd (pb-constraint)
  "perform 2nd set of normalization steps"
  (gcd-reduction
   (sort-coefficients
    (trim-coefficients pb-constraint))))

(defun trivialp (pb-constraint)
  "true iff the constraint is trivially satisfied"
  (or (and (equal (rel pb-constraint) '=)
           (for-all (dot (curry #'eql 0) #'tcoef)
                    (lhs pb-constraint)))
      (and (equal (rel pb-constraint) '>=)
           (<= (rhs pb-constraint) 0))))

(defun normalize-all (pb-constraints)
  "normalize all constraints, and remove trivially satisfied"
  (let* ((pb-constraints (mapcar #'normalize-1st pb-constraints))
         (pb-constraints (delete-if #'trivialp pb-constraints)))
    (mapcar #'normalize-2nd pb-constraints)))

(defun cardinality (pb-constraint)
  "true iff the constraint is cardinality"
  (for-all (dot (curry #'eql 1) #'tcoef)
           (lhs pb-constraint)))

(defun easy-cardinality (pb-constraint)
  "true if the constraint leads to a relatively small BDD"
  (let* ((lhs (lhs pb-constraint))
         (k (rhs pb-constraint))
         (n (length lhs)))
    (and (cardinality pb-constraint)
         (<= (/ (* (- (1+ n) k) k) n) 8))))

(defun cardinality>=1 (pb-constraint)
  "true if the constraint is a clause"
  (and (cardinality pb-constraint)
       (eql '>= (rel pb-constraint))
       (eql 1 (rhs pb-constraint))))

(defun add-cardinality=1-constraint (constraint)
  "quadratic encoding for = 1 cardinality constraints"
  #+assert (assert (and (cardinality constraint)
                        (eql (rhs constraint) 1)
                        (eql (rel constraint) '=)))
  (let ((literals (mapcar #'tvar (lhs constraint))))
    ;; one of them has to be true
    (add-clause (apply #'cl literals))
    (mapl (lambda (l)
            (let ((literal (car l))
                  (rest (cdr l)))
              (dolist (literal1 rest)
                ;; at most one of them can be true
                #+assert (assert (and (integerp literal)
                                      (integerp literal1)))
                (add-clause (cl (~ literal) (~ literal1))))))
          literals)))

(defun add-cardinality>=n-1-constraint (constraint)
  "quadratic encoding for >= n - 1 cardinality constraints"
  #+assert (assert (and (cardinality constraint)
                        (eql (rhs constraint)
                             (1- (length (lhs constraint))))
                        (eql (rel constraint) '>=)))
  (let ((literals (mapcar #'tvar (lhs constraint))))
    (mapl (lambda (l)
            (let ((literal (car l))
                  (rest (cdr l)))
              (dolist (literal1 rest)
                ;; at most one of them can be false
                #+assert (assert (and (integerp literal)
                                      (integerp literal1)))
                (add-clause (cl literal literal1)))))
          literals)))

(defun add-constraint (constraint &optional (bdd-limit *bdd-limit*))
  "add constraint to PB solver (pick best encoding)"
  (cond
    ((cardinality constraint)
     ;; BDDs for these no matter what
     (add-bdd constraint))
    ((not *adders*)
     (let ((b (build-bdd constraint bdd-limit))
           (m (equal (rel constraint) '>=)))
       (if (equal b :fail)
           (progn
             (format t "c info: BDD limit exceeded, using adder~%")
             (add-adder-constraint constraint))
           (convert-bdd b m))))
    (t (add-adder-constraint constraint))))

(defun add-big-bdd (constraints &optional (bdd-limit *bdd-limit*))
  "build BDD for the conjunction of constraints, and convert to CNF"
  (let* ((constraints (mapcar #'sort-coefficients constraints)))
    (if (endp (cdr constraints))
        (add-constraint (car constraints))
        (let ((b (build-big-bdd constraints bdd-limit)))
          (if (equal b :fail)
              (progn
                (format t "c WARNING: add-big-bdd failed~%")
                (format t "c adding individual constraints~%")
                (mapc #'add-constraint constraints)
                (format t "c added individual constraints~%"))
              (convert-bdd b nil))))))

(defvar *found-pb-unit* nil)

(defun propagate-get-units (terms rhs)
  (let* ((sum (apply #'+ (mapcar #'tcoef terms)))
         (term (find-if
                (lambda (term)
                  (> rhs (- sum (tcoef term))))
                terms)))
    (if term
        (let* ((coef (tcoef term))
               (rhs (- rhs coef))
               (terms (delete-if (curry #'equal term) terms)))
          (setf *found-pb-unit* t)
          (picosat:add-clause (cl (tvar term)))
          (propagate-get-units terms rhs))
        (values terms rhs))))

(defun propagate-in-constraint (pb-constraint)
  "constraint propagation for a single constraint"
  (let ((lhs (lhs pb-constraint))
        (rhs (rhs pb-constraint))
        (rel (rel pb-constraint)))
    #+assert (assert (for-all (dot (curry #'< 0) #'tcoef) lhs))
    (multiple-value-bind (s-true s-other new-lhs)
        (loop
           for (var . coef) in lhs
           for assignment = (assignment var :dl0 t)
           when (eql assignment 1)
           sum coef into s-true
           when (eql assignment 0)
           collect (cons var coef) into new-lhs and
           sum coef into s-other
           finally (return (values s-true s-other new-lhs)))
      (cond
        ((and (eql rel '>=) (>= s-true rhs)) nil)
        ((and (eql s-true rhs) (eq rel '=))
         (loop
            for (var . coef) in new-lhs
            do (progn
                 #+assert (assert (eql (assignment var :dl0 t) 0))
                 (setf *found-pb-unit* t)
                 (picosat:add-clause (cl (- var))))
            finally (return nil)))
        ((< (+ s-true s-other) rhs)
         (answer-unsat))
        (t (multiple-value-bind (new-lhs rhs)
               (propagate-get-units new-lhs (- rhs s-true))
             (cond
               ((<= rhs 0) nil)
               ((not new-lhs) (answer-unsat))
               (t (let* ((constraint (make-constraint rel new-lhs rhs))
                         (constraint (gcd-reduction constraint))
                         (constraint (trim-coefficients constraint)))
                    (if (cardinality>=1 constraint)
                        (let ((clause (mapcar #'tvar (lhs constraint))))
                          (add-clause (apply #'cl clause))
                          nil)
                        constraint))))))))))

(defun propagate-class (class &optional query dl)
  (if (and query (eql (picosat:sat dl) 20))
      (answer-unsat)
      (loop
         for constraint in class
         for v = (propagate-in-constraint constraint)
         when v
         collect v)))

(defun propagate-classes (classes &optional (dl 0))
  "perform constraint propagation on classes"
  (if (eql (picosat:sat dl) 20)
      (answer-unsat)
      (loop
         for class in classes
         for v = (propagate-class class)
         when v
         collect v)))

(defun propagate-loop (constraints &key (dl 0))
  "constraint propagation fixpoint for a list of constraints"
  (let* ((*found-pb-unit* nil)
         (constraints (propagate-class constraints t dl)))
    ;; repeat, till we reach a fixpoint
    (if *found-pb-unit*
        (propagate-loop constraints :dl dl)
        constraints)))

(defun propagate-loop-classes (classes &key (dl 0))
  "constraint propagation fixpoint for a list of constraint classes"
  (let* ((*found-pb-unit* nil)
         (classes (propagate-classes classes dl)))
    ;; repeat, till we reach a fixpoint
    (if *found-pb-unit*
        (propagate-loop-classes classes :dl dl)
        classes)))

(defun sum-coefficients (pb-constraint)
  "sum left-hand side coefficents of PB constraint"
  (apply #'+ (mapcar #'tcoef (lhs pb-constraint))))

(defun add-constraints (constraints &key (n 0)
                        (f #'add-constraint) (dl *dl*))
  "add CNF representation of PB constraints to solver"
  (if (consp constraints)
      (progn
        (funcall f (car constraints))
        (let ((constraints (propagate-loop
                            (cdr constraints) :dl dl)))
          (add-constraints constraints :n (+ n 1) :f f :dl dl)))
      (format t "c added ~A constraints~%" n)))

(defun add-classes (classes &key (n 0) (dl *dl*))
  "add CNF representation of PB constraints to solver"
  (if (consp classes)
      (progn
        (add-big-bdd (car classes))
        (add-classes (propagate-loop-classes (cdr classes) :dl dl)
                     :n (+ n 1) :dl dl))
      (format t "c added ~A constraints~%" n)))

(defun learn-simple-disjunction (constraint)
  "extract a disjunction of literals implied by the constraint"
  (let* ((lhs (lhs constraint))
         (rhs (rhs constraint))
         (sum (apply #'+ (mapcar #'tcoef lhs))))
    (let ((vars (loop
                   for (var . coef) in lhs
                   collect var into vars
                   sum coef into sum-prefix
                   until (< (- sum sum-prefix) rhs)
                   finally (return vars))))
      (if (and vars (<= (length vars) *max-implied-clause-length*))
          (add-clause (apply #'cl vars))))))

(defun solver-loop (classes &key (objective nil) (dl *dl*))
  "main solver loop (adds falsified constraints in each iteration)"
  (let ((classes-number (length classes)))
    (labels

        ((sll-aux (classes i n k solution)
           (cond
             ((eql (picosat:sat -1) 10)
              (sll-sat classes (1+ i) n k solution))
             (solution (answer-opt solution))
             (t (answer-unsat))))

         (sll-sat (classes i n k solution)
           (multiple-value-bind (satisfied falsified)
               (partition (curry #'for-all #'evaluate-pb-constraint)
                          classes)
             (let* ((len-true (length satisfied))
                    (len-false (length falsified))
                    (len (+ len-true len-false))
                    (k1 (count-known-units)))

               (format t "c ~A/~A falsified~%" len-false len)
               (format t "c ~A units known after round ~A~%" k1 i)

               (cond
                 ((not (or falsified objective))
                  (format t "c solution with ~A constraints~%" n)
                  (answer-sat))
                 ((not falsified)
                  (assert (not (falsified-pb-constraints)))
                  (let* ((v (evaluate-lhs objective))
                         (c (make-constraint '<= objective (1- v)))
                         (c (normalize-1st c))
                         (c (normalize-2nd c))
                         (c (propagate-in-constraint c)))
                    #+assert (assert (or (not solution)
                                         (< v solution)))
                    (format t "c NEW SOLUTION FOUND: ~A~%" v)
                    (if c (add-constraint c))
                    (format t "c added constraint~%")
                    (picosat:reset-phases)
                    (picosat:set-global-default-phase 3)
                    (format t "c repeating~%")
                    (sll-aux classes i n k1 v)))
                 ((or (<= len (* 0.3 classes-number))
                      (< len 10))
                  (format t "c adding remaining ~A constraints~%" len)
                  (mapc #'add-big-bdd
                        (if (> k1 k)
                            (propagate-loop-classes classes :dl dl)
                            classes))
                  (sll-aux nil i (+ n len) k1 solution))
                 (t (mapc #'add-big-bdd falsified)
                    (sll-aux (if (> k1 k)
                                 (propagate-loop-classes
                                  satisfied :dl dl)
                                 satisfied)
                             i (+ n len-false) k1 solution)))))))

      (sll-aux classes 0 0 0 nil))))

(defun get-assignment (&optional (only-pb t))
  "return current assignment"
  (loop
     for i from 1 to (if only-pb *pb-variables* *last-variable*)
     collect (if (> (assignment i) 0) i (- i))))

(defun extract-more-units (constraints &key (dl *udl*))
  "extract units implied by the current propositional formula"
  
  (labels

      ((filter-candidates (candidates)
         (delete-if (dot (curry #'eql -1) #'assignment)
                    candidates))

       (randomize-phases ()
         (picosat:reset-phases)
         (picosat:set-global-default-phase 3))

       (gcu-aux (candidates m n)
         (if (endp candidates)
             (values m n)
             (let ((u (car candidates))
                   (rest (cdr candidates)))
               (if (eql (assignment u :dl0 t) 0)
                   (progn
                     (picosat:assume (- u))
                     (case (picosat:sat
                            (if (< (- m n) 8)
                                (progn (randomize-phases) -1)
                                dl))
                       (10 (gcu-aux (filter-candidates rest)
                                    (1+ m) n))
                       (20 (add-clause (cl u))
                           (gcu-aux rest (1+ m) (1+ n)))
                       (otherwise (gcu-aux rest (1+ m) n))))
                   (gcu-aux rest m n))))))
    
    (if (eql (picosat:sat -1) 10)
        (let* ((a (delete-if
                   (lambda (u)
                     (eql (assignment u :dl0 t) 1))
                   (get-assignment)))
               (t0 (get-internal-real-time))
               (constraints (propagate-loop constraints)))
          (format t "c ~A known units after 0th call~%"
                  (count-known-units))
          (multiple-value-bind (m n)
              (gcu-aux a 0 0)
            (let* ((t1 (get-internal-run-time))
                   (td (/ (- t1 t0) internal-time-units-per-second))
                   (td (float td)))
              (format t "c ~A calls, ~A units, ~A seconds taken~%"
                      m n td)
              (format t "c ~A total known units~%"
                      (count-known-units))
              (format t "c SAT time: ~A~%" (picosat:seconds))
              (values constraints a))))
        (answer-unsat))))

(defun set-variable-phases (constraints)
  "set default PB variable phases"
  (let ((h (make-hash-table)))
    (dolist (constraint constraints)
      (let ((rhs (rhs constraint))
            (rel (rel constraint)))
        (if (eql rel '>=)
            (dolist (term (lhs constraint))
              (let* ((lit (tvar term))
                     (coef (tcoef term))
                     (percent (/ coef rhs))
                     (percent (if (> lit 0) percent (- percent)))
                     (old-phase (gethash (abs lit) h))
                     (old-phase (if old-phase old-phase 0)))
                (setf (gethash (abs lit) h)
                      (+ percent old-phase)))))))
    (loop
       for k being the hash-key of h
       using (hash-value v)
       when (> v 0)
       do (picosat:set-default-phase-lit k 1)
       when (< v 0)
       do (picosat:set-default-phase-lit k -1))))

(defun signature (constraint)
  "sorted list of variables that appear in the constraint"
  (sort (mapcar (dot #'abs #'tvar) (lhs constraint)) #'<))

(defun constraint-equivalence-classes (constraints)
  "find groups of constraints with exactly the same variables"
  (let ((h (make-hash-table :test 'equal)))
    (dolist (c constraints)
      (push c (gethash (signature c) h)))
    (loop
       for k being the hash-key of h
       using (hash-value v)
       collect v)))

(defun solver (constraints &key objective monolithic cnf-file)
  "the main entrypoint of our solver"
  (init)
  (if objective (picosat:set-global-default-phase 3))
  (if cnf-file (setf *store-clauses* t))
  (let* ((constraints (normalize-all constraints)))
    (multiple-value-bind (clauses constraints)
        (partition #'cardinality>=1 constraints)
      (format t "c found ~A clauses~%" (length clauses))
      (mapc (dot #'add-clause (curry #'mapcar #'tvar) #'lhs) clauses)
      (set-variable-phases constraints)
      (multiple-value-bind (easy-constraints constraints)
          (partition #'easy-cardinality
                     (propagate-loop constraints :dl 0))
        (format t "c ~A units after propagation~%" (count-known-units))
        (add-constraints easy-constraints :f #'add-bdd)
        (if (> *max-implied-clause-length* 0)
            (mapc #'learn-simple-disjunction constraints))
        (let* ((constraints (propagate-loop constraints :dl 0))
               (constraints
                (if *more-units*
                    (extract-more-units constraints)
                    constraints))
               (ec (if *merging*
                       (constraint-equivalence-classes constraints)
                       (mapcar #'list constraints))))
          (cond (cnf-file
                 ;; convert to CNF and print to file
                 (format t "c adding ~A constraints~%" (length ec))
                 (add-classes ec :n 0)
                 (print-clauses cnf-file *clauses*))
                (monolithic
                 ;; convert to CNF and solve
                 (format t "c adding ~A constraints~%" (length ec))
                 (add-classes ec :n 0)
                 (solve-and-answer))
                (t (solver-loop ec :objective objective))))))))
