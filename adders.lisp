(defun bits-of (n acc)
  "list of t|nil for the binary representation of n (car is LSB)"
  (if (> n 0)
      (multiple-value-bind (n r) (floor n 2)
        (if (> r 0)
            (bits-of n (cons t acc))
            (bits-of n (cons nil acc))))
      (reverse acc)))

;; a really simple implementation of priority queues

(defun prio-pair (value priority)
  "a pair of (value, priority) for priority queues"
  (cons priority value))

(defun prio-priority (pair)
  "get priority from (value, priority) tuple"
  (car pair))

(defun prio-value (pair)
  "get value from (value, priority) tuple"
  (cdr pair))

(defun prio-queue-add (q v p &optional acc)
  "added value v to prio-queue q with priority q"
  (if (endp q)
      (reverse (cons (prio-pair v p) acc))
      (let* ((fst (car q))
             (rest (cdr q))
             (p1 (prio-priority fst)))
        ;; deep circuits
        (if (or (and *deep-circuits* (> p p1))
                (and (not *deep-circuits*) (<= p p1)))
            (append (reverse acc) (cons (prio-pair v p) q))
            (prio-queue-add rest v p (cons fst acc))))))

(defvar *max-priority* 0)

(defun prio-queue-get (q)
  "get element with highest priority in q"
  (let* ((pair (car q))
         (v (prio-value pair))
         (p (prio-priority pair))
         (q1 (cdr q)))
    (if (< p *max-priority*)
        (setf *max-priority* p))
    (values v p q1)))


(defun to-buckets (bits var buckets n)
  "fills the buckets with instances of var (see MS+ paper)"
  (cond
    ((endp bits) n)
    ((car bits)
     (push var (gethash n buckets))
     (to-buckets (cdr bits) var buckets (1+ n)))
    (t (to-buckets (cdr bits) var buckets (1+ n)))))

(defun tare (n)
  "tare to round number to a power of 2"
  (if (> n 0)
      (let ((length (ceiling (log n 2))))
        (values (- (ash 1 length) n) length))
      (values 0 0)))

(defun prio-circuit (&rest args)
  "priority of a node in a circuit"
  #+assert (assert (not (find-if-not #'numberp args)))
  (1+ (apply #'max args)))

(defun rec-bucket (b1 b2 &optional (generate-sum t))
  #+assert (assert b1)
  (labels ((sum-carry-two (x y px py b1 b2)
             #+assert (assert (and (integerp x)
                                   (integerp y)))
             (let* ((carry (get-or x y))
                    ;; skip CNF for the sum bit if we can
                    (sum (if (or b1 generate-sum)
                             (- (get-xor2 x y))))
                    (p (prio-circuit px py))
                    (b1 (prio-queue-add b1 sum p))
                    (b2 (prio-queue-add b2 carry p)))
               (rec-bucket b1 b2 generate-sum))))
    (cond
      ((endp (cdr b1)) (values (prio-queue-get b1) b2))
      ((endp (cddr b1))
       (multiple-value-bind (x px b11)
           (prio-queue-get b1)
         (multiple-value-bind (y py b12)
             (prio-queue-get b11)
           (declare (ignorable b12))
           ;; #+assert
           ;; (assert (not b12))
           (cond
             ((eql x t)
              #+assert (assert (integerp y))
              (values (- y) (prio-queue-add b2 y py)))
             ((eql y t)
              #+assert (assert (integerp x))
              (let ((b2 (prio-queue-add b2 x px)))
                (values (- x) b2)))
             (t (let* ((carry (get-and x y))
                       (sum (if generate-sum (get-xor2 x y)))
                       (p (prio-circuit px py))
                       (b2 (prio-queue-add b2 carry p)))
                  (values sum b2)))))))
      (t (multiple-value-bind (x px b11)
             (prio-queue-get b1)
           (multiple-value-bind (y py b12)
               (prio-queue-get b11)
             (multiple-value-bind (z pz b13)
                 (prio-queue-get b12)
               (cond
                 ((eql x t) (sum-carry-two y z py pz b13 b2))
                 ((eql y t) (sum-carry-two x z px pz b13 b2))
                 ((eql z t) (sum-carry-two x y px py b13 b2))
                 (t #+assert (assert (and (integerp x)
                                          (integerp y)
                                          (integerp z)))
                    (let* ((carry (get-maj3 x y z))
                           (sum (if (or b13 generate-sum)
                                    (get-xor3 x y z)))
                           (p (prio-circuit px py pz))
                           (b1 (prio-queue-add b13 sum p))
                           (b2 (prio-queue-add b2 carry p)))
                      (rec-bucket b1 b2 generate-sum)))))))))))

(defun remaining-bits (n buckets)
  "bits remaining in buckets of value higher than n"
  (loop
     for k being the hash-keys of buckets
     using (hash-value l)
     when (>= k n)
     append (mapcar #'prio-value l)))

(defun adder-cnf (l &optional (tare nil) (tare-n 0))
  "create a MiniSAT+-like adder circuit for a list of terms"
  (let* ((l (sort
             (copy-list l)
             (lambda (t1 t2)
               (let* ((bits-t1 (bits-of (tcoef t1) nil))
                      (bits-t2 (bits-of (tcoef t2) nil))
                      (l1 (delete-if-not #'identity bits-t1))
                      (l2 (delete-if-not #'identity bits-t2)))
                 (< (length l1) (length l2))))))
         (buckets (make-hash-table)))

    (if tare (to-buckets (bits-of tare nil) (prio-pair t 0) buckets 0))

    (dolist (e l)
      (to-buckets (bits-of (tcoef e) nil)
                  (prio-pair (tvar e) 1)
                  buckets 0))
    (labels

        ((no-more-buckets (n buckets)
           (loop
              for k being the hash-keys of buckets
              when (> k n)
              do (return nil)
              finally (return t)))

         (rec-all (n acc)
           (let ((b1 (gethash n buckets)))
             (cond
               ;; ;; no real improvement
               ;; ((and (>= n tare-n) *skip-sums*)
               ;;  (let ((l (remaining-bits n buckets)))
               ;;    (format t "l: ~A~%" l)
               ;;    l))
               (b1 (multiple-value-bind (r b2)
                       (rec-bucket b1 (gethash (1+ n) buckets)
                                   (or (>= n tare-n)
                                       (not *skip-sums*)))
                     (setf (gethash (1+ n) buckets) b2)
                     (rec-all (1+ n) (cons r acc))))
               ((no-more-buckets n buckets) (values acc))
               (t (rec-all (1+ n) (cons nil acc)))))))

      (reverse (rec-all 0 nil)))))


(defun xor-bv (lhs rhs)
  "generate XOR for LHS (vector of SAT vars) and RHS (constants)"
  ;; do not generate anything if XOR is trivially true
  (unless (find-if
           (lambda (x)
             (let* ((lhs-bit (car x))
                    (rhs-bit (cdr x)))
               (and (not lhs-bit) rhs-bit)))
           (mapcar #'cons lhs rhs))
    ;; collect the literals of our clause
    (loop
       for x in lhs
       for y in rhs
       when x
       collect (if y (~ x) x))))

(defun padding (bv n)
  "pad bitvector with nils"
  (append bv
          (loop
             for i from 1 to n
             collect nil)))

(defun geq-cnf (lhs-bits rhs)
  "generate a lexicographic >= circuit"
  (let* ((rhs-bits (bits-of rhs nil))
         (d (- (length lhs-bits) (length rhs-bits))))
    (if (< d 0)
        (format nil "warning: infeasible constraint~%")
        (let ((rhs-bits (padding rhs-bits d)))
          (mapl (lambda (lhs-bits rhs-bits)
                  (let ((b1 (car lhs-bits))
                        (b2 (car rhs-bits)))
                    (if b2
                        (let ((c (xor-bv (cdr lhs-bits)
                                         (cdr rhs-bits))))
                          (if (or c (not (cdr lhs-bits)))
                              (add-clause (if b1 (cons b1 c) c)))))))
                lhs-bits
                rhs-bits)
          nil))))

(defun eq-cnf (lhs-bits rhs)
  "generate equality circuit"
  (let* ((rhs-bits (bits-of rhs nil))
         (d (- (length lhs-bits)
               (length rhs-bits))))
    (if (< d 0)
        (format nil "warning: infeasible constraint~%")
        (let ((rhs-bits (padding rhs-bits d)))
          (mapc (lambda (lhs-bit rhs-bit)
                  (cond ((and lhs-bit rhs-bit)
                         #+assert (assert (not (eql lhs-bit t)))
                         (add-clause (cl lhs-bit)))
                        ((and lhs-bit (not rhs-bit))
                         #+assert (assert (not (eql lhs-bit t)))
                         (add-clause (cl (~ lhs-bit))))
                        ((and (not lhs-bit) rhs-bit)
                         (format nil "warning: infeasible constraint~%"))
                        (t nil)))
                lhs-bits
                rhs-bits)
          nil))))

(defun add-clausal-part (constraint)
  "extract clausal part of PB constraint and add it"
  (let* ((lhs (lhs constraint))
         (rhs (rhs constraint))
         (rel (rel constraint))
         (literals (loop
                      for (var . coef) in lhs
                      when (eql coef rhs)
                      collect var)))
    (if (cdr literals)
        (let* ((rest (remove-if (dot (curry #'eql rhs) #'tcoef) lhs))
               (v (apply #'get-or literals)))
          (make-constraint rel (cons (cons v rhs) rest) rhs))
        constraint)))

(defun add-adder-constraint (constraint)
  "encode PB constraint as an adder"
  (let ((rel (rel constraint)))
    (case rel
      (>= (let ((constraint (add-clausal-part constraint))
                (rhs (rhs constraint)))
            (multiple-value-bind (tare n) (tare rhs)
              #+assert (assert (= (expt 2 n) (+ tare rhs)))
              (let ((lhs-bits (adder-cnf (lhs constraint) tare n)))
                (add-clause (apply #'cl (nthcdr n lhs-bits)))))))
      (= (eq-cnf (adder-cnf (lhs constraint)) (rhs constraint)))
      (otherwise (error (format nil "unknown rel: ~A~%" rel))))))
