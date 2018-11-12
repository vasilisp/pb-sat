(ql:quickload "cffi")
(ql:quickload "getopt")
(ql:quickload "cl-ppcre")

(load "parameters.lisp")
(load "prelude.lisp")
(load "parser.lisp")
(load "picosat.lisp")
(load "cnf.lisp")
(load "bdds.lisp")
(load "adders.lisp")
(load "solver.lisp")

(defvar *save-executable* nil)
(defvar *cnf-filename*)
(defvar *monolithic*)

;; i don't like this
(defconstant +options+
  (list
   (list "important-variables" :none
         (lambda () (setf *important-variables* t)))
   (list "no-important-variables" :none
         (lambda () (setf *important-variables* nil)))
   (list "dl" :required
         (lambda (v) (setf *dl* (parse-integer v))))
   (list "adders" :none
         (lambda () (setf *adders* t)))
   (list "no-adders" :none
         (lambda () (setf *adders* nil)))
   (list "extra-clauses" :none
         (lambda () (setf *extra-clauses* t)))
   (list "no-extra-clauses" :none
         (lambda () (setf *extra-clauses* nil)))
   (list "udl" :required
         (lambda (v) (setf *udl* (parse-integer v))))
   (list "bdd-limit" :required
         (lambda (v) (setf *bdd-limit* (parse-integer v))))
   (list "cnf" :required
         (lambda (v) (setf *cnf-filename* v)))
   (list "monolithic" :none
         (lambda () (setf *monolithic* t)))
   (list "no-monolithic" :none
         (lambda () (setf *monolithic* nil)))
   (list "merging" :none
         (lambda () (setf *merging* t)))
   (list "no-merging" :none
         (lambda () (setf *merging* nil)))
   (list "more-units" :none
         (lambda () (setf *more-units* t)))
   (list "no-more-units" :none
         (lambda () (setf *more-units* nil)))))

(defun parse-options (l)
  (dolist (pair l)
    (let* ((option (car pair))
           (value (cdr pair))
           (triple (find-if (dot (curry #'equal option) #'car)
                            +options+))
           (f (third triple)))
      (if (eql (second triple) :none)
          (funcall f)
          (funcall f value)))))

(defun main ()
  (let ((*cnf-filename* nil)
        (*monolithic* nil)
        (options (mapcar #'butlast +options+)))
    (multiple-value-bind (l1 l2 l3)
        (getopt:getopt (cdr *posix-argv*) options)
      (declare (ignorable l3))
      (assert l1)
      (parse-options l2)
      (format t "c file: ~A~%" (car l1))
      (multiple-value-bind (*pb-constraints* objective)
          (parse-file (car l1))
        (solver *pb-constraints*
                :monolithic *monolithic*
                :cnf-file *cnf-filename*
                :objective objective)))))

#+sbcl
(if *save-executable*
    (save-lisp-and-die "pb-sat" :toplevel #'main :executable t))
