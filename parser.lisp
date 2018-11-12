(defvar *pb-variables* 0)
(defvar *last-variable* 0)

;;; data-types used throughout the solver

(defun tcoef (term)
  "coeficient of a term"
  (cdr term))

(defun tvar (term)
  "variable of a term"
  (car term)) 

(defun rel (c)
  "relation of a PB constraint"
  (first c))

(defun lhs (c)
  "left-hand side of a PB constraint"
  (second c))

(defun rhs (c)
  "right-hand side of a PB constraint"
  (third c))

(defun make-constraint (rel lhs rhs)
  "make a pb constraint out of an LHS, relation, and RHS"
  (assert (for-all
           (lambda (x)
             (and (consp x)
                  (or (integerp (car x)) (consp (car x)))
                  (integerp (cdr x))))
           lhs))
  (assert (in rel (list '>= '<= '=)))
  (assert (integerp rhs))
  (list rel lhs rhs))

(defun lhs-c (p)
  "coeficients of the LHS of a PB constraint"
  (mapcar #'tcoef (lhs p)))

(defun lhs-v (p)
  "variables that appear in the LHS of a PB constraint"
  (mapcar #'tvar (lhs p)))

(defun make-lhs (lhs-coefs lhs-vars)
  "make a LHS out of a list of coefs and a list of vars"
  (mapcar #'cons lhs-vars lhs-coefs))

;; Parser is too liberal, e.g. it will tolerate arbitrary strings
;; between terms. It is not very efficient either.

(defconstant +token-re+
  (cl-ppcre:parse-string "(min:)|([\+-]?\\d+)|(~)|x(\\d+)|(>=|<=|=)"))

(defun parse-line (line)
  "parse OPB line"
  (let* ((tokens (cl-ppcre:all-matches-as-strings +token-re+ line))
         (found-min nil)
         (found-rel nil)
         (found-rhs nil)
         (found-coef nil)
         (found-neg nil)
         (literals nil)
         (terms nil))
    (flet ((push-term ()
             (when (and found-coef literals)
               (push (cons (if (endp (cdr literals))
                               (car literals)
                               literals)
                           found-coef)
                     terms)
               (setf found-coef nil literals nil))))
      (dolist (token tokens)
        (cond ((equal token "min:")
               (setf found-min t))
              ((equal token "~")
               (setf found-neg t))
              ((eql (aref token 0) #\x)
               (if found-coef
                   (let* ((id (parse-integer (subseq token 1)))
                          (literal (if found-neg (- id) id)))
                     (if (> id *last-variable*)
                         (setf *last-variable* id
                               *pb-variables* id))
                     (setf found-neg nil)
                     (push literal literals))
                   (error "parse error")))
              ((in token (list ">=" "<=" "=") :test #'equal)
               (if found-rel
                   (error "parse error")
                   (progn
                     (push-term)
                     (setf found-rel (intern token)))))
              (t (let ((v (parse-integer token)))
                   (cond
                     ((and found-rel found-rhs)
                      (error "parse error"))
                     (found-rel (setf found-rhs v))
                     (t (push-term)
                        (setf found-coef v)))))))
      (cond ((and terms found-min)
             (push-term)
             (list nil terms nil))
            ((and terms found-rel found-rhs)
             (make-constraint found-rel terms found-rhs))
            (t (error "parse error"))))))

(defun parse-file (filename)
  "parse file in OPB format"
  (let ((constraints nil)
        (objective nil))
    (with-open-file (st filename)
      (do ((line (read-line st nil)
                 (read-line st nil)))
          ((null line))
        (unless (eql (aref line 0) #\*)
          (let ((constraint (parse-line line)))
            (if (not (rel constraint))
                (setf objective (lhs constraint))
                (push constraint constraints))))))
    (values constraints objective)))
