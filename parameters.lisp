;;; general

;; PB variables are more important than the others
(defparameter *important-variables* nil)
;; length limit for clauses implied by PB constraints
(defparameter *max-implied-clause-length* 3)
;; limited solving instead of pure BCP: allow up to *dl* decisions
(defparameter *dl* 0)

;;; adders

;; use adders (if nil, they will be used as fallback)
(defparameter *adders* nil)
;; prefer deep circuits for adders
(defparameter *deep-circuits* t)
;; add extra clauses that help with propagation (for adders)
(defparameter *extra-clauses* t)
;; skip generation of not needed sum bits for adders
(defparameter *skip-sums* t)

;;; BDDs

;; 500000 ITE nodes per BDD
(defparameter *bdd-limit* 500000)
;; build BDDs for conjunctions of constraints that share variables
(defparameter *merging* nil)

;;; extracting more units

;; call algorithm for extracting more units
(defparameter *more-units* nil)
;; decision limit for more-units algorithm
(defparameter *udl* 10)
