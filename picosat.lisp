(defpackage :picosat
  (:use :common-lisp :cffi)
  (:export :init :reset :reset-phases :fopen :set-output :print
           :measure-all-calls :set-prefix :set-verbosity
           :set-global-default-phase :set-default-phase-lit
           :set-seed :enable-trace-generation :inc-max-var
           :adjust :variables :added-original-clauses
           :max-bytes-allocated :time-stamp :stats :seconds :add
           :assume :add-ado-lit :sat :res :deref :deref-toplevel
           :inconsistent :changed :set-more-important-lit
           :add-clause))

(in-package :picosat)

(define-foreign-library libpicosat
    (:unix (:or "libpicosat.so.0" "libpicosat.so"))
  (t (:default "libpicosat")))

(use-foreign-library libpicosat)

(defctype size :unsigned-int)

;; wrapped picosat API; everything is here except the functions with
;; FILE arguments
;;
;; API documentation in picosat.h

;; (cffi:defcfun "picosat_version" :string)
(cffi:defcfun ("picosat_init" init) :void)
(cffi:defcfun ("picosat_reset" reset) :void)
(cffi:defcfun ("picosat_reset_phases" reset-phases) :void)
(cffi:defcfun "fopen" :pointer (filename :string) (mode :string))
(cffi:defcfun ("picosat_set_output" set-output)
    :void (filename :pointer))
(cffi:defcfun ("picosat_print" psprint) :void (filename :pointer))
(cffi:defcfun ("picosat_measure_all_calls" measure-all-calls)
    :void)
(cffi:defcfun ("picosat_set_prefix" set-prefix) :string)
(cffi:defcfun ("picosat_set_verbosity" set-verbosity)
    :void (verbosity :int))
(cffi:defcfun
    ("picosat_set_global_default_phase" set-global-default-phase)
    :void (n :int))
(cffi:defcfun
    ("picosat_set_default_phase_lit" set-default-phase-lit)
    :void (lit :int) (phase :int))
(cffi:defcfun ("picosat_set_seed" set-seed)
    :void (seed :unsigned-int))
(cffi:defcfun
    ("picosat_enable_trace_generation" enable-trace-generation)
    :void)
(cffi:defcfun ("picosat_inc_max_var" inc-max-var) :int)
(cffi:defcfun ("picosat_adjust" adjust) :void (max-idx :int))
(cffi:defcfun ("picosat_variables" variables) :int)
(cffi:defcfun
    ("picosat_added_original_clauses" added-original-clauses)
    :int)
(cffi:defcfun
    ("picosat_max_bytes_allocated" max-bytes-allocated)
    size)
(cffi:defcfun
    ("picosat_time_stamp" time-stamp)
    :double)
(cffi:defcfun ("picosat_stats" stats) :void)
(cffi:defcfun ("picosat_seconds" seconds) :double)
(cffi:defcfun ("picosat_add" add) :int (lit :int))
(cffi:defcfun ("picosat_assume" assume) :void (lit :int))
(cffi:defcfun ("picosat_add_ado_lit" add-ado-lit)
    :void (lit :int))
(cffi:defcfun ("picosat_sat" sat) :int (decision-limit :int))
(cffi:defcfun ("picosat_res" res) :int)
(cffi:defcfun ("picosat_deref" deref) :int (lit :int))
(cffi:defcfun ("picosat_deref_toplevel" deref-toplevel)
    :int (lit :int))
(cffi:defcfun ("picosat_inconsistent" inconsistent) :int)
(cffi:defcfun ("picosat_changed" changed) :int)
(cffi:defcfun
    ("picosat_set_more_important_lit" set-more-important-lit)
    :void (lit :int))

(defun add-clause (clause)
  "add clause to solver"
  #+assert (assert (> (length clause) 0))
  (dolist (literal clause)
    #+assert (assert (not (equal literal 0)))
    (add literal))
  (add 0))
