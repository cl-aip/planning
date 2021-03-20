;;; -*- Mode: common-lisp; Syntax: Common-Lisp; -*-

;; copyright (c) 2004-2006 Franz Inc., Oakland CA
;;
;; The software, data and information contained herein are proprietary
;; to, and comprise valuable trade secrets of, Franz, Inc.  They are
;; given in confidence by Franz, Inc. pursuant to a written license
;; agreement, and may be stored and used only in accordance with the terms
;; of such license.
;;
;; Restricted Rights Legend
;; ------------------------
;; Use, duplication, and disclosure of the software, data and information
;; contained herein by any agency, department or entity of the U.S.
;; Government are subject to restrictions of Restricted Rights for
;; Commercial Software developed at private expense as specified in
;; DOD FAR Supplement 52.227-7013 (c) (1) (ii), as applicable.

(eval-when (compile)
  (error "This defsys file should be loaded interpreted, not compiled."))

;; (setf compiler::*compile-with-compilation-unit-override* nil)

(excl:defsystem :planning
    (:default-pathname #.*load-pathname*)
  (:serial
   "callcc"
   "utilities"
   "infix"
   "unify"
   "normal"
   "fol"
   "statespace"
   "operator"
   "planning"
   "STN"
   ))

(format t "~%;;To compile and load, execute these forms:~%~s~%~s~%"
	'(excl:compile-system :planning :recompile t)
	'(excl:load-system    :planning))

(format t ";;To create a single fasl file, execute:~%~s~%~%"
	'(excl:concatenate-system :planning "planning.fasl"))

