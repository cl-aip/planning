;;; -*- Mode:  Common-Lisp; Syntax:  Common-Lisp; Base: 10 -*-
;;;
;;;; Continuation module in Common Lisp
;;; This module provides the functionality of continuation in Lisp such as Scheme does.
;;; The trick of continuation is the closure that is hidden from programmer's eyes using macros and the combined functions.
;;; The following forms look like a function but they are macros and call corresponding functions 
;;; respectively with the closure that involves the environment.
;;;
;;; Copyright (c) Seiji Koide 2007, 2008
;;; Part of this code, copyright (c) 1993 Paul Graham
;;
;; History
;; -------
;; 2007.05.04    File created, copied from Paul Graham's 'On Lisp' by hand

(cl:defpackage :callcc
  (:export =lambda =defun =bind =values =funcall =apply
           choose choose-bind fail)
  )

(in-package :callcc)

(declaim (special *cont* *saved*))

(setq *cont* #'values)

(defmacro =lambda (parms &body body)
  "macro for continuous lambda form. It replaces the form with the stack of closures."
  `#'(lambda (*cont* ,@parms) ,@body))

(defmacro =defun (name parms &body body)
  "defines macro and function named '=<name>' with the stack of closures."
  (let ((f (intern (concatenate 'string "=" (symbol-name name)))))
    `(progn
       (defmacro ,name ,parms
         `(,',f *cont* ,,@parms))
       (defun ,f (*cont* ,@parms) ,@body))))

(defmacro =bind (parms expr &body body)
  "this is used for making parameter bindings in continuous functions instead of let form."
  `(let ((*cont* #'(lambda ,parms ,@body))) ,expr))

(defmacro =values (&rest retvals)
  "this is used for making multiple value returning in continuous functions instead of values form."
  `(funcall *cont* ,@retvals))

(defmacro =funcall (fn &rest args)
  "this is used for making a funcall form in continuous functions."
  `(funcall ,fn *cont* ,@args))

(defmacro =apply (fn &rest args)
  "this is used for making an apply form in continuous functions."
  `(apply ,fn *cont* ,@args))

#|
(=defun add1 (x) (=values (1+ x)))
(macroexpand '(=defun add1 (x) (=values (1+ x))))
-> (progn (defmacro add1 (x) (excl::bq-list '=add1 `*cont* x)) (defun =add1 (*cont* x) (=values (1+ x))))
(macroexpand '(=values (1+ x)))
-> (funcall *cont* (1+ x))

(=defun bar (x)
        (=values (list 'a (add1 x))))
-> =bar
(bar 5) -> (a 6)

(=defun message ()
        (=values 'hello 'there))
-> =message
(=defun baz ()
        (=bind (m n) (message)
               (=values (list m n))))
-> =baz
(baz) -> (hello there)

(let ((fn (=lambda (n) (add1 n))))
  (=bind (y) (=funcall fn 9)
         (format nil "9 + 1 = ~A" y)))
-> "9 + 1 = 10"
|#

(defun dft (tree)
  (cond ((null tree) nil)
        ((atom tree) (princ tree))
        (t (dft (car tree))
           (dft (cdr tree)))))

(setq *saved* nil)

(=defun cc-restart ()
        (if *saved*
            (funcall (pop *saved*))
          (=values 'done)))

(=defun dft-node (tree)
        (cond ((null tree) (cc-restart))
              ((atom tree) (=values tree))
              (t (push #'(lambda () (dft-node (cdr tree)))
                       *saved*)
                 (dft-node (car tree)))))

(=defun dft2 (tree)
        (setq *saved* nil)
        (=bind (node) (dft-node tree)
               (cond ((eq node 'done) (=values nil))
                     (t (princ node)
                        (cc-restart)))))

#|
(setq t1 '(a (b (d h)) (c e (f i) g)))
(setq t2 '(1 (2 (3 6 7)) 4 5))
(dft2 t1) -> abdhcefig
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defparameter *paths* nil "stack of continuation for undeterministic choice.")
(defconstant failsym '@ "marker of no backtrack point.")

(defmacro choose (&rest choices)
  "if <choices> is not empty, undeterministically choose one of choices and 
   evaluates it."
  (if choices
      `(progn 
         ,@(mapcar #'(lambda (c)
                       `(push #'(lambda () ,c) *paths*))
             (reverse (cdr choices)))
         ,(car choices))
    '(fail)))

(defmacro choose-bind (var choices &body body)
  "undeterministically chooses one of <choices> and binds it to <var>, then 
   evaluates <body> in the binding." 
  `(cb #'(lambda (,var) ,@body) ,choices))

(defun cb (fn choices)
  "this is used in <choose-bind>."
  (if choices
      (progn
        (if (cdr choices)
            (push #'(lambda () (cb fn (cdr choices)))
                  *paths*))
        (funcall fn (car choices)))
    (fail)))

(defun fail ()
  "backtracks to the last point of continuation and calls the continuation."
  (format t "~%Failed.")
  (if *paths*
      (funcall (pop *paths*))
    failsym))

;;;
#|
(defun do2 (x)
  (choose (+ x 2) (* x 2) (expt x 2)))
(do2 3) -> 3
*paths*
->
(#<Interpreted Closure (:internal do2) @ #x20ca8102>
 #<Interpreted Closure (:internal do2) @ #x20ca8132>)
(fail) -> 6
(fail) -> 9
(fail) -> @
(choose-bind x '(marrakesh strasbourg vegas)
             (format nil "Let's go to ~A." x))
-> "Let's go to marrakesh."
(fail) -> "Let's go to strasbourg."
(fail) -> "Let's go to vegas."
(fail) -> @
|#
