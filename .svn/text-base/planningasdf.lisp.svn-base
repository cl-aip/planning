;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; Package: cl-user; Base: 10; Lowercase: Yes -*-

(in-package :cl-user)

(eval-when (:load-toplevel :execute)
  (defparameter *planning-directory*
    (make-pathname :host (pathname-host *load-truename*)
                   :device (pathname-device *load-truename*)
                   :directory (pathname-directory *load-truename*)))
  (setf (logical-pathname-translations "PLANNING")
    `(("**;*.*"
       ,(make-pathname
         :host (pathname-host *planning-directory*)
         :device (pathname-device *planning-directory*)
         :directory (append (pathname-directory *planning-directory*)
                            (list :wild-inferiors))
         :name :wild
         :type :wild
         ))))
) ; end of eval-when

(asdf:defsystem :planning
  :description "Planning System by Ghallab, Nau, and Traverso"
  :version "0.90"
  :author "Seiji Koide"
  :licence "Norvig's Licence Agreement, cf http://www.norvig.com/license.html."
  :components ((:module "utils" :components ((:file "utils/callcc")
                                             (:file "utils/utilities")))
               (:module "fol" :components ((:file "fol/infix"
                                                  :depends-on ((:module "utils" :components ((:file "utils/utilities")))))
                                           (:file "fol/unify"
                                                  :depends-on ((:module "utils" :components ((:file "utils/utilities")))))
                                           (:file "fol/normal"
                                                  :depends-on ((:module "utils" :components ((:file "utils/utilities")))
                                                               (:file "fol/infix")
                                                               (:file "fol/unify")))
                                           (:file "fol/fol"
                                                  :depends-on ((:module "utils" :components ((:file "utils/utilities")))
                                                               (:file "fol/unify")
                                                               (:file "fol/normal"))))
                        )
               (:file "plan/statespace" :depends-on ("fol"))
               (:file "plan/operator"   :depends-on ("fol"))
               (:file "plan/FrwdBkwd"   :depends-on ("fol"))
               (:file "plan/STRIPS"     :depends-on ("fol"))
               (:file "plan/planspace"  :depends-on ("fol"))
               (:file "plan/PSP"        :depends-on ("fol"))
               (:file "plan/STN"        :depends-on ("fol"))
               (:file "RusselProblem"   :depends-on ("plan/PSP"))
               (:file "Travel"          :depends-on ("plan/STN"))
               ))