;;; -*- Mode: Lisp; Syntax: ANSI-Common-Lisp; Package: cl-user; Base: 10; Lowercase: Yes -*-

(in-package #:asdf)

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

;;; (defmethod source-file-type ((c cl-source-file) (s module)) "cl")

(asdf:defsystem #:utils
    :name "Utils"
  :description "Utilities for Planning System"
  :version "0.90"
  :author "Peter Norvig & Paul Graham"
  :maintainer "Seiji Koide <SeijiKoide@aol.com>"
  :licence "Norvig's Licence Agreement, cf http://www.norvig.com/license.html."
  :components ((:module "utils"
                        :components ((:file "callcc")
                                     (:file "utilities")))))

(asdf:defsystem #:fol
  :description "FOL subsystem for Planning System"
  :version "0.90"
  :author "Peter Norvig"
  :maintainer "Seiji Koide <SeijiKoide@aol.com>"
  :licence "Norvig's Licence Agreement, cf http://www.norvig.com/license.html."
  :depends-on ("utils")
  :components ((:module "fol" 
                        :components ((:file "infix")
                                     (:file "unify")
                                     (:file "normal"
                                            :depends-on ("infix" "unify" ))
                                     (:file "fol"
                                            :depends-on ("unify" "normal"))))))

(asdf:defsystem #:plan
  :description "plan subsystem for Planning System"
  :version "0.90"
  :author "Seiji Koide"
  :maintainer "Seiji Koide <SeijiKoide@aol.com>"
  :licence "Norvig's Licence Agreement, cf http://www.norvig.com/license.html."
  :depends-on ("fol")
  :components ((:module "plan"
                        :components ((:file "statespace")
                                     (:file "operator")
                                     (:file "FrwdBkwd")
                                     (:file "STRIPS")
                                     (:file "planspace")
                                     (:file "PSP")
                                     (:file "STN")))))

(asdf:defsystem #:planning
  :description "Planning System"
  :version "0.90"
  :author "Seiji Koide"
  :maintainer "Seiji Koide <SeijiKoide@aol.com>"
  :licence "Norvig's Licence Agreement, cf http://www.norvig.com/license.html."
  :depends-on ("plan")
  :components ((:file "RusselProblem")
               (:file "Travel")))