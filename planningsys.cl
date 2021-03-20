;;; -*- Mode: common-lisp; Syntax: Common-Lisp; -*-

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

(excl:defsystem :utils (:pretty-name "Utils subsystem of Planning system"
                                     :default-pathname #,*planning-directory*)
  (:module :callcc "utils/callcc")
  (:module :utilities "utils/utilities")
  )

(excl:defsystem :FOL (:pretty-name "FOL subsystem of Planning system"
                                   :default-pathname #,*planning-directory*)
  (:module :utils :utils)
  (:module :infix "FOL/infix" (:uses-definitions-from (:utils)))
  (:module :unify "FOL/unify" (:uses-definitions-from (:utils)))
  (:module :normal "FOL/normal" (:uses-definitions-from (:utils :infix :unify)))
  (:module :fol "FOL/fol" (:uses-definitions-from (:utils :unify :normal)))
  )

(excl:defsystem :plan (:pretty-name "Plan subsystem of Planning system"
                                    :default-pathname #,*planning-directory*)
  (:module :FOL :FOL)
  (:module :statespace "plan/statespace" (:uses-definitions-from (:FOL)))
  (:module :operator "plan/operator" (:uses-definitions-from (:FOL)))
  (:module :FrwdBkwd "plan/FrwdBkwd" (:uses-definitions-from (:FOL)))
  (:module :STRIPS "plan/STRIPS" (:uses-definitions-from (:FOL)))
  (:module :planspace "plan/planspace" (:uses-definitions-from (:FOL)))
  (:module :PSP "plan/PSP" (:uses-definitions-from (:FOL)))
  (:module :STN "plan/STN" (:uses-definitions-from (:operator :FOL)))
  )

(excl:defsystem :planning (:pretty-name "Planning system"
                                        :default-pathname #,*planning-directory*)
  (:module :FOL :FOL)
  (:module :plan :plan)
  (:module :RusselProblem "RusselProblem" (:uses-definitions-from (:FOL :plan)))
  (:module :Travel "Travel" (:uses-definitions-from (:FOL :plan)))
  )

(format t "~%;;To compile and load, execute these forms:~%~s~%~s~%"
	'(excl:compile-system :planning :recompile t)
	'(excl:load-system    :planning))

(format t ";;To create a single fasl file, execute:~%~s~%~%"
	'(excl:concatenate-system :planning "planning.fasl"))

