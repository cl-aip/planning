;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;;;; Russel&Novig Planning Probrem in AIMA
;;;

(in-package :plan)

#|
(defoperator "Go(h,l)"
  :precond "at(h)"
  :effects "at(l),~at(h)")

(defoperator "Buy(s,x)"
  :precond "sells(s,x),at(s)"
  :effects "have(x)")

(PSP (make-minimal-plan "at(Home),sells(HWS,Drill),sells(SM,Milk),sells(SM,Banana)"
                        "have(Drill),have(Milk),have(Banana),at(Home)"))
(trace =PSP)
|#