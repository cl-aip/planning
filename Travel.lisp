;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;;;; Travel Planning Probrem
;;;

(in-package :plan)
#|
(define-method "air_travel(x,y)" "travel planning problem"
  :task "travel(x,y)"
  :precond "long_distance(x,y)"
  :subtasks "buy_ticket(a, b), travel(x,a), fly(a, b), travel(b,y)"
  :constr ":u1<<:u3, :u2<<:u3, :u3<<:u4")

(define-method "taxi_travel(x,y)" "travel planning problem"
  :task "travel(x,y)"
  :precond "~long_distance(x,y)"
  :subtasks "GET_TAXI(), RIDE(x,y), PAY_DRIVER()"
  :constr ":u1<<:u2, :u2<<:u3")

(defoperator "GET_TAXI()"
    "catch or call a taxi"
  :precond "~getTaxi()"
  :effects "getTaxi()")

(defoperator "RIDE(x,y)"
    "ride on the taxi"
  :precond "getTaxi(), at(x)"
  :effects "~at(x), at(y)")

(setq *state*
      (state
       "{at(UMD)}"))
(setq *goal*
      (state "{at(Toulouse)}"))
|#