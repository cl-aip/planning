;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;; The Automated Planning - Theory and Practice is a textbook for planning by Malik Ghallab, 
;; Dana Nau, and Paolo Traverso, from Morgan Kaufmann. 
;; This program is a realization of algorithms that are published on the book, coded by Seiji 
;; Koide. 

;;;; STRIPS Module (Figure 4.4 and Exercise 4.11)
;;; All rights on programs are reserved by Seiji Koide. 
;;; 
;;; Copyrights (c), 2008, Seiji Koide

(cl:defpackage :plan
  (:shadowing-import-from :fol compound-unify compound-unify?)
  (:use common-lisp :utils :fol :callcc)
  (:export 
   )
  )

(in-package :plan)

;;;; STRIPS
;;; In <lifted-backward-search>, subgoal in regression process is a union of <precond> and 
;;; set-difference of <goal> and <effects>, partially instantiated by partially matched 
;;; unifier between <goal> and <effects>. However, in backward search of STRIPS, subgoal is 
;;; taken only from precond of partially instantiated operator that is relevant to goal. 
;;;
;;; There are two main loops in STRIPS. One is a regressive search process that starts at 
;;; the given goal and reaches the initial state. In this process, relevant operators are 
;;; retrieved, but neither regression of goal nor progression of state happen. The subgoal 
;;; is just a partially instantiated precond of relevant operator. This regressive search 
;;; process is done by recursive call that involves undeterministic choice of relevants and 
;;; backtracking control. 
;;;
;;; Once we find the satisfiable subgoal to the initial state, then another loop is 
;;; conducted. This loop explicitely and deterministically controls the progression of state 
;;; from the initial state to the given goal with the substitution between the intermediate 
;;; state and the subgoal in each iteration. 
;;;
;;; Namely, as we have found the correct answer in search process, and we now have the 
;;; initial state (let it be <s0>) that satisfies the precond of action (<a1>), so 
;;; we can obtain the next state <s1> by one step progression with <a1>. Then, we go to 
;;; the top of loop with having this <s1>. Note that <s1> satisfies precond of <a2> with 
;;; appropriate substitution. Then, we can obtain the next state <s2> by one step progression
;;; with <a2>. This progressive loop and recursion process is repeated again and again with 
;;; having <s2>, <s3>, ..., until we reach at the given goal with updated last state. Of course, 
;;; the final initial state satisfies the goal, then we obtain completely instantiated answer of 
;;; planning. Note that the answer of planning is incrementally instantiated in progressive 
;;; iteration.
;;; 

(=defun STRIPS (state goal plan)
        "searches relevant operators and returns a list of actions."
        ;; plan accumulates possible operation sequence that is partially instantiated.
        ;; state is always intial condition for input data
        ;; goal is subgoal that is precond(action).
        (let ((bindings ())
              (action ())
              (answer ())
              (sofar ()))
          (loop
            (if (setq bindings (satisfy-p state goal)) ; always true in progressive loop
                (return-from =STRIPS (=values (subst-bindings bindings (or answer plan))))
              ;; answer is always empty at search process and plan is accumulated in 
              ;; searching recursive call. once <state> satisfied <goal>, it is always 
              ;; returned in progressive recursive call with instantiation.
              (let ((relevant
                     (loop for o in *operators* with bindings-list
                         do (setq o (rename-variables o))
                         when (setq bindings-list
                                    (operator-unify-for-regression o goal +no-bindings+))
                         append (loop for bindings in bindings-list
                                    when (goal-relevant-p o goal bindings)
                                    collect (make-relevant :operator o :bindings bindings)))))
                (if (null relevant) (fail)
                  (choose-bind rel relevant
                    (format t "~%Relevant chosen:~S~%  precond:~S~%  effects:~S~%~S~%Goal:~S"
                      (operator-name (relevant-operator rel))
                      (operator-precond (relevant-operator rel))
                      (operator-effects (relevant-operator rel))
                      (relevant-bindings rel)
                      goal)
                    (setq action (subst-bindings (relevant-bindings rel)
                                                 (relevant-operator rel)))
                    (setq answer (STRIPS state (action-precond action) (cons action plan)))
                    (when (eq plan callcc::failsym) (fail))
                    ;; if we get here, then plan achieves precond(action) from state
                    (format t "~%Plan:~S" (mapcar #'action-name plan))
                    (setq sofar (subseq answer 0 (- (length answer) (length plan))))
                    (format t "~%Sofar:~S" (mapcar #'operator-name sofar))
                    (loop for action in sofar
                        do (setq state (progress-action action state)))
                    ))))
            ;; end of loop
            )
          answer))


#|
(setq *state*
      (state
       "{attach(p1,loc1),in(c1,p1),top(c1,p1),on(c1,pallet),
         attach(p2,loc1),in(c2,p2),top(c2,p2),on(c2,pallet),
         belong(crane1,loc1),holding(crane1,c3),adjacent(loc1,loc2),
         adjacent(loc2,loc1),at(r1,loc2),occupied(loc2),unloaded(r1)}"))
(defoperator "move(r,l,m)"
    "robot <r> moves from location <l> to an adjacent location <m>"
  :precond "adjacent(l,m),at(r,l),~occupied(m)"
  :effects "at(r,m),occupied(m),~occupied(l),~at(r,l)")
(defoperator "load(k,l,c,r)"
    "crane <k> at location <l> loads container <c> onto robot <r>"
  :precond "belong(k,l),holding(k,c),at(r,l),unloaded(r)"
  :effects "empty(k),~holding(k,c),loaded(r,c),~unloaded(r)")
(setq *goal*
      (state "{at(r1,loc1),loaded(r1,c3)}"))
(STRIPS *state* *goal* ())
|#