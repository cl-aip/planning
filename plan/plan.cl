;;;-*- mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;;
;;; Automated Planning - Theory and Practice
;;;  by Malik Ghallab, Dana Nau, and Paolo Traverso, from Morgan Kaufmann
;;;  programmed by Seiji Koide
;;;  2007 (c) Seiji Koide
;;;

;;; Chapter 2 Classical Planning
;;;   2.3.2 Operators and Actions
;;; Chapter 4 State-Space Planning

(cl:defpackage :plan
  (:shadow method make-method defmethod)
  (:use common-lisp :callcc :utils :fol)
  (:export make-statevar statevar-p statevar-name statevar-val statevar-parms
           ope-name-p make-ope-name ope-name-symbol ope-name-parms
           operator operator-p make-operator operator-name operator-symbol operator-variables 
           operator-comment operator-precond operator-effects
           method method-name make-method method-comment method-task method-subtasks 
           method-constr set-method-constr method-variables set-method-variables defmethod
           task task-p make-task task-symbol task-terms set-task-terms
           node-p make-node node-task)
  )

(eval-when (:execute :load-toplevel :compile-toplevel)
  ) ; end of eval-when

(in-package :plan)

(defun statevar-unify (statevar state bindings)
  "returns a list of possible bindings of statevar against state."
  ;; positive-statevar-unify is straight.
  ;; negative-statevar-unify is 
  (loop for st in state with result
      when (not (eq (setq result (unify statevar st bindings))
                    +fail+))
      collect result))
  
(defun positive-statevar-p (statevar)
  (statevar-val statevar))

(defun precond-unify (precond state bindings)
  "returns a list of possible bindings of condition against state."
  (loop for svar in precond with bindings-list = (list bindings)
      do (setq bindings-list
               (mappend #'(lambda (bindings)
                            (statevar-unify svar state bindings))
                        bindings-list))
        ;(format t "~%    Bindings List for ~S~%                ~S" svar bindings-list)
      finally (return bindings-list)))

(defun effects-unify (effects goal bindings)
  "returns a list of possible bindings of effects against goal."
  ;; effects must be a normal form.
  (loop for svar in effects with bindings-list = (list bindings)
      do (setq bindings-list
               (mappend #'(lambda (bindings)
                            (statevar-unify svar goal bindings))
                        bindings-list))
      finally (return bindings-list)))

(defun goal-relevant-p (operator goal bindings) ; See p.46 and p.31
  "returns a list of bindings that operator's effects can be unified against goal.
   Note that effects and goal may include object variables.
   Any variable in effects must be different from any variables in goal."
  ;; effects-unify implies relevant condition in p.31 and p.46
  (let* ((effects (mapcar #'normal-statevar (operator-effects operator)))
         (bindings-list (effects-unify (intersection effects goal :test #'statevar-equalp-with-unify)
                                       (intersection goal effects :test #'statevar-equalp-with-unify)
                                       bindings)))
    bindings-list))

(defun operator-unify-for-progression (operator state bindings)
  "makes an action from operator by unification with bindings."
  (let ((bindings-list
         (precond-unify (operator-precond operator)
                        state bindings)))
    (loop for bindings in bindings-list
        collect (make-action-from operator bindings state))))

(defun operator-unify-for-regression (operator goal bindings)
  "makes a partially instantiated operator by unification with bindings."
  (let ((bindings-list
         (effects-unify (mapcar #'normal-statevar (operator-effects operator))
                        goal bindings)))
    (loop for bindings in bindings-list
        collect (instantiate-relevant-from operator bindings))))
  
(defun instantiate-operator (operator state bindings)
  "returns substituted operator with precond unification against state.
   This function returns nil if operator is not unifiable."
  (operator-unify-for-progression operator state bindings))

(=defun forward-search (operators state goal plan)
        (if (satisfy-p state goal) (=values (reverse plan))
          (let ((applicable
                 (remove-if-not #'(lambda (a) (applicable-action-p a state))
                                (mappend #'(lambda (o)
                                             (instantiate-operator o state +no-bindings+))
                                         operators))))
            ;(format t "~%RawApplicable:~S" applicable)
            (setq applicable
                  (remove-if #'(lambda (action)
                                 (some #'(lambda (occurence) (same-action-p action occurence))
                                       plan))
                             applicable))
            ;(format t "~%Applicable:~S" applicable)
            (cond ((null applicable) (fail))
                  (t (choose-bind action applicable
                                  (forward-search operators (progress-action action state) goal 
                                                  (cons action plan))))))))

#|
(in-package :plan)
;; Figure 2.3
(setq *state*
      (make-state
       '((attach(p1) = loc1) (in(c1) = p1) (top(c1) = p1) (on(c1) = pallet)
         (attach(p2) = loc1) (in(c2) = p2) (top(c2) = p2) (on(c2) = pallet)
         (belong(crane1 loc1)) (holding(crane1) = c3)
         (adjacent(loc1 loc2)) (adjacent(loc2 loc1))
         (loc(r1) = loc2) (occupied(loc2) = t) (unloaded(r1) = t))))
(defoperator load(?k ?l ?c ?r)
  "crane k loads container c to robot r at location l"
  :precond ((loc(?r) = ?l) (belong(?k ?l)) (holding(?k) = ?c) (unloaded(?r) = t))
  :effects ((loc(?r) = ?l) (empty(?k) = t) (holding(?k ?c) = nil) (loaded(?r) = ?c) (unloaded(?r) = nil)))
(defoperator move(?r ?l ?m)
  ""
  :precond ((loc(?r) = ?l)                    (occupied(?l) = t) (adjacent(?l ?m)))
  :effects ((loc(?r) = ?m) (loc(?r ?l) = nil) (occupied(?l) = nil) (occupied(?m) = t)))
(instantiate-operator (car *operators*) *state* +no-bindings+)
(instantiate-operator (cadr *operators*) *state* +no-bindings+)
(setq *goal*
      (make-state '((loc(r1) = loc1) (loaded(r1) = c3)
                    (belong(crane1 loc1)) (empty(crane1) = t)
                    (adjacent(loc1 loc2)) (adjacent(loc2 loc1)))))
(trace =forward-search)
(forward-search *operators* *state* *goal* ())
|#

;;;
;;; Backward Search
;;;

(defun regressive-action (operator goal)
  "takes inverse action regressively from goal, and returns sub goal."
  (union (set-difference goal
                         (mapcar #'normal-statevar (operator-effects operator))
                         :test #'statevar-equalp)
         (operator-precond operator)
         :test #'statevar-equalp))

(defun normal-statevar (svar)
  (case (statevar-val svar)
    ((t nil) svar)
    (otherwise (make-statevar :name (statevar-name svar)
                              :parms (append (statevar-parms svar) (list (statevar-val svar)))
                              :val t))))

(defun same-statevar-p (svar1 svar2)
  "tests equality with possible unification."
  (and (eql (statevar-name svar1) (statevar-name svar2))
       (every #'(lambda (v1 v2) (cond ((variable? v1) t)
                                      ((variable? v2) t)
                                      (t (eql v1 v2))))
              (statevar-parms svar1) (statevar-parms svar2))))

(defun relevant-unify-in-backward-search (relevant goal bindings)
  (let ((bindings-list
         (effects-unify (operator-effects relevant) goal bindings)))
    (loop for bindings in bindings-list
        collect (relevant-operators-from relevant bindings))))

(defun relevant-operators (operator state goal)
  "returns partially substituted operator with effects unification against goal."
  (declare (ignore state))
  (when (goal-relevant-p operator goal +no-bindings+)
    (let ((result (relevant-unify-in-backward-search operator goal +no-bindings+)))
      (when (car result)
        result))))

(defun instantiate-plan (plan)
  (%instatiate-plan (car plan) (rest plan) *state* ()))
(defun %instatiate-plan (operator successors state instantiated)
  (cond ((null operator) (nreverse instantiated))
        (t (let ((action (instantiate-operator operator state +no-bindings+)))
             (%instatiate-plan (car successors) (rest successors)
                               (progress-action action state)
                               (cons action instantiated))))))
  
(=defun backward-search (operators state goal plan)
        (if (satisfy-p state goal) (=values (instantiate-plan plan))
          (let ((relevants (mappend #'(lambda (o) (relevant-operators o state goal)) operators)))
            ;(format t "~%Relevants:~S" relevants)
            (cond ((null relevants) (fail))
                  (t (choose-bind relevant relevants
                                  (backward-search operators state
                                                   (regressive-action relevant goal) 
                                                   (cons relevant plan))))))))

(defun make-relevant (operator bindings)
  (cons operator bindings))
(defun relevant-operator (relevant)
  (car relevant))
(defun relevant-bindings (relevant)
  (cdr relevant))

(=defun lifted-backward-search (operators state goal plan)
        (let ((final-bindings ()))
          (if (setq final-bindings (satisfy-p state goal))
              (=values (subst-bindings final-bindings plan))
            (let ((relevants 
                   (loop for o in operators with bindings-list
                       do (setq o (rename-variables o))
                       append (mapcar #'(lambda (bindings)
                                          (make-relevant o bindings))
                                (goal-relevant-p o goal +no-bindings+)))))
              (format t "~%RawRelevants:~S" relevants)
              (setq relevants
                    (remove-if #'(lambda (relevant)
                                   (some #'(lambda (occurence)
                                             (same-operator-p-with-unify
                                              (subst-bindings (relevant-bindings relevant)
                                                                    (relevant-operator relevant))
                                              occurence))
                                         plan))
                               relevants))
              (format t "~%Relevants:~S" relevants)
              (cond ((null relevants) (fail))
                    (t (choose-bind relevant relevants
                                    (let* ((bindings (relevant-bindings relevant))
                                           (ope (subst-bindings
                                                 bindings
                                                 (relevant-operator relevant))))
                                      (lifted-backward-search
                                       operators state
                                       (regressive-action
                                        ope
                                        (subst-bindings bindings goal))
                                       (cons ope
                                             (subst-bindings bindings plan)))))))))))
        
#|
(goal-relevant-p (cadr *operators*) *goal* +no-bindings+)
(goal-relevant-p (car *operators*) *goal* +no-bindings+)
(trace =lifted-backward-search)
(lifted-backward-search *operators* *state* *goal* ())
|#