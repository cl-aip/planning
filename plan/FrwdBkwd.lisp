;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;; The Automated Planning - Theory and Practice is a textbook for planning by Malik Ghallab, 
;; Dana Nau, and Paolo Traverso, from Morgan Kaufmann. 
;; This program is a realization of algorithms that are published on the book, coded by Seiji 
;; Koide. 

;;;; Forward-search and Backward-search Module (4.2 Forward Search, 4.3 Backward Search)
;;; All rights on programs are reserved by Seiji Koide. 
;;; 
;;; Copyrights (c), 2008, Seiji Koide

(cl:defpackage :plan
  (:shadowing-import-from :fol compound-unify compound-unify?)
  (:use common-lisp :utils :fol :callcc)
  (:export satisfy-p 
   )
  )

(in-package :plan)

;;;; Goal
;;; In state space planning, a goal in planning is given as a set of state variables. To set a goal, 
;;; set a set of statevars to global var *goal*. See the following example.
;;; ----------------------------------------------------------------------------------
;;; (setq *goal* (state "{at(r1,loc1),loaded(r1,c3)}"))
;;; ----------------------------------------------------------------------------------

(defvar *goal* nil "goal in a planning problem")

;;;
;;;; Forward Search (Figure 4.1)
;;;
;;; Note that forward-search finds possibly applicable actions in <operators> and instantiates 
;;; them against current <state> and choose one of applicable actions against 
;;; <state>. No action is chosen that once occured in the past state in this implementation. 
;;; It is not a complete solution for the problem of infinite loop by repeated action but simple 
;;; and easy to avoid unterminate computation. 
;;; To plan in forward-search, see the following example of Figure 2.3.
;;; ----------------------------------------------------------------------------------
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
 (setq *goal* (state "{at(r1,loc1),loaded(r1,c3)}"))
 (forward-search *operators* *state* *goal* ())
 -> (move(r1 loc2 loc1) load(crane1 loc1 c3 r1))
|#
;;; ----------------------------------------------------------------------------------
;;; 
;;; To implement the undeterministic choice of actions and backtracking in search, the continuable 
;;; function that provides the functionality of continuation in lisp is used. See callcc module in 
;;; detail.

(=defun forward-search (operators state goal plan)
        "This program searches <state> that satisfies <goal>, and returns an 
         accumulated sequence of actions or <plan> that achieves <goal>. 
         Starting at initial <state>, finding actions that are applicable to 
         <state>, and this continuable function nondeterministically chooses 
         one of applicable actions, then progresses <state> with the application 
         of the action, and recursively calls with new <state> and partial <plan>.
         Here, <state> is a set of ground statevars but <goal> may include variables. 
         If there is no applicable action, then the search is failed and the program 
         control backtracks up to the next choice of applicable actions. 
         Exactly, ''forward-search'' is a macro name and ''=forward-search'' is 
         actually a function name. Both together pretends to support the continuation 
         like Scheme. See callcc module in detail."
        (if (satisfy-p state goal) (=values (reverse plan))
          (let ((applicable
                 (remove-if-not #'(lambda (a) (applicable-action-p a state))
                                (mappend #'(lambda (o)
                                             (operator-unify-for-progression
                                                o state +no-bindings+))
                                         operators))))
            (setq applicable (remove-action-occured applicable plan))
            (if (null applicable) (fail)
              (choose-bind action applicable
                           (format t "~&Action taken ~S" (action-name action))
                           (forward-search operators
                                           (progress-action action state)
                                           goal 
                                           (cons action plan)))))))

;;;; Satisfy Goal
;;;
;;; When there is a substitution such that every positive literal of <goal> is in <state>, 
;;; and no negative literals in <goal> match positive <state>, 
;;; (and no positive literals in <goal> match negative <state>,) we say that <state> satisfies 
;;; <goal>.
;;;

(defun satisfy-p (state goal)
  "tests <state> satisfies <goal>, and returns unifiable bindings if so, 
   otherwise returns false. Note that <goal> may include variables any 
   time, <state> does not include any variables in forward search but may 
   include in backward search."
  (let ((bindings +no-bindings+)
        (positive-goal (remove-if-not #'statevar-val goal))
        (negative-goal (remove-if     #'statevar-val goal))
        (positive-state (remove-if-not #'statevar-val state))
        (negative-state (remove-if     #'statevar-val state)))
    (flet ((satisfy-p-with-bindings-accumulation (gl st)
             ;; if unifiable updates bindings, otherwise no effects and returns nil
             (let ((result (compound-unify gl st bindings)))
               (unless (equal result +fail+)
                 (setq bindings result)))))
      (when (and (subsetp positive-goal positive-state
                          :test #'satisfy-p-with-bindings-accumulation)
                 (null (intersection negative-goal positive-state
                                     :test #'satisfy-p-with-bindings-accumulation))
                 (null (intersection positive-goal negative-state
                                     :test #'satisfy-p-with-bindings-accumulation)))
        bindings))))

;;;; Instantiation in Progression
;;;
;;; <operator-unify-for-progression> makes unification between <operator>'s precond and <state>,
;;; and then partially instantiates an <operator> with the substitutions of unification bindings.

(defun operator-unify-for-progression (operator state bindings)
  "computes multiple substitutions between <operator>'s precond and <state>, 
   then instantiates <operator> with computed substitutions. Note that this function 
   computes possible multi-substitutions for <operator> and <state>, and such 
   multi-substitutions generate possible multi-instantiations in pallarel, 
   so this function returns a set of completely instantiated <operator>s."
  (mapcar #'(lambda (bindings) (make-action-from operator bindings))
    (precond-unify (operator-precond operator) state bindings)))

;;;
;;; In unification for progression, every literal in precond of operator must be satisfied by state with 
;;; appropriate bindings. Thus, the point is a computation for bindings between precond and state.
;;; The following two functions <precond-unify> and <statevar-unify> produce multiple possibilities of
;;; substitutions. For example, "at(r,l)" in precond matches "at(r1,l1)" and "at(r2,l2)" in 
;;; state. So, this unification produces two possible substitutions (r/r1, l/l1) and (r/r2, l/l2). 
;;; Then, such multiple possibilities must be inherited to the unification of next literals in precond. 
;;; See the following example, in which a variable $m has two possible 
;;; bindings ($m . l2) and ($m . l1) in the correspondence of two binding possibilities on $l and $r.
;;; ----------------------------------------------------------------------------------
;;; Ex.
;;;   (precond-unify (state "{at(r,l)}")
;;;                  (state "{at(r1,l1),at(r2,l2),adjacent(l1,l2),adjacent(l2,l1)}")
;;;                  +no-bindings+)
;;;   -> ((($l . l1) ($r . r1)) (($l . l2) ($r . r2)))
;;;   (precond-unify (state "{at(r,l),adjacent(l,m)}")
;;;                  (state "{at(r1,l1),at(r2,l2),adjacent(l1,l2),adjacent(l2,l1)}")
;;;                  +no-bindings+)
;;;   -> ((($m . l2) ($l . l1) ($r . r1)) (($m . l1) ($l . l2) ($r . r2)))
;;; ----------------------------------------------------------------------------------
;;;
;;; Next, suppose planning for block-building. Let a given precond be a condition of bridging two blocks 
;;; e.g., "on(b,c),on(b,d)" where "b", "c", and "d" denote blocks. Then, if we have a condition "on(b3,b1),on(b3,b2)" 
;;; in state, two set of unification bindings, (d/b2, c/b1, b/b3) or (d/b1, c/b2, b/b3) are deduced, but 
;;; (d/b1, c/b1, b/b3) and (d/b2, c/b2, b/b3) should not be deduced, because block "c" and "d" in the precond 
;;; "on(b,c),on(b,d)" denotes different objects. Namely the unification of a precond must obey the Unique Name 
;;; Assumption (UNA) with respect to one precond.
;;; ----------------------------------------------------------------------------------
;;; Ex.
;;;   (precond-unify (state "{on(b,c),on(b,d)}") (state "{on(b3,b1),on(b3,b2)}")
;;;                  +no-bindings+)
;;;   Violate UNA:$d b1 (($c . b1) ($b . b3))
;;;   Violate UNA:$d b2 (($c . b2) ($b . b3))
;;;   -> ((($d . b2) ($c . b1) ($b . b3)) (($d . b1) ($c . b2) ($b . b3)))
;;; ----------------------------------------------------------------------------------

(defun precond-unify (precond state bindings)
  "returns a list of possible new bindings between <precond> and <state>.
   Every positive <precond> must meet <state> with unification, and every 
   negative <precond> must not meet <state> with binding constraint. 
   So, positive <precond> produces possible bindings and negative <precond> 
   filters unsatisfiable bindings."
  (let ((positive-precond (remove-if-not #'statevar-val precond))
        (negative-precond (remove-if     #'statevar-val precond))
        (bindings-list (list bindings)))
    (loop for svar+ in positive-precond
        do (setq bindings-list
                 (mappend #'(lambda (bindings)
                              (statevar-unify svar+ state bindings))
                          bindings-list)))
    (setq bindings-list
          (remove-if #'(lambda (bindings)
                         (loop for svar- in negative-precond
                             when (setq bindings (opposite-statevar-unify svar- state bindings))
                             do (return t)))
                     bindings-list))))

(defun statevar-unify (statevar state bindings)
  "returns a list of possible bindings of statevar against <state>.
   This function collects all possibilities for <state>."
  (loop for st in state with new-bindings
      unless (eq (setq new-bindings (compound-unify statevar st bindings)) +fail+)
      collect new-bindings))

#|
(statevar-unify (statevar "at(r,l)") (state "{at(r1,l1),at(r2,l2)}") +no-bindings+)
|#

(defun opposite-statevar-unify (statevar state bindings)
  "returns a list of possible bindings of positive(negative) <statevar> against negative(positive) <state>.
   If there is no unifiable element in <state> with <bindings> constraint, returns false."
  (loop for st in state with new-bindings
      unless (eq (setq new-bindings (opposite-compound-unify statevar st bindings)) +fail+)
      collect new-bindings))

;;;; Progress State
;;;
;;; With <add-list> and <del-list>, a planner makes a progress of <state> in state space.
;;; Namely, a <state> is altered to the union of <add-list> and set difference (<state> - <del-list>).

(defun progress-action (action state)
  "returns the new state produced by applying action to the state."
  (progress state
            (remove-if-not #'statevar-val (action-effects action)) ; positive-effects
            (remove-if     #'statevar-val (action-effects action)) ; negative-effects
            ))

(defun progress (state add-list del-list)
  "computes a union of <add-list> and set difference (<state> - <del-list>)"
  (union (set-difference state del-list :test #'pseudo-statevar-equalp) add-list
         :test #'statevar-equalp))

(defun remove-action-occured (actions plan)
  "removes any action in <actions> such that once occured in <plan>."
  (remove-if #'(lambda (action)
                 (some #'(lambda (occurence) (same-action-p action occurence))
                       plan))
             actions))

;;;
;;;; Lifted Backward Search (Figure 4.3)
;;;
;;; In backward search, relevant operators to given <goal> are retrieved from a set of <operators>.
;;; Then, one of relevants is nondeterministically chosen and <goal> is inversely progressed (regressed) 
;;; toward initial <state>, then <goal> is updated to new subgoal with partial substitution by bindings. 
;;; <lifted-backward-search> is recursively called with the new sub-goal as <goal>. The relevant operator 
;;; retrieved is instantiated with substitution of unifier between its effects and the goal. The 
;;; instantiated operators are accumulated in recursive calls of <lifted-backward-search>, then 
;;; accumulated and instantiated action sequence or <plan> is returned when initial <state> satisfies 
;;; <goal>(instantiated sub-goal). 
;;;
;;; If you want to set breakpoint to this function, use function name < =lifted-backward-search >
;;; rather than <lifted-backward-search>.
;;; To plan in lifted-backward-search, see the following example of Figure 2.3.
;;; ----------------------------------------------------------------------------------
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
 (setq *goal* (state "{at(r1,loc1),loaded(r1,c3)}"))
 (lifted-backward-search *operators* *state* *goal* ())
 -> (move(r1 loc2 loc1) load(crane1 loc1 c3 r1))
|#
;;; ----------------------------------------------------------------------------------

(=defun lifted-backward-search (operators state goal plan)
        "<goal> may include logic variable symbols. Therefore, any operator is standardized in 
         variables, namely, renamed with respect to variables before unification to <goal>. "
        (let ((bindings ()))
          (if (setq bindings (satisfy-p state goal)) (=values (subst-bindings bindings plan))
            (let ((relevant
                   (loop for o in operators with bindings-list
                       do (setq o (rename-variables o))
                       when (setq bindings-list
                                  (operator-unify-for-regression o goal +no-bindings+))
                       append (loop for bindings in bindings-list
                                  when (goal-relevant-p o goal bindings)
                                  collect (relevant o bindings)))))
              (setq relevant (remove-relevant-occured relevant plan))
              (if (null relevant) (fail)
                (choose-bind rel relevant
                             (format t "~%Relevant chosen:~S~%  precond:~S~%  effects:~S~%~S~%Goal:~S"
                               (operator-name (relevant-operator rel))
                               (operator-precond (relevant-operator rel))
                               (operator-effects (relevant-operator rel))
                               (relevant-bindings rel)
                               goal)
                             (setq plan (cons (subst-bindings (relevant-bindings rel)
                                                              (relevant-operator rel))
                                              (subst-bindings (relevant-bindings rel) plan)))
                             (lifted-backward-search operators state 
                                                     (regression-operation rel goal) plan)))))))

;;;; Unification in Regression
;;;
;;; In unification for regression, a part of effects is unified to goal. The unified conditions 
;;; should be supported at the precond of the operator, then the precond and effects are partially 
;;; instantiated with the computed unification bindings. The un-unified conditions and the partially 
;;; instantiated precond are unioned and captured as new subgoal in regression process. Thus, the 
;;; unsatisfied fragments of goal must be instantiated or unified later in regressive planning process. 
;;;
;;; For example, for goal "at(r1,loc1),loaded(r1,c3)", unification of effects in operator load(k,l,c,r), 
;;; "empty(k),~holding(k,c),loaded(r,c),~unloaded(r)" produces bindings (r/r1, c/c3), and this 
;;; bindings instantiate the effects to "empty(k),~holding(k,c),loaded(r1,c3),~unloaded(r1)" and 
;;; instantiates the precond "belong(k,l),holding(k,c),at(r,l),unloaded(r)" to 
;;; "belong(k,l),holding(k,c3),at(r1,l),unloaded(r1)". Thus, the union of remained goal "at(r1,loc1)" and 
;;; the instantiated precond are set as subgoal.
;;; 
;;; Note that the unification is lastly done between the initial state and the last subgoal, and this last 
;;; unifier must be reflected to every actions in sequence so far or <plan>. 

(defun operator-unify-for-regression (operator goal bindings)
  "returns multiple set of bindings, of which one set is the result of possible 
   unification of <operator> to <goal> with <bindings>. At first, <operator>'s 
   effects are attempted to unify <goal> with <bindings> (and it generates a set 
   of new possible bindings), then <operator>'s precond are unified 
   with the constraint of each bindings newly generated ."
  (mappend #'(lambda (bindings)
               (partial-unify (operator-precond operator) goal bindings))
           (partial-unify (operator-effects operator) goal bindings)))

(defun partial-unify (cond goal bindings)
  "returns a list of possible bindings of a part of <cond> against <goal>. This function allows to match 
   a possible element in <cond> to a possible element in <goal>. Unmatched elements are remained
   in both of <cond> and <goal>. Any negative effect must not match to positive <goal>."
  (let ((positive-cond (remove-if-not #'statevar-val cond))
        (negative-cond (remove-if     #'statevar-val cond))
        (bindings-list (list bindings)))
    (loop for svar in positive-cond with result
        when (setq result
                   (mappend #'(lambda (bindings)
                                (statevar-unify svar goal bindings))
                            bindings-list))
        do (setq bindings-list result))
    (setq bindings-list
          (remove-if #'(lambda (bindings)
                         (loop for svar- in negative-cond
                             when (setq bindings (opposite-statevar-unify svar- goal bindings))
                             do (return t)))
                     bindings-list))
    (if (equal bindings-list (list +no-bindings+)) nil bindings-list)))

;;;; Relevant to Goal
;;; An operator and a set of bindings by which effects of the operator partially match to goal 
;;; is called <relevant>. In regressive planning process, the relevant 
;;; (which is a pair of operator and bindings) to goal is computed and one relevant is 
;;; undeterministically chosen.

(defstruct (relevant (:type list)) operator bindings)

(defun relevant (operator bindings)
  "makes an instance of <relevant> with <operator> and <bindings>."
  (make-relevant :operator operator :bindings bindings))

(defun goal-relevant-p (operator goal bindings) ; See p.46 and p.31
  "returns a list of bindings that operator's effects can be unified against goal.
   Note that effects and goal may include object variables.
   Any variable in effects must be different from any variables in goal."
  ;; partial-unify implies relevant condition in p.31 and p.46
  (let* ((effects (operator-effects operator))
         (bindings-list (partial-unify (intersection effects goal
                                                     :test #'statevar-equalp-with-unify)
                                       (intersection goal effects
                                                     :test #'statevar-equalp-with-unify)
                                       bindings)))
    bindings-list))

;;;; Regressive Operation
;;; In regressive operation, variables in operator must be partially instantiated, and 
;;; new subgoal must be set up.

(defun regression-operation (relevant goal)
  "computes the regression, namely instatiates relevant operation in <relevant> 
   and <goal> with bindings in <relevant>, then makes a union of the operator precond 
   and the set difference, (<goal> - <operator effects>)."
  (let ((operator (relevant-operator relevant))
        (bindings (relevant-bindings relevant)))
    (setq operator (subst-bindings bindings operator))
    (setq goal (subst-bindings bindings goal))
    (regress goal
             (operator-precond operator)
             (operator-effects operator))))

(defun regress (goal add-list del-list)
  "returns a union of <add-list> and set-difference (<goal> - <del-list>)."
  (union (set-difference goal del-list :test #'pseudo-statevar-equalp) add-list
         :test #'statevar-equalp))

(defun remove-relevant-occured (relevant plan)
  "removes similar operators that occured in <plan>. Note that this function also 
   removes operators that include variables in parameters and similar exept the variables."
  (remove-if #'(lambda (rel)
                 (some #'(lambda (o)
                           (and (eq (operator-symbol o)
                                    (operator-symbol (relevant-operator rel)))
                                (every #'(lambda (t1 t2) (or (equal t1 t2)
                                                             (variable? t1)
                                                             (variable? t2)))
                                       (operator-variables o)
                                       (operator-variables (relevant-operator rel)))))
                       plan))
             relevant))

#|
(in-package :plan)
;; Figure 2.3 (p.30)
(setq *state*
      (state
       "{attached(p1,loc1),in(c1,p1),top(c1,p1),on(c1,pallet),
         attached(p2,loc1),in(c2,p2),top(c2,p2),on(c2,pallet),
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
(setq *goal* (state "{at(r1,loc1),loaded(r1,c3)}"))
(forward-search *operators* *state* *goal* ())         ; =forward-search
(lifted-backward-search *operators* *state* *goal* ()) ; =lifted-backward-search

(operator-unify-for-regression (first *operators*) *goal* +no-bindings+)
|#