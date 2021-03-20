;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;; The Automated Planning - Theory and Practice is a textbook for planning by Malik Ghallab, 
;; Dana Nau, and Paolo Traverso, from Morgan Kaufmann. 
;; This program is a realization of algorithms that are published on the book, coded by Seiji 
;; Koide. 

;;;; PSP Module (Figure 5.6)
;;; All rights on these programs are reserved by Seiji Koide. 
;;; 
;;; Copyrights (c), 2008, Seiji Koide

(cl:defpackage :plan
  (:shadowing-import-from :fol compound-unify compound-unify?)
  (:use common-lisp :utils :fol :callcc)
  (:export 
   )
  )

(in-package :plan)

;;;; PSP (Figure 5.6)
;;; PSP is an acronym of Plan Space Planning.
;;; PSP incrementally refines an incomplete plan starting at a trivial simple plan 
;;; (<start> &lt;&lt; <finish>), in which the <start> action includes a given initial state 
;;; in effects, and the <finish> action includes a given goal in precond. This algorithm 
;;; determistically choose a <flaw> in plan and underterministically choose a <resolver> 
;;; of the <flaw> chosen, then refines <plan> using the <resolver> chosen.

(=defun PSP (plan)
        "retrieves flaws from <plan>, picks one flaw, creates a resolver for flaw, 
         underministically choose one resolver, then recursively calls PSP with refined 
         <plan> by the resolver. If there is no resolver, the backtrack occures and another 
         resolver is chosen. If there is no flaw in <plan>, it means <plan> is complete, so 
         returns <plan>."
        (format t "~%Operators:~S" (plan-operators plan))
        (format t "~%Orderings:~S" (plan-orderings plan))
        (format t "~%Causal Links:~S" (plan-causal-links plan))
        (format t "~%Bindings:~S" (plan-bindings plan))
        (let ((flaws (union (collect-open-goals plan) (collect-threats plan)))
              (resolvers ()))
          (format t "~%Flaws:~S" flaws)
          (if (null flaws) (return-from =PSP (=values plan))
            (loop for flaw in flaws
                do (setq resolvers (collect-resolvers flaw plan))
                  (setq resolvers (remove-if #'unsatisfiable-resolver-p resolvers))
                  (format t "~%Resolvers:~S~%  for flaw:~S" resolvers flaw)
                  (if (null resolvers) (fail)
                    (choose-bind resolver resolvers
                                 (format t "~%Resolver:~S chosen!" resolver)
                                 (when (and (consp resolver)
                                            (typep (first resolver) 'causal-link)
                                            (not (consistent-bindings-in-plan-p (third resolver) plan)))
                                   (fail))
                                 (PSP (refine flaw resolver plan))))))))

;;;; Flaws
;;; Flaws are a union set of <open goal>s and <threat>s in plan.

(defun closer-flaw-up-to (operator proposition1 proposition2 links)
  "returns true if <proposition1> is closer or not far than <link2> to <operation> in <links>."
  (%closer-flaw-up-to operator
                      (find-link-related-to proposition1 links)
                      (find-link-related-to proposition2 links)
                      links))
(defun %closer-flaw-up-to (operator link1 link2 links)
  "returns true if causal-link <link1> is closer or not far than <link2> to <operation> <links>."
  (cond ((null link1) nil) ; no effect for sorting
        ((null link2) nil) ; no effect for sorting
        ((operator-equal-p operator (causal-link-producer link1)) t)
        ((operator-equal-p operator (causal-link-producer link2)) nil)
        (t (%closer-flaw-up-to operator
                               (find (causal-link-consumer link1) links
                                     :key #'causal-link-producer :test #'operator-equal-p)
                               (find (causal-link-consumer link2) links
                                     :key #'causal-link-producer :test #'operator-equal-p)
                               links))))

;;;; Open Goals
;;; An atom in operator precond that appears in <causal-link-proposition>s in plan is 
;;; called <supported>. It means such an atom holds if the <causal-link-producer> action 
;;; is established. Any <unsupported> atom in operator preconds in plan is called <open>.
;;; <Open> atoms in operator preconds in plan are called <open goals>.

(defun collect-open-goals (plan)
  "collect unsupported atoms in precond of every operator in <plan> and 
   returns a set of them."
  (let ((causal-link-propositions
         (mappend #'causal-link-proposition (plan-causal-links plan))))
    (format t "~%Causal-link-propositions:~S" causal-link-propositions)
    (loop for action in (plan-operators plan) with result = ()
        when (action-precond action)
        do (loop for st in (action-precond action)
               unless (member st causal-link-propositions :test #'statevar-equalp)
               do (pushnew st result :test #'statevar-equalp))
        finally (return (reverse result)))))

(defun find-consumer-action-related-to (flaw plan)
  "finds an action in <plan> of which precond includes <flaw> and returns it.
   This function is used in <collect-resolvers> in order to find an action 
   that resolves <flaw>."
  (find-if #'(lambda (action)
               (member flaw (action-precond action) :test #'statevar-equalp))
           (plan-operators plan)))

(defun find-effect-related-to (flaw action)
  "finds an effect in effects of <action> that is unifiable to <flaw> and returns it.
   This function is used in <collect-resolvers> in order to make an action resolvers
   to <flaw>."
  (find flaw (action-effects action) :test #'statevar-equalp-with-unify))

;;;; Threats
;;; A threat is a special action that possiblly holds special effects such as
;;;  * a threat has a negative effect that is possiblly inconsistent with a proposition of some causal-link in plan, and
;;;  * the threat may interleave the producer and consumer of the above causal-link in orderings in plan, and
;;;  * a binding between the negative effect of the threat and the proposition of the causal-link are consistent with bindings in plan.
;;; For example, ''move(<r>,<l>,<m>)'' where <r> is a robot, <l> is a location at which <r> is located, 
;;; and <m> is a destination of moving, may be a threat for a causal link ''(move(r1,<n>,l1) -&gt; load(k1,c1,r1,l1)'', 
;;; because ''move(<r>,<l>,<m>)'' possiblly beats the effect ''at(r1,l1)'' of the movement with 
;;; a binding ''<n>/l1'' if it interlieves both actions of the causal link.

(defun threat-action-p (action link plan)
  "returns true if <action> is a threat against <link> in <plan>."
  (and (inconsistent-effects-p (remove-if #'statevar-val (action-effects action)) ; negative precond
                               (causal-link-proposition link))
       (consistent-ordering-p (ordering (causal-link-producer link) action)
                              (plan-orderings plan))
       (consistent-ordering-p (ordering action (causal-link-consumer link))
                              (plan-orderings plan))
       (consistent-unifiable-p (causal-link-proposition link)                     ; positive proposition
                               (remove-if #'statevar-val (action-effects action)) ; negative precond
                               (plan-bindings plan))))

(defun inconsistent-effects-p (negative-effects proposition)
  "returns true if <negative-effects> and positive <proposition> unifiablly intersect 
   with ignoring the truth values."
  (intersection negative-effects (remove-if-not #'statevar-val proposition)
                :test #'pseudo-statevar-equalp-with-unify))

(defun consistent-unifiable-p (proposition negative-precond plan-bindings)
  "computes a binding between positive <proposition> and <negative-precond>, 
   and returns it if the possible binding is consistent to <plan-bindings>."
  (setq proposition (remove-if-not #'statevar-val proposition)) ; positives
  (let ((bindings-list (list +no-bindings+)))
    (loop for svar+ in proposition
        do (setq bindings-list
                 (mappend #'(lambda (bindings)
                              (opposite-statevar-unify svar+ negative-precond bindings))
                          bindings-list)))
    (cond ((null bindings-list) nil)
          ((length=1 bindings-list)
           (consistent-bindings-p (first bindings-list) plan-bindings))
          (t (error "Not Yet!")))))

(defun compute-consistent-bindings (state1 state2 bindings)
  (cond (state2
         (loop for statevar in state1 with bindings-list = (list bindings)
             do (setq bindings-list
                      (mappend #'(lambda (bindings) (statevar-unify statevar state2 bindings))
                               bindings-list))
             finally (return bindings-list)))
        (t bindings)))

#|
(compute-consistent-bindings (state "{at(r,l)}") (state "{at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{~at(r,l)}") (state "{~at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l)}") (state "{at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l)}") (state "{~at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l)}") (state "{at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l),load(k1,c1,r1,l1)}") (state "{at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{~at(r,l),load(k1,c1,r1,l1)}") (state "{~at(r1,l1),at(r2,l2),~load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l),load(k1,c1,r1,l1)}") (state "{at(r1,l1),at(r2,l2),~load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l),load(k1,c1,r1,l1)}") (state "{~at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
(compute-consistent-bindings (state "{at(r,l),load(k1,c1,r1,l1)}") (state "{at(r1,l1),at(r2,l2),load(k1,c1,r1,l1)}") +no-bindings+)
|#

(defun consistent-bindings-p (bindings1 bindings2)
  "returns true if <bindings1> and <bindings2> is not inconsistent."
  (not (inconsistent-bindings-p bindings1 bindings2)))

(defun inconsistent-bindings-p (bindings1 bindings2)
  "returns true if <bindings1> or <bindings2> includes some binding that results different 
   substitution when <bindings1> and <bindings2> are merged."
  (let ((bindings (union bindings1 bindings2 :test #'equalp)))
    (or (some #'(lambda (binding) (not (equalp (lookup (binding-var binding) bindings1)
                                               (lookup (binding-var binding) bindings))))
                bindings1)
        (some #'(lambda (binding) (not (equalp (lookup (binding-var binding) bindings2)
                                               (lookup (binding-var binding) bindings))))
                bindings2))))

(defun consistent-bindings-in-plan-p (bindings plan)
  "checks whether <bindings> causes inconsistent effects of operators in <plan>."
  (notany #'(lambda (operator) 
              (unsatisfiable-state-p (subst-bindings bindings (operator-effects operator))))
          (plan-operators plan)))

#|
(consistent-unifiable-p (state "{at(r1,x),at(r2,y)}") (state "{~at(r1,l),~at(r2,m)}") '(($l . l1) ($m . l2)))
(consistent-unifiable-p (state "{at(r1,l),at(r2,x)}") (state "{~at(r1,l),~at(r2,m)}") '(($l . l1) ($m . l2)))
(consistent-unifiable-p (state "{at(r1,x),at(r2,l)}") (state "{~at(r1,l),~at(r2,m)}") '(($l . l1) ($m . l2)))
(consistent-unifiable-p (state "{at(r1,x),at(r2,y)}") (state "{~at(r1,l),~at(r2,l)}") '(($l . l1) ($m . l2)))
(consistent-unifiable-p (list (statevar "at(r1,l)")) (state "{adjacent(l,m),~at(r1,m)}") '(($l . l1) ($m . l2)))
|#
#|
(defun inconsistent-binding-p (var bindings1 bindings2)
  "returns true if <bindings1> and <bindings2> results different values by s
   ubstitution on <var>."
  (cond ((variable? var)
         (let ((val1 (subst-bindings bindings1 var))
               (val2 (subst-bindings bindings2 var)))
           (format t "~%Val1=~S Val2=~S" val1 val2)
           (and (not (equalp val1 val2))
                (not (eq var val1))
                (not (eq var val2)))))
        (t (error "Bug?"))))

(defun consistent-binding-p (var bindings1 bindings2)
  "returns true if <bindings1> and <bindings2> results a same value by substitution 
   on <var>, or if there is no substition in <bindings1> or <bindings2>."
  (cond ((variable? var)
         (let ((val1 (subst-bindings bindings1 var))
               (val2 (subst-bindings bindings2 var)))
           (format t "~%Val1=~S Val2=~S" val1 val2)
           (or (equalp val1 val2)  ; same bindings
               (eq var val1)       ; no effective bindings in bindings1
               (eq var val2))))    ; no effective bindings in bindings2
        (t (error "Bug?"))))
|#
#|
Figure 5.2
(in-package :plan)
(setq plan
      (let ((start (start "empty(k1),empty(k2),at(r1,l3),unloaded(r1),occupied(l3),
                           in(c1,p1),on(c1,pallet),
                           top(c1,p1),top(pallet,p2)"))
            (take (action "take(k1,c1,p1,l1)"
                          :precond "in(c1,p1),empty(k1)"
                          :effects "holding(k1,c1),~in(c1,p1)"))
            (move (action "move(r1,l,l1)"
                           :precond "adjacent(l,l1),at(r1,l),~occupied(l1)"
                           :effects "at(r1,l1),~at(r1,l),occupied(l1),~occyoued(l)"))
            (load (action "load(k1,c1,r1,l1)"
                           :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
                           :effects "loaded(r1,c1),empty(r1)"))
            (finish (finish "in(c1,p2)")))
        (plan (list start take move load finish)
              (list (ordering start take) (ordering start move)
                    (ordering take load) (ordering move load) (ordering load finish))
              +no-bindings+
              (list (causal-link start take) (causal-link start move)
                    (causal-link take load) (causal-link move load)))))
(defoperator "move(r,l,m)"
    "robot <r> moves from location <l> to an adjacent location <m>"
  :precond "adjacent(l,m),at(r,l),~occupied(m)"
  :effects "at(r,m),occupied(m),~occupied(l),~at(r,l)")
(threat-action-p (first *operators*)
          (first (last (plan-causal-links plan)))
                 plan)
|#

;;;
;;; If you like, you can create an instance of <threat>, which consists of 
;;; <threat-action> and <threat-link>.
;;;

(defstruct threat action link)

(defun collect-threats (plan)
  "collects all threat actions in <plan> for every causal links in <plan>, 
   then, makes threats from the collection of actions with the related link."
  (loop for action in (plan-operators plan)
      append (loop for link in (plan-causal-links plan)
                 when (threat-action-p action link plan) 
                 collect (make-threat :action action :link link))))

;;;; Resolvers
;;; There are several kinds of resolvers for flaws according to the type of flaw. In the following sentences, 
;;; ''consistent'' means consistent to orderings or bindings in plan. 
;;; As resolvers for threats,
;;;  * promotion: a consistent ordering composed of flaw's threat action and a producer of flaw's threat link
;;;  * demotion: a consistent ordering composed of flaw's threat action and a consumer of flaw's threat link
;;;  * separation: a consistent binding that lets a possively unifiable pair of a negative effect and a link proposition nonunifiable.
;;; As resolvers for open goals,
;;;  * a causal link in plan that provides the open goal as an effect of producer of the link
;;;  * a new operator in system that does not appear in plan, but it provides the open goal as an effect of the operator
;;; Note that a new operator brings two new orderings ''(start &lt;&lt; <new operator>)''
;;; and ''(<new operator> &lt;&lt; <action that provides open goal>)'', 
;;; a new causal-link ''(<new operator> -&gt; <action that provides open goal>)'', and 
;;; the new bindings between both.

(defun collect-resolvers (flaw plan)
  "collects all resolvers for <flaw> according to the type of flaw, threat or open goal, 
   and returns them."
  (etypecase flaw
    (threat (let* ((action (threat-action flaw))
                   (link (threat-link flaw))
                   (promotion (ordering action (causal-link-producer link)))
                   (demotion (ordering (causal-link-consumer link) action))
                   (separation ()))
              (declare (ignore separation))
              (format t "~%Promotion:~S" promotion)
              (format t "~%Demotion:~S" demotion)
              (append (when (and (consistent-ordering-p promotion (plan-orderings plan)))
                        (list promotion))
                      (when (and (consistent-ordering-p demotion (plan-orderings plan)))
                        (list demotion))
                      ;; separation here
                      )))
    (statevar (or (retrieve-causal-link-resolvers flaw (plan-causal-links plan) (plan-orderings plan))
                  (retrieve-action-resolvers flaw (append *operators* (list *start*)) plan)))))

(defun retrieve-causal-link-resolvers (flaw causal-links plan-orderings)
  "finds some pair of producer and consumer of a link from <causal-links> such that 
   the producer includes an effect unifiable to <flaw> and the pair as ordering is 
   new and consistent to <plan-orderings>. This function returns a list of 
   the link, the ordering, and new bindings as a result of unification between 
   <flaw> and the unifiable effect."
  (loop for link in causal-links with ordering and bindings = +no-bindings+
      when (and (unifiable-link-p-to flaw link bindings)
                (consistent-ordering-p
                 (setq ordering
                       (ordering (causal-link-producer link) (causal-link-consumer link)))
                 plan-orderings)
                (not (ordering-satisfied-p ordering plan-orderings)))
      collect (list link ordering
                    (or (loop for effect in (action-effects (causal-link-producer link))
                              with result
                            when (setq result (unify flaw effect))
                            return result)
                        +no-bindings+))))

(defun unifiable-link-p-to (flaw link bindings)
  "If <flaw> is unifiable to positive effects of producer of <link>, and 
   <flaw> is unifiable to positive precond of consumer of <link>, and
   <flaw> is not unified to negative effects of consumer of <link>, then
   the <link> may be a resolver of <flaw>."
  (and
   ;; match to positive effects in producer effects
   (setq bindings 
         (statevar-unify flaw (action-effects (causal-link-producer link))
                         bindings))
   ;; match to positive precond in consumer precond
   (setq bindings
         (statevar-unify flaw (action-precond (causal-link-consumer link))
                         bindings))
   ;; do not match to negative effects in consumer effects
   (not (opposite-statevar-unify flaw (action-effects (causal-link-consumer link))
                                bindings))))

(defun retrieve-action-resolvers (flaw operators plan)
  "finds some operator in <operators> of which effects include an effect that is unifiable 
   to <flaw>. This function returns a list of the resolving action, an ordering such that 
   the action to successive action in <plan> through the relation of <flaw>, and bindings 
   obtained by unification between the effect and <flaw>."
  (loop for operator in operators with effect and bindings
      when (setq effect (find flaw (operator-effects operator) 
                              :test #'statevar-equalp-with-unify))
      collect (progn
                (format t "~%New Resolver:~S for ~S" operator flaw)
                (setq bindings (or (unify effect flaw) +no-bindings+))  ; got substitution for action
                (let ((action (subst-bindings bindings operator)))
                  (multiple-value-setq (action bindings) (rename-variables action))
                  (list action
                        (ordering action
                                  (subst-bindings bindings
                                                  (find-consumer-action-related-to flaw plan)))
                        bindings)))))

(defun unsatisfiable-resolver-p (resolver)
  "If <resolver> is an action and its effects is unsatisfiable such as holding ''A ^ ~A'', returns true."
  (etypecase resolver
    ;; for threats 
    (ordering nil)
    ;; for open goals
    (cons (typecase (first resolver)
            ;; from causal-link
            (causal-link nil)
            ;; new operator
            (operator (let ((action (first resolver)))
                        (unsatisfiable-state-p (action-effects action))))
            (otherwise (error "Not Yet!"))))))

;;;; Refine
;;; If we have a resolver, we can apply it to resolve the flaw. For a threat, we apply 
;;; a promotion, or a demotion, or a separation. For an open goal, we do an action to 
;;; meet the goal (precond). In this implementation, any redundant ordering in plan orderings is 
;;; removed when a new ordering is added. 

(defun refine (flaw resolver plan)
  (etypecase resolver
    ;; for threats 
    (ordering (format t "~%Refining with flaw:~S ~%resolver:~S" flaw resolver)
              (multiple-value-bind (predecessor successor)
                  (compute-safety-ordering (ordering-predecessor resolver) (ordering-successor resolver) plan)
                (format t "~%Safty pair:~%~S to ~%~S" predecessor successor)
                (add-ordering (ordering predecessor successor) plan)
                ))
    ;; for open goals
    (cons (typecase (first resolver)
            ;; from causal-link
            (causal-link (let ((link (first resolver))
                               (ordering (second resolver))
                               (bindings (third resolver)))
                           (format t "~%Refining with ~%  causal-link:~S~%  ordering:~S~%  bindings:~S"
                             link ordering bindings)
                           (add-causal-link link plan)
                           (add-ordering ordering plan)
                           (add-bindings bindings plan)))
            ;; new operator
            (operator (let ((action (first resolver))
                            (ordering (second resolver))
                            (bindings (third resolver)))
                        (format t "~%Refining with ~%  action:~S~%  ordering:~S~%  bindings:~S"
                          action ordering bindings)
                        (when (consistent-ordering-p ordering (plan-orderings plan))
                          (assert (equalp action (ordering-predecessor ordering)))
                          (add-bindings bindings plan)   ; this is 1st.
                          (add-action action plan)
                          (when (not (operator-equal-p *start* action))
                            (pushnew (ordering *start* action) (plan-orderings plan)))
                          (add-ordering ordering plan)
                          (add-causal-link
                           (causal-link action (ordering-successor ordering)) plan))))
;;;            (otherwise (binding-constraint-manager))
            )))
  plan)

(defun compute-safety-ordering (predecessor successor plan)
  ;(format t "~%~S ~S" predecessor successor)
  (let ((pre-causal-link (find predecessor (plan-causal-links plan)
                               :key #'causal-link-producer :test #'operator-equal-p))
        (suc-causal-link (find successor (plan-causal-links plan)
                               :key #'causal-link-consumer :test #'operator-equal-p)))
    ;(format t "~%~S ~S" pre-causal-link suc-causal-link)
    (cond ((and pre-causal-link (threat-action-p successor pre-causal-link plan))
           (compute-safety-ordering (causal-link-consumer pre-causal-link) successor plan))
          ((and suc-causal-link (threat-action-p predecessor suc-causal-link plan))
           (compute-safety-ordering predecessor (causal-link-producer suc-causal-link) plan))
          (t (values predecessor successor)))))

(defun add-action (action plan)
  "adds <action> into operators in <plan>."
  (unless (member action (plan-operators plan) :test #'operator-equal-p)
    (setf (plan-operators plan)
      (append (plan-operators plan) (list action)))))   ; resembling width first search

(defun add-ordering (ordering plan)
  "adds <ordering> into orderings in <plan>, then removes redundants in orderings, 
   and returns non-redundant orderings. Note that this addition must not involve 
   inconsistency."
  (let ((orderings (plan-orderings plan)))
    (unless (member ordering orderings :test #'ordering-equal-p)
      (setq orderings (append orderings (list ordering))))   ; resembling width first search
    (setf (plan-orderings plan) (remove-redundant-orderings orderings))))

(defun remove-redundant-orderings (orderings)
  "This function picks up every ordering in <orderings>, and if it is entailed the other 
   orderings, then remove it, finally returns non-redundant set of orderings."
  (%remove-redundant-orderings 0 orderings))
(defun %remove-redundant-orderings (pos orderings)
  (let ((orderings-1 ()))
    (cond ((= pos (length orderings)) orderings)
          ((ordering-satisfied-p (elt orderings pos)
                                 (setq orderings-1 
                                       (append (subseq orderings 0 pos)
                                               (subseq orderings (1+ pos)))))
           (%remove-redundant-orderings pos orderings-1))
          (t (%remove-redundant-orderings (1+ pos) orderings)))))

(defun add-bindings (bindings plan)
  (unless (eq bindings +no-bindings+)
    (setf (plan-orderings plan)
      (mapcar #'(lambda (ordering)
                  (ordering (subst-bindings bindings (ordering-predecessor ordering))
                            (subst-bindings bindings (ordering-successor ordering))))
        (plan-orderings plan)))
    (setf (plan-causal-links plan)
      (mapcar #'(lambda (link)
                  (causal-link (subst-bindings bindings (causal-link-producer link))
                               (subst-bindings bindings (causal-link-consumer link))))
        (plan-causal-links plan)))
    (setf (plan-operators plan)
      (mapcar #'(lambda (operator) (subst-bindings bindings operator))
        (plan-operators plan)))
    (let ((plan-bindings (plan-bindings plan)))
      (cond ((eq plan-bindings +no-bindings+)
             (setf (plan-bindings plan) bindings))
            (t (setf (plan-bindings plan)
                 (union bindings (plan-bindings plan) :test #'equalp)))))))

(defun add-causal-link (causal-link plan)
  (pushnew causal-link (plan-causal-links plan)))