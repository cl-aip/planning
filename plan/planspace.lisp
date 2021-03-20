;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;; The Automated Planning - Theory and Practice is a textbook for planning by Malik Ghallab, 
;; Dana Nau, and Paolo Traverso, from Morgan Kaufmann. 
;; This program is a realization of algorithms that are published on the book, coded by Seiji 
;; Koide. 

;;;; Planspace Module (Section 5.2 and 5.3)
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

;;;; Plan
;;; A plan in plan space is 4-tuple of partially instantiated operators, a set of partial ordering of operation, 
;;; a binding constraint, and a set of causal-links.
;;; ----------------------------------------------------------------------------------
;;; (let ((start (start "empty(k1),empty(k2),at(r1,l3),unloaded(r1),occupied(l3),
;;;                      in(c1,p1),on(c1,pallet),top(c1,p1),top(pallet,p2)"))
;;;       (take (action "take(k1,c1,p1,l1)"
;;;                     :precond "in(c1,p1),empty(k1)"
;;;                     :effects "holding(k1,c1),~in(c1,p1)"))
;;;       (move (action "move(r1,l,l1)"
;;;                     :precond "adjacent(l,l1),at(r1,l),~occupied(l1)"
;;;                     :effects "at(r1,l1),~at(r1,l),occupied(l1),~occyoued(l)"))
;;;       (load (action "load(k1,c1,r1,l1)"
;;;                     :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
;;;                     :effects "loaded(r1,c1),empty(r1)"))
;;;       (finish (finish "in(c1,p2)")))
;;;   (plan (list start take move load finish)
;;;         (list (ordering start take) (ordering start move)
;;;               (ordering take load) (ordering move load) (ordering load finish))
;;;         +no-bindings+
;;;         (list (causal-link start take) (causal-link start move)
;;;               (causal-link take load) (causal-link move load))))
;;; -->
;;; (plan (start empty(k1) empty(k2) at(r1 l3) unloaded(r1) occupied(l3) in(c1 p1) 
;;;              on(c1 pallet) top(c1 p1) top(pallet p2))
;;;       (operator take(k1 c1 p1 l1)
;;;                 (:precond in(c1 p1) empty(k1))
;;;                 (:effects holding(k1 c1) ~in(c1 p1)))
;;;       (operator move(r1 $l l1)
;;;                 (:precond adjacent($l l1) at(r1 $l) ~occupied(l1))
;;;                 (:effects at(r1 l1) ~at(r1 $l) occupied(l1) ~occyoued($l)))
;;;       (operator load(k1 c1 r1 l1)
;;;                 (:precond at(r1 l1) holding(k1 c1) unloaded(r1))
;;;                 (:effects loaded(r1 c1) empty(r1)))
;;;       (finish in(c1 p2))
;;;       (:orderings (start << take(k1 c1 p1 l1)) (start << move(r1 $l l1))
;;;                   (take(k1 c1 p1 l1) << load(k1 c1 r1 l1)) 
;;;                   (move(r1 $l l1) << load(k1 c1 r1 l1))
;;;                   (load(k1 c1 r1 l1) << finish))
;;;       (:bindings (nil))
;;;       (:causal-links (start -> take(k1 c1 p1 l1)) (start -> move(r1 $l l1))
;;;                      (take(k1 c1 p1 l1) -> load(k1 c1 r1 l1)) 
;;;                      (move(r1 $l l1) -> load(k1 c1 r1 l1))))
;;; ----------------------------------------------------------------------------------

(defstruct (plan (:print-function print-plan)) operators orderings bindings causal-links)
(defun print-plan (x stream depth)
  "prints <plan> like ''(plan operator* (:orderings ordering*) (:bindigns binding*)
   (:causal-links causal-link*)''"
  (declare (ignore depth))
  (format stream "~<(plan~;~:1I~{ ~W~_~}~@[ (:orderings~:1I~{ ~W~:_~}) ~]~I~_~@[ (:bindings~:1I~{ ~W~:_~})~]~I~_~@[ (:causal-links~:1I~{ ~W~:_~})~]~;)~:>"
      (list (plan-operators x) (plan-orderings x) (plan-bindings x) (plan-causal-links x))))

(defun plan (operators orderings bindings causal-links)
  "reads 4-tuple and makes a plan"
  (make-plan :operators operators
             :orderings orderings
             :bindings bindings
             :causal-links causal-links))

;;;; Ordering Constraint
;;; An ordering is a pair of predecessor and successor, and it is printed as "(<predecessor> &lt;&lt; <successor>)"
;;; in this implementation.
;;; Each predecessor and successor is a partially instantiated operator called <action> here and after.
;;; A set of orderings makes a partial ordering constraint of actions as a whole.

(defstruct (ordering (:print-function print-ordering)) predecessor successor)
(defun print-ordering (x stream depth)
  "prints an ordering like ''(<predecessor> &lt;&lt; <successor>)''"
  (declare (ignore depth))
  (format stream "(~S << ~S)" (action-name (ordering-predecessor x)) (action-name (ordering-successor x))))

(defun ordering-equal-p (ordering1 ordering2)
  "returns true if <ordergin1> and <ordering2> is equal."
  (and (operator-equal-p (ordering-predecessor ordering1) (ordering-predecessor ordering2))
       (operator-equal-p (ordering-successor   ordering1) (ordering-successor   ordering2))))

(defun ordering (predecessor &optional successor)
  "makes an ordering and returns it. Note that two parameters should be a partially instantiated operation."
  (make-ordering :predecessor predecessor :successor successor))

(cl:defmethod subst-bindings (bindings (x ordering))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-ordering :predecessor (subst-bindings bindings (ordering-predecessor x))
                          :successor (subst-bindings bindings (ordering-successor x))))))

;;;
;;;; Ordering Constraint Satisfaction
;;;
;;; If an indirect ordering is entailed from a set of orderings by transitive nature of ordering, 
;;; it is called <satisfied>.
;;; ----------------------------------------------------------------------------------
;;; (setq orderings
;;;       (let ((start (start "empty(k1),empty(k2),at(r1,l3),unloaded(r1),occupied(l3),
;;;                            in(c1,p1),on(c1,pallet),top(c1,p1),top(pallet,p2)"))
;;;             (take (action "take(k1,c1,p1,l1)" :precond "in(c1,p1),empty(k1)" 
;;;                                               :effects "holding(k1,c1),~in(c1,p1)"))
;;;             (move (action "move(r1,l3,l1)"
;;;                           :precond "adjacent(l3,l1),at(r1,l),~occupied(l1)"
;;;                           :effects "at(r1,l1),~at(r1,l3),occupied(l1),~occyoued(l3)"))
;;;             (load (action "load(k1,c1,r1,l1)"
;;;                           :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
;;;                           :effects "loaded(r1,c1),empty(r1)"))
;;;             (finish (finish "in(c1,p2)")))
;;;         (list (ordering start take) (ordering start move)
;;;               (ordering take load) (ordering move load) (ordering load finish))))
;;; -->
;;; ((start << take(k1 c1 p1 l1)) (start << move(r1 l3 l1))
;;;  (take(k1 c1 p1 l1) << load(k1 c1 r1 l1))
;;;  (move(r1 l3 l1) << load(k1 c1 r1 l1)) (load(k1 c1 r1 l1) << finish))
;;;
;;; (ordering-satisfied-p
;;;   (ordering (start "empty(k1),empty(k2),at(r1,l3),unloaded(r1),occupied(l3),
;;;                     in(c1,p1),on(c1,pallet),top(c1,p1),top(pallet,p2)")
;;;             (finish "in(c1,p2)"))
;;;   orderings)
;;; --> true
;;; ----------------------------------------------------------------------------------

(defun ordering-satisfied-p (ordering orderings)
  "returns true if <ordering> is satisfied by <orderings>. Note that <orderings> must be consistent and asyclic."
  (let ((successor (ordering-successor ordering)))
    (labels ((search-successor-upwardly (pre)
               (cond ((operator-equal-p pre successor) t) ; found
                     (t (let ((o (find pre orderings :key #'ordering-predecessor :test #'operator-equal-p)))
                          (cond ((null o) nil)                                 ; missing
                                (t (search-successor-upwardly (ordering-successor o)))))))))
      (search-successor-upwardly (ordering-predecessor ordering)))))

;;;
;;; If an ordering does not contradict to a set of orderings, namely inverse ordering is not entailed, 
;;; it is called <consistent>.
;;; A consistent ordering can be added into the orderings, if you would like.
;;; ----------------------------------------------------------------------------------
;;; (consistent-ordering-p
;;;   (ordering (action "load(k1,c1,r1,l1)"
;;;                     :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
;;;                     :effects "loaded(r1,c1),empty(r1)")
;;;             (action "move(r1,l1,l2)" 
;;;                     :precond "adjacent(l1,l2),at(r1,l1),~occupied(l2)"
;;;                     :effects "at(r1,l2),~at(r1,l1),occupied(l2),~occyoued(l1)"))
;;;   orderings)
;;; --> true
;;; (consistent-ordering-p
;;;   (ordering (action "load(k1,c1,r1,l1)"
;;;                     :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
;;;                     :effects "loaded(r1,c1),empty(r1)")
;;;             (action "move(r1,l3,l1)"
;;;                     :precond "adjacent(l3,l1),at(r1,l),~occupied(l1)"
;;;                     :effects "at(r1,l1),~at(r1,l3),occupied(l1),~occyoued(l3)"))
;;;   orderings)
;;; --> false
;;; ----------------------------------------------------------------------------------

(defun consistent-ordering-p (ordering orderings)
  "returns true if <ordering> is consistent to <orderings>."
  (not (ordering-satisfied-p (ordering (ordering-successor ordering) (ordering-predecessor ordering))
                             orderings)))

;;;
;;; Sometime we need to retrieve earliest predecessors in orderings

(defun earliest-predecessors-in (orderings &key (test #'equalp))
  "returns all predecessors that do not appear as successor in <orderings>.
   The default of <test> is equalp."
  (set-difference (mapcar #'ordering-predecessor orderings)
                  (mapcar #'ordering-successor orderings)
                  :test test))

#|
(setq orderings
      (let ((start (start "empty(k1),empty(k2),at(r1,l3),unloaded(r1),occupied(l3),in(c1,p1),on(c1,pallet),
                           top(c1,p1),top(pallet,p2)"))
            (take (action "take(k1,c1,p1,l1)" :precond "in(c1,p1),empty(k1)" :effects "holding(k1,c1),~in(c1,p1)"))
            (move (action "move(r1,l3,l1)"
                          :precond "adjacent(l3,l1),at(r1,l),~occupied(l1)"
                          :effects "at(r1,l1),~at(r1,l3),occupied(l1),~occyoued(l3)"))
            (load (action "load(k1,c1,r1,l1)"
                          :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
                          :effects "loaded(r1,c1),empty(r1)"))
            (finish (finish "in(c1,p2)")))
        (list (ordering start take) (ordering start move)
              (ordering take load) (ordering move load) (ordering load finish))))
(ordering-satisfied-p (ordering (action "take(k1,c1,p1,l1)" :precond "in(c1,p1),empty(k1)" :effects "holding(k1,c1),~in(c1,p1)")
                                (action "load(k1,c1,r1,l1)"
                                        :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
                                        :effects "loaded(r1,c1),empty(r1)"))
                      orderings)
(consistent-ordering-p (ordering (action "move(r1,l1,l2)" 
                                         :precond "adjacent(l1,l2),at(r1,l1),~occupied(l2)"
                                         :effects "at(r1,l2),~at(r1,l1),occupied(l2),~occyoued(l1)")
                                 (action "move(r1,l3,l1)"
                                         :precond "adjacent(l3,l1),at(r1,l),~occupied(l1)"
                                         :effects "at(r1,l1),~at(r1,l3),occupied(l1),~occyoued(l3)"))
                       orderings)
(consistent-ordering-p (ordering (action "load(k1,c1,r1,l1)"
                                         :precond "at(r1,l1),holding(k1,c1),unloaded(r1)"
                                         :effects "loaded(r1,c1),empty(r1)")
                                 (action "move(r1,l1,l2)" 
                                         :precond "adjacent(l1,l2),at(r1,l1),~occupied(l2)"
                                         :effects "at(r1,l2),~at(r1,l1),occupied(l2),~occyoued(l1)"))
                      orderings)
|#

;;;; Causal Link
;;; A causal link is a pair of producer and consumer, and it is printed as "(<producer> -&gt; <consumer>)" in this implementation.
(defstruct (causal-link (:print-function print-causal-link)) producer consumer)
(defun print-causal-link (x stream depth)
  "prints a <causal-link> like ''(<producer> -&gt; <consumer>)''."
  (declare (ignore depth))
  (format stream "(~S -> ~S)" (action-name (causal-link-producer x)) (action-name (causal-link-consumer x))))

(defun causal-link (producer consumer)
  "makes a causal-link from <producer> and <consumer> and returns it."
  (make-causal-link :producer producer :consumer consumer))

(defun causal-link-proposition (link)
  "returns propositions of this <link>, namely an intersection of producer's effects and 
   consumer's precond. Note that this returns a list of propositional atoms."
  (intersection (action-effects (causal-link-producer link))
                (action-precond (causal-link-consumer link))
                :test #'statevar-equalp-with-unify))

(defun find-link-related-to (proposition links)
  "returns a link in <links> that has <proposition> as causal link proposition."
  (find-if #'(lambda (link)
               (let ((pro (causal-link-proposition link)))
                 (assert (length=1 pro))
                 (statevar-equalp (first pro) proposition)))
           links))


;;;; Start and Finish
;;; In plan state, start operation that has an empty precond and non-empty effects that represent 
;;; a given initail state is made, and it is used in plan state space instead of a initial state in state space.
;;; Similarly, finish operation that has an empty effects and non-empty precond that represent 
;;; a given goal is made, and used in plan state space instead of a goal in state space.

(defvar *start* () "holds a start operation.")

(defvar *finish* () "holds a finish operation.")

(defun start (initial)
  "makes a start operation and store it into *start*. This function returns the start operation."
  (setq *start* (action (make-action-name :symbol 'start) :effects initial)))

(defun finish (goal)
  "makes a finish operation and store it into *finish*. This function returns the finish operation."
  (setq *finish* (action (make-action-name :symbol 'finish) :precond goal)))

(defun make-minimal-plan (initial goal)
  "This function is used for create a initial plan space that includes the return value of 
   this function, that is a node composed of start operator and finish operator. 
   The start operator contains only <initial> as operator effects, and the finish operator 
   contains only <goal> as operator precond." 
  (let ((start (start initial))
        (finish (finish goal)))
    (make-plan :operators `(,start ,finish)
               :orderings `(,(ordering start finish))
               :bindings +no-bindings+
               :causal-links '())))

#|
Figure 5.2 and 5.4
(let ((start (start "empty(k1),empty(k2),at(r1,l3),unloaded(r1),occupied(l3),in(c1,p1),on(c1,pallet),
                     top(c1,p1),top(pallet,p2)"))
      (take (action "take(k1,c1,p1,l1)" :precond "in(c1,p1),empty(k1)" :effects "holding(k1,c1),~in(c1,p1)"))
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
              (causal-link take load) (causal-link move load))))
|#

