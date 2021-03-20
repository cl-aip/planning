;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;; The Automated Planning - Theory and Practice is a textbook for planning by Malik Ghallab, 
;; Dana Nau, and Paolo Traverso, from Morgan Kaufmann. 
;; This program is a realization of algorithms that are published on the book, coded by Seiji 
;; Koide. 

;;;; State Space Module (Section 2.3 Classical Representation, Chapter 4 State-Space Planning)
;;; All rights on programs are reserved by Seiji Koide. However, Anyone can use and modify anyway
;;; As IS, while the programmer Seiji Koide do not take any respocibility on any results.
;;; 
;;; Copyrights (c), 2008, 2021 Seiji Koide

(cl:defpackage :plan
  #+:rdfs (:shadowing-import-from :gx typep type-of subtypep)
  (:shadowing-import-from :fol compound-unify compound-unify?)
  (:use common-lisp :utils :fol)
  (:export *state* state make-state
           statevar statevar-p defstatevar defrelation
           ground-p statevar-equalp
           make-statevar statevar-val statevar-parms statevar-symbol normalize-statevar
           positive-statevar-p unnormalize-statevar single-var-p)
  )

(in-package :plan)

;;;
;;;; State
;;;
;;; A <state> in classical planning is a set of ground atoms of a first-order language. 
;;; A state is represented in lisp as a list of literals of the first-order logic, and operated 
;;; by set-operation such as intersection, union, set-difference, etc.
;;; 

(defvar *state* () "A global var in which initial state is stored.")

;;; 
;;; An atom in first-order languages is expressed by a predicate symbol and arguments.
;;; However, an atom of state in state space is represented in functional expression as state 
;;; variable. In practice, a predicate symbol is not a function in lisp nor function symbol in logic.
;;; It just looks like functional in state space. For example, a location at which a robot is located 
;;; is expressed in infix expression like "at(r1) = l1" as string at some time point. It may changed 
;;; such as "at(r1) = l2" at next time point. Note that the expression is automatically transformed 
;;; to prefix lisp expression like "(= (at r1) l1)" using function fol:logic. See <logic> in fol module.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (logic "load(r1)=c1")  -> (= (load r1) c1)
;;;   Ex. (logic "~load(r1)=c1") -> (not (= (load r1) c1))
;;; ----------------------------------------------------------------------------------
;;; To make a state, call function <state> with infix notation as string, or prefix notation as 
;;; list. Prefix tilder in infix notation denotes a negative literal. Following three expressions 
;;; are evaluated to the same result.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (state "{at(r1)=l1,load(r1)=nil,cpos(c1)=l1,cpos(c2)=l2}")
;;;   Ex. (state "{at(r1)=l1,~load(r1),cpos(c1)=l1,cpos(c2)=l2}")
;;;   Ex. (state '((= (at r1) l1) (not (load r1)) (= (cpos c1) l1) (= (cpos c2) l2)))
;;; ----------------------------------------------------------------------------------

(defun state (exp)
  "makes and returns a list of statevar instances. The <exp> should be either a string 
   in infix notation or a list in prefix notation. A sequence of literals in infix 
   notation must be enveloped by braces."
  (if (stringp exp)
      (state (logic exp))
    (mapcar #'statevar exp)))

;;;
;;;; State Vairable
;;;
;;; A <state variable> in state space is composed of <state-variable symbol>, its 
;;; <arguments>, and its <value>.
;;; In this implementation, structure <statevar> is composed of <symbol>, <args>, and <val>.

(defstruct (statevar (:print-function print-statevar))
  symbol args val)

;;; The statevar structure is printed out as "<symbol>(<args>)" if <val> is true, 
;;; "~<symbol>(<args>)" if <val> is false, and "<symbol>(<args>)=<val>" otherwise.

(defun print-statevar (x stream depth)
  "prints statevar <x> in infix notation."
  (declare (ignore depth))
  (case (statevar-val x)
    ((t) (format stream "~S~:[~;~:*~S~]" (statevar-symbol x) (statevar-args x)))
    ((nil) (format stream "~~~S~:[~;~:*~S~]" (statevar-symbol x) (statevar-args x)))
    (otherwise (format stream "~S~:[~;~:*~S~]=~S" (statevar-symbol x) (statevar-args x)
                 (statevar-val x)))))

;;;
;;; Function <statevar> makes an instance of statevar from <exp>. See the following examples.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (statevar "rloc(r1)=l1")           -> rloc(r1)=l1
;;;   Ex. (statevar '(= (rloc r1) l1))       -> rloc(r1)=l1
;;;   Ex. (statevar "~rloc(r1)=l1")          -> ~rloc(r1 l1)
;;;   Ex. (statevar '(not (= (rloc r1) l1))) -> ~rloc(r1 l1)
;;; ----------------------------------------------------------------------------------
;;; No argument for statevar results making a constant as statevar. 
;;; ----------------------------------------------------------------------------------
;;;   Ex. > (describe (statevar "constant1()")) 
;;;       constant1 is a structure of type statevar.  It has these slots:
;;;        symbol             constant1
;;;        args               nil
;;;        val                t
;;;   Ex. > (describe (statevar "constant1")) 
;;;       constant1 is a structure of type statevar.  It has these slots:
;;;        symbol             constant1
;;;        args               nil
;;;        val                t
;;;   Ex. > (statevar-equalp (statevar "constant1()") (statevar "constant1")) -> true
;;; ----------------------------------------------------------------------------------

(defun statevar (exp)
  "makes a statevar instance. If <exp> is a string, the infix expression is converted to 
   a prefix expression and recursively called."
  (if (stringp exp) (statevar (logic exp))
    (case (op exp)
      (not (case (op (arg1 exp))
             (=                         ; (not (= x y))
              (make-statevar :symbol (op (arg1 (arg1 exp)))
                             :args (append (args (arg1 (arg1 exp))) (list (arg2 (arg1 exp))))
                             :val nil))
             (otherwise (make-statevar :symbol (op (arg1 exp)) :args (args (arg1 exp)) :val nil))))
      (= (let ((val (arg2 exp)))
           (when (eq val 'true) (setq val t))
           (when (eq val 'false) (setq val nil))
           (make-statevar :symbol (op (arg1 exp)) :args (args (arg1 exp)) :val val)))
      (otherwise (make-statevar :symbol (op exp) :args (args exp) :val t)))))

(defun negative-statevar-p (statevar)
  "returns true if <statevar> is negative."
  (null (statevar-val statevar)))

(defun positive-statevar-p (statevar)
  "returns true if <statevar> is positive."
  (statevar-val statevar))

(defun single-var-p (statevar)
  "returns true if <statevar> has only one state variable, or 
   if <statevar> has two arguments in unnormalized expression.
   See <normalize-statevar> and <unnormalize-statevar>."
  (length=1 (statevar-args (unnormalize-statevar statevar))))

;;;; Unsatisfiability of State
;;; If two statevars are inconsistent such as "on(c1,pallet)" and "~on(c1,pallet)", it is called 
;;; <unsatisfiable> condition.
;;; If <state> includes any <unsatisfiable> condition or any unsatisfiable pair of statevars, 
;;; the <state> is called <unsatisfiable>.

(defun unsatisfiable-state-p (state)
  "returns true if <state> is unsatisfiable."
  (loop for state1 on state with statevar1
      do (setq statevar1 (first state1))
        (loop for statevar2 in (cdr state1)
            when (unsatisfiable-statevar-p statevar1 statevar2)
            do (format t "~%Unsatisfiable pair:<~S ~S>" statevar1 statevar2)
              (return-from unsatisfiable-state-p t))))

;;;
;;;; Ground Literal
;;;
;;; A state variable is called <ground>, if every argument in a state variable is a constant symbol.
;;; Note that in this implementation variable symbols in the first-order language is expressed as a lisp 
;;; symbol that starts with '?' or '$' character. Otherwise, lisp symbols in statevar arguments are 
;;; constant terms. See, unify module in FOL directory. 
;;; ----------------------------------------------------------------------------------
;;;   Ex. (ground-p (statevar '(= (rloc r1) l1))) --> true
;;;   Ex. (ground-p (statevar "rloc(r)=l1"))      --> false
;;;   Ex. (ground-p (statevar '(= (rloc ?r) l1))) --> false
;;; ----------------------------------------------------------------------------------
;;; Note here that symbols expressed as one character in infix notation turn out variables. For example, 
;;; for "at(r,l)" "r" and "l" are variables in logics, and for "at(r1,l1)" "r1" and "l1" are constant terms.

(defmethod ground-p ((x statevar))
  "returns true if statevar <x> does not include any variable."
  (notany #'variable? (statevar-args x)))

;;;
;;;; State Variable Expression to Normal Literal Expression
;;;
;;; A statevar "pred(x,y)=val" is expressed as "pred(x,y,val)" in normal first-order literal 
;;; formula, of which the truth value is assigned true. Therefore, a statevar "pred(x,y)=val" 
;;; can be transformed to "pred(x,y,val)=t" as positive literal. Similary, a negative literal 
;;; "~pred(x,y)" can be transformed to "pred(x,y)=nil" in this program. All statevars must be 
;;; tranformed to noramal literal expression before unification.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (statevar "rloc(r1)=l1")                       -> rloc(r1)=l1
;;;   Ex. (normalize-statevar (statevar "rloc(r1)=l1"))  -> rloc(r1 l1)
;;; ----------------------------------------------------------------------------------

(defun normalize-statevar (statevar)
  "transforms <statevar> into normal literal expression assigned truth value."
  (case (statevar-val statevar)
    ((nil t) statevar)
    (otherwise (make-statevar :symbol (statevar-symbol statevar)
                              :args (append (statevar-args statevar)
                                             (list (statevar-val statevar)))
                              :val t))))

(defun unnormalize-statevar (statevar)
  "transforms <statevar> into the form that has a value except t."
  (case (statevar-val statevar)
    ((t) (make-statevar :symbol (statevar-symbol statevar)
                        :args (butlast (statevar-args statevar))
                        :val (car (last (statevar-args statevar)))))
    ((nil) `(not ,(make-statevar :symbol (statevar-symbol statevar)
                                 :args (butlast (statevar-args statevar))
                                 :val (car (last (statevar-args statevar))))))
    (otherwise statevar)))

;;;
;;;; Equality of State Variable
;;;
;;; There are four predicate functions for equality testing for statevars.
;;; 
;;; <statevar-equalp> is available as normal one in definition of state variable.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (statevar-equalp 
;;;                  (statevar "load(r1) = c3") (statevar "load(r1,c3)"))  -> true
;;;   Ex. (statevar-equalp 
;;;                  (statevar "load(r1)") (statevar "load(r1,c3)"))       -> false
;;;   Ex. (statevar-equalp 
;;;                  (statevar "~load(r1)") (statevar "~load(r1,c3)"))     -> true
;;;   Ex. (statevar-equalp 
;;;                  (statevar "~load(r1)=c3") (statevar "load(r1,c3)"))   -> false
;;; ----------------------------------------------------------------------------------
;;; <pseudo-statevar-equalp> is prepared for matching with ignoring statevar's value. 
;;; This is useful to test to match positive state and negative precond.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (pseudo-statevar-equalp 
;;;                  (statevar "~load(r1)") (statevar "load(r1) = c3")) -> true
;;;   Ex. (pseudo-statevar-equalp 
;;;                  (statevar "~load(r1)") (statevar "~load(r1,c3)"))  -> true
;;;   Ex. (pseudo-statevar-equalp 
;;;                  (statevar "load(r1)") (statevar "load(r1,c3)"))    -> false
;;;   Ex. (pseudo-statevar-equalp 
;;;                  (statevar "~load(r1)") (statevar "~load(r1,c3)"))  -> true
;;; ----------------------------------------------------------------------------------
;;; <statevar-equalp-with-unify> returns true if two states are unifiable and equal as a 
;;; result of appopriate substitution.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (statevar-equalp-with-unify 
;;;                  (statevar "load(r1) = c3") (statevar "load(r,c)"))  -> true
;;;   Ex. (statevar-equalp-with-unify 
;;;                  (statevar "~load(r1) = c3") (statevar "load(r,c)")) -> false
;;;   Ex. (statevar-equalp-with-unify 
;;;                  (statevar "at($r,$l)") (statevar "at(r1,l1)"))      -> true
;;;   Ex. (statevar-equalp-with-unify 
;;;                  (statevar "~at($r,$l)") (statevar "at(r1,l1)"))     -> false
;;; ----------------------------------------------------------------------------------
;;; <pseudo-statevar-equalp-with-unify> returns true if two states are equal as a result of 
;;; appopriate unification.
;;; ----------------------------------------------------------------------------------
;;;   Ex. (pseudo-statevar-equalp-with-unify
;;;                  (statevar "load(r1) = c3") (statevar "load(r,c)"))  -> true
;;;   Ex. (pseudo-statevar-equalp-with-unify 
;;;                  (statevar "~load(r1) = c3") (statevar "load(r,c)")) -> true
;;;   Ex. (pseudo-statevar-equalp-with-unify 
;;;                  (statevar "at($r,$l)") (statevar "at(r1,l1)"))      -> true
;;;   Ex. (pseudo-statevar-equalp-with-unify 
;;;                  (statevar "~at($r,$l)") (statevar "at(r1,l1)"))     -> true
;;; ----------------------------------------------------------------------------------

(defun statevar-equalp (s1 s2)
  "returns true if <s1> and <s2> is equal in semantics of state variable, otherwise false."
  (or (equalp s1 s2)   ; symbols, args, vals equal 
      (and (eq (statevar-symbol s1) (statevar-symbol s2))
           (let ((args1 (statevar-args s1))
                 (args2 (statevar-args s2))
                 (val1 (statevar-val s1))
                 (val2 (statevar-val s2)))
             (cond ((equalp val1 val2)
                    (cond ((eq val1 t) nil)     ; t x t and args different
                          ((eq val1 nil)        ; nil x nil
                           (and (length-in-1diff args1 args2)
                                (every #'equal args1 args2)))
                          (t nil)))             ; a x a and args different
                   ((and (eq val1 t) (not (eq val2 nil)))  ; t x a
                    (and (= (1- (length args1)) (length args2))
                         (equalp (car (last args1)) val2)
                         (every #'equal args1 args2)))
                   ((and (not (eq val1 nil)) (eq val2 t))  ; a x t
                    (and (= (length args1) (1- (length args2)))
                         (equalp val1 (car (last args2)))
                         (every #'equal args1 args2)))
                   (t ;; t x nil, nil x t then return nil
                    nil))))))

(defun pseudo-statevar-equalp (s1 s2)
  "this function does not care about truth value asigned to <s1> and <s2>."
  (or (equalp s1 s2)   ; symbols, args, vals equal 
      (and (eq (statevar-symbol s1) (statevar-symbol s2))
           (let ((args1 (statevar-args s1))
                 (args2 (statevar-args s2))
                 (val1 (statevar-val s1))
                 (val2 (statevar-val s2)))
             (cond ((equalp val1 val2)
                    (cond ((eq val1 t) nil)     ; t x t and args different
                          ((eq val1 nil)        ; nil x nil
                           (and (length-in-1diff args1 args2)
                                (every #'equal args1 args2)))
                          (t nil)))             ; a x a and args different
                   ((and (eq val1 t) (eq val2 nil))
                    (equalp args1 args2))     ; length must be same.
                   ((and (eq val1 nil) (eq val2 t))
                    (equalp args1 args2))     ; length must be same.
                   ((eq val2 nil)               ; a x nil
                    (and (= (length args1) (length args2))
                         (every #'equal args1 args2)))
                   ((eq val1 nil)               ; nil x a
                    (and (= (length args1) (length args2))
                         (every #'equal args1 args2)))
                   )))))

(defun statevar-equalp-with-unify (s1 s2)
  "returns true if <s1> and <s2> is unifiable and equal with appropriate substitution."
  (or (equalp s1 s2)   ; symbols, args, vals equal 
      (and (eq (statevar-symbol s1) (statevar-symbol s2))
           (let ((args1 (statevar-args s1))
                 (args2 (statevar-args s2))
                 (val1 (statevar-val s1))
                 (val2 (statevar-val s2)))
             (cond ((= (length args1) (length args2))
                    (and (unify args1 args2 (unify val1 val2))
                         t))
                   (t (and (unify (normalize-statevar s1) (normalize-statevar s2))
                           t)))))))

(defun pseudo-statevar-equalp-with-unify (s1 s2)
  "returns true if <s1> and <s2> is unifiable and equal with appropriate substitution. 
   Note that this function does not care about assigned truth values."
  (or (equalp s1 s2)   ; symbols, args, vals equal 
      (and (eq (statevar-symbol s1) (statevar-symbol s2))
           (let ((args1 (statevar-args s1))
                 (args2 (statevar-args s2)))
             (cond ((= (length args1) (length args2))
                    (and (unify args1 args2)
                         t))
                   (t (and (unify (statevar-args (normalize-statevar s1))
                                  (statevar-args (normalize-statevar s2)))
                           t)))))))

;;;; Unsatisfiability of Statevars
;;; If two statevars are strictly equal except their truth value, and both truth values are opposite,
;;; then, the pair of statevars is called <unsatisfiable>. 
;;; Namely, "pred(a,b,c)" and "~pred(a,b,c)" are unsatisfiable.

(defun statevar-opposite-p (s1 s2)
  "returns true if truth value of <s1> and <s2> is opposite in semantics of state variable."
  (and (eq (statevar-symbol s1) (statevar-symbol s2))
       (let ((args1 (statevar-args s1))
             (args2 (statevar-args s2))
             (val1 (statevar-val s1))
             (val2 (statevar-val s2)))
         (cond ((or (and (eq val1 t) (eq val2 nil))
                    (and (eq val1 nil) (eq val2 t)))
                (every #'equalp args1 args2))
               ((and (eq val1 t) (eq val2 t)) nil)
               ((and (eq val1 nil) (eq val2 nil)) nil)
               ((and (eq val1 nil) (not (eq val2 nil)))  ; nil x a
                (and (= (1- (length args1)) (length args2))
                     (equalp (car (last args1)) val2)
                     (every #'equal args1 args2)))
               ((and (not (eq val1 nil)) (eq val2 nil))  ; a x nil
                (and (= (length args1) (1- (length args2)))
                     (equalp val1 (car (last args2)))
                     (every #'equal args1 args2)))))))

(defun unsatisfiable-statevar-p (s1 s2)
  "returns true if <s1> and <s2> make a unsatisfiable pair. This is same as statevar-opposite-p."
  (and (eq (statevar-symbol s1) (statevar-symbol s2))
       (let ((args1 (statevar-args s1))
             (args2 (statevar-args s2))
             (val1 (statevar-val s1))
             (val2 (statevar-val s2)))
         (cond ((or (and (eq val1 t) (eq val2 nil))
                    (and (eq val1 nil) (eq val1 t)))
                (every #'equalp args1 args2))
               ((and (eq val1 t) (eq val2 t)) nil)
               ((and (eq val1 nil) (eq val2 nil)) nil)
               ((and (eq val1 nil) (not (eq val2 nil)))  ; nil x a
                (and (= (1- (length args1)) (length args2))
                     (equalp (car (last args1)) val2)
                     (every #'equal args1 args2)))
               ((and (not (eq val1 nil)) (eq val2 nil))  ; a x nil
                (and (= (length args1) (1- (length args2)))
                     (equalp val1 (car (last args2)))
                     (every #'equal args1 args2)))))))

;;;
;;;; Unification for State Variable
;;; Following methods work in a part of function unify. See unify in fol module in detail.

(defmethod compound-unify? ((x statevar) (y statevar))
  "trivially returns true because <x> and <y> are instances of statevar."
  t)
(defmethod compound-unify ((x statevar) (y statevar) bindings)
  "returns bindings as a result of unification of <x> and <y>. Statevars in unification 
   must be normalized."
  (cond ((eql (statevar-symbol x) (statevar-symbol y))
         ;; x and y must be normal statevar form.
         (setq x (normalize-statevar x))
         (setq y (normalize-statevar y))
         (cond ((eql (statevar-val x) (statevar-val y))
                ;; if xval = yval with t&t or nil&nil
                ;; args must be unified
                (unify (statevar-args x) (statevar-args y) bindings))
               (t ;; else t&nil or nil&t
                +fail+
                )))
        (t +fail+)))

(defmethod opposite-compound-unify ((x statevar) (y statevar) bindings)
  "returns bindings as a result of unification, if both truth values are  
   opposite. This is used for threat computing in PSP module."
  (cond ((eq (statevar-symbol x) (statevar-symbol y))
         ;; x and y must be normal statevar form.
         (cond ((not (eql (statevar-val x) (statevar-val y)))
                ;; if xval /= yval with t&nil or nil&t
                ;; args must be unified
                (unify (statevar-args x) (statevar-args y) bindings))
               (t ;; else t&nil or nil&t
                +fail+
                )))
        (t +fail+)))

(defmethod subst-bindings (bindings (x statevar))
  "substitutes <x> with <bindings> and returns the result."
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-statevar :symbol (statevar-symbol x)
                          :args (subst-bindings bindings (statevar-args x))
                          :val (subst-bindings bindings (statevar-val x))))))

(defmethod variables-in ((x statevar))
  "returns variables in <x>."
  (variables-in (statevar-args x)))

;;;
;;;; Simple but very often used utilities
;;;

(defmethod op ((exp statevar)) (statevar-symbol exp))
(defmethod args ((exp statevar)) (statevar-args exp))
(defmethod arg1 ((exp statevar)) (first (statevar-args exp)))
(defmethod arg2 ((exp statevar)) (second (statevar-args exp)))

#|
(in-package :plan)
(logic "load(r1)=c1") -> (= (load r1) c1)
(logic "~load(r1)=c1") -> (not (= (load r1) c1))
(state "{at(r1)=l1,load(r1)=nil,cpos(c1)=l1,cpos(c2)=l2}") -> (at(r1)=l1 ~load(r1) cpos(c1)=l1 cpos(c2)=l2)
(state "{at(r1)=l1,~load(r1),cpos(c1)=l1,cpos(c2)=l2}") -> (at(r1)=l1 ~load(r1) cpos(c1)=l1 cpos(c2)=l2)
(state '((= (at r1) l1) (not (load r1)) (= (cpos c1) l1) (= (cpos c2) l2))) -> (at(r1)=l1 ~load(r1) cpos(c1)=l1 cpos(c2)=l2)
(statevar "rloc(r1)=l1") -> rloc(r1)=l1
(statevar '(= (rloc r1) l1)) -> rloc(r1)=l1
(statevar "~rloc(r1)=l1") -> ~rloc(r1 l1)
(statevar '(not (= (rloc r1) l1))) -> ~rloc(r1 l1)
(normalize-statevar (statevar "rloc(r1)=l1")) -> rloc(r1 l1)
(statevar-equalp (statevar "load(r1) = c3") (statevar "load(r1,c3)")) -> t
(statevar-equalp (statevar "load(r1)") (statevar "load(r1,c3)")) -> nil
(statevar-equalp (statevar "~load(r1)") (statevar "~load(r1,c3)")) -> t
(statevar-equalp (statevar "~load(r1)=c3") (statevar "load(r1,c3)")) -> nil
(pseudo-statevar-equalp (statevar "~load(r1)") (statevar "load(r1) = c3")) -> t
(pseudo-statevar-equalp (statevar "~load(r1)") (statevar "~load(r1,c3)")) -> t
(pseudo-statevar-equalp (statevar "load(r1)") (statevar "load(r1,c3)")) -> nil
(pseudo-statevar-equalp (statevar "~load(r1)") (statevar "~load(r1,c3)")) -> t
(statevar-equalp-with-unify (statevar "load(r1) = c3") (statevar "load(r,c)")) -> t
(statevar-equalp-with-unify (statevar "~load(r1) = c3") (statevar "load(r,c)")) -> nil
(statevar-equalp-with-unify (statevar "at($r,$l)") (statevar "at(r1,l1)")) -> t
(statevar-equalp-with-unify (statevar "~at($r,$l)") (statevar "at(r1,l1)")) -> nil
(pseudo-statevar-equalp-with-unify (statevar "load(r1) = c3") (statevar "load(r,c)")) -> t
(pseudo-statevar-equalp-with-unify (statevar "~load(r1) = c3") (statevar "load(r,c)")) -> t
(pseudo-statevar-equalp-with-unify (statevar "at($r,$l)") (statevar "at(r1,l1)")) -> t
(pseudo-statevar-equalp-with-unify (statevar "~at($r,$l)") (statevar "at(r1,l1)")) -> t

(ground-p (statevar "rloc(r1)=l1")) -> t

(setq *state* (state "{hasAppointment(Lucy)=LucysAppt, hasAppointment(HAL)=HALsAppt}"))
|#