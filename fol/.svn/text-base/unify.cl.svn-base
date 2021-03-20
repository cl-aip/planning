;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*- File: logic/unify.lisp

;;;; Unification and Substitutions (aka Binding Lists)

;;; Most of this code is borrowed from "Paradigms of AI Programming: Case Studies
;;; in Common Lisp", by Peter Norvig, published by Morgan Kaufmann, 1992.
;;; The complete code from that book is available for ftp at mkp.com in
;;; the directory "pub/Norvig".  Note that it uses the term "bindings"
;;; rather than "substitution" or "theta".  The meaning is the same.
;;;
;;; However, <get-mgu> and <get-disagreement-set> are programed by Seiji Koide.
;;; All rights on these programs are reserved by Seiji Koide. 
;;; 
;;; Copyrights (c), 2008, Seiji Koide

(cl:defpackage :fol
  (:use common-lisp :utils)
  (:export unify tunify subst-bindings get-mgu
           variable? rename-variables variables-in
           compound-unify tcompound-unify compound-unify? 
           binding-var lookup new-variable
           extend-bindings get-binding occurs-in?)
  )

(eval-when (:execute :load-toplevel :compile-toplevel)
  ) ; end of eval-when

(in-package :fol)

;;;; Constants

(defconstant +fail+ nil "Indicates unification failure")

(defconstant +no-bindings+ '((nil))
  "Indicates unification success, with no variables.")

;;;; Most General Unifier
;;;
;;; <get-mgu> computes MGU from a set of clauses. This function is more useful than <unify>, which computes 
;;; a substitution from two arguments. 
;;; 
;;; This algorithm is by Nagao and Fuchi published from Iwanami.

(defun get-mgu (clauses &optional (bindings +no-bindings+))
  (setq clauses (subst-bindings bindings clauses))
  (when (let ((this (car clauses)))
          (every #'(lambda (other) (equal this other)) (cdr clauses)))
    (return-from get-mgu bindings))
  (let ((disagreement-set (get-disagreement-set clauses)))
    (when (null disagreement-set) (return-from get-mgu bindings))
    (let ((var (find-if #'variable? disagreement-set)))
      (let ((val (find-if-not
                  #'(lambda (term) (find-anywhere-if #'(lambda (x) (equal var x)) term))
                  disagreement-set)))
        (when (not (and var val)) (return-from get-mgu nil))
        (if (eq bindings +no-bindings+)
            (get-mgu clauses (list (cons var val)))
          (get-mgu clauses (append bindings (list (cons var val)))))))))

(defun get-disagreement-set (literals)
  (cond ((every #'null literals) nil)
        ((some #'null literals) literals)
        ;; we assume every element must be same type.
        ((listp (car literals))      ; in travelling parms or elements are logical atoms as list
         (let ((firsts (mapcar #'car literals))
               (rests (mapcar #'cdr literals)))
           (cond ((every #'consp firsts)               ; functional structure in params
                  (or (get-disagreement-set firsts)
                      (get-disagreement-set rests)))
                 ((some #'consp firsts)
                  (mapcar #'car literals))
                 ((same-element-p #'eql firsts)        ; match firsts, op or arg
                  (get-disagreement-set rests))        ; then next
                 (t firsts))))                         ; disagreement
        ((same-element-p #'eq (mapcar #'op literals))    ; list of structs
         (get-disagreement-set (mapcar #'args literals)))
        (t literals)))

;;;
;;;; Unifier from AIMA
;;;

(defun unify (x y &optional (bindings +no-bindings+))
  "See if x and y match with given bindings.  If they do,
  return a binding list that would make them equal [p 303]."
  (cond ((eq bindings +fail+) +fail+)
        ((eql x y) bindings)
        ((variable? x) (unify-var x y bindings))
        ((variable? y) (unify-var y x bindings))
        ((compound-unify? x y) (compound-unify x y bindings))
        ((and (consp x) (consp y))
         (unify (rest x) (rest y) 
                (unify (first x) (first y) bindings)))
        (t +fail+)))

(defgeneric compound-unify? (exp1 exp2) (:documentation "Is this expression unifiable?"))
(defmethod compound-unify? (exp1 exp2) 
  (declare (ignore exp1 exp2))
  nil)

(defgeneric compound-unify (exp1 exp2 bindings) (:documentation "unify compounds"))
(defgeneric tcompound-unify (exp1 exp2 bindings env tbindings) (:documentation "unify compounds"))

(defun rename-variables (x)
  "Replace all variables in x with new ones."
  (let ((bindings (mapcar #'(lambda (var) (make-binding var (new-variable var)))
                    (variables-in x))))
    (cond (bindings (values (subst-bindings bindings x) bindings))
          (t (values x +no-bindings+)))))

#|
(defun rename-subtasks* (subtasks)
  "this function renames variables in tasks as keeping identity of same variables."
  (let ((bindings (mapcar #'(lambda (var) (make-binding var (new-variable var)))
                    (reduce #'union (mapcar #'variables-in subtasks)))))
    (mapcar #'(lambda (task)
                (set-task-terms task (sublis bindings (task-terms task))))
      subtasks))
  subtasks)

(defun rename-method* (method)
  (let ((bindings (mapcar #'(lambda (var) (make-binding var (new-variable var)))
                    (method-variables method))))
    (set-method-variables method
                               (subst-bindings bindings (method-variables method)))
    (set-task-terms (method-task method)
                         (subst-bindings bindings
                                         (task-terms (method-task method))))
    (mapcar #'(lambda (task)
                (set-task-terms task (sublis bindings (task-terms task))))
      (method-subtasks method))
    ;; then subtasks in constraint are also renamed by side effects.
    ;; but variables in precond and effects are not yet.
    (set-constraint-precond
     (method-constr method)
     (loop for prec in (constraint-precond (method-constr method))
         collect (cl:list (first prec) ; task
                          (subst-bindings bindings (second prec)))))
    (set-constraint-effects
     (method-constr method)
     (loop for effect in (constraint-effects (method-constr method))
         collect (cl:list (first effect) ; task
                          (subst-bindings bindings (second effect)))))
    ))

(defun rename-variables-in-method (method)
  (let ((bindings (mapcar #'(lambda (var) (make-binding var (new-variable var)))
                    (method-variables method))))
    (subst-bindings bindings method)))

(defun rename-variables-in-task (task)
  (let ((bindings (mapcar #'(lambda (var) (make-binding var (new-variable var)))
                    (task-terms task))))
    (subst-bindings bindings task)))
|#

;;;; Auxiliary Functions

(defun unify-var (var x bindings)
  "Unify var with x, using (and maybe extending) bindings [p 303]."
  (cond ((get-binding var bindings)
         (unify (lookup var bindings) x bindings))
        ((and (variable? x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings))
        ((occurs-in? var x bindings)
         +fail+)
        ((violate-una? var x bindings)
         +fail+)
        (t (extend-bindings var x bindings))))

(defun violate-una? (var x bindings)
  (cond ((rassoc x bindings)
         (cond ((eq (car (rassoc x bindings)) var) (error "Cant happen!"))
               (t (format t "~&Violate UNA:~S ~S ~S" var x bindings)
                  t)))))

(defun variable? (x)
  "Is x a variable (a symbol starting with $ or ?)?"
  (cond ((symbolp x)
         (or (char= (char (symbol-name x) 0) #\$)
             (char= (char (symbol-name x) 0) #\?)))
        ((and (consp x) (= (length x) 3) (symbolp (second x)) (string= (second x) '-))
         (or (char= (char (symbol-name (first x)) 0) #\$)
             (char= (char (symbol-name (first x)) 0) #\?)))))

(defun get-binding (var bindings)
  "Find a (variable . value) pair in a binding list."
  (assoc var bindings))

(defun binding-var (binding)
  "Get the variable part of a single binding."
  (car binding))

(defun binding-val (binding)
  "Get the value part of a single binding."
  (cdr binding))

(defun make-binding (var val) (cons var val))

(defun lookup (var bindings)
  "Get the value part (for var) from a binding list."
  (binding-val (get-binding var bindings)))

(defun extend-bindings (var val bindings)
  "Add a (var . value) pair to a binding list."
  (cons (make-binding var val)
        ;; Once we add a "real" binding,
        ;; we can get rid of the dummy +no-bindings+
        (if (eq bindings +no-bindings+)
            nil
            bindings)))

(defun occurs-in? (var x bindings)
  "Does var occur anywhere inside x?"
  (cond ((eq var x) t)
        ((and (variable? x) (get-binding x bindings))
         (occurs-in? var (lookup x bindings) bindings))
        ((consp x) (or (occurs-in? var (first x) bindings)
                       (occurs-in? var (rest x) bindings)))
        (t nil)))

(defmethod subst-bindings (bindings x)
  "Substitute the value of variables in bindings into x,
  taking recursively bound variables into account."
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        ((and (variable? x) (get-binding x bindings))
         (subst-bindings bindings (lookup x bindings)))
        #|
        ((task-p x)
         (make-task :symbol (task-symbol x)
                         :terms (subst-bindings bindings (task-terms x))))
        ((node-p x)
         (make-node :task (subst-bindings bindings (node-task x))))
        ((meth-name-p x)
         (make-meth-name :symbol (meth-name-symbol x)
                              :parms (subst-bindings bindings (meth-name-parms x))))
        ((constraint-p x)
         (make-constraint :precond (subst-bindings bindings (constraint-precond x))
                               :orders  (subst-bindings bindings (constraint-orders x))
                               :effects (subst-bindings bindings (constraint-effects x))))
        ((method-p x)
         (make-method :name (subst-bindings bindings (method-name x))
                           :comment (method-comment x)
                           :task (subst-bindings bindings (method-task x))
                           :subtasks (subst-bindings bindings (method-subtasks x))
                           :constr (subst-bindings bindings (method-constr x))))
|#
        ((atom x) x)
        (t (reuse-cons (subst-bindings bindings (car x))
                       (subst-bindings bindings (cdr x))
                       x))))

(defun subst-bindings* (bindings x)
  "subst-bindings as side effects."
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        ((and (variable? x) (get-binding x bindings))
         (subst-bindings* bindings (lookup x bindings))
         x)
        #|
        ((task-p x)
         (set-task-terms x (subst-bindings* bindings (task-terms x)))
         x)
|#
        ((atom x) x)
        (t (reuse-cons (subst-bindings bindings (car x))
                       (subst-bindings bindings (cdr x))
                       x))))

(defun unifier (x y)
 "Return something that unifies with both x and y (or fail)."
  (subst-bindings (unify x y) x))

(defmethod variables-in (exp)
  (declare (ignore exp))
  nil)

(defmethod variables-in ((exp cons))
  "Return a list of all the variables in EXP."
  (unique-find-anywhere-if #'variable? exp))

(defun unique-find-anywhere-if (predicate tree &optional found-so-far)
  "Return a list of leaves of tree satisfying predicate,
  with duplicates removed."
  (if (atom tree)
      (if (funcall predicate tree)
          (pushnew tree found-so-far)
          found-so-far)
      (unique-find-anywhere-if
        predicate
        (first tree)
        (unique-find-anywhere-if predicate (rest tree)
                                 found-so-far))))

(defun find-anywhere-if (predicate tree)
  "Does predicate apply to any atom in the tree?"  
  (if (atom tree)
      (funcall predicate tree)
      (or (find-anywhere-if predicate (first tree))
          (find-anywhere-if predicate (rest tree)))))

(defvar *new-variable-counter* 0)

(defun new-variable (var)
  "Create a new variable.  Assumes user never types variables of form $X.9"
  (concat-symbol (if (variable? var) "" "$")
                 var "." (incf *new-variable-counter*)))

#|
(unify '(Knows John ?x) '(Knows John Jane))      -> ((?x . Jane))
(unify '(Knows John ?x) '(Knows ?y Bill))        -> ((?x . Bill) (?y . John))
(unify '(Knows John ?x) '(Knows ?y (Mother ?y))) -> ((?x Mother ?y) (?y . John))
(unify '(Knows John ?x) '(Knows ?x Elizabeth))   -> nil
|#
