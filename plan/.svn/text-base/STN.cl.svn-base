;;;-*- Mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;
;; The Automated Planning - Theory and Practice is a textbook for planning by Malik Ghallab, 
;; Dana Nau, and Paolo Traverso, from Morgan Kaufmann. 
;; This program is a realization of algorithms that are published on the book, coded by Seiji 
;; Koide. 

;;;; STN (Simple Task Network) Planning Module (Chapter 11)
;;; All rights on programs are reserved by Seiji Koide. 
;;; 
;;; Copyrights (c), 2008, Seiji Koide

(cl:defpackage :plan
  (:shadowing-import-from :fol compound-unify compound-unify?)
  (:shadow method make-method)
  (:use common-lisp :callcc :utils :fol)
  (:export statevar-p statevar-symbol statevar-val statevar-args
           ope-name-p make-ope-name ope-name-symbol ope-name-parms
           operator operator-p make-operator operator-name operator-symbol operator-variables 
           operator-comment operator-precond operator-effects
           method method-name make-method method-comment method-task method-subtasks 
           method-constr set-method-constr method-variables method define-method
           meth-name-p make-meth-name meth-name-symbol meth-name-parms
           task task-p make-task task-symbol task-terms set-task-terms
           node-p make-node node-task)
  )

(in-package :plan)

;;;; Task
;;; A <task> looks like <ope-name> at a glance, as a <task> is composed of task <symbol> and 
;;; <terms>. However the <task> is an abstract concept of <operator>s. It stands for a singleton or chunk of 
;;; operation. It is a concept very close to the workflow.
;;;
;;; Note that syntactically task name cannot include characters, +, -, /, &gt;, &lt;, =, etc. in string logical 
;;; expression for infix notation. Therefore, when you input a task name as string, please avoid to type these 
;;; characters such as "transfer_two_containers" instead of "transfer-two-containers".
;;;
;;; See the following example to make a task named "setup".
;;; ----------------------------------------------------------------------------------
;;;   Ex. (task "setup(c,r)")  --> setup($c $r)
;;; ----------------------------------------------------------------------------------

(defstruct (task (:print-function print-task)) symbol terms)

(defun print-task (x stream depth)
  "prints <task> like ''setup($c $r)''."
  (declare (ignore depth))
  (format stream "~A~S" (task-symbol x) (task-terms x)))

(defun set-task-terms (x val)
  "sets <val> to task terms of <x>."
  (setf (task-terms x) val))

(defun task-equalp (task1 task2)
  "returns true if <task1> and <task2> are equal as task."
  (or (equalp task1 task2)
      (and (task-p task1) (task-p task2)
           (eq (task-symbol task1) (task-symbol task2))
           (equalp (task-terms task1) (task-terms task2)))))

(declaim (special +task+ +subtasks+))

(defun task (exp)
  "<exp> is either an instance of task, infix notation as string, or prefix notation as S-expression.
   This function creates an instance of task and returns it, if <exp> is a string or list.
   If <exp> is an instance of task, simply returns it. In any case, the return value is set at 
   special var <+task+>."
  (setq +task+ 
        (if (task-p exp) exp
          (if (stringp exp) (task (logic exp))
            (make-task :symbol (op exp) :terms (args exp))))))

;;;
;;;; For Unification of Task
;;;

(cl:defmethod compound-unify? ((x task) (y task)) t)
(cl:defmethod compound-unify ((x task) (y task) bindings)
  (cond ((eql (task-symbol x) (task-symbol y))
         (unify (task-terms x) (task-terms y) bindings))
        (t +fail+)))

(cl:defmethod subst-bindings (bindings (x task))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-task :symbol (task-symbol x)
                      :terms (subst-bindings bindings (task-terms x))))))

(cl:defmethod variables-in ((x task))
  (variables-in (task-terms x)))

;;;
;;;; Method
;;; A <method> in HTN describes how a task can be performed by subtasks and it is comprised of four tuple 
;;; &lt;<meth-name, task, subtasks, constr>&gt;. 
;;;  * <meth-name> is similar to <op-name>, as it is composed of <symbol> and <parms>.
;;;  * <task> is a relevant task to this <method>. 
;;;  * <subtasks> is a list of subtasks but the order of performance is governed by the ordering constraint in <constr>. 
;;;  * <constr> means constraints among <subtasks>.

(defstruct (meth-name (:print-function print-meth-name)) symbol parms)
(defun print-meth-name (x stream depth)
  "prints <meth-name> like ''do_setup($c $r)''."
  (declare (ignore depth))
  (format stream "~A~S" (task-symbol x) (task-terms x)))

(defun meth-name (exp)
  "makes an instance of <meth-name> from <exp> and returns it.
   If <exp> is a string, it should be in infix notation like ''do_setup(c,r)'', otherwise it should be 
   a list in prefix notation like ''(do_setup $c $r)''.
   Note that a single character in string turns out an object variable with its name in logics."
  (if (meth-name-p exp) exp
    (if (stringp exp) (meth-name (logic exp))
      (make-meth-name :symbol (op exp) :parms (args exp)))))

(defstruct (method (:print-function print-method)) name comment task subtasks constr)
(defun print-method (x stream depth)
  "prints <meth-name> like ''(method do_setup($c $r) setup($c $r) ...)''."
  (declare (ignore depth))
  (cond ((method-comment x)
         (format stream "~<(method ~;~W ~_~:I~W~_(:task ~W) ~_(:subtasks~{ ~W~}) ~_(:constr~{ ~W~})~;)~:>"
           (list (method-name x) (method-comment x) (method-task x)
                 (method-subtasks x) (constraint-set (method-constr x)))))
        (t (format stream "~<(method ~;~W ~_~:I(:task ~W) ~_(:subtasks~{ ~W~}) ~_(:constr~{ ~W~})~;)~:>"
             (list (method-name x) (method-task x) (method-subtasks x) (constraint-set (method-constr x)))))))

(defun method-symbol (method)
  "returns a name symbol of <method>."
  (meth-name-symbol (method-name method)))
(defun method-variables (method)
  "returns variables of method name of <method>."
  (meth-name-parms (method-name method)))

(defun set-method-variables (method val)
  "sets <val> to variables of method name of <method>."
  (setf (meth-name-parms (method-name method)) val))

;;;
;;; All methods in HTN system should be stored in a global var <*methods*>. Macro <define-method> 
;;; do it. To denote the constraint of method, three keywords, :precond, :orderings, :effects, 
;;; or one keyword :contr are used. See the following examples.
;;; ----------------------------------------------------------------------------------
;;; (define-method "do_setup(c,d,k,l,p,r)"
;;;     "method to prepare for moving a container"
;;;   :task "setup(c,r)"
;;;   :subtasks "take(k,l,c,d,p),load(k,l,c,r)"
;;;   :precond "on(c)=d,attached(p)=l,in(c)=p,belong(k)=l,at(r)=l,empty(k),
;;;             unloaded(r),top(c)=p")
;;;
;;; (define-method "do_setup(c,d,k,l,p,r)"
;;;     "method to prepare for moving a container"
;;;   :task "setup(c,r)"
;;;   :subtasks "take(k,l,c,d,p),load(k,l,c,r)"
;;;   :constr ":u1&lt;&lt;:u2, 
;;;            before({:u1},on(c)=d), before({:u1},attached(p)=l),
;;;            before({:u1},in(c)=p), before({:u1},belong(k)=l),
;;;            before({:u1},at(r)=l), before({:u1},empty(k)),
;;;            before({:u1},unloaded(r)), before({:u1},top(c)=p)")
;;; ----------------------------------------------------------------------------------
;;; Where :u1 stands for the first task in the subtask list. Similarly :u2 stands for the second 
;;; task in the subtask list. The form ":u1&lt;&lt;:u2" in :constr value means a partial ordering.
;;; Use :u0 to refer the task itself rather than one of subtasks.

(defvar *methods* () "A global var in which defined methods are stored.")

;; subtasks in subtasks slots and constr slots are in eq-relation.
(defmacro define-method (meth-name &rest initargs)
  "defines a method and pushes the result into <*methods*>."
  `(car
    (setq *methods*
          (cons (method ',meth-name
                        :comment ,(if (stringp (car initargs)) (car initargs))
                        :task ',(if (stringp (car initargs))
                                    (getf (cdr initargs) :task)
                                  (getf initargs :task))
                        :subtasks ',(if (stringp (car initargs))
                                        (getf (cdr initargs) :subtasks)
                                      (getf initargs :subtasks))
                        :precond ',(if (stringp (car initargs))
                                       (getf (cdr initargs) :precond)
                                     (getf initargs :precond))
                        :orderings ',(if (stringp (car initargs))
                                         (getf (cdr initargs) :orderings)
                                       (getf initargs :orderings))
                        :effects ',(if (stringp (car initargs))
                                       (getf (cdr initargs) :effects)
                                     (getf initargs :effects))
                        :constr ',(if (stringp (car initargs))
                                      (getf (cdr initargs) :constr)
                                    (getf initargs :constr)))
                *methods*))))

(defun method (meth-name &key task subtasks constr precond orderings effects comment)
  "makes a method in HTN and returns it."
  (let ((+task+ nil)
        (+subtasks+ nil))
    (setq task (task task))                      ; and set +task+
    (setq subtasks (make-subtasks1 subtasks))    ; and set +subtasks+
    (when precond
      (setq precond (make-before-const
                     :task (or (first +subtasks+) +task+)
                     :const (mapcar #'normalize-statevar
                              (mapcar #'statevar
                                (if (stringp precond) (logic (with-brace precond)) precond))))))
    (when effects
      (setq effects (make-after-const
                     :task (or (car (last +subtasks+)) +task+)
                     :const (mapcar #'normalize-statevar
                              (mapcar #'statevar
                                (if (stringp effects) (logic (with-brace effects)) effects))))))
    (setq orderings (replace-task-in-orderings
                     (mapcar #'(lambda (ord) (cond ((eq (op ord) '<<)
                                                    (ordering (arg1 ord) (arg2 ord)))
                                                   ((error "Illegal ordering form!"))))
                       (if (stringp orderings) (logic (with-brace orderings)) orderings))))
    (setq constr (make-constr1 (if (stringp constr) (logic (with-brace constr)) constr)))
    (make-method :name (meth-name meth-name)
                 :task (task task)
                 :subtasks subtasks
                 :constr (constraint (append orderings (mklist precond) (mklist effects) constr))
                 :comment comment
                 )))

;;;
;;;; Unification for Method
;;;

(cl:defmethod compound-unify? ((x meth-name) (y meth-name)) t)
(cl:defmethod compound-unify ((x meth-name) (y meth-name) bindings)
  (cond ((eql (meth-name-symbol x) (meth-name-symbol y))
         (unify (meth-name-parms x) (meth-name-parms y) bindings))
        (t +fail+)))

(cl:defmethod compound-unify? ((x method) (y method)) t)
(cl:defmethod compound-unify ((x method) (y method) bindings)
  (cond ((eql (method-symbol x) (method-symbol y))
         (unify (method-variables x) (method-variables y) bindings))
        (t +fail+)))

(cl:defmethod subst-bindings (bindings (x meth-name))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-meth-name :symbol (meth-name-symbol x)
                           :parms (subst-bindings bindings (meth-name-parms x))))))

(cl:defmethod subst-bindings (bindings (x method))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-method :name (subst-bindings bindings (method-name x))
                        :comment (method-comment x)
                        :task (subst-bindings bindings (method-task x))
                        :subtasks (subst-bindings bindings (method-subtasks x))
                        :constr (constraint (subst-bindings bindings (constraint-set (method-constr x))))))))

(cl:defmethod variables-in ((x method))
  (variables-in (method-variables x)))

;;;
;;;; Other Utilities for Task and Subtasks
;;;

(defun make-subtasks1 (subtasks)
  "returns subtasks which are made from <subtasks>. <subtasks> is a list of tasks in S-exression, or 
   a sequence of subtasks as string in infix notation. This function sets the results to special var <+subtasks+>."
  (setq +subtasks+
        (mapcar #'task
          (if (stringp subtasks) (logic (with-brace subtasks)) subtasks))))

(defun replace-task-in-orderings (orderings)
  "replace task-indicators :u<n> in <orderings> with corresponding tasks."
  (mapcar #'replace-task-in-precedence-ordering orderings))

(defun replace-task-in-precedence-ordering (ordering)
  "this is used in replace-task-in-orderings."
  (ordering (%task-of (ordering-predecessor ordering))
            (%task-of (ordering-successor ordering))))

(defun replace-task-in-precedence-consts (consts)
  "replace task-indicators :u<n> in <consts> with corresponding tasks."
  (mapcar #'replace-task-in-precedence-const consts))

(defun replace-task-in-precedence-const (const)
  "this is used in replace-task-in-precedence-consts."
  (make-precedence-const
   :precedence (%task-of (precedence-const-precedence const))
   :task       (%task-of (precedence-const-task const))))

(defun %task-of (var)
  "returns eq-subtasks from parameters of task-indicator :u<n>."
  (cond ((eq :u0 var) +task+)
        ((eq :u1 var) (first +subtasks+))
        ((eq :u2 var) (second +subtasks+))
        ((eq :u3 var) (third +subtasks+))
        ((eq :u4 var) (fourth +subtasks+))
        ((eq :u5 var) (fifth +subtasks+))
        ((eq :u6 var) (sixth +subtasks+))
        ((eq :u7 var) (seventh +subtasks+))
        ((error "not yet!"))))

;; Adding infix operator "<<" into *infix-ops* before ","
(setq fol::*infix-ops* (append (butlast fol::*infix-ops*) (list '((<<))) (last fol::*infix-ops*)))

(defun make-constr1 (forms)
  "makes a constraint from <forms> and returns it."
  ;; subtasks are eq-relation with the result of make-subtasks1.
  (when (stringp forms)
    (make-constr1 (logic (with-brace forms))))
  (mapcar #'%make-constr1 forms))

(defun %make-constr1 (form)
  "this is used in make-constr1."
  (ecase (op form)
    (<< (replace-task-in-precedence-const
         (make-precedence-const :precedence (arg1 form) :task (arg2 form))))
    (before (let ((task (arg1 form))
                  (const (state (cdr (args form)))))
              (when (and (consp task) (eq (first task) 'fol::elts))
                (setq task (cdr task)))
              (assert (length=1 task))
              (make-before-const :task (%task-of (car task)) :const const)))
    (after (let ((task (arg1 form))
                 (const (state (cdr (args form)))))
             (when (and (consp task) (eq (first task) 'fol::elts))
               (setq task (cdr task)))
             (assert (length=1 task))
             (make-after-const :task (%task-of (car task)) :const const)))))

;;;; Constraints
;;;
;;; The constraint type is devided into three sub types, i.e., <before-constraint>, <after-constraint>, and 
;;; <precedence-constraint>. The <before-constraint> denotes a precondition that should be satisfied before the 
;;; performance of a task, and the <after-constraint> denotes a post condition that should be established after 
;;; the performance of a task. The <precedence-constraint> denotes partial orderings among subtask on the performance.
;;;
;;; The constraint set is a list of constraints, namely, a list of instances of 
;;; <before-constraint>, <after-constraint>, and <precedence-constraint>.

(defstruct (constraint (:print-function print-constraint)) set)
(defun print-constraint (x stream depth)
  "prints out <constraint> such as ''(constraint ...)''."
  (declare (ignore depth))
  (format stream "(constraint~@[~{ ~S~}~]~@[~{ ~S~}~]~@[~{ ~S~}~])"
    (constraint-orderings x) (constraint-precond x) (constraint-effects x)))

(defun constraint (set)
  "makes a constraint and returns it."
  (make-constraint :set set))

;;;
;;; The following is a substitution method for constraint.

(cl:defmethod subst-bindings (bindings (x constraint))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (constraint (subst-bindings bindings (constraint-set x))))))

;;;
;;; <before-constraint>, <after-constraint>, and <precedence-constraint> is defined as structure.

(defstruct (before-const (:print-function print-before-const)) task const)
(defstruct (after-const (:print-function print-after-const)) task const)
(defstruct (precedence-const (:print-function print-precedence-const)) precedence task)
(defun print-before-const (x stream depth)
  (declare (ignore depth))
  (format stream "(before ~S~@[~{ ~W~}~])" (task-symbol (before-const-task x)) (before-const-const x)))
(defun print-after-const (x stream depth)
  (declare (ignore depth))
  (format stream "(before ~S~@[~{ ~W~}~])" (task-symbol (after-const-task x)) (after-const-const x)))
(defun print-precedence-const (x stream depth)
  (declare (ignore depth))
  (format stream "(~S << ~S)" (task-symbol (precedence-const-precedence x)) (task-symbol (precedence-const-task x))))

;;;
;;; The followings are substitution methods for each constraint.

(cl:defmethod subst-bindings (bindings (x before-const))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-before-const :task (subst-bindings bindings (before-const-task x))
                              :const (subst-bindings bindings (before-const-const x))))))

(cl:defmethod subst-bindings (bindings (x after-const))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-after-const :task (subst-bindings bindings (after-const-task x))
                             :const (subst-bindings bindings (after-const-const x))))))

(cl:defmethod subst-bindings (bindings (x precedence-const))
  (cond ((eq bindings +fail+) +fail+)
        ((eq bindings +no-bindings+) x)
        (t (make-precedence-const :precedence (subst-bindings bindings (precedence-const-precedence x))
                                  :task (subst-bindings bindings (precedence-const-task x))))))

;;;
;;; The precedence constraints are transformed into normal orderings. Function <constraint-orderings>
;;; generates a list of orderings from precedence constraint in <const>.

(defun constraint-orderings (const)
  "collects precedence constraints from <const> and returns a set of task orderings."
  (when const
    (loop for cst in (constraint-set const)
        when (or (ordering-p cst) (precedence-const-p cst))
        collect (cond ((ordering-p cst)
                       cst)
                      ((precedence-const-p cst)
                       (ordering (precedence-const-precedence cst) (precedence-const-task cst)))))))

;;;
;;; The before constraints are transformed into normal precond constraint. Function <constraint-precond>
;;; generates precond from before-constraits in <const>.

(defun constraint-precond (const)
  "collects before constraints from <consts> and returns a set of precond."
  (when const
    (loop for cst in (constraint-set const)
        when (before-const-p cst)
        collect cst)))

;;;
;;; The after constraints are transformed into normal effects. Function <constraint-effects>
;;; generates effects from after-constraints in <const>.

(defun constraint-effects (const)
  "collects after constraints from <const> and returns a set of effects."
  (when const
    (loop for cst in (constraint-set const)
        when (after-const-p cst)
        collect cst)))

;;;
;;; Syntax of before constraint looks like allowing to specify one constraint for :u1 and another constraint for another :u2, 
;;; and so on. However, actually it is not permitted in this implementation. You can only specify either :u0 (designates 
;;; before constrant for task itself) or :u1 (designates the first subtask in subtask list).
;;; Such implemental restriction is the same for after constraint. You can specify either :u0 or the last task-indicator 
;;; in after constraint.

(defun task-orderings-in (method)
  "collects precedence constraints from <method> and returns a set of task orderings."
  (constraint-orderings (method-constr method)))

(defun method-precond (method)
  "collects before constraints from <method> and returns a set of precond."
  (mappend #'before-const-const (constraint-precond (method-constr method))))

(defun method-effects (method)
  "collects after constraints from <method> and returns a set of effects."
  (mappend #'after-const-const (constraint-effects (method-constr method))))

;(defun set-constraint-precond (constraint val)
;  (setf (constraint-precond constraint) val))

(cl:defmethod ground-p ((x method))
  "returns true if method precond in <x> does not include any variable."
  (every #'ground-p (method-precond x)))

;;;
;;;; A Node in Task Network
;;;
;;; A task can turn out a node in task network. In other words, word "node" is synonymous to "task" 
;;; in the context of task network. In this implementation, a type of node is implemented as structure 
;;; that has only task slot. 
;;;
;;; You should use function 'node-task' for retrieving a task from a node instance. 

(defstruct node task)

(defun node-equalp (node1 node2)
  "returns true if the task of <node1> is equal to the task of <node2>."
  (task-equalp (node-task node1) (node-task node2)))

;;;; Task Network
;;; A task network in HTN is composed of nodes and edges.
;;; Nodes in network is a set of tasks, and edges is a set of partial orderings between nodes as node type
;;; rather than task type.

(defstruct network nodes edges)

(defun edge-equal-p (edge1 edge2)
  "returns true if <edge1> is equal to <edge2> as node ordering."
  (or (equalp edge1 edge2)
      (and (node-equalp (ordering-predecessor edge1)
                        (ordering-predecessor edge2))
           (node-equalp (ordering-successor edge1)
                        (ordering-successor edge2)))))

;;;
;;; The minimal set of task network is generated by function <network-of> from one method. 

(defun network-of (method)
  "generates and returns the minimal set of network from <method>.
   Its nodes comprise of subtasks of <method> and its edges are 
   generated from orderings of subtasks in <method>."
  (make-network :nodes (mapcar #'(lambda (tsk) (make-node :task tsk))
                         (method-subtasks method))
                :edges (mapcar #'(lambda (odr)
                                   (ordering (make-node :task (ordering-predecessor odr))
                                             (make-node :task (ordering-successor odr))))
                         (task-orderings-in method))))

;;;
;;; Initially, you may need to find <open node>, namely the node that has no predecessor in the network.
;;;

(defun no-predecessor-p (node network)
  "returns true if there is no occurence of <node> as ordering successor in <network>."
  (notany #'(lambda (e)
              (node-equalp node (ordering-successor e)))
          (network-edges network)))

(defun collect-open-nodes-in (network)
  "returns a set of <open node>s, which are no appearance as successor node in orderings of <network>."
  (remove-if-not #'(lambda (u) (no-predecessor-p u network)) (network-nodes network)))

;;;
;;;; Relevant task and Operator/Method
;;;
;;; In HTN task planning, if a task symbol is same as an operator symbol, the operator 
;;; is called relevant to the task. The terms of task is usually instantiated, then the 
;;; task must be unifiable to the operator in some environment.

(defun relevant-operator-p (task operator &optional (bindings +no-bindings+))
  "returns true if <task> and the task in <operator> is unifiable with <bindings>."
  (and (eq (task-symbol task) (operator-symbol operator))
       (unify (task-terms task) (operator-variables operator) bindings)))

;;;
;;; If a task symbol is same as a task symbol in a method and 
;;; both terms are unifiable, then the method is called relevant to the task.

(defun relevant-method-p (task method &optional (bindings +no-bindings+))
  "returns true if <task> and the task in <method> is unifiable with <bindings>."
  (and (eq (task-symbol task) (task-symbol (method-task method)))
       (unify (task-terms task) (task-terms (method-task method)) bindings)))

(defun relevant-operator-of (task &optional (bindings +no-bindings+))
  "retrieves a relevant operator to <task> from operators defined in system."
  (find task *operators* :test #'(lambda (tsk ope) (relevant-operator-p tsk ope bindings))))

(defun relevant-method-of (task &optional (bindings +no-bindings+))
  "retrieves a relevant method to <task> from methods defined in system."
  (find task *methods* :test #'(lambda (tsk meth) (relevant-method-p tsk meth bindings))))

;;;
;;;; Primitive Task
;;;
;;; A task that has same task symbol as an operator name symbol is called <primitive>. 
;;; A task that is relevant to a method is usally called <non-primitive> or <composite-task>. However, 
;;; if the task in a method is empty, we call the method primitive. It is illegal that
;;; a method has a primitive task in task slot, but any method can have primitive or 
;;; non-primitive tasks in subtasks slot. 
;;; If a node task in network is primitive, then the node is primitive.
;;; If every node in network is primitive, then the network is called primitive.

(defun primitive-p (x)
  "returns true if <x> is a primitive task, method, node, or network."
  (etypecase x
    (task (cond ((find (task-symbol x) *operators* :key #'(lambda (o) (operator-symbol o))) t)
                (t nil)))
    (method (cond ((null (method-task x)) t)
                  ((primitive-p (method-task x))
                   (error "Illegal definition of primitive task:~S" x))
                  (t nil)))
    (node (primitive-p (node-task x)))
    (network (every #'primitive-p (network-nodes x)))))

;;;
;;;; Decomposition of Composite Task (page 235, Definition 11.5)
;;;
;;; Given a node <u> and a method <m> that is relevant to the <u>'s task, the node task is decomposed using subtasks 
;;; in the method. The procedure of decomposition is a little bit complicated, especially for edges.
;;; Let us look up what happens in simple case. 
;;;
;;; Here we have several methods and tasks, task <transfer_one_container> transfers one container 
;;; by setting up a container on a robot, moving it, then finishing it.
;;; Setting-up is done by task <setup> which includes two operator <TAKE> and <LOAD>.
;;; At first, suppose we have only one node for task <transfer_one_container> and no edges in the network. 
;;; Then, the decomposition and the network evolution is like the followings.
;;; ----------------------------------------------------------------------------------
;;; --------------------------------------       -------------------------------------
;;;            Method                                        Network
;;; --------------------------------------       -------------------------------------
;;;                                              nodes:{transfer_one_container}
;;;                                              edges:{ }
;;;  task:transfer_one_container
;;;  subtasks:{setup, move, finish}
;;;  orderings:{setup&lt;&lt;move, move&lt;&lt;finish}
;;;                                              nodes:{setup}
;;;                                              edges:{setup&lt;&lt;move, move&lt;&lt;finish}
;;; --------------------------------------       -------------------------------------
;;; ----------------------------------------------------------------------------------
;;; <transfer_one_container> is open in the network, namely it has no predecessor, then it is picked up
;;; (and deleted from nodes) and its subtasks and the orderings are brought up for discussion. The locally open 
;;; tasks among the subtasks with this orderings are newly added to nodes, that is <setup> here, 
;;; and the orderings for subtasks are also added to edges.
;;;
;;; In the next step, globally open task <setup> in the network is picked up again. Then, the local open task 
;;; in <setup>'s subtasks, that is TAKE, is added into the nodes. An edge that has <setup> as predecessor is picked up, 
;;; then it is replaced with the edge that has an ordering with the closing subtask, namely it does not appear 
;;; in any predecessor of the subtask orderings, that is LOAD here, to the successor of picked edge. 
;;; The subtasks orderings in method are also added into the edges.
;;; ----------------------------------------------------------------------------------
;;; --------------------------------------       -------------------------------------
;;;            Method                                        Network
;;; --------------------------------------       -------------------------------------
;;;                                              nodes:{setup}
;;;                                              edges:{setup&lt;&lt;move, move&lt;&lt;finish}
;;;  task:setup
;;;  subtasks:{TAKE, LOAD}
;;;  orderings:{TAKE&lt;&lt;LOAD}
;;;                                              nodes:{TAKE}
;;;                                              edges:{TAKE&lt;&lt;LOAD, LOAD&lt;&lt;move,
;;;                                                     move&lt;&lt;finish}
;;; --------------------------------------       -------------------------------------
;;; ----------------------------------------------------------------------------------
;;;
;;; The procedure is as follows.
;; # standardize variables in <m>.
;;; # The unifier between task terms in <u> and <m> is computed.
;;; # <m> is substituted with the unifier.
;;; # Let U be a set of nodes in network, calculate (U - {<u>}) and substitute with the unifier above.
;;;   Here {<u>} stands for a set of one element <u>.
;;; # Let E be a set of edges in network, calculate (E - {<e>|pred(<e>)=<u>}), and substitute with the unifier above, 
;;;   where {<e>|pred(<e>)=<u>} is a subset of E of which predecessor is <u>. 
;;; # Collect succ(<e>|pred(<e>)=<u>) from E, and substitute with the unifier above.
;;; # Let Um be nodes from <m>'s subtasks, U = union(U - {<u>}, Um'). Where Um' = ({<sub>} - {succ(<o>)}), 
;;;   and {<sub>} denotes nodes from subtasks of <m>, and <o> denotes one of (every) task orderings in <m>. 
;;;   Therefore, Um' means a collection of open nodes in subtasks.
;;; # Let Em be edges from <m>, E = union(E - {<e>|pred(<e>)=<u>}, Em, {<v>&lt;&lt;<u'>|succ(<e>|pred(<e>)=<u>)=<u'>}). 
;;;   Where Em denotes edges generated from subtask orderings of <m>.
;;;   <v> denotes one of closing subtasks of <m>, then {<v>&lt;&lt;<u'>|succ(<e>|pred(<e>)=<u>)=<u'>} denotes 
;;;   the replacement of {<u>&lt;&lt;<u'>} to {<v>&lt;&lt;<u'>} in decomposition <m>.

(defun decompose (node network method binds)
  "returns new network with decomposition of <node>.
   <method> is relevant to this <node>."
  ;(setq method (rename-variables method))
  (format t "~%Decomposing ~S~% in ~S~% with ~S~% bindings ~S" node network method binds)
  (setq binds
        (unify (task-terms (method-task method))
               (task-terms (node-task node))
               binds))
  (format t "~%Task terms matching caused bindings evolution ~S." binds)
  (setq method (subst-bindings binds method))
  (format t "~%Refined:~S" method)
  (let ((rest-nodes (subst-bindings binds
                                    (remove node (network-nodes network)
                                            :test #'node-equalp)))
        (next-nodes (subst-bindings binds
                                    (mapcar #'ordering-successor
                                      (remove node (network-edges network) 
                                              :key #'ordering-predecessor
                                              :test-not #'node-equalp))))
        (rest-edges (subst-bindings binds
                                    (remove node (network-edges network)
                                            :key #'ordering-predecessor
                                            :test #'node-equalp)))
        #|
        (relevant-edges (subst-bindings binds
                                        (remove node (network-edges network)
                                                :key #'ordering-predecessor
                                                :test-not #'node-equalp))) |#
        (subtasks (method-subtasks method))
        (orderings (task-orderings-in method)))
    (format t "~%Rest nodes: ~S" rest-nodes)
    (format t "~%Next nodes: ~S" next-nodes)
    (format t "~%Rest edges: ~S" rest-edges)
    (let ((open-subtasks (set-difference subtasks
                                         (mapcar #'(lambda (o) (ordering-successor o))
                                           orderings)
                                         :test #'task-equalp))
          (close-subtasks (remove-if-not
                           #'(lambda (sub)
                               ;; completely closed sub?
                               (notany #'(lambda (o) (task-equalp sub (ordering-predecessor o)))
                                       orderings))
                           subtasks)))
      (format t "~%Open subtasks: ~S" open-subtasks)
      (format t "~%Close subtasks: ~S" close-subtasks)
      (make-network :nodes (union 
                            (if open-subtasks
                                (mapcar #'(lambda (tsk) (make-node :task tsk)) open-subtasks)
                              next-nodes)
                            rest-nodes :test #'node-equalp)
                    :edges (union (mapcar #'(lambda (ordr)
                                              (ordering (make-node
                                                         :task (ordering-predecessor ordr))
                                                        (make-node
                                                         :task (ordering-successor ordr))))
                                    (reverse orderings))
                                  (union (mapcan
                                             #'(lambda (next)
                                                 (mapcar #'(lambda (cls)
                                                             (ordering (make-node :task cls) next))
                                                   close-subtasks))
                                           next-nodes)
                                         rest-edges :test #'edge-equal-p)
                                  :test #'edge-equal-p)))))

;;;
;;;; Evolution of Network for Primitive Task
;;;
;;; The algorithm of network evolution for primitive task is much simpler than non-primitive task, because there is 
;;; no method and no decomposition. 
;;;
;;; With a global open node <u> in the network and <unifier>, 
;;; # Compute the relevant edges {<e>|pred(<e>)=<u>} from network edges.
;;; # Compute the unrelevant edges {<e>|pred(<e>)/=<u>} from network edges.
;;; # Compute the open nodes ({succ(<e>|pred(<e>)=<u>)} - {succ(<e>|pred(<e>)/=<u>)}).
;;; # Let U be a set of nodes in network, U = substitution with <unifier> of 
;;;   union(U - {<u>}, {succ(<e>|pred(<e>)=<u>)} - {succ(<e>|pred(<e>)/=<u>)})
;;; # Let E be a set of edges in network, E = substitution of {<e>|pred(<e>)/=<u>} with <unifier>.
;;; Note that every node in nodes are open, and the successors of node tasks will be added, 
;;; if it will be open, when the predecessors are removed from network. 

(defun evolve-network (node network binds)
  "returns a network evolved by doing the task of <node>."
  (let ((rest-nodes (remove node (network-nodes network) :test #'node-equalp))
        (rest-edges (remove node (network-edges network)
                            :key #'ordering-predecessor
                            :test #'node-equalp))
        (relevant-edges (remove node (network-edges network)
                                :key #'ordering-predecessor
                                :test-not #'node-equalp)))
    (let ((open-nodes (set-difference (mapcar #'(lambda (edge) (ordering-successor edge)) relevant-edges)
                                      (mapcar #'(lambda (edge) (ordering-successor edge)) rest-edges)
                                      :test #'node-equalp)))
      (let ((nodes (union open-nodes rest-nodes :test #'node-equalp)))
        (format t "~%Evolving Nodes:~S -> ~S" (network-nodes network) nodes binds)
        (format t "~%Evolving Edges:~S -> ~S~%     bindings ~S" (network-edges network) rest-edges binds)
        (make-network :nodes (subst-bindings binds nodes)
                      :edges (subst-bindings binds rest-edges))))))

;;;
;;;; Ground Task
;;;
;;; A state variable that does not include any variable symbol is called <ground>.
;;; An operator and action that has no variable in its precond is called <ground>.
;;; A method of which precond has no variable is called <ground>.
;;; A task of which relevant method or operator is ground is called <ground>.

(cl:defmethod ground-p ((x task))
  "returns true if relevant operator/method to <x> is ground."
  (if (primitive-p x) (ground-p (relevant-operator-of x))
    (ground-p (relevant-method-of x))))

(cl:defmethod ground-p ((x node))
  "returns true if the node task of <x> is ground."
  (ground-p (node-task x)))

(cl:defmethod ground-p ((x network))
  "returns true if every node in <x> is ground."
  (every #'ground-p (network-nodes x)))

;;;
;;;; Applicability
;;;
;;; If a precond of operator is satisfied by <state>, it is called <applicable>.
;;; Namely, if every statevar in a precond of an operator can be unified with some statevar in <state>, 
;;; then the operator is called <applicable> in <state>.
;;; If a precond of method is satisfied by <state>, the method is called <applicable>.

(cl:defmethod applicable-p ((x operator) state &optional (bindings +no-bindings+))
  "returns a list of new bindings resulted by unification between precond of <x> 
   and <state> with <bindings>."
  (unless (eq bindings +fail+)
    (let ((bindings-list (precond-unify (operator-precond x) state bindings)))
      (when (not (eq (car bindings-list) +fail+))
        bindings-list))))

(cl:defmethod applicable-p ((x method) state &optional (bindings +no-bindings+))
  "returns a list of new bindings resulted by unification between precond of <x> 
   and <state> with <bindings>."
  (unless (eq bindings +fail+)
    (let ((bindings-list (precond-unify (method-precond x) state bindings)))
      (when (not (eq (car bindings-list) +fail+))
        bindings-list)
      )))

(defun activate-operator (operator bindings)
  "instantiates <operator> with <bindings>."
  (subst-bindings bindings operator))

(defun activate-method (method bindings)
  "instantiates <method> with <bindings>."
  (subst-bindings bindings method))

;;;; Lifted-PFD (Parital-order Forward Decomposition) Procedure (Figure 11.9)
;;; The procedure of Lifted-PFD in this implementation is as follows.
;;; 
;;; With given parameters <state>, <goal>, <network>, and <plan>,
;;;  # If <state> satisfies <goal> then returns value of <plan>.
;;;  # If nodes in <network> is empty returns failure.
;;;  # Otherwise, undeterministically choose one <open node> in <network>. If it is primitive then do primitive task 
;;;    procedure (4) else do non-primitive procedure (7).
;;;  # If primitive, getting applicable operators that relevant to the node chosen, and activate them.
;;;  # If there is no active action, then fail, and backtrack is caused.
;;;  # If there are actions (applicable and activated operator), undeterministically chooses one action then 
;;;    progresses the <state>, evolves the network and recursively calls with accumlated action in <plan>.
;;;  # If non-primitive, getting applicable methods that relevant to the node chosen, and activate them.
;;;  # If there is no active method, then fail, and backtrack is caused.
;;;  # If there are active methods (applicable and activated methods), undeterministically choose one method 
;;;    and decompose the task, and recursively calls with new network.

(defvar *global-counter* 0)
(defvar *global-counter-limit* 700)

(=defun Lifted-PFD (state goal network plan)
        (format t "~%Plan:~S" (mapcar #'operator-name plan))
        (format t "~%Network:~S" network)
        (cond ((satisfy-p state goal) (=values (reverse plan)))
              ((null (network-nodes network)) (fail))
              ((= *global-counter* *global-counter-limit*) 
               (error "Global counter limit exceed."))
              ((and (> *global-counter* 5)
                    (subsetp state *state* :test #'statevar-equalp)
                    (subsetp *state* state :test #'statevar-equalp))
               (fail))
              (t
               (incf *global-counter*)
               (choose-bind node (collect-open-nodes-in network)
                            (format t "~%Node chosen:~S" node)
                            (if (primitive-p node)
                                ;; primitive task
                                (let ((active
                                       (loop for ope in *operators* with bindings-list
                                           do (setq ope (rename-variables ope))
                                           when (setq bindings-list
                                                      (applicable-p ope state
                                                                    (relevant-operator-p (node-task node) ope)))
                                           append (mapcar #'(lambda (bindings)
                                                              (relevant
                                                               (activate-operator ope bindings)
                                                               bindings))
                                                    bindings-list))))
                                  (setq active
                                        (remove-if #'(lambda (a)
                                                       (reverse-action-p (relevant-operator a)
                                                                         plan))
                                                   active))
                                  ;(format t "~%Active:~S" active)
                                  (if (null active) (fail)
                                    (choose-bind a active
                                                 (format t "~%Relevant chosen:~S" a)
                                                 (Lifted-PFD
                                                  (progress-action 
                                                   (relevant-operator a) state)
                                                  goal
                                                  (evolve-network node network
                                                                  (relevant-bindings a))
                                                  (cons (relevant-operator a) plan)))))
                              ;; non-primitive task
                              (let ((active
                                     (loop for method in *methods* with bindings-list
                                         do (setq method (rename-variables method))
                                         when (setq bindings-list 
                                                    (applicable-p method state
                                                                  (relevant-method-p (node-task node) method)))
                                         append (mapcar #'(lambda (bindings)
                                                            (relevant
                                                             (activate-method method bindings)
                                                             bindings))
                                                  bindings-list))))
                                (format t "~%Active:~S" active)
                                (if (null active) (fail)
                                  (choose-bind m active
                                               ;(format t "~%Chosen:~S" m)
                                               (Lifted-PFD state goal
                                                           (decompose node network
                                                                      (relevant-method m)
                                                                      (relevant-bindings m))
                                                           plan)))))))))

(defun relevant-method (relevant)
  (car relevant))

(defun reverse-action-p (action plan)
  (when plan
    (let ((previous (car plan)))
      (negate-state-p (operator-effects action) (operator-effects previous)))))

(defun negate-state-p (state1 state2)
  (and (subsetp state1 state2 :test #'statevar-opposite-p)
       (subsetp state2 state1 :test #'statevar-opposite-p)))
    

#|
(in-package :plan)
;;--------------------------------------------------------
;; pallet and pile is only one on each location.
(defoperator "MOVE(r,l,m)"
  "robot $r moves from location $l to an adjacent location $m"
  :precond "         at(r)=l,~occupied(m),adjacent(l,m)"
  :effects "at(r)=m,~at(r)=l, occupied(m),~occupied(l)")
(defoperator "LOAD(k,l,c,r)"
  "crane $k at location $l loads container $c onto robot $r"
  :precond "belong(k,l),holding(k)=c,  at(r)=l,   unloaded(r)"
  :effects "empty(k),  ~holding(k)=c,loaded(r)=c,~unloaded(r)")
(defoperator "UNLOAD(k,l,c,r)"
  "crane $k at location $l takes container $c from robot $r"
  :precond " empty(k),belong(k,l), at(r)= l,    loaded(r)=c"
  :effects "~empty(k),holding(k)=c,unloaded(r),~loaded(r)=c")
(defoperator "PUT(k,l,c,d,p)"
  "crane $k at location $l puts $c onto $d in pile $p"
  :precond "belong(k,l),attached(p)=l,holding(k)=c,top(d)=p"
  :effects "~holding(k,c),empty(k),in(c)=p,top(c)=p,on(c)=d,~top(d,p)")
(defoperator "TAKE(k,l,c,d,p)"
  "crane $k at location $l takes $c off $d in pile $p"
  :precond "belong(k,l),attached(p)=l,empty(k),          top(c)=p, on(c)=d"
  :effects "holding(k)=c,            ~empty(k),~in(c)=p,~top(c)=p,~on(c)=d,top(d)=p")

(setq *state*
      (state
       "{attached(p1,loc1),attached(p2,loc2),
         in(c1,p1),top(c1,p1),on(c1,pallet),
         top(pallet,p2),
         belong(crane1,loc1),belong(crane2,loc2),empty(crane1),empty(crane2),adjacent(loc1,loc2),adjacent(loc2,loc1),
         at(r1,loc1),occupied(loc1),unloaded(r1)}"))
(setq *goal* (state "{in(c1,p2),top(c1,p2)}"))

(setq top
(define-method "transfer1(c,l,m,r)"
  :task "transfer_one_container(c,l,m,r)"
  :subtasks "setup(c,r),move_robot(l,m),finish(c,r)"
  :constr ":u1<<:u2,:u2<<:u3")
)
(define-method "move1(r,l,m)"
  :task "move_robot(l,m)"
  :subtasks "MOVE(r,l,m)"
  :precond "at(r)=l")
(define-method "move0(r,l,m)"
  :task "move_robot(l,m)"
  :precond "at(r)=m")
(define-method "do_setup(c,d,k,l,p,r)"
  :task "setup(c,r)"
  :subtasks "TAKE(k,l,c,d,p),LOAD(k,l,c,r)"
  :precond "on(c)=d,attached(p)=l,in(c)=p,belong(k)=l,at(r)=l"
  :constr ":u1<<:u2")
(define-method "unload_robot(c,d,k,l,p,r)"
  :task "finish(c,r)"
  :subtasks "UNLOAD(k,l,c,r),PUT(k,l,c,d,p)"
  :precond "attached(p)=l,loaded(r,c),top(d)=p,belong(k)=l,at(r)=l"
  :constr ":u1<<:u2")

(setq *global-counter* 0)
(Lifted-PFD *state* *goal*
     (make-network :nodes (list (make-node :task (method-task top))
                                )
                   :edges nil)
     ())
(trace =Lifted-PFD)
;;--------------------------------------------------------
(in-package :plan)
;; Figure 11.5
(setq *state*
      (state
       "{attached(p11,loc1), attached(p12,loc1),
         attached(p21,loc2), attached(p22,loc2),
         in(c1,p11),         in(c2,p12),
         top(c1,p11),        top(c2,p12),
         on(c1,pallet),      on(c2,pallet),
         top(pallet,p21),    top(pallet,p22),
         belong(crane1,loc1),belong(crane2,loc2),
         empty(crane1),      empty(crane2),
         adjacent(loc1,loc2),adjacent(loc2,loc1), 
         at(r1,loc1),        occupied(loc1),
         unloaded(r1)}"))
;; final goal
(setq *goal*
      (state
       "{in(c1,p21),in(c2,p22),top(c1,p21),top(c2,p22)}"))
;; Intermediate point
(setq *subgoal*
      (state
       "{in(c1,p21),top(c1,p21),at(r1,loc1)}"))

(setq top
(define-method "transfer2(c,d,l,m,r)"
  :task "transfer_two_containers(c,d,l,m,r)"
  :subtasks "transfer_one_container(c,l,m,r),transfer_one_container(d,l,m,r)"
  :orderings ":u1<<:u2")
)
(define-method "transfer1(c,l,m,r)"
  :task "transfer_one_container(c,l,m,r)"
  :subtasks "setup(c,r),move_robot(l,m),finish(c,r)"
  :orderings ":u1<<:u2,:u2<<:u3")
(setq top2
(define-method "move1(r,l,m)"
  :task "move_robot(l,m)"
  :subtasks "MOVE(r,l,m)"
  :precond "at(r)=l")
)
(define-method "move0(r,l,m)"
  :task "move_robot(l,m)"
  :precond "at(r)=m")
(define-method "do_setup(c,d,k,l,p,r)"
  :task "setup(c,r)"
  :subtasks "move_robot(m,l),TAKE(k,l,c,d,p),LOAD(k,l,c,r)"
  :precond "on(c)=d,attached(p)=l,in(c)=p,belong(k)=l,empty(k),unloaded(r),top(c)=p" ; no precond with at(l)
  :orderings ":u1<<:u2,:u2<<:u3")
(define-method "unload_robot(c,d,k,l,p,r)"
  :task "finish(c,r)"
  :subtasks "UNLOAD(k,l,c,r),PUT(k,l,c,d,p)"
  :precond "attached(p)=l,loaded(r)=c,top(d)=p,belong(k)=l,at(r)=l,empty(k)"
  :orderings ":u1<<:u2")
;;--------------------------------------------------------
(defoperator "MOVE(r,l,m)"
  "robot r moves from location l to an adjacent location m"
  :precond "         at(r)=l,~occupied(m),adjacent(l,m)"
  :effects "at(r)=m,~at(r)=l, occupied(m),~occupied(l)")
(defoperator "LOAD(k,l,c,r)"
  "crane k at location l loads container c onto robot r"
  :precond "belong(k,l),holding(k)=c,  at(r)=l,   unloaded(r)"
  :effects "empty(k),  ~holding(k)=c,loaded(r)=c,~unloaded(r)")
(defoperator "UNLOAD(k,l,c,r)"
  "crane k at location l takes container c from robot r"
  :precond " empty(k),belong(k,l), at(r)= l,    loaded(r)=c"
  :effects "~empty(k),holding(k)=c,unloaded(r),~loaded(r)=c")
(defoperator "PUT(k,l,c,d,p)"
  "crane k at location l puts c onto d in pile p"
  :precond "belong(k,l),attached(p)=l,holding(k)=c,top(d)=p"
  :effects "~holding(k,c),empty(k),in(c)=p,top(c)=p,on(c)=d,~top(d,p)")
(defoperator "TAKE(k,l,c,d,p)"
  "crane k at location l takes c off d in pile p"
  :precond "belong(k,l),attached(p)=l,empty(k),          top(c)=p, on(c)=d"
  :effects "holding(k)=c,            ~empty(k),~in(c)=p,~top(c)=p,~on(c)=d,top(d)=p")

(trace =Lifted-PFD)
(trace applicable-p)
(trace precond-unify)
(trace decompose)
(trace evolve-network)
(trace progress-action)
(setq *global-counter* 0)
(Lifted-PFD *state* *goal*
     (make-network :nodes (list (make-node :task (rename-variables (method-task top)))
                                ;(make-node :task (rename-variables (method-task top2)))
                                )
                   :edges nil)
     ())
;;--------------------------------------------------------
;; Example 11.11
(define-method "transfer2(c,d,l,m,r)" "method to move c and d from pile p1 to pile p2"
  :task "transfer_two_containers(c,d,l,m,r)"
  :subtasks "transfer_one_container(c,l,m,r),transfer_one_container(d,l,m,r)"
  :constr ":u1<<:u2")
(define-method "transfer1(c,l,m,r)" "method to transfer c"
  :task "transfer_one_container(c,l,m,r)"
  :subtasks "setup(c,r),move_robot(r,l,m),finish(c,r)"
  :constr ":u1<<:u2,:u2<<:u3")
(define-method "move1(r,l,m)" "method to move r if its is not at m"
  :task "move_robot(l,m)"
  :subtasks "move(r,l,m)"
  :constr "before({:u1},at(r,l))")
(define-method "move0(r,l,m)" "method to do nothing if r is already at m"
  :task "move_robot(l,m)"
  :subtasks nil
  :constr "before({:u0},at(r,l))")
(define-method "do_setup(c,d,k,l,p,r)" "method to prepare for moving a container"
  :task "setup(c,r)"
  :subtasks "take(k,l,c,d,p),load(k,l,c,r)"
  :constr ":u1<<:u2,before({:u1},on(c)=d),before({:u1},attached(p)=l),
           before({:u1},in(c)=p),before({:u1},belong(k)=l),before({:u1},at(r)=l),
           before({:u1},empty(k)),before({:u1},unloaded(r)),before({:u1},top(c)=p)")
(define-method "unload-robot(c,d,k,l,p,r)" "method to finish after moving a container"
  :task "finish(c,r)"
  :subtasks "unload(k,l,c,r),put(k,l,c,d,p)"
  :constr ":u1<<:u2,before({:u1},attached(p,l)),before({:u1},loaded(r,c)),
           before({:u1},top(d,p)),before({:u1},belong(k,l)),before({:u1},at(r,l))")
|#