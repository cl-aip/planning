;;;  -*- Mode: Lisp; Syntax: Common-Lisp -*-
;;;
;;; Automated Planning - Theory and Practice
;;;  by Malik Ghallab, Dana Nau, and Paolo Traverso, from Morgan Kaufmann
;;;  programmed by Seiji Koide
;;;  2008 (c) Seiji Koide
;;;
;;; This system handling system is bollowed from AIMA by Norvig, and modified by Seiji.
;;;

;;;; Vendor-Specific Customizations

;; by Seiji
;; in order to compile, macro definitions are needed. The followings are 
;; taken from ACL8.0 source files.
#+allegro
(eval-when (compile load eval)
  (defmacro assoc-guts (test-guy)
    `(do ((alist alist (cdr alist)))
         ((endp alist))
       (if* (car alist)
          then (if* ,test-guy then (return (car alist))))))
  (defmacro funcall-key (elt)
    ;; for use in sequence files, if key is non nil it is a guaranteed
    ;; function object; use it to extract the element, else assume 'identity'
    `(if* key
        then (funcall (the function key) ,elt)
        else ,elt))
  )
;; by Seiji
;; cl:sublis must be redefined as follows in order to function AIMA.
;; However, Franz insists that this code and AIMA does not fit the specification of 
;; sublis which Franz considers.
#+allegro
(excl:without-package-locks 
    (defun sublis (alist tree
                         &key key
                         (test #'eql)
                         (test-not nil notp))
      ;; Substitutes from alist into tree nondestructively.
      (declare (dynamic-extent key test test-not))
      (setq key (excl::ensure-function-object key :key #'identity))
      (labels ((s (subtree)
                  (let* ((key-val (funcall-key subtree))
                         (assoc
                          (if notp
                              (assoc-guts (not (funcall test-not
                                                        key-val
                                                        (caar alist))))
                            (assoc-guts (funcall test
                                                 key-val
                                                 (caar alist))))))
                    (cond (assoc (cdr assoc))
                          ((atom subtree) subtree)
                          ; by seiji begin
                          ((null (cdr subtree))
                           (let ((car (s (car subtree))))
                             (if (eq car (car subtree))
                                 subtree
                               (list car))))
                          ; by seiji end
                          (t (let ((car (s (car subtree)))
                                   (cdr (s (cdr subtree))))
                               (if (and (eq car (car subtree))
                                        (eq cdr (cdr subtree)))
                                   subtree
                                 (cons car cdr))))))))
        (s tree)))
  )

#+Lucid (setq *warn-if-no-in-package* nil)

;; 6oct05 charley cox
;; print-structure symbol conflicts with existing symbol in Allegro Common
;; Graphics
;; by Seiji
;; eval-when environment added
#+allegro
(eval-when (compile load eval)
  (shadow 'print-structure)
  )

;;;; A minimal facility for defining systems of files

(defparameter *planning-system-names* nil
  "A list of names of the systems that have been defined.")

(defstruct planning-system
  name (requires nil) (doc "") (parts nil) (examples nil) (loaded? nil))

(defun target-system-requires (system)
  (loop for mod in (ds:modules system)
      when (get-target-system mod)
      collect it))

(defun target-system-parts (system)
  (loop for mod in (ds:modules system)
      when (typep mod 'ds:default-module)
      collect mod))

;;;; The Top-Level Functions:

(defmacro def-planning-system (name requires doc &body parts)
  "Define a system as a list of parts.  A part can be a string, which denotes
  a file name; or a symbol, which denotes a (sub)system name; or a list of the
  form (subdirectory / part...), which means the parts are in a subdirectory.
  The <requires> argument is a list of systems that must be loaded before this 
  one.  Note that a documentation string is mandatory."
  `(add-planning-system :name ',name
                        :requires ',requires :doc ',doc :parts ',parts))

;;;; Support Functions

(defun add-planning-system (&key name requires doc parts examples)
  (pushnew name *planning-system-names*)
  (setf (get 'planning-system name)
    (make-planning-system :name name :examples examples
                          :requires requires :doc doc :parts parts)))

(defun get-target-system (name)
  "Return the system with this name.  (If argument is a system, return it.)"
  (cond ((typep name 'ds:default-system) name)
        ((symbolp name) (find-system name))
        (t nil)))

(defun operate-on-target-system (target part operation &key (path nil) (load t)
                                        (directory-operation #'identity))
  "Perform the operation on the part (or system) and its subparts (if any).
  Reasonable operations are load, load-binary, compile-load, and echo.
  If LOAD is true, then load any required systems that are unloaded."
  (let (system)
    (cond
     ((typep part 'ds:default-module) (funcall operation (ds:source-pathname part)))
     ((stringp part) (funcall operation (target-file part :planning :path path)))
     ((and (consp part) (eq (second part) '/))
      (let* ((subdirectory (mklist (first part)))
             (new-path (append path subdirectory)))
        (funcall directory-operation new-path)
        (dolist (subpart (nthcdr 2 part))
          (operate-on-target-system target subpart operation :load load 
                                    :path new-path
                                    :directory-operation directory-operation))))
     ((consp part)
      (dolist (subpart part)
        (operate-on-target-system target subpart operation :load load :path path
                                  :directory-operation directory-operation)))
     ((setf system (get-target-system part))
      ;; Load the required systems, then operate on the parts
      (load-system system)
      (operate-on-target-system target (target-system-parts system) operation
                                :load load :path path
                                :directory-operation directory-operation))
     (t (warn "Unrecognized part: ~S in path ~A" part path)))))

(defun target-file (name system &key (type nil) (path nil))
  "Given a file name and maybe a file type and a relative path from the 
  Planning directory, return the right complete pathname."
  (make-pathname :name name :type type :defaults #+:asdf (asdf:component-pathname (asdf:find-system system))
                                                 #-:asdf (ds:default-pathname (find-system system))
                 :directory (append (pathname-directory #+:asdf (asdf:component-pathname (asdf:find-system system))
                                                        #-:asdf (ds:default-pathname (find-system system)))
                                    (mklist path))))

(defun mklist (x)
  "If x is a list, return it; otherwise return a singleton list, (x)."
  (if (listp x) x (list x)))

;;; ----------------------------------------------------------------------
;;;; Definitions of Systems
;;; ----------------------------------------------------------------------

(def-planning-system :utils ()
  "Basic functions that are loaded every time, and used by many other systems."
  ("utils" / "callcc" "utilities"))

(def-planning-system :FOL (:utils)
  "First Order Logics functions that are used as utilities in planning system."
  ("fol" / "infix" "unify" "normal" "fol"))

(def-planning-system :plan (:FOL)
  "Planning program"
  ("plan" / "statespace" "operator" "FrwdBkwd" "STRIPS" "planspace" "PSP" "STN"))

(def-planning-system all ()
  "All systems except the utilities system, which is always already loaded"
  fol plan)

(def-planning-system everything ()
  "All the code, including the utilities"
  utils all)

(setf *planning-system-names* (nreverse *planning-system-names*))

;;;; Always load the utilities
;; by Seiji
;(when (string= "nIL" (symbol-name (read-from-string "nIL")))
;  (cerror
;   "Continue loading Planning code."
;   "Lisp reader is case-sensitive.  Some Planning code may not work correctly."))

(load-system :utils)

#|
> :cd C:\allegro-projects\planning
> :ld planning
> (planning-compile 'utils)
> (planning-compile 'fol)
> (planning-load 'plan)
;; OR
> (planning-compile)
> (planning-load)
;; test
> (test 'utils)
> (test 'search)
> (test 'logic)
|#
