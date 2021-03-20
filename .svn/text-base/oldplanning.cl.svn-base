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

(defparameter *planning-root* (truename "C:\\\allegro-projects\\\planning\\")
  "The root directory where the code is stored.")

(defparameter *planning-binary-type*
  (first (list   ; <<<<<<<<<<<<<<<<<<<< Edit this <<<<<<<<<
          #+Lispworks system::*binary-file-type*
          #+Lucid (first lucid::*load-binary-pathname-types*)
          #+allegro excl:*fasl-default-type*
          #+(or AKCL KCL) "o"
          #+CMU "sparcf"
          #+CLISP "fas"))
  "If calling planning-load loads your source files and not your compiled
  binary files, insert the file type for your binaries before the <<<<
  and load systems with (planning-load-binary NAME).")

(defconstant *planning-version*
    "0.01 Planning Code, April Fool Version, 01-Apr-2008")

(defparameter *planning-system-names* nil
  "A list of names of the systems that have been defined.")

(defstruct planning-system
  name (requires nil) (doc "") (parts nil) (examples nil) (loaded? nil))

;;;; The Top-Level Functions:

(defmacro def-planning-system (name requires doc &body parts)
  "Define a system as a list of parts.  A part can be a string, which denotes
  a file name; or a symbol, which denotes a (sub)system name; or a list of the
  form (subdirectory / part...), which means the parts are in a subdirectory.
  The <requires> argument is a list of systems that must be loaded before this 
  one.  Note that a documentation string is mandatory."
  `(add-planning-system :name ',name
                        :requires ',requires :doc ',doc :parts ',parts))

(defun planning-load (&optional (name 'all))
  "Load file(s), trying the system-dependent method first."
  (operate-on-planning-system name 'load-something))

(defun planning-load-binary (&optional (name 'all))
  "Load file(s), prefering binaries to source."
  (operate-on-planning-system name 'load-binary))			  

(defun planning-compile (&optional (name 'everything))
  "Compile (and load) the file or files that make up an Planning system."
  (operate-on-planning-system name 'compile-load))

(defun planning-load-if-unloaded (name)
  (let ((system (get-planning-system name)))
    (unless (and system (planning-system-loaded? system))
      (planning-load system))
    system))

;;;; Support Functions

(defun add-planning-system (&key name requires doc parts examples)
  (pushnew name *planning-system-names*)
  (setf (get 'planning-system name)
    (make-planning-system :name name :examples examples
                          :requires requires :doc doc :parts parts)))

(defun get-planning-system (name)
  "Return the system with this name.  (If argument is a system, return it.)"
  (cond ((planning-system-p name) name)
        ((symbolp name) (get 'planning-system name))
        (t nil)))

(defun operate-on-planning-system (part operation &key (path nil) (load t)
                                        (directory-operation #'identity))
  "Perform the operation on the part (or system) and its subparts (if any).
  Reasonable operations are load, load-binary, compile-load, and echo.
  If LOAD is true, then load any required systems that are unloaded."
  (let (system)
    (cond
     ((stringp part) (funcall operation (planning-file part :path path)))
     ((and (consp part) (eq (second part) '/))
      (let* ((subdirectory (mklist (first part)))
             (new-path (append path subdirectory)))
        (funcall directory-operation new-path)
        (dolist (subpart (nthcdr 2 part))
          (operate-on-planning-system subpart operation :load load 
                                      :path new-path
                                      :directory-operation directory-operation))))
     ((consp part)
      (dolist (subpart part)
        (operate-on-planning-system subpart operation :load load :path path
                                    :directory-operation directory-operation)))
     ((setf system (get-planning-system part))
      ;; Load the required systems, then operate on the parts
      (when load (mapc #'planning-load-if-unloaded (planning-system-requires system)))
      (operate-on-planning-system (planning-system-parts system) operation
                                  :load load :path path
                                  :directory-operation directory-operation)
      (setf (planning-system-loaded? system) t))
     (t (warn "Unrecognized part: ~S in path ~A" part path)))))

(defun planning-file (name &key (type nil) (path nil))
  "Given a file name and maybe a file type and a relative path from the 
  Planning directory, return the right complete pathname."
  (make-pathname :name name :type type :defaults *planning-root*
                 :directory (append (pathname-directory *planning-root*)
                                    (mklist path))))

#-MCL ;; Macintosh Common Lisp already defines this function
(defun compile-load (file)
  "Compile file and then load it."
  ;; This could be made more sophisticated, to compile only when out of date.
  (compile-file (file-with-type file "cl"))
  (load-binary file))

(defun load-binary (file)
  "Load file, trying the binary first, but loading the source if necessary."
  (load-something file '(binary nil "cl")))

(defun load-something (file &optional (types '(nil binary "cl")))
  "Try each of the types in turn until we get a file that loads.
  Complain if we can't find anything.  By default, try the system-dependent
  method first, then the binary, and finally the source (lisp) file."
  (dolist (type types (warn "Can't find file: ~A" file))
    (when (load (file-with-type file type) :if-does-not-exist nil)
      (return t))))

(defun file-with-type (file type)
  "Return a pathname with the given type."
  (if (null type)
      file
    (merge-pathnames
     (make-pathname :type (if (eq type 'binary) *planning-binary-type* type))
     file)))

(defun mklist (x)
  "If x is a list, return it; otherwise return a singleton list, (x)."
  (if (listp x) x (list x)))

;;; ----------------------------------------------------------------------
;;;; Definitions of Systems
;;; ----------------------------------------------------------------------

(def-planning-system utils ()
  "Basic functions that are loaded every time, and used by many other systems."
  ("utils" / "callcc" "utilities"))

(def-planning-system fol (utils)
  "First Order Logics functions that are used as utilities in planning system."
  ("fol" / "infix" "unify" "normal" "fol"))

(def-planning-system plan (fol)
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

(planning-load 'utils)

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
