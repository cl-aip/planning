;;;-*- mode: common-lisp; syntax: common-lisp; base: 10 -*-
;;;
;;; Automated Planning - Theory and Practice
;;;  by Malik Ghallab, Dana Nau, and Paolo Traverso, from Morgan Kaufmann
;;;  programmed by Seiji Koide
;;;  2008 (c) Seiji Koide
;;;
;;; This indexing system is bollowed from AIMA by Norvig, and modified by Seiji.
;;;

;;;; Make an Index to all the Lisp Functions, Variables, and Types

(defparameter *planning-root* #.*load-pathname*
  "The root directory where the code is stored.")

(let ((*default-pathname-defaults* #.*load-pathname*))
  (load "planning.cl"))

(defparameter *files* ())

(map-system :planning 
            '(lambda (module) (setq *files* (cons (slot-value module 'defsystem::file) *files*)))
            )

(setq *files* (nreverse *files*))

(defun planning-file (name &key (type nil) (path nil))
  "Given a file name and maybe a file type and a relative path from the 
  planning directory, return the right complete pathname."
  (make-pathname :name name :type type :defaults *planning-root*
                 :directory (append (pathname-directory *planning-root*)
                                    (mklist path))))

;;; Just call (gen-index) to produce output in the files
;;; "entries.html", and "overview-*.html" in the code/doc directory.
;;; All the names of definitions will be listed, alphabetically in
;;; entries.html, and in overview.html you will get a
;;; function-by-function listing with name, parameteres, and
;;; documentation strings.  Comments with three semicolons (like this
;;; one) will be printed in the overview, and comments with 4
;;; semicolons will be printed as a section header.

(defmacro do-file ((var file &key (by '#'read)) &body body)
  "Execute body with <var> bound to succesive expressions from <file>."
  `(block nil (map-file #'(lambda (,var) ,@body) ,file :read ,by)))

(defun map-file (fn file &key (read #'read))
  "Apply fn to every expression in file."
  (with-open-file (s file :direction :input)
    (let ((eof "EOF"))
      (do ((x (funcall read s nil eof) (funcall read s nil eof)))
          ((eq x eof) nil)
        (funcall fn x)))))

(defparameter *user-symbols* (make-hash-table :test #'eq)
  "Table with a count of uses and definitions of each user symbol.")

(defvar *cl-symbols* (make-hash-table :test #'eq)
  "Table with a count of uses of each built-in Common Lisp symbol.")

(defvar *counts* '(total 0) 
  "Count of definitions, files, etc.")

(defvar *planning-system* nil "Keep track of current system.")

(defstruct (entry (:type list))
  "An entry representing a name, number of uses and all its definitions."
  name (count 0) (page nil) (defs nil))

(defstruct def
  "A def is a definition: a kind (function, variable, etc), system
  file (or page number) and for defmethods, the type of the first argument."
  ;; Note that file is currently unused, except for page numbers
  kind system file arg-type)

(defun gen-index (&optional (system-names *planning-system-names*))
  "Create the index of all functions, variables, etc. in all files."
  (clrhash *user-symbols*)
  (clrhash *cl-symbols*)
  (record-book-pages)
  (setf *counts* '(total 0))
  (gen-overview system-names)
  (gen-entries (planning-file "entries" :type "html" :path '("doc"))))

(defun gen-overview (system-names)
  ;; Loop through systems, recording entries and writing output
  (dolist (name system-names)
    (unless (member name '(all everything))
      (with-open-file (stream (planning-file 
                               (format nil "overview-~A" name)
                               :type "html" :path '("doc"))
                              :direction :output :if-exists :supersede)
        (format t "~&Working on system ~A~%" (setq *planning-system* name))
        (do-file (line (planning-file "README" :type "html"
                                      :path (list (string-downcase name)))
                       :by #'read-line)
          (if (equal line "<LISP>")
              (gen-files-overview name stream)
            (format stream "~A~%" line)))))))

(defun gen-files-overview (name stream)
  (format stream "<P><HR size=3>")
  ;; List all the files:
  (operate-on-sub-system
   name
   #'(lambda (file)
       (setq file (file-with-type file "lisp"))
       (format stream "<LI><A HREF=\"#~A\"><B>~A.lisp</B></A> ~A"
         (planning-namestring file)
         (pathname-name file) (or (file-title file) "")))
   :directory-operation
   #'(lambda (path)
       (format stream "</UL><A HREF=\"../~A\"><B>~:*~A</B></A>:~%<UL> "
         (planning-namestring (planning-file nil :type nil :path path)))))
  (format stream "</UL>~%~%")
  ;; Now list the functions in the files:
  (operate-on-sub-system
   name
   #'(lambda (file)
       (incf (getf *counts* 'file 0))
       (format t "Working on file ~A~%" file)
       (overview-entries file stream)))
  ;; Finally print the trailer
  (format stream
      "<HR>
<TABLE BORDER=4 CELLPADDING=4 CELLSPACING=0><tr>
<td> <A HREF=\"http://www.laas.fr/planning/\">AUTOMATED PLANNING Home</A>
<td> <A HREF=\"../../contact.html\">Authors</A>
<td> <A HREF=\"overview.html\">Lisp Code</A>
<td> <A HREF=\"../../prog.html\">AI Programming</A>
<td> <A HREF=\"../../instructors.html\">Instructors Pages</A>
</TABLE>"))

(defun alphabetize (table if)
  "Alphabetize a table of entries."
  (sort (hashtable-vals table if) #'string-lessp 
        :key #'(lambda (x) (stringify (entry-name x)))))

(defun mapcarhash (fn table)
  "Do a maphash, and keep the results."
  (let ((result nil))
    (maphash #'(lambda (key val) (push (funcall fn key val) result)) 
             table)
    result))

(defun hashtable-vals (table if)
  (let ((result nil))
    (maphash #'(lambda (key val) (declare (ignore key)) 
                 (when (funcall if val) (push val result)))
             table)
    result))

(defun gen-entries (entries.html)
  "Sort *user-symbols* and *cl-symbols* and print entries.html files.
  These are alphabetized, with A-Z 'tabs', and printed in two columns."
  (let* ((entries (alphabetize *user-symbols* 
                               #'(lambda (x) 
                                   (or (entry-defs x) (entry-page x)))))
         (symbols (alphabetize *cl-symbols* #'true))
         (width (reduce #'max (mapcar #'entry-width entries))))
    (with-open-file (stream entries.html :direction :output 
                            :if-exists :supersede)
      (format stream "<HTML><TITLE>Index of AUTOMATED PLANNING Code</TITLE>
 <BODY bgcolor=\"#ffffff\">
 <H1>Index of AUTOMATED PLANNING Code</H1>~%")
      (format stream "There are ~D definitions (~D functions, ~D macros, ~D global variables and ~D types) defined in ~D files in the <I>Planning</I> code."
        (reduce #'+ (remove-if-not #'numberp *counts*))
        (getf *counts* 'f)
        (getf *counts* 'm)
        (getf *counts* 'v)
        (getf *counts* 't)
        (getf *counts* 'file))
      (format stream "  They are listed below in the left column, with links
  to the overview of each definition (documentation string, and parameter
  list for functions).  From the overview you can link to the source code.
  The letters F, M, V, and T in the links stand for function, macro, variable 
  and type, respectively; also given is the page number in the book where some
  of these definitions occur.  <P> In the right
  column are the ~D built-in Common Lisp symbols used in the code (along with
  the number of times each is used).  You can
  follow a link to the definition of each one in the 
  <A HREF=\"http://www.harlequin.com/books/HyperSpec/FrontMatter/index.html\">
  Common Lisp Hyperspec</A> (based on the ANSI standard document).
  You can also go directly to the <A HREF=\"overview.html\">overview</A> 
  or the <A HREF=\"../\">code directory</A>.
  <P><CENTER>
  <A HREF=\"#*\"> *</A>
  <A HREF=\"#A\"> A</A> <A HREF=\"#B\"> B</A> <A HREF=\"#C\"> C</A>
  <A HREF=\"#D\"> D</A> <A HREF=\"#E\"> E</A> <A HREF=\"#F\"> F</A>
  <A HREF=\"#G\"> G</A> <A HREF=\"#H\"> H</A> <A HREF=\"#I\"> I</A>
  <A HREF=\"#J\"> J</A> <A HREF=\"#K\"> K</A> <A HREF=\"#L\"> L</A>
  <A HREF=\"#M\"> M</A> <A HREF=\"#N\"> N</A> <A HREF=\"#O\"> O</A>
  <A HREF=\"#P\"> P</A> <A HREF=\"#Q\"> Q</A> <A HREF=\"#R\"> R</A>
  <A HREF=\"#S\"> S</A> <A HREF=\"#T\"> T</A> <A HREF=\"#U\"> U</A>
  <A HREF=\"#V\"> V</A> <A HREF=\"#W\"> W</A> <A HREF=\"#X\"> X</A>
  <A HREF=\"#Y\"> Y</A> <A HREF=\"#Z\"> Z</A> </CENTER>~%<PRE>~%" 
        (length symbols))
      (format stream "AUTOMATED PLANNING Symbols~VTCommon Lisp Symbols~%" width)
      (format stream "==========================~VT===================~%" width)
      ;; Loop until both lists empty:
      ;;   Print tab
      ;;   Loop: print all entries with that tab
      (loop (when (and (null entries) (null symbols)) (return))
            (let ((ch (char-upcase 
                       (char (entry-name (or (first entries) (first symbols))) 0)))
                  c1 c2)
              (format stream "~&~VT<B><A NAME=~C>~C</A></B>~%" (- width 4) ch ch)
              (loop 
                (if (setq c1 (and entries 
                                  (char-ok? (entry-name (first entries)) ch)))
                    (format-entry-link stream (pop entries) width)
                  (format stream "~&~VT" width))
                (if (setq c2 (and symbols 
                                  (char-ok? (entry-name (first symbols)) ch)))
                    (format-symbol-link stream (pop symbols))
                  (format stream "~%"))
                (unless (or c1 c2) (return))))))))

(defun char-ok? (name ch)
  "Its ok to list name under ch if name starts with ch, or if
  both ch and name's first character are both symbols less than A."
  (let ((name-ch (char-upcase (char (string name) 0))))
    (or (char-equal ch name-ch)
        (and (char< ch #\A) (char< name-ch #\A)))))

(defun format-entry-link (stream entry width)
  "Print the entry and tab over to width.
  It looks like: NAME (34) [p. xxx] F F F"
  (format stream "~&~A (~D)~@[ [p. ~D]~]" 
    (entry-name entry) (entry-count entry) (entry-page entry))
  (dolist (def (entry-defs entry))
    (format stream " <A HREF=\"overview-~A.html#~A\">~A</A>" 
      (def-system def)
      (overview-tag-name 
       (def-kind def) (entry-name entry) (def-arg-type def))
      (def-kind def)))
  (print-repeated " " (- width (entry-width entry)) stream))

(defun format-symbol-link (stream entry)
  (format stream "~A (~D) ~%" 
    (hyperspec-link (intern (string-upcase (entry-name entry))))
    (entry-count entry)))

(defun entry-width (entry)
  "Width in characters of printed output for entry,"
  (+ (length (entry-name entry))
     (if (entry-page entry) (+ 6 (number-width (entry-page entry))) 0)
     (+ 3 (number-width (entry-count entry)))
     (* 2 (length (entry-defs entry)))
     (* 4 (count-if #'numberp (entry-defs entry) :key #'def-file))))

(defun number-width (n)
  (cond ((< n 10) 1)
        ((< n 100) 2)
        ((< n 1000) 3)
        (t (+ 1 (ceiling (log (- n 1) 10))))))

;;;; Prepare the Overview File

(defvar *comment-readtable* (copy-readtable))

;;; The text (string) and number of leading semicolons (level) in a comment.
(defstruct semi-comment level string)

(defmethod print-structure ((exp semi-comment) stream)
  (when (= (semi-comment-level exp) 4) (format stream "<H2>"))
  (if (equal (semi-comment-string exp) "")
      (format stream "<P>~%")
    (format stream "<I>~A</I>~%" (semi-comment-string exp)))
  (when (= (semi-comment-level exp) 4) (format stream "</H2>~%")))

(defun read-semi-comment (stream char)
  "Build a comment structure."
  (declare (ignore char))
  (let ((num-semis 1))
    (loop while (eql (peek-char nil stream) #\;) do    ; by seiji
          (read-char stream)
          (incf num-semis))
    (if (>= num-semis 3)
        (make-semi-comment :level num-semis :string (read-line stream))
      (progn (read-line stream) (values)))))

(set-macro-character #\; 'read-semi-comment nil *comment-readtable*)

(defun overview-entries (file stream)
  "List all the definitions in this file."
  ;; The stream is a file in code/doc, so the links have a .. in them.
  (setf file (file-with-type file "lisp"))
  (format stream "<A NAME=\"~A\"><HR>~%<H2>File <A HREF=\"../~A\">~A</A></H2></A>~%"  
    (planning-namestring file) (planning-namestring file) (planning-namestring file))
  (let ((*readtable* *comment-readtable*))
    (do-file (exp file)
      (record-exp exp file)
      (overview-exp exp stream file))))

(defun overview-exp (exp stream file)
  "Top-level strings are outputted as HTML, quoted strings as headers,
  and DEFUN, DEFVAR, etc. as an interface summary."
  (cond
   ((and (semi-comment-p exp) (>= (semi-comment-level exp) 3)
         (not (search "-*- Mode:" (semi-comment-string exp))))
    (print-structure exp stream))
   ((consp exp)
    (let* ((name (first (mklist (second exp))))
           (doc (or (find-if #'stringp (rest exp))
                    (second (find-if #'(lambda (x)
                                         (starts-with x :documentation))
                                     (rest exp)))))
           (args "")
           (kind
            (case (first exp)
              ((defun defgeneric) 
               (setq args (or (remove-&aux (mapcar #'first-atom (third exp)))
                              "()"))
               "function")
              ((defmethod) (setq args (third exp)) "method")
              ((defmacro) (setq args (third exp)) "macro")
              ((defvar defparameter) "variable")
              ((defconstant) "constant")
              ((deftype) "type")
              ((defstruct defstructure)
               (setq args (mapcar #'first-atom
                            (remove-if #'stringp (nthcdr 2 exp))))
               "type")
              ((progn define-if-undefined when unless)         
               (dolist (x (rest exp))
                 (overview-exp x stream file))
               nil))))
      (when kind
        (format stream 
            "<A NAME=~S><P><A HREF=\"../~A\"><B>~(~A~)</B></A></A> <I>~A</I> ~(~A~)
  ~@[<blockquote>~A</blockquote>~]~A~%"
          (overview-tag-name kind name (defmethod-arg-type exp))
          (planning-namestring file)
          name kind (remove-&aux args) doc 
          (if (null doc) "<P>" "") ;???
          ))))))

(defun overview-tag-name (kind name arg-type)
  (declare (ignore kind))
  (format nil "~(~A~@[:~A~]~)" name arg-type))

(defun defmethod-arg-type (exp)
  (when (starts-with exp 'defmethod) 
    (let ((arg1 (first (third exp))))
      (if (consp arg1) (second arg1) 't))))

(defun remove-&aux (list)
  (if (consp list) 
      (ldiff list (member '&aux list))
    list))

(defun record-exp (exp file)
  (when (consp exp)
    (let ((name (op (second exp))))
      (record-symbols-counts exp name)
      (case (first exp)
        ((defun defgeneric)             (record-entry name file 'f))
        ((defmethod)                    (record-entry 
                                         name file 'f
                                         (defmethod-arg-type exp)))
        ((defmacro)                     (record-entry name file 'm))
        ((defvar defparameter defconstant) (record-entry name file 'v))
        ((defstruct deftype)            (record-entry name file 't))
        ((progn define-if-undefined
           when unless)            (dolist (subexp (rest exp))
                                     (record-exp subexp file)))))))

(defun get-entry (name table)
  (let ((symbol (if (symbolp name) (intern (string-upcase name)) name))
        (name2 (if (stringp name) name (string-downcase name))))
    (or (gethash symbol table)
        (setf (gethash symbol table) (make-entry :name name2)))))

(defun record-entry (name file-or-page &optional (kind 'f) arg-type)
  (incf (getf *counts* kind 0))
  (let ((entry (get-entry name *user-symbols*)))
    (if (numberp file-or-page)
        (setf (entry-page entry) file-or-page)
      (push (make-def :kind kind :arg-type arg-type :system *planning-system*
                      :file (planning-namestring file-or-page))
            (entry-defs entry)))))

(defun first-atom (x) (if (atom x) x (first-atom (first x))))

(defun planning-namestring (file)
  (enough-namestring (truename file) (truename *planning-root*)))

(defun file-title (pathname)
  "If the file starts with a ;;;; comment, return it."
  (let ((*readtable* *comment-readtable*))
    (do-file (exp pathname)
      (cond ((not (semi-comment-p exp)) (return nil))
            ((= 4 (semi-comment-level exp) )
             (return (semi-comment-string exp)))))))

(defun record-symbols-counts (exp name)
  "Record uses of any symbols in the Common Lisp or user packages.
  Don't count uses of NAME; the idea is that this counts non-recursive refs."
  (case (type-of exp)
    (cons (record-symbols-counts (car exp) name)
          (if (cdr exp) (record-symbols-counts (cdr exp) name)))
    (symbol (cond ((eq exp name) nil)
                  ((eq (symbol-package exp)
                       #.(or (find-package "common-lisp") 
                             (find-package "lisp")))
                   (incf (entry-count (get-entry exp *cl-symbols*))))
                  ((eq (symbol-package exp)
                       #.(or (find-package "common-lisp-user") 
                             (find-package "user")))
                   (incf (entry-count (get-entry exp *user-symbols*))))))))



;;; Record page numbers for functions from the book
;;; The book means here "Automated Planning Theory and Practice" by Ghallab, Nau, and Traverso.
;;; Elsevier and Morgan Kaufmann, 2004.

(defun mapply (fn list)
  "Each element of list is a list of args; apply fn to it, collect results."
  (mapcar #'(lambda (args) (apply fn args)) list))

(defun record-book-pages ()
  (mapcar #'(lambda (args) (apply #'record-entry args))
    '(
      (forward-search                   70)
      (backward-search                  73)
      (lifted-backward-search           75)
      (ground-STRIPS                    76)
      (recursive-forward-search         82)
      (PSP                              95) 
      (PoP                             100)
      (expand                          124)
      (extract                         127)
      (GP-search                       128)
      (graphplan                       129)
      (davis-putnum                    152)
      (local-search-SAT                157)
      (basic-GSAT                      158)
      (iterative-repair                158)
      (backtrack                       179)
      (forward-checking                180)
      (AC3                             182)
      (PC                              183)
      (IPC                             184)
      (abstract-search                 195)
      (depth-first-search              200)
      (delta                           203)
      (heuristic-forward-search        203)
      (heuristic-backward-search       204)
      (TFD                             239)
      (PFD                             243)
      (abstract-HTN                    249)
      (TPS                             324)
      (CP                              338)
      (value-iteration                 390)
      (execute-policy                  406)
      (strong-plan                     409)
      (strong-cyclic-plan              411)
      (prune-out-going                 412)
      (strong-conformant-davis-putnum  443)
      )))

(defun operate-on-sub-system (part operation &key (path nil) (load t)
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
	  (operate-on-sub-system subpart operation :load load 
				  :path new-path
				  :directory-operation directory-operation))))
     ((consp part)
      (dolist (subpart part)
	(operate-on-sub-system subpart operation :load load :path path
				:directory-operation directory-operation)))
     ((setf system (get-planning-system part))
      ;; Load the required systems, then operate on the parts
      (when load (mapc #'planning-load-if-unloaded (planning-system-requires system)))
      (operate-on-sub-system (planning-system-parts system) operation
			      :load load :path path
			      :directory-operation directory-operation)
      (setf (planning-system-loaded? system) t))
     (t (warn "Unrecognized part: ~S in path ~A" part path)))))
