;;;; functional-trees.lisp --- Tree data structure with functional manipulation
;;;;
;;;; Copyright (C) 2020 GrammaTech, Inc.
;;;;
;;;; This code is licensed under the MIT license. See the LICENSE.txt
;;;; file in the project root for license terms.
;;;;
;;;; This project is sponsored by the Office of Naval Research, One
;;;; Liberty Center, 875 N. Randolph Street, Arlington, VA 22203 under
;;;; contract # N68335-17-C-0700.  The content of the information does
;;;; not necessarily reflect the position or policy of the Government
;;;; and no official endorsement should be inferred.
(defpackage :functional-trees
  (:nicknames :ft :functional-trees/functional-trees)
  (:use :common-lisp :alexandria :iterate :cl-store :bordeaux-threads)
  (:import-from :serapeum
                :with-item-key-function
                :with-two-arg-test
                :with-boolean
                :def)
  (:shadowing-import-from :fset
                          :@ :do-seq :seq :lookup :alist :size
                          :unionf :appendf :with :less :splice :insert :removef
                          ;; Shadowed set operations
                          :union :intersection :set-difference :complement
                          ;; Shadowed sequence operations
                          :first :last :subseq :reverse :sort :stable-sort
                          :reduce
                          :find :find-if :find-if-not
                          :count :count-if :count-if-not
                          :position :position-if :position-if-not
                          :remove :remove-if :remove-if-not :filter
                          :substitute :substitute-if :substitute-if-not
                          :some :every :notany :notevery
                          ;; Additional stuff
                          :identity-ordering-mixin :serial-number
                          :compare :convert)
  (:shadow :subst :subst-if :subst-if-not :assert :mapc :mapcar)
  (:shadowing-import-from :alexandria :compose)
  (:shadowing-import-from :functional-trees/interval-trees)
  (:import-from :uiop/utility :nest)
  (:import-from :serapeum :queue :qconc :qpreconc :qlist
                :set-hash-table :length<)
  (:import-from :closer-mop
                :slot-definition-name
                :slot-definition-allocation
                :slot-definition-initform
                :slot-definition-initargs
                :class-slots
                :ensure-finalized)
  (:export :copy :tree-copy
           :copy-with-children-alist
           :node :child-slots
           :child-slot-specifiers
           :serial-number
           :descendant-map :path
           :path-of-node
           :rpath-to-node
           :path-equalp
           :path-equalp-butlast
           :path-later-p
           :parent
           :predecessor
           :successor
           :children
           :children-alist
           :children-slot-specifier-alist
           :do-tree :mapc :mapcar
           :swap
           :define-node-class :define-methods-for-node-class
           :child-position-if
           :child-position
           :subst :subst-if :subst-if-not)
  (:documentation
   "Prototype implementation of functional trees w. finger objects"))
(in-package :functional-trees)

(defmacro assert (&body body)
  ;; Copy the body of the assert so it doesn't pollute coverage reports
  `(cl:assert ,@(copy-tree body)))


(eval-when (:compile-toplevel :load-toplevel :execute)

  ;; Allocate blocks of serial numbers on a per-thread basis. This
  ;; solves the problem where parsing in parallel would lead to
  ;; extremely deep trees that were extremely slow to traverse due to
  ;; widely-separated serial numbers.

  ;; Note this is a standard technique in other contexts where serial
  ;; numbers are used (databases, for example, allocate blocks of
  ;; serial numbers to workers in this way).

  (defvar *serial-number-index* 0)
  (def +serial-number-block-size+ 10000)
  (defvar *current-serial-number-block* nil)
  (defstruct serial-number-block
    (end (required-argument :end) :read-only t)
    (index (required-argument :index))
    (thread (bt:current-thread)))

  (def +serial-number-lock+
    (bt:make-lock "functional-trees serial-number"))

  (defun allocate-serial-number-block ()
    (bt:with-lock-held (+serial-number-lock+)
      (let ((serial-block
              (make-serial-number-block :end (+ *serial-number-index*
                                                +serial-number-block-size+)
                                        ;; NB The initial index
                                        ;; belongs to the last block
                                        ;; allocated.
                                        :index (1+ *serial-number-index*))))
        (incf *serial-number-index* +serial-number-block-size+)
        serial-block)))

  (defun next-serial-number ()
    "Return the next serial number in the current thread's block"
    ;; if first call on thread, initialize block
    (if (or (null *current-serial-number-block*)
            (= (serial-number-block-index *current-serial-number-block*)
               (serial-number-block-end *current-serial-number-block*)))
        (setf *current-serial-number-block* (allocate-serial-number-block)))
    (assert (eql (bt:current-thread)
                 (serial-number-block-thread *current-serial-number-block*)))
    (1- (incf (serial-number-block-index *current-serial-number-block*))))

  ;; ensure that each thread gets its own binding of serial number block
  (pushnew '(*current-serial-number-block* . nil)
           bt:*default-special-bindings*
           :test #'equal)

  ;; Clear the serial number block when saving an image.

  (defun clear-serial-number-block ()
    (setf *current-serial-number-block* nil))

  (uiop:register-image-dump-hook 'clear-serial-number-block)

  (defclass descendant-map-mixin ()
    ((descendant-map :initarg :descendant-map
                     :documentation "Map from serial numbers to child slots"))
    (:documentation "Mixin for the descendant-map slot"))

  (defclass node-identity-ordering-mixin (identity-ordering-mixin) ())

  ;;; NOTE: We might want to propose a patch to FSet to allow setting
  ;;; serial-number with an initialization argument.
  (defmethod initialize-instance :after
      ((node node-identity-ordering-mixin)
       &key (serial-number nil) &allow-other-keys)
    (setf (slot-value node 'serial-number)
          (or serial-number (next-serial-number)))
    node)

  (defclass node (node-identity-ordering-mixin descendant-map-mixin)
    ((size :reader size
           :type (integer 1)
           :documentation "Number of nodes in tree rooted here.")
     (child-slots :reader child-slots
                  :initform nil
                  :allocation :class
                  :type list ;; of (or symbol cons)
                  :documentation
                  "List of child slots with optional arity.
This field should be specified as :allocation :class if defined by a
subclass of `node'.  List of either symbols specifying a slot holding
a list of children or a cons of (symbol . number) where number
specifies a specific number of children held in the slot.")
     (child-slot-specifiers :reader child-slot-specifiers
                            :allocation :class
                            :type list
                            :documentation "The list CHILD-SLOTS
converted to a list of slot-specifier objects"))
    (:documentation "A node in a tree."))

  (defclass slot-specifier ()
    ((class :reader slot-specifier-class
            :initarg :class
            :documentation "The class to which the slot belongs")
     (slot :reader slot-specifier-slot
           :initarg :slot
           :type symbol
           :documentation "The name of the slot")
     (arity :reader slot-specifier-arity
            :type (integer 0)
            :initarg :arity
            :documentation "The arity of the slot"))
    (:documentation "Object that represents the slots of a class")))

(defmethod convert ((to-type (eql 'node)) (node node) &key)
  node)

(declaim (inline descendant-map))
(defun descendant-map (obj)
  (slot-value obj 'descendant-map))

(defun make-slot-specifier (&rest args)
  (apply #'make-instance 'slot-specifier args))

(defmethod slot-unbound ((class t) (obj node) (slot (eql 'child-slot-specifiers)))
  (setf (slot-value obj slot)
        (iter (for p in (child-slots obj))
              (collecting
               (etypecase p
                 (symbol (make-slot-specifier
                          :class class :slot p :arity 0))
                 (cons (make-slot-specifier
                        :class class :slot (car p)
                        :arity (or (cdr p) 0))))))))

(defgeneric slot-specifier-for-slot (obj slot &optional error?)
  (:documentation "Returns the child slot SLOT in node OBJ.  If it is not
the name of a child slot, return NIL if error? is NIL and error if error?
is true (the default.)")
  (:method ((obj node) (slot slot-specifier) &optional (error? t))
    (when (and (not (eql (slot-specifier-class slot) (class-of obj)))
               error?)
      (error "Slot specifier class ~a does not match object ~a's class"
             (slot-specifier-class slot) obj))
    slot)
  (:method ((obj node) (slot symbol) &optional (error? t))
    (let ((slot-spec (find slot (child-slot-specifiers obj) :key #'slot-specifier-slot)))
      (or slot-spec
          (when error?
            (error "Not a slot in ~a: ~a" obj slot))))))

(declaim (inline slot-spec-slot slot-spec-arity child-list))

(defun slot-spec-slot (slot-spec)
  (if (consp slot-spec) (car slot-spec) slot-spec))

(defun slot-spec-arity (slot-spec)
  (or (and (consp slot-spec) (cdr slot-spec)) 0))

(defgeneric slot-spec-of-slot (obj slot &optional error?)
  (:documentation "Returns the slot spec pair of a slot in OBJ.  If ERROR? is
true (the default) signal an error if SLOT is not a child slot of OBJ.
Otherwise, in that case return NIL.")
  (:method ((obj node) (slot symbol) &optional (error? t))
    (dolist (p (child-slots obj)
             (when error? (error "Not a child slot of ~a: ~a" obj slot)))
      (etypecase p
        (symbol (when (eql p slot) (return p)))
        (cons (when (eql (car p) slot) (return p)))))))

;;;; Core functional tree definitions.
(deftype path ()
  `(and list (satisfies path-p)))

(defun path-p (list)
  (every (lambda (x)
           (typecase x
             ((integer 0) t)            ; Index into `children'.
             (symbol t)                 ; Name of scalar child-slot.
             ((cons (integer 0)         ; Non-scalar child-slot w/index.
                    (cons integer null))
              (<= (first x) (second x)))
             ((cons symbol null) t)
             ((cons symbol (integer 0)) t)
             (t nil)))
         list))

(defgeneric path-equalp (path-a path-b)
  (:documentation "Are path-a and path-b the same path?")
  (:method ((path-a t) (path-b t))
    (and (length= path-a path-b)
         (every #'path-element-= path-a path-b))))

(defgeneric path-equalp-butlast (path-a path-b)
  (:documentation "Are path-a and path-b the same, except possibly
for their last entries?")
  (:method ((path-a t) (path-b t))
    (path-equalp (butlast path-a) (butlast path-b))))

(defgeneric slot-position-in-node (node slot)
  (:method ((node node) (slot symbol))
    (cl:position slot (child-slots node) :key #'slot-spec-slot)))

(defmacro cons-0-de ((&rest syms) &body body)
  (assert (every #'identity syms))
  (assert (every #'symbolp syms))
  (assert (length= syms (remove-duplicates syms)))
  `(let ,(cl:mapcar (lambda (s)`(,s (cons ,s 0))) syms)
     (declare (dynamic-extent ,@syms))
     ,@body))

(defgeneric path-element-> (node a b)
  (:documentation "Ordering function for elements of paths")
  (:method ((node t) (a real) (b real))
    (> a b))
  (:method ((node node) (a cons) (b cons))
    (let ((ca (car a))
          (cb (car b))
          (na (or (cdr a) 0))
          (nb (or (cdr b) 0)))
      (assert (symbolp ca))
      (assert (symbolp cb))
      (cond
        ((eql ca cb) (> na nb))
        ;; (t (string> (symbol-name ca) (symbol-name cb)))
        (t
         (> (slot-position-in-node node ca)
            (slot-position-in-node node cb)))
        )))
  (:method ((node t) (a symbol) (b symbol))
    (cons-0-de (a b) (path-element-> node a b)))
  (:method ((node t) (a symbol) (b t))
    (cons-0-de (a) (path-element-> node a b)))
  (:method ((node t) (a t) (b symbol))
    (cons-0-de (b) (path-element-> node a b)))
  (:method ((node t) (a cons) (b real)) nil)
  (:method ((node t) (a real) (b cons)) t))

(defgeneric path-element-= (a b)
  (:documentation "Equality function for elements of a path, taking
into account the representation of named children")
  (:method ((a real) (b real)) (eql a b))
  (:method ((a cons) (b real)) nil)
  (:method ((a real) (b cons)) nil)
  (:method ((a symbol) (b symbol)) (eql a b))
  (:method ((a symbol) (b t))
    (cons-0-de (a) (path-element-= a b)))
  (:method ((a t) (b symbol))
    (cons-0-de (b) (path-element-= a b)))
  (:method ((a cons) (b cons))
    (and (eql (car a) (car b))
         (eql (or (cdr a) 0)
              (or (cdr b) 0)))))

;;; TODO: determine if this may or should be combined with lexicographic-<

(defgeneric path-later-p (node path-a path-b)
  (:documentation "Does PATH-A from NODE represent an NODE path after
PATH-B from NODE?   Use this to sort NODE nodes for mutations that perform
multiple operations.")
  (:method ((node t) (path-a null) (path-b null)) nil)
  (:method ((node node) (path-a null) (path-b null)) nil)
  (:method ((node t) (path-a null) (path-b cons)) nil)
  (:method ((node node) (path-a null) (path-b cons)) nil)
  (:method ((node t) (path-a cons) (path-b null)) t)
  (:method ((node node) (path-a cons) (path-b null)) t)
  (:method ((node t) (path-a list) (path-b list))
    ;; Consider longer paths to be later, so in case of nested NODEs we
    ;; will sort inner one first. Mutating the outer NODE could
    ;; invalidate the inner node.
    (nest (destructuring-bind (head-a . tail-a) path-a)
          (destructuring-bind (head-b . tail-b) path-b)
          (cond
            ((path-element-> node head-a head-b) t)
            ((path-element-> node head-b head-a) nil)
            ((path-element-= head-a head-b)
             (path-later-p (@ node head-a) tail-a tail-b))))))

;;; FIXME: Should we replace this with an explicit deep copy?  We
;;; wouldn't be able to re-use `copy-array', `copy-seq', etc but we
;;; could then remove `copy-tree' and just use this generic copy
;;; universally instead.  It would also then more closely mimic the
;;; behavior of the `equal?' method defined in GT and FSET.
(defgeneric copy (obj &key &allow-other-keys)
  (:documentation "Generic COPY method.") ; TODO: Extend from generic-cl?
  (:method ((obj t) &key &allow-other-keys) obj)
  (:method ((obj array) &key &allow-other-keys) (copy-array obj))
  (:method ((obj hash-table) &key &allow-other-keys) (copy-hash-table obj))
  (:method ((obj list) &key &allow-other-keys) (copy-list obj))
  (:method ((obj sequence) &key &allow-other-keys) (copy-seq obj))
  (:method ((obj symbol) &key &allow-other-keys) (copy-symbol obj)))

(defgeneric copy-with-children-alist (obj children-alist &rest args)
  (:documentation "Perform a copy of node OBJ, with children-alist being
used to initialize some children")
  (:method ((obj node) (children-alist list) &rest args)
    (apply #'copy obj (nconc (mapcan (lambda (p)
                                       (typecase (car p)
                                         (slot-specifier
                                          (list (make-keyword (slot-specifier-slot (car p)))
                                                (if (eql (slot-specifier-arity (car p)) 1)
                                                    (cadr p)
                                                    (cdr p))))
                                         (t (list (car p) (cdr p)))))
                                     children-alist)
                             args))))

(defgeneric tree-copy (obj)
  (:documentation "Copy method that descends into a tree and copies all
its nodes.")
  (:method ((obj t)) obj)
  (:method ((obj list)) (cl:mapcar #'tree-copy obj)))

(defmacro define-node-class (name superclasses slots &rest rest)
  (flet ((method-options-p (item)
           (and (consp item) (eq :method-options (car item)))))
    `(progn
       (eval-when (:load-toplevel :compile-toplevel :execute)
         (defclass ,name ,superclasses
           ((child-slot-specifiers :allocation :class)
            ,@slots)
           ,@(remove-if #'method-options-p rest))
         (define-methods-for-node-class ,name
             ,(cdr (find-if #'method-options-p rest)))))))

;; debug macro
(defmacro dump (&body forms)
  `(progn
     ,@(iter (for form in forms)
             (collecting `(format t "~a = ~s~%"
                                  ,(format nil "~s" form)
                                  ,form)))))

(defvar *node-obj-code* (register-code 45 'node))

(defstore-cl-store (obj node stream)
  (let ((*store-class-slots* nil))
    (output-type-code *node-obj-code* stream)
    (cl-store::store-type-object obj stream)))

(defrestore-cl-store (node stream)
  (cl-store::restore-type-object stream))

(define-compiler-macro children (node)
  `(locally (declare (notinline children))
     (the (values list &optional) (children ,node))))

(defgeneric children (node)
  (:documentation "Return all children of NODE.")
  (:method ((node node))
    (mappend (lambda (slot-spec)
               (multiple-value-bind (slot arity)
                   (etypecase slot-spec
                     (cons (values (car slot-spec) (cdr slot-spec)))
                     (symbol (values slot-spec 0)))
                 (if (eql 1 arity)
                     (list (slot-value node slot))
                     (slot-value node slot))))
             (child-slots node))))

(defgeneric children-alist (node)
  (:documentation "Return an alist mapping child slots
of NODE to their members.")
  (:method ((node node))
    (cl:mapcar (lambda (slot-spec)
                 (multiple-value-bind (slot arity)
                     (etypecase slot-spec
                       (cons (values (car slot-spec) (cdr slot-spec)))
                       (symbol (values slot-spec 0)))
                   (if (eql 1 arity)
                       (list slot (slot-value node slot))
                       (cons slot (slot-value node slot)))))
               (child-slots node))))

(defgeneric children-slot-specifier-alist (node)
  (:documentation "Return an alist mapping child slot specifiers
of NODE to their members")
  (:method ((node node))
    (cl:mapcar (lambda (ss)
                 (let ((v (slot-value node (slot-specifier-slot ss))))
                   (if (eql (slot-specifier-arity ss) 1)
                     (if v (list ss v) (list ss))
                     (cons ss v))))
               (child-slot-specifiers node))))

(defun expand-children-defmethod (class child-slots)
  `(defmethod children ((node ,class))
     ;; NOTE: For now just append everything together wrapping
     ;; singleton arity slots in `(list ...)'.  Down the line
     ;; perhaps something smarter that takes advantage of the
     ;; known size of some--maybe all--slots would be better.
     (append ,@(cl:mapcar (lambda (form)
                            (destructuring-bind (slot . arity)
                                (etypecase form
                                  (symbol (cons form nil))
                                  (cons form))
                              (if (and arity (= (the fixnum arity) 1))
                                  `(list (slot-value node ',slot))
                                  `(slot-value node ',slot))))
                          child-slots))))

(defun store-actual-slot (key actual-slot)
  (assert (keywordp key))
  (assert (equal (symbol-name key)
                 (symbol-name actual-slot)))
  (assert (not (eql key actual-slot)))
  (let ((a (get key 'actual-slot)))
    (when (and a (not (eql a actual-slot)))
      (error "Keyword ~s corresponds to two different slots: ~s and ~s"
             key a actual-slot))
    (unless a
      (setf (get key 'actual-slot) actual-slot))
    actual-slot))

(defun store-actual-slots (slot-names)
  (dolist (slot-name slot-names)
    (store-actual-slot (make-keyword slot-name) slot-name)))

(defun get-actual-slot (slot)
  (etypecase slot
    (keyword (or (get slot 'actual-slot)
                 (error "Keyword ~a does not correspond to an actual slot" slot)))
    (symbol slot)))

(defmethod lookup ((obj node) (slot symbol))
  (if-let ((actual-slot (and (keywordp slot)
                             (get-actual-slot slot))))
          (slot-value obj actual-slot)
          (call-next-method)))

(eval-when (:compile-toplevel :load-toplevel)
  (defun slot-setf-expander (node slot-name env)
    (nest
     (let ((key (make-keyword slot-name))))
     (multiple-value-bind (temps vals stores store-form access-form)
         (get-setf-expansion node env))
     (let ((val-temp (gensym))
           (coll-temp (car stores)))
       (when (cdr stores)
         (error "Too many values required in `setf' of `~a'" slot-name)))
     (values temps
             (cons key vals)
             (list val-temp)
             `(let ((,coll-temp (with ,access-form ',key ,val-temp)))
                ,store-form
                ,val-temp)
             `(lookup ,access-form ',key)))))

;;; TODO -- change this so keywords are handled differently
(defun expand-lookup-specialization (class child-slots)
  (let ((child-slot-names
          (iter (for cs in child-slots)
                (collect (etypecase cs
                           (symbol cs)
                           (cons (car cs)))))))
    `(progn
       ;; Storing the actual slot needs to be done as part of the
       ;; macroexpansion, within an eval-when form, rather than in the
       ;; macro itself, so the mapping persists beyond compile time.
       ,@(when child-slot-names
           `((store-actual-slots ',child-slot-names)))
       ,@(unless (subtypep class 'node)
           (cl:mapcar (lambda (slot)
                        `(defmethod lookup
                             ((obj ,class) (key (eql ,(make-keyword slot))))
                           (slot-value obj ',slot)))
                      child-slot-names)))))

(defun expand-setf-error-methods (class child-slots)
  "Generate (setf <slot>) methods for CLASS that just signal errors
telling the user to use (setf (@ ... :<slot>) ...)"
  `(progn
     ,@(cl:mapcar (lambda (form)
                    (let ((slot (etypecase form
                                  (symbol form)
                                  (cons (car form)))))
                      `(defmethod (setf ,slot) ((obj ,class) (value t))
                         (error "Functional setf to slot ~A of class ~A should be via setf of (@ <obj> ~s)"
                                ',slot ',class ,(make-keyword slot)))))
                  child-slots)))

(defmacro define-methods-for-node-class (class-name method-options
                                         &environment env)
  (let ((class (find-class class-name env)))
    (assert class () "No class found for ~s" class-name)
    (ensure-finalized class)
    (let ((child-slots
           (nest (eval)
                 (slot-definition-initform)
                 (find-if
                  (lambda (slot)
                    (and (eql 'child-slots (slot-definition-name slot))
                         (eql :class (slot-definition-allocation slot)))))
                 (class-slots class))))
      ;; Confirm that all child slots have an initarg that is a keyword
      ;; of the same name
      (let ((slot-defs (class-slots class)))
        (iter (for def in slot-defs)
              (let ((name (slot-definition-name def)))
                (when (member name child-slots)
                  (let ((desired-initarg (make-keyword name))
                        (actual-initargs (slot-definition-initargs def)))
                    (unless (member desired-initarg actual-initargs)
                      (error "Class ~a does not have initarg ~s for slot ~a"
                             class-name desired-initarg name)))))))
      `(progn
         ,(unless (member :skip-children-definition method-options)
            (expand-children-defmethod class child-slots))
         ,(expand-lookup-specialization class child-slots)
         ,(expand-setf-error-methods class child-slots)
         ))))

(defmethod slot-unbound ((class t) (obj node) (slot-name (eql 'size)))
  (setf (slot-value obj 'size)
        (reduce #'+ (children obj) :key #'size :initial-value 1)))

;;; NOTE: There should be a way to chain together methods for COPY for
;;; classes and their superclasses, perhaps using the initialization
;;; infrastructure in CL for objects.
(defmethod copy ((node node) &rest keys)
  (nest
   (compute-descendant-map node)
   (apply #'make-instance (class-of node))
   (apply #'append keys)
   (cl:mapcar (lambda (slot) (list (make-keyword slot) (slot-value node slot))))
   (cl:remove-if-not (lambda (slot) (slot-boundp node slot)))
   (cl:mapcar #'slot-definition-name)
   (remove-if (lambda (slot) (eql :class (slot-definition-allocation slot))))
   (class-slots (class-of node))))

;;; Fill in the slot lazily

(defmethod slot-unbound ((class t) (node node) (slot (eql 'descendant-map)))
  (let* ((intervals
           (iter (for slot-spec in (child-slot-specifiers node))
             (let* ((slot (slot-specifier-slot slot-spec))
                    (val (slot-value node slot)))
               (nconcing
                (if (listp val)
                    (iter (for v in val)
                      (nconcing (add-slot-to-intervals (intervals-of-node v) slot)))
                    (add-slot-to-intervals (intervals-of-node val) slot))))))
         (sn (serial-number node)))
    (setf (slot-value node 'descendant-map)
          (convert 'ft/it:itree (cons (list (cons sn sn) nil) intervals)))))

(defgeneric intervals-of-node (node)
  (:documentation "Compute a fresh list of intervals for the subtree rooted at NODE.")
  (:method ((node node))
    (ft/it:intervals-of-itree (descendant-map node)))
  (:method ((node t)) nil))

(defun add-slot-to-intervals (intervals slot)
  "Returns a fresh list of (interval slot) pairs"
  (mapcar (lambda (interval) (list interval slot)) intervals))

(defun set-difference/hash (list1 list2)
  "Like `set-difference', but use a hash table if the set is large enough.
Duplicates are allowed in both lists."
  (cond ((equal list1 list2) nil)
        ((length< list2 20)
         (set-difference list1 list2))
        ;; Allow duplicates.
        (t
         (let ((hash-set (set-hash-table list2 :strict nil)))
           (remove-if (lambda (x)
                        (gethash x hash-set))
                      list1)))))

;;; Fill in the descendant-map field of a node after copy

;;; TODO -- do not fill in the map if the node's size is below
;;; a threshold.  Instead, lookups that would use the map would
;;; instead search the subtree directly.
(defgeneric compute-descendant-map (old-node new-node)
  (:method ((old-node t) (new-node t)) new-node)
  (:method ((old-node node) (new-node node))
    (assert (eql (class-of old-node) (class-of new-node)))
    (let* ((old-dm (descendant-map old-node))
           (differing-child-slot-specifiers
             ;; The specifiers for the slots on which old-node
             ;; and new-node differ
             (iter (for slot-spec in (child-slot-specifiers new-node))
                   (let ((slot (slot-specifier-slot slot-spec)))
                     (unless (eql (slot-value old-node slot)
                                  (slot-value new-node slot))
                       (collecting slot-spec)))))
           (old-sn (serial-number old-node))
           (intervals-to-remove (queue `(,old-sn . ,old-sn)))
           (new-sn (serial-number new-node))
           (intervals-to-add (queue `((,new-sn . ,new-sn)))))
      (iter (for slot-spec in differing-child-slot-specifiers)
            (let* ((slot (slot-specifier-slot slot-spec))
                   (old (slot-value old-node slot))
                   (new (slot-value new-node slot)))
              (cond
                ((and (listp old) (listp new))
                 (let ((removed-children (set-difference/hash old new))
                       (added-children (set-difference/hash new old)))
                   ;; (format t "Removed children: ~a~%" removed-children)
                   ;; (format t "Added children: ~a~%" added-children)
                   (iter (for removed-child in removed-children)
                         (qconc intervals-to-remove (intervals-of-node removed-child)))
                   (iter (for added-child in added-children)
                         (qconc intervals-to-add (add-slot-to-intervals (intervals-of-node added-child) slot)))))
                (t ;; was (and (not (listp old)) (not (listp new)))
                 (qpreconc (intervals-of-node old) intervals-to-remove)
                 (qpreconc (add-slot-to-intervals (intervals-of-node new) slot) intervals-to-add)))))
      (setf (slot-value new-node 'descendant-map)
            (ft/it:itree-add-intervals
             (ft/it:itree-remove-intervals old-dm
                                           (qlist intervals-to-remove))
             (qlist intervals-to-add))))
    new-node))

;;; TODO -- specialize this in define-node-class
(defmethod tree-copy ((node node))
  (let* ((child-slots (slot-value node 'child-slots))
         (slots (remove-if (lambda (slot) (eql :class (slot-definition-allocation slot)))
                           (class-slots (class-of node))))
         (slot-names (remove-if (lambda (s) (or (eql s 'serial-number)
                                                (eql s 'descendant-map)))
                                (cl:mapcar #'slot-definition-name slots)))
         (initializers (mappend (lambda (slot)
                                  (and (slot-boundp node slot)
                                       (list (make-keyword slot)
                                             (slot-value node slot))))
                                slot-names))
         (new-node (apply #'make-instance (class-of node)
                          initializers)))
    ;; Now write over the child slots
    ;; This is ok, as the descendant-map slot is uninitialized
    (iter (for c in child-slots)
          (if (consp c)
              (destructuring-bind (child-slot-name . arity) c
                (if (eql arity 1)
                    ;; Special case: a singleton child
                    (setf (slot-value new-node child-slot-name)
                          (tree-copy (slot-value new-node child-slot-name)))
                    (setf (slot-value new-node child-slot-name)
                          (cl:mapcar #'tree-copy (slot-value new-node child-slot-name)))))
              (setf (slot-value new-node c)
                    (cl:mapcar #'tree-copy (slot-value new-node c)))))
    new-node))

(defun childs-list (node slot)
  (let ((val (slot-value node slot)))
    (if (listp val) val (list val))))

(defun child-slot-with-sn (node sn)
  (when-let ((itree-node (ft/it::itree-find-node-splay (descendant-map node) sn)))
     (ft/it:node-data itree-node)))

(defgeneric rpath-to-node (root node &key error)
  (:documentation "Returns the (reversed) path from ROOT to a node
with the same serial number as NODE, as a list of nodes.  Note that this does
not include NODE itself.

Also return the node found.  If no such node is in the tree, return NIL NIL, or
signal an error if ERROR is true.")
  (:method ((root node) (node node) &key error)
    (rpath-to-node root (serial-number node) :error error))
  (:method ((root node) (sn integer) &key error)
    (unless (eql (serial-number root) sn)
      (let ((node root)
            (rpath nil)
            (child-slot (child-slot-with-sn root sn)))
        (iter (while node)
              (unless child-slot
                (if error
                    (error "Serial number ~a not found in tree ~a" sn root)
                    (return (values nil nil))))
              (push node rpath)
              (iter (for child-node in (childs-list node child-slot))
                    (when (typep child-node 'node)
                      (when (eql (serial-number child-node) sn)
                        (return-from rpath-to-node (values rpath child-node)))
                      (let ((grandchild-slot (child-slot-with-sn child-node sn)))
                        (when grandchild-slot
                          (setf child-slot grandchild-slot
                                node child-node)
                          (return))))
                    (finally
                     ;; This should never happen if the tree is well formed
                     (error "Could not find child with sn ~a in slot ~a"
                            sn child-slot))))))))

(defgeneric path-of-node (root node &key error)
  (:documentation "Return the path from ROOT to NODE, in a form
suitable for use by @ or LOOKUP.  If the node is not in the tree
return NIL, unless ERROR is true, in which case error.")
  (:method ((root node) (node node) &key (error nil))
    (path-of-node root (serial-number node) :error error))
  (:method ((root node) (serial-number integer) &key (error nil))
    (multiple-value-bind (rpath found) (rpath-to-node root serial-number)
      (if found
          ;; Translate the rpath to actual path
          (let ((child found)
                (path nil))
            (iter (for a in rpath)
                  (let ((slot (when-let ((itree-node (ft/it::itree-find-node-splay
                                                      (descendant-map a)
                                                      (serial-number child)
                                                      )))
                                        (ft/it:node-data itree-node))))
                    (assert slot () "Could not find SLOT of ~a in descendant map of ~a" child a)
                    (let ((v (slot-value a slot)))
                      (push
                       (if (listp v)
                           (let ((pos (position child v)))
                             (assert pos () "Could not find ~a in slot ~a of ~a" child slot a)
                             (cons slot pos))
                           (progn
                             (assert (eq v child) () "Child ~a is not the value of slot ~a of ~a" child slot a)
                             slot))
                       path)))
                  (setf child a))
            path)
          (if error (error "Could not find ~a in ~a" serial-number root) nil)))))

(defgeneric parent (root node)
  (:documentation "Return the parent of NODE.
Return nil if NODE is equal to ROOT or is not in the subtree of ROOT.")
  (:method ((root node) (node node))
    (car (rpath-to-node root node))))

(defgeneric predecessor (root node)
  (:documentation "Return the predecessor of NODE with respect to ROOT if one exists.")
  (:method ((root node) (node node))
    (when-let (parent (parent root node))
      (iter (for child in (children parent))
            (for prev previous child)
            (when (eq child node)
              (return prev))))))

(defgeneric successor (root node)
  (:documentation "Return the successor of NODE with respect to ROOT if one exists.")
  (:method ((root node) (node node))
    (when-let (parent (parent root node))
      (second (member node (children parent))))))

(defun child-list (node slot-spec)
  (let ((children (slot-value node (slot-spec-slot slot-spec))))
    (if (eql 1 (slot-spec-arity slot-spec))
        (list children)
        children)))

(defmacro do-tree ((var tree
                        &key
                        ;; (start nil startp) (end nil endp)
                        ;; (from-end nil from-end-p)
                        (index nil indexp) (rebuild)
                        (value nil valuep))
                   &body body)
  "Generalized tree traversal used to implement common lisp sequence functions.
VALUE is the value to return upon completion.  INDEX may hold a
variable bound in BODY to the *reversed* path leading to the current
node.  If REBUILD then the body should return the new node that will
replace NODE, NODE itself if it is not to be replaced, and NIL if NODE
is to be deleted (from a variable arity list of children in its parent)."
  ;; (declare (ignorable start end from-end))
  ;; (when (or startp endp from-end-p)
  ;;   (warn "TODO: implement start end and from-end-p."))
  (when (and rebuild indexp)
    (error "Does not support :index with :rebuild"))
  (with-gensyms (block-name body-fn tree-var)
    `(progn
       (nest
        (block ,block-name)
        (flet ((,body-fn (,var ,@(when indexp (list index)))
                 ,@(if rebuild
                       body
                       `((multiple-value-bind (exit result)
                             (let () ,@body)
                           (when exit (return-from ,block-name
                                        (values exit result))))
                         nil))))
          (declare (dynamic-extent #',body-fn)))
        (let ((,tree-var ,tree)))
        ,(cond
           ;; (rebuild `(update-predecessor-tree ,tree-var (traverse-tree ,tree-var #',body-fn)))
           (rebuild `(compute-descendant-map ,tree-var (traverse-tree ,tree-var #',body-fn)))
           (indexp `(pure-traverse-tree/i ,tree-var nil #',body-fn))
           (t `(pure-traverse-tree ,tree-var #',body-fn))))
       ,@(when valuep (list value)))))

(defgeneric pure-traverse-tree/i (node index fn)
  (:documentation "Traverse tree below NODE in preorder, calling
FN on each node (and with the reversed path INDEX to that node)."))

(defmethod pure-traverse-tree/i ((node t) (index list) (fn function)) nil)

(defmethod pure-traverse-tree/i ((node node) (index list) (fn function))
  (funcall fn node index)
  (map-children/i node index fn))

(defgeneric pure-traverse-tree (node fn)
  (:documentation "Traverse tree at and below NODE in preorder,
calling FN on each node."))

(defmethod pure-traverse-tree ((node t) (fn function)) nil)

(defmethod pure-traverse-tree ((node node) (fn function))
  (funcall fn node)
  (map-children node fn))

(defgeneric traverse-tree (node fn)
  (:documentation "Traverse tree rooted at NODE in preorder.  At each
node, call FN.  If the returned value is non-nil, it replaces the node
and traversal continues.  If the returned value is nil stop traversal.
If any child is replaced also replace the parent node (as the trees
are applicative.)"))

(defmethod traverse-tree ((node t) (fn function)) node)

(defmethod traverse-tree ((node node) (fn function))
  (block nil
    (let ((new (funcall fn node)))
      (when (null new) (return nil))
      (if-let ((keys (mapcar-children new fn)))
        (apply #'copy new keys)
        new))))

(defgeneric map-only-children/i (node index fn)
  (:documentation "Call FN on each child of NODE, along with
the INDEX augmented by the label of that child.  Do not descend
into subtrees."))

(defgeneric map-children/i (node index fn)
  (:documentation "Call FN on each child of NODE, along with the INDEX
  augmented by the label of that child, and descrend into subtrees in
  depth first order"))

(defmacro def-map-children/i (name child-op)
  "Define a method for a map-children-like method.  There was much
code duplication here before."
  ;; TODO: change this to work with slot-specifier objects
  `(defmethod ,name ((node node) (index list) (fn function))
     (let* ((child-slots (child-slots node)))
       (declare (type fixnum))
       (dolist (child-slot child-slots)
         (let ((name (slot-spec-slot child-slot)))
           (if (eql 1 (slot-spec-arity child-slot))
               ;; Single arity just add slot name.
               (,child-op (slot-value node name)
                          ;; TODO: precompute this keyword in slot-spec
                          (list* name index)
                          fn)
               ;; Otherwise add slot name and index into slot.
               (let ((child-list (child-list node child-slot))
                     (counter 0))
                 (declare (type fixnum counter))
                 (dolist (child child-list)
                   (,child-op
                    child (list* (cons name counter) index) fn)
                   (incf counter)))))))))

(def-map-children/i map-children/i pure-traverse-tree/i)
(def-map-children/i map-only-children/i (lambda (child path fn) (funcall fn child path)))

(defmethod map-children ((node t) (fn function)) nil)

(defmethod map-children ((node node) (fn function))
  (let ((child-slots (child-slots node)))
    (dolist (child-slot child-slots)
      (dolist (child (child-list node child-slot))
        (pure-traverse-tree child fn)))))

(defgeneric mapcar-children (node fn)
  (:documentation "Apply traverse-children recursively to children of NODE,
returning a plist suitable for passing to COPY"))

(defmethod mapcar-children ((node t) (fn function)) nil)

;;; TODO change this to work with slot-specifier objects
(defmethod mapcar-children ((node node) (fn function))
  (mappend
   (lambda (child-slot &aux modifiedp)
      (let ((children
             (cl:mapcar (lambda (child)
                          (let ((new (traverse-tree child fn)))
                            (unless (eq new child) (setf modifiedp t))
                            new))
                        (child-list node child-slot))))
        ;; Adjust the children list for special arities.
        (case (slot-spec-arity child-slot)
          ;; Unpack a single-arity child from the list.
          (1 (setf children (car children)))
          ;; Remove nils from flexible-arity child lists.
          (0 (setf children (remove nil children))))
        (when modifiedp
          ;; TODO: precompute keyword in slot spec
          (list (make-keyword (slot-spec-slot child-slot))
                children))))
   (child-slots node)))

(defgeneric node-valid (node)
  (:documentation "True if the tree rooted at NODE have EQL unique
serial-numbers, and no node occurs on two different paths in the tree"))

(defmethod node-valid ((node node))
  (let ((serial-number-table (make-hash-table)))
    (do-tree (n node :value t)
      (prog1 nil
        (let ((serial-number (serial-number n)))
          (when (gethash serial-number serial-number-table)
            (return-from node-valid nil))
          (setf (gethash serial-number serial-number-table) n))))))

(defun store-nodes (node table)
  (do-tree (n node) (prog1 nil (setf (gethash (serial-number n) table) n))))

(defgeneric nodes-disjoint (node1 node2)
  (:documentation "Return true if NODE1 and NODE2 do not share
any serial-number"))

(defmethod nodes-disjoint ((node1 node) (node2 node))
  (let ((serial-number-table (make-hash-table)))
    ;; Populate serial-number table
    (store-nodes node1 serial-number-table)
    ;; Now check for collisions
    (do-tree (n node2 :value t)
      (prog1 nil
        (when (gethash (serial-number n) serial-number-table)
          (return-from nodes-disjoint nil))))))

(defgeneric node-can-implant (root at-node new-node)
  (:documentation "Check if new-node can replace the subtree rooted at at-node
below ROOT and produce a valid tree."))

;;; TODO -- reimplement this with descendant-map
(defmethod node-can-implant ((root node) (at-node node) (new-node node))
  (let ((serial-number-table (make-hash-table)))
    ;; Populate serial-number table
    (do-tree (n root)
      ;; Do not store serial-numbers at or below at-node
      (if (eq n at-node)
          t
          (prog1 nil
            (setf (gethash (slot-value n 'serial-number) serial-number-table)
                  n))))

    ;; Check for collisions
    (do-tree (n new-node :value t)
      (prog1 nil
        (when (gethash (serial-number n) serial-number-table)
          (return-from node-can-implant nil))))))

(defun lexicographic-< (list1 list2)
  "Lexicographic comparison of lists of reals,  symbols, or pairs.
Symbols are considered to be less than reals, and symbols
are compared with each other using fset:compare"
  (loop
     (unless list1
       (return (not (null list2))))
     (unless list2
       (return nil))
     (let ((c1 (pop list1))
           (c2 (pop list2)))
       (cond
         ((symbolp c1)
          (unless (symbolp c2) (return t))
          (unless (eql c1 c2)
            (return (string< c1 c2))))
         ((symbolp c2) (return nil))
         ((consp c1)
          (unless (consp c2)
            (return t))
          (let ((c1a (car c1))
                (c2a (car c2)))
            (assert (symbolp c1a))
            (assert (symbolp c2a))
            (unless (eql c1a c2a)
              (return (string< c1a c2a))))
          (let ((c1d (cdr c1))
                (c2d (cdr c2)))
            (cond
              ((< c1d c2d) (return t))
              ((> c1d c2d) (return nil)))))
         ((consp c2) (return nil))
         ((<= c1 c2)
          (when (< c1 c2)
            (return t)))
         (t (return nil))))))

(defun prefix? (p1 p2)
  "True if list P1 is a prefix of P2"
  (loop (cond
          ((null p1) (return t))
          ((null p2) (return nil))
          ((eql (car p1) (car p2))
           (pop p1)
           (pop p2))
          (t (return nil)))))

(defgeneric equal? (a b)
  (:documentation "Test equality of A and B.")
  (:method ((a t) (b t)) (fset:equal? a b))
  (:method ((node1 node) (node2 node))
    (and (eql (serial-number node1) (serial-number node2))
         (eql (type-of node1) (type-of node2))
         (let ((c1 (children node1))
               (c2 (children node2)))
           (and (length= c1 c2)
                (every #'equal? c1 c2))))))


;;; Rewrite encapsulation
;;; The idea here is to allow grouping of several changes to a tree
;;; into a single change.  The intermediate changes do not need to be
;;; remembered, and the tree need not be in a consistent state during
;;; them.

(defun encapsulate (tree rewrite-fn)
  "Apply REWRITE-FN to TREE, producing a new tree.  The new
tree has its predecessor set to TREE."
  (funcall rewrite-fn tree))

;;; This is deprecated
(defmacro with-encapsulation (tree &body body)
  (let ((var (gensym)))
    `(encapsulate ,tree #'(lambda (,var) (declare (ignore ,var)) ,@body))))


;;;; FSet interoperability.

;;; Define `lookup' methods to work with FSet's `@' macro.
(defmethod lookup ((node t) (path null)) node)
(defmethod lookup ((node t) (location node))
  (lookup node (path-of-node node location)))
(defmethod lookup ((node node) (path cons))
  (etypecase path
    (proper-list
     (lookup (lookup node (car path)) (cdr path)))
    (cons
     (destructuring-bind (slot . i) path
       (lookup (slot-value node (get-actual-slot slot)) i)))))
(defmethod lookup ((node node) (slot null))
  node)
(defmethod lookup ((node node) (slot symbol))
  (slot-value node (get-actual-slot slot)))
(defmethod lookup ((node node) (i integer))
  (elt (children node) i))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defun parse-specialized-lambda-list (lambda-list)
    "Similar to Alexandria's PARSE-ORDINARY-LAMBDA-LIST, but can
handle lambda lists for method argments."
    (let ((args nil))
      (iter (while (consp lambda-list))
        (let ((p (car lambda-list)))
          (while (or (consp p)
                     (and (symbolp p)
                          (not (member p lambda-list-keywords)))))
          (push (if (symbolp p) p (car p)) args)
          (pop lambda-list)))
      (parse-ordinary-lambda-list (nreconc args lambda-list))))

  (defun vars-of-specialized-lambda-list (lambda-list)
    "List of the variables bound by a lambda list"
    (multiple-value-bind (req opt rest key allow-other-keys aux)
        (parse-specialized-lambda-list lambda-list)
      (declare (ignore allow-other-keys))
      (append req
              (cl:mapcar #'car opt)
              (cl:remove nil (cl:mapcar #'caddr opt))
              (when rest (list rest))
              (cl:mapcar #'cadar key)
              (cl:remove nil (cl:mapcar #'caddr key))
              (cl:mapcar #'car aux)))))


;;; TODO change this to work with slot-specifier objects
(defmacro descend ((name &key other-args extra-args replace splice checks
                           (missing :error))
                   &body new
                     ;; VARS is used to generate IGNORABLE declarations to avoid
                     ;; style warnings
                   &aux (vars (vars-of-specialized-lambda-list (append other-args extra-args))))
  "Define generic functions which descend (and return) through functional trees.
This is useful to define standard FSet functions such as `with',
`less', etc...  Keyword arguments control specifics of how the
recursion works and how the generic functions are defined.  OTHER-ARGS
specifies additional arguments that are used.  EXTRA-ARGS defines
additional arguments that are not used.  REPLACE is a boolean flagging
if NEW replaces the target or is added alongside the target.  SPLICE
is a boolean flagging if NEW is inserted or spliced.  CHECKS allows
for the specification of checks to run at the beginning of the
functions.  MISSING specifies what to do if a node argument
is not present in the tree:  :ERROR means signal an error,
:NOOP means do nothing (return the unchanged tree), and :ROOT
act on the root of the tree (the previous behavior)."
  (flet ((arg-values (args) (cl:mapcar #'car (cl:remove '&optional args))))
    `(progn
       (defmethod ,name ((tree node) (path null) ,@other-args ,@extra-args)
          (declare (ignorable ,@vars))
         ,@checks (values ,@new))
       (defmethod ,name ((tree node) (location node) ,@other-args ,@extra-args)
         (declare (ignorable ,@vars))
         ,@checks
         (let ((path (path-of-node tree location)))
           ,(ecase missing
              (:root `(,name tree path ,@(arg-values other-args)))
              (:noop `(if (and (null path) (not (eql location tree)))
                          tree
                          (,name tree path ,@(arg-values other-args))))
              (:error `(if (and (null path) (not (eql location tree)))
                           (error "In ~a, node ~a not found in tree ~a"
                                  ',name location tree)
                           (,name tree path ,@(arg-values other-args)))))))
       (defmethod ,name ((tree node) (slot symbol) ,@other-args ,@extra-args)
          (declare (ignorable ,@vars))
         ,@checks (copy tree (make-keyword slot) ,@new))
       (defmethod ,name ((tree node) (path cons) ,@other-args ,@extra-args)
          (declare (ignorable ,@vars))
         ,@checks
         ;; At the end of the path, so act directly.
         (typecase (cdr path)
           (null (,name tree (car path) ,@(arg-values other-args)))
           (cons
             (etypecase (car path)
               (symbol
                (copy tree
                      (make-keyword (if (symbolp (car path))
                                        (car path)
                                        (caar path)))
                      (,name (lookup tree (car path)) (cdr path)
                             ,@(arg-values other-args))
                      ))
               ((cons symbol (integer 0))
                (let ((slot (caar path))
                      (i (cdar path)))
                  (copy tree
                        (make-keyword slot)
                        (let ((subs (lookup tree slot)))
                          (assert (listp subs))
                          (append (subseq subs 0 i)
                                  (cons (,name (elt subs i) (cdr path)
                                               ,@(arg-values other-args))
                                        (subseq subs (1+ i))))))))
               ((integer 0)
                ;; (format t "(integer 0)~%")
                (reduce
                 (lambda (i child-slot)
                   (nest
                    (let* ((slot (if (consp child-slot)
                                     (car child-slot)
                                     child-slot))
                           (children (slot-value tree slot))
                           (account (if (listp children) (length children) 1))))
                    (if (>= i account) (- i account))
                    (return-from ,name
                      (copy tree (make-keyword slot)
                            (if (listp children)
                                (append (subseq children 0 i)
                                        (list (,name (nth i children) (cdr path)
                                                     ,@(arg-values other-args)))
                                        (subseq children (1+ i)))
                                ,@new)))))
                 (child-slots tree)
                 :initial-value (car path)))))
           (t ;; must be (<symbol> . <index>)
            (assert (symbolp (car path)))
            (assert (typep (cdr path) '(integer 0)))
            (copy tree
                  (make-keyword (car path))
                  (,name (lookup tree (car path)) (cdr path)
                         ,@(arg-values other-args))))
           ))
       (defmethod ,name ((tree node) (i integer) ,@other-args ,@extra-args)
         (declare (ignorable ,@vars))
         ,@checks
         (reduce (lambda (i child-slot)
                   (let* ((slot (if (consp child-slot)
                                    (car child-slot)
                                    child-slot))
                          (children (slot-value tree slot))
                          (account (cond
                                     ;; Explicit arity
                                     ((and (consp child-slot)
                                           ;; Explicit arity of 0
                                           ;; means unspecified hence
                                           ;; '(integer 1).
                                           (typep (cdr child-slot) '(integer 1)))
                                      (cdr child-slot))
                                     ;; Populated children
                                     ((listp children) (length children))
                                     (t 1))))
                     (if (>= i account)
                         (- i account)
                         (return-from ,name
                           (copy tree (make-keyword slot)
                                 (if children
                                     (if (listp children)
                                         (,name children i
                                                ,@(arg-values other-args))
                                         ,@new)
                                     ,@new))))))
                 (child-slots tree)
                 :initial-value i)
         (error ,(format nil "Cannot ~a beyond end of children." name)))
       (defmethod ,name ((list list) (i integer) ,@other-args ,@extra-args)
         (declare (ignorable ,@vars))
         ,@checks
         (append (subseq list 0 i)
                 ,@(if splice `,new `((list ,@new)))
                 (subseq list ,(if replace '(1+ i) 'i)))))))

(descend (with :other-args (&optional (value nil valuep))
               :checks ((fset::check-three-arguments valuep 'with 'node))
               :replace t)
  value)

(descend (less :extra-args (&optional (arg2 nil arg2p))
               :checks ((declare (ignore arg2))
                        (fset::check-two-arguments arg2p 'less 'node))
               :replace t :splice t)
  nil)

(descend (splice :other-args ((values list)) :splice t) values)

(descend (insert :other-args ((value t))) value)

(defgeneric swap (tree location-1 location-2)
  (:documentation "Swap the contents of LOCATION-1 and LOCATION-2 in TREE.")
  (:method ((tree node) (location-1 list) (location-2 list))
    (let ((value-1 (@ tree location-1))
          (value-2 (@ tree location-2)))
      ;; Use a temporary place-holder node to ensure that neither node
      ;; ever appears twice in the tree at the same time.
      (reduce (lambda (tree pair)
                (destructuring-bind (location . value) pair
                  (with tree location value)))
              (list (cons location-1 (make-instance (class-of value-1)))
                    (cons location-2 value-1)
                    (cons location-1 value-2))
              :initial-value tree)))
  (:method ((tree node) (location-1 node) location-2)
    (swap tree (path-of-node tree location-1) location-2))
  (:method ((tree node) location-1 (location-2 node))
    (swap tree location-1 (path-of-node tree location-2)))
  (:method :around ((tree node) (location-1 t) (location-2 t))
    (with-encapsulation tree (call-next-method))))

(defmethod size ((other t)) 0)

(defmethod print-object ((obj node) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a" (serial-number obj) (cdr (convert 'list obj))))))

(defmethod print-object ((obj slot-specifier) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a" (slot-specifier-slot obj)
                (slot-specifier-arity obj)))))

;;;; FSET conversion operations
(defmethod convert ((to-type (eql 'list)) (node node) &key &allow-other-keys &aux all)
  "Convert NODE of type node to a list."
  (mapc (lambda (node) (push node all)) node)
  (nreverse all))

(defmethod convert ((to-type (eql 'alist)) (node node)
                    &key (value-fn nil value-fn-p) &allow-other-keys)
  (convert
   'list node :value-fn
   (if value-fn-p value-fn
       (let ((slots
              (nest
               (cl:remove-if
                (rcurry #'member (append '(serial-number transform finger
                                           child-slots size descendant-map)
                                         (cl:mapcar (lambda (slot)
                                                      (etypecase slot
                                                        (symbol slot)
                                                        (cons (car slot))))
                                                    (child-slots node)))))
               (cl:mapcar #'slot-definition-name
                          (class-slots (class-of node))))))
         (lambda (node)
           (apply #'append
                  (cl:mapcar (lambda (slot)
                               (when-let ((val (slot-value node slot)))
                                         (list (cons (make-keyword slot) val))))
                             slots)))))))


;;; FSET sequence operations (+ two) for functional tree.

(defmacro define-map-compiler-macro (ft-fn cl-fn)
  "Define a compiler macro for mapping functions."
  `(define-compiler-macro ,ft-fn (&whole call fn container &rest more)
     (if (not more)
         (once-only (fn container)
           `(if (consp ,container)
                (,',cl-fn ,fn ,container)
                (locally (declare (notinline ,',ft-fn))
                  (,',ft-fn ,fn ,container))))
         call)))

(define-map-compiler-macro mapc cl:mapc)
(define-map-compiler-macro mapcar cl:mapcar)

(defgeneric mapc (function container &rest more)
  (:documentation "Map FUNCTION over CONTAINER.")
  (:method (function (nothing null) &rest more)
    (declare (ignorable more))
    nil)
  (:method (function (anything t) &rest more)
    (prog1 anything (apply function anything more)))
  ;; ;; TODO: Ensure this doesn't override the list implementation.
  ;; (:method (function (cons cons) &rest more)
  ;;   (fset::check-two-arguments more 'mapc 'cons)
  ;;   (warn "mapc cons overriding list on ~S?" cons)
  ;;   (prog1 cons
  ;;     (mapc function (car cons))
  ;;     (mapc function (cdr cons))))
  (:method (function (sequence sequence) &rest more)
    (apply #'cl:mapc function sequence more)))

(defmethod mapc (function (tree node) &rest more)
  (fset::check-two-arguments more 'mapc 'node)
  (let ((function (ensure-function function)))
    (do-tree (node tree :value tree)
      (funcall function node)
      nil)))

(defgeneric mapcar (function container &rest more)
  (:documentation "Map FUNCTION over CONTAINER.")
  (:method (function (nothing null) &rest more)
    (declare (ignorable more))
    nil)
  (:method (function (anything t) &rest more) (apply function anything more))
  ;; ;; TODO: Ensure this doesn't override the list implementation.
  ;; (:method (function (cons cons) &rest more)
  ;;   (fset::check-two-arguments more 'mapcar 'cons)
  ;;   (warn "mapcar cons overriding list on ~S?" cons)
  ;;   (cons (mapcar function (car cons))
  ;;         (mapcar function (cdr cons))))
  (:method (function (sequence sequence) &rest more)
    (apply #'cl:mapcar function sequence more))
  (:method (predicate (seq seq) &rest more &aux result)
    ;; TODO: handle MORE.
    (declare (ignorable more))
    (let ((predicate (ensure-function predicate)))
      (do-seq (element seq)
        (push (funcall predicate element) result))
      (convert 'seq (nreverse result))))
  (:method (function (sequence list) &rest more)
    (apply #'cl:mapcar function sequence more)))

(defmethod mapcar (function (tree node) &rest more)
  "Map FUNCTION over TREE collecting the results into a new tree.
Non-nil return values of FUNCTION replace the current node in the tree
and nil return values of FUNCTION leave the existing node."
  (fset::check-two-arguments more 'mapcar 'node)
  (let ((function (ensure-function function)))
    (do-tree (node tree :rebuild t)
      (or (funcall function node) node))))

(defmethod reduce
    (fn (node node)
      &key key initial-value ;; start end from-end
      &allow-other-keys
      &aux (accumulator initial-value))
  (let ((fn (ensure-function fn)))
    (with-item-key-function (key)
      (do-tree (node node :value accumulator)
        (setf accumulator (funcall fn accumulator (key node)))
        nil))))

(defmacro test-handler (fn)
  "This macro is an idiom that occurs in many methods.  It handles
checking and normalization of :TEST and :TEST-NOT arguments."
  `(nest
    (if test-p (progn
                 (assert (not test-not-p) () ,(format nil "~a given both :TEST and :TEST-NOT" fn))
                 (setf test (coerce test 'function))))
    (when test-not-p (setf test (complement (coerce test-not 'function))))))

(defmethod find-if (predicate (node node)
                    &key from-end end start key)
  (assert (not (or from-end end start))
          (from-end end start)
          "TODO: implement support for ~a key in `find-if'"
          (cdr (find-if #'car
                        (cl:mapcar #'cons
                                   (list from-end end start)
                                   '(from-end end start)))))
  (block done
    (let ((predicate (ensure-function predicate)))
      (with-item-key-function (key)
        (do-tree (node node)
          (when (funcall predicate (key node))
            (return-from done node)))))))

(defmethod find-if-not
    (predicate (node node) &key (key nil key-p) &allow-other-keys)
  (multiple-value-call #'find-if (complement predicate) node
                       (if key-p (values :key key) (values))))

(defmethod find (item (node node)
                 &key (test #'eql test-p) (test-not nil test-not-p) (key nil key-p) &allow-other-keys)
  (test-handler position)
  (multiple-value-call #'find-if (curry test item) node
                       (if key-p (values :key key) (values))))

(defmethod count-if (predicate (node node)
                     &key from-end end start key &allow-other-keys
                     &aux (count 0))
  (assert (not (or from-end end start))
          (from-end end start)
          "TODO: implement support for ~a key in `find-if'"
          (cdr (find-if #'car
                        (cl:mapcar #'cons
                                   (list from-end end start)
                                   '(from-end end start)))))
  (let ((predicate (ensure-function predicate)))
    (with-item-key-function (key)
      (do-tree (node node :value count)
        (when (funcall predicate (key node))
          (incf count))
        nil))))

(defmethod count-if-not (predicate (node node)
                         &key (key nil key-p) &allow-other-keys)
  (multiple-value-call #'count-if (complement predicate) node
                       (if key-p (values :key key) (values))))

(defmethod count
    (item (node node)
     &key (test #'eql test-p) (test-not nil test-not-p) (key nil key-p)
       &allow-other-keys)
  (test-handler position)
  (multiple-value-call #'count-if (curry test item) node
                       (if key-p (values :key key) (values))))

(defmethod position-if (predicate (node node)
                        &key from-end end start
                          (key nil))
  (assert (not (or from-end end start))
          (from-end end start)
          "TODO: implement support for ~a key in `position-if'"
          (cdr (find-if #'car
                        (cl:mapcar #'cons
                                   (list from-end end start)
                                   '(from-end end start)))))
  (let ((predicate (ensure-function predicate)))
    (with-item-key-function (key)
      (do-tree (node node :index index)
        (when (funcall predicate (key node))
          (return-from position-if (values (nreverse index) t)))))))

(defmethod position-if-not (predicate (node node) &rest args
                            &key &allow-other-keys)
  (apply #'position-if (values (complement predicate)) node args))

(defmethod position (item (node node) &key (test #'eql test-p)
                                        (test-not nil test-not-p)
                                        (key nil key-p)
                                        &allow-other-keys)
  (test-handler position)
  (if (and (null key-p) (or (null test-p) (eql test 'eq) (eql test 'eql)
                            (eql test #'eq) (eql test #'eql)))
      (path-of-node node item :error nil)
      (multiple-value-call #'position-if (curry test item) node
        (if key-p (values :key key) (values)))))

(defgeneric child-position-if (predicate node &key key)
  (:documentation "Like POSITION-IF, but only apply to the children of NODE"))

(defmethod child-position-if (predicate (node node) &key (key nil))
  (block done
    (let ((predicate (ensure-function predicate)))
      (with-item-key-function (key)
        (flet ((fn (c i)
                 (when (funcall predicate (key c))
                   (return-from done i))))
          (declare (dynamic-extent #'fn))
          (map-only-children/i node nil #'fn))))))

(defgeneric child-position (value node &key key test)
  (:documentation "Like POSITION, but apply to the children of NODE.
Returns the path from NODE to the child, or NIL if not found.")
  (:method ((value t) (node node) &key key (test #'eql))
    (with-two-arg-test (test)
      (child-position-if (lambda (c) (test value c)) node :key key))))

(defmethod remove-if (predicate (node node) &key key &allow-other-keys)
  (let ((predicate (ensure-function predicate)))
    (with-item-key-function (key)
      (do-tree (node node :rebuild t)
        (and (not (funcall predicate (key node)))
             node)))))

;; TODO -- remove this
(defmethod remove-if :around (predicate (node node) &key &allow-other-keys)
  (call-next-method))

(defmethod remove-if-not (predicate (node node)
                          &key key  &allow-other-keys)
  (multiple-value-call
      #'remove-if (complement predicate) node
      (if key (values :key key) (values))))

(defmethod filter (predicate (node node))
  (remove-if-not predicate node))

(defmethod remove (item (node node)
                   &key (test #'eql test-p) (test-not nil test-not-p) key &allow-other-keys)
  (test-handler remove)
  (multiple-value-call #'remove-if (curry test item) node
                       (if key (values :key key) (values))))

(defmethod substitute-if (newitem predicate (node node)
                          &key (copy nil copy-p) key &allow-other-keys)
  (when copy-p (setf copy (coerce copy 'function)))
  (let ((predicate (ensure-function predicate)))
    (with-item-key-function (key)
      (with-boolean (copy-p)
        (let ((copy (:if copy-p (ensure-function copy) nil)))
          (declare (ignorable copy))
          (do-tree (node node :rebuild t)
            (if (funcall predicate (key node))
                (:if copy-p (funcall copy newitem) newitem)
                node)))))))

(defmethod substitute-if-not (newitem predicate (node node)
                              &key key copy &allow-other-keys)
  (multiple-value-call
      #'substitute-if newitem (values (complement predicate)) node
      (if key (values :key key) (values))
      (if copy (values :copy copy) (values))))

(defmethod substitute (newitem olditem (node node)
                       &key (test #'eql test-p) (test-not nil test-not-p)
                         key (copy nil copy-p) &allow-other-keys)
  (test-handler substitute)
  (multiple-value-call
      #'substitute-if newitem (curry test olditem) node
    (if key (values :key key) (values))
    (if copy-p (values :copy copy) (values))))

(defgeneric subst (new old tree &key key test test-not copy)
  (:documentation "If TREE is not a node, this simply calls `cl:subst'.")
  (:method (new old (tree node) &rest rest &key &allow-other-keys)
    (apply #'substitute new old tree rest))
  (:method (new old (tree t) &rest rest &key &allow-other-keys)
    (apply #'cl:subst new old tree rest)))

(defgeneric subst-if (new test tree &key key copy)
  (:documentation "If TREE is not a node, this simply calls `cl:subst-if'.
Also works on a functional tree node.")
  (:method (new test (tree node) &rest rest &key &allow-other-keys)
    (apply #'substitute-if new test tree rest))
  (:method (new test (tree t) &rest rest &key &allow-other-keys)
    (apply #'cl:subst-if new test tree rest)))

(defgeneric subst-if-not (new test tree &key key copy)
  (:documentation "Complements the test, and calls `subst-if'.
Also works on a functional tree node.")
  (:method (new test tree &key (key nil key-p) (copy nil copy-p))
    (multiple-value-call
        #'subst-if new (complement test) tree
        (if key-p (values :key key) (values))
        (if copy-p (values :copy copy) (values)))))
