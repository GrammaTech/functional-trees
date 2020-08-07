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
  (:use :common-lisp :alexandria :iterate :cl-store)
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
                          :remove :remove-if :remove-if-not
                          :substitute :substitute-if :substitute-if-not
                          :some :every :notany :notevery
                          ;; Additional stuff
                          :identity-ordering-mixin :serial-number
                          :compare :convert)
  (:shadow :subst :subst-if :subst-if-not :assert :mapc :mapcar)
  (:shadowing-import-from :alexandria :compose)
  (:import-from :uiop/utility :nest)
  (:import-from :closer-mop
                :slot-definition-name
                :slot-definition-allocation
                :slot-definition-initform
                :slot-definition-initargs
                :class-slots)
  (:export :copy :tree-copy
           :node :transform :child-slots :finger
           :path :transform-finger-to :populate-fingers :residue
           :serial-number
           :path-equalp
           :path-equalp-butlast
           :path-later-p
           :children
           :do-tree :mapc :mapcar
           :swap
           :define-node-class :define-methods-for-node-class)
  (:documentation
   "Prototype implementation of functional trees w. finger objects"))
(in-package :functional-trees)
;;; TODO: implement successor
;;; TODO: implement predecessor
;;; TODO: implement parent

(defmacro assert (&body body)
  ;; Copy the body of the assert so it doesn't pollute coverage reports
  `(cl:assert ,@(copy-tree body)))


(defclass node (identity-ordering-mixin)
  ((transform :reader transform
              :initarg :transform
              :initform nil
              ;; TODO: change the back pointer to a weak vector
              ;; containing the pointer.
              :type (or null node path-transform #+sbcl sb-ext:weak-pointer)
              :documentation "If non-nil, is either a PATH-TRANSFORM object
to this node, or the node that led to this node.")
   (size :reader size
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
   (finger :reader finger
           :initform nil
           :type (or null node finger)
           :documentation "A finger back to the root of the (a?) tree."))
  (:documentation "A node in a tree."))

(declaim (inline slot-spec-slot slot-spec-arity child-list))

(defun slot-spec-slot (slot-spec)
  (if (consp slot-spec) (car slot-spec) slot-spec))

(defun slot-spec-arity (slot-spec)
  (or (and (consp slot-spec) (cdr slot-spec)) 0))


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
    (and (= (length path-a) (length path-b))
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
  (assert (= (length syms) (length (remove-duplicates syms))))
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
  (:documentation "Does PATH-A from NODE represent an AST path after
PATH-B from NODE?   Use this to sort AST asts for mutations that perform
multiple operations.")
  (:method ((node t) (path-a null) (path-b null)) nil)
  (:method ((node node) (path-a null) (path-b null)) nil)
  (:method ((node t) (path-a null) (path-b cons)) nil)
  (:method ((node node) (path-a null) (path-b cons)) nil)
  (:method ((node t) (path-a cons) (path-b null)) t)
  (:method ((node node) (path-a cons) (path-b null)) t)
  (:method ((node t) (path-a list) (path-b list))
    ;; Consider longer paths to be later, so in case of nested ASTs we
    ;; will sort inner one first. Mutating the outer AST could
    ;; invalidate the inner ast.
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

(defgeneric tree-copy (obj)
  (:documentation "Copy method that descends into a tree and copies all
its nodes.")
  (:method ((obj t)) obj)
  (:method ((obj list)) (cl:mapcar #'tree-copy obj)))

(defmacro define-node-class (name &rest rest)
  `(progn
     (eval-when (:load-toplevel :compile-toplevel :execute)
       (defclass ,name ,@rest))
     (define-methods-for-node-class ,name)))

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

(defgeneric children (node)
  (:documentation "Return all children of NODE.")
  (:method ((node node))
    (mappend (lambda (slot)
               (destructuring-bind (name . arity)
                   (etypecase slot
                     (cons slot)
                     (symbol (cons slot 0)))
                 (if (= 1 arity)
                     (list (slot-value node name))
                     (slot-value node name))))
             (child-slots node))))

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

(defun expand-copying-setf-writers (class child-slots)
  `(progn
     ,@(cl:mapcar
        (lambda (form)
          (destructuring-bind (slot . arity)
              (etypecase form
                (symbol (cons form nil))
                (cons form))
            `(defmethod (setf ,slot) (new (obj ,class))
               ,@(when (and arity (numberp arity))
                   `((assert
                      (= ,arity (length new))
                      ()
                      ,(format nil "New value for ~a has wrong arity ~~a not ~a."
                               slot arity)
                      (length new))))
               ;; TODO: Actually I'm not sure what we want here.
               (copy obj ,(make-keyword slot) new))))
        child-slots)))

(defun expand-lookup-specialization (class child-slots)
  `(progn
     ,@(cl:mapcar (lambda (form)
                    (let ((slot (etypecase form
                                  (symbol form)
                                  (cons (car form)))))
                      `(defmethod lookup
                           ((obj ,class) (key (eql ,(make-keyword slot))))
                         (slot-value obj ',slot))))
                  child-slots)))

(defmacro define-methods-for-node-class (class-name &environment env)
  (let ((class (find-class class-name env)))
    (assert class () "No class found for ~s" class-name)
    ;; create an instance to cause the class to be finalized
    (make-instance class-name)
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
         ,(expand-children-defmethod class child-slots)
         ,(expand-lookup-specialization class child-slots)
         ,(expand-copying-setf-writers class child-slots)))))

;;; NOTE: We might want to propose a patch to FSet to allow setting
;;; serial-number with an initialization argument.
(defmethod initialize-instance :after
  ((node node) &key (serial-number nil serial-number-p) &allow-other-keys)
  (when serial-number-p
    (setf (slot-value node 'serial-number) serial-number)))

(defmethod transform :around ((n node))
  ;; Compute the PT lazily, when TRANSFORM is a node
  (let ((tr (call-next-method)))
    (if (typep tr 'node)
        (progn
          ; (format t "Compute path transform from ~a to ~a~%" tr n)
          (setf (slot-value n 'transform) (path-transform-of tr n)))
        tr)))

(defmethod slot-unbound ((class t) (obj node) (slot-name (eql 'size)))
  (setf (slot-value obj 'size)
        (reduce #'+ (children obj) :key #'size :initial-value 1)))

;;; NOTE: There should be a way to chain together methods for COPY for
;;; classes and their superclasses, perhaps using the initialization
;;; infrastructure in CL for objects.
(defmethod copy ((node node) &rest keys)
  (nest
   (apply #'make-instance (class-name (class-of node)))
   (apply #'append keys)
   (cl:mapcar (lambda (slot) (list (make-keyword slot) (slot-value node slot))))
   (cl:mapcar #'slot-definition-name )
   (remove-if (lambda (slot) (eql :class (slot-definition-allocation slot))))
   (class-slots (class-of node))))

;;; TODO -- specialize this in define-node-class
(defmethod tree-copy ((node node))
  (let* ((child-slots (slot-value node 'child-slots))
         (slots (remove-if (lambda (slot) (eql :class (slot-definition-allocation slot)))
                           (class-slots (class-of node))))
         (slot-names (remove 'serial-number
                             (cl:mapcar #'slot-definition-name slots)))
         (initializers (mappend (lambda (slot) (list (make-keyword slot)
                                                     (slot-value node slot)))
                                slot-names))
         (new-node (apply #'make-instance (class-name (class-of node))
                          initializers)))
    ;; Now write over the child slots
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

(defclass finger ()
  ((node :reader node :initarg :node
         :type node
         :initform (required-argument :node)
         :documentation "The node to which this finger pertains,
considered as the root of a tree.")
   (path :reader path :initarg :path
         :type path
         :initform (required-argument :path)
         :documentation "A list of nonnegative integer values
giving a path from node down to another node.")
   (residue :reader residue :initarg :residue
            :initform nil ;; (required-argument :residue)
            :type list
            :documentation "If this finger was created from another
finger by a path-transform, some part of the path may not have been
translated.  If so, this field is the part that could not be handled.
Otherwise, it is NIL.")
   (cache :accessor cache
         :documentation "Internal slot used to cache the lookup of a node."))
  (:documentation "A wrapper for a path to get to a node"))



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
is to be deleted (from a variable arity list of children in its parent."
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
           (rebuild `(update-predecessor-tree ,tree-var (traverse-tree ,tree-var #',body-fn)))
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

(defgeneric update-predecessor-tree (old-tree new-tree)
  (:documentation "Sets the back pointer of NEW-TREE to be OLD-TREE,
if NEW-TREE lacks a back pointer.  Returns NEW-TREE."))

(defmethod update-predecessor-tree ((old-tree t) (new-tree t)) new-tree)

(defmethod update-predecessor-tree ((old-tree node) (new-tree node))
  (or (slot-value new-tree 'transform)
      (setf (slot-value new-tree 'transform) old-tree))
  new-tree)

(defgeneric traverse-tree (node fn)
  (:documentation "Traverse tree rooted at NODE in preorder.
At each node, call FN.  If the first value returned is true,
replaced node by the second returned value and continued the
traversal.  If any child is replaced also replace the parent
node (as the trees are applicative.)"))

(defmethod traverse-tree ((node t) (fn function)) node)

(defmethod traverse-tree ((node node) (fn function))
  (block nil
    (let ((new (funcall fn node)))
      (when (null new) (return nil))
      (if-let ((keys (mapcar-children new fn)))
        (apply #'copy new keys)
        new))))

(defgeneric map-children/i (node index fn)
  (:documentation "Call FN on each child of NODE, along with the INDEX
augmented by the label of that child."))

(defmethod map-children/i ((node node) (index list) (fn function))
  (let* ((child-slots (child-slots node))
         (num-slots (length child-slots)))
    (declare (type fixnum))
    (dolist (child-slot child-slots)
      (let ((name (slot-spec-slot child-slot)))
        (if (eql 1 (slot-spec-arity child-slot))
            ;; Single arity just add slot name.
            (pure-traverse-tree/i (slot-value node name)
                                  ;; TODO: precompute this keyword in slot-spec
                                  (list* name index)
                                  fn)
            ;; Otherwise add slot name and index into slot.
            (let ((child-list (child-list node child-slot))
                  (counter 0))
              (declare (type fixnum counter))
              (if (and (eql 1 num-slots) (eql name 'children))
                  (dolist (child child-list)
                    (pure-traverse-tree/i child (list* counter index) fn)
                    (incf counter))
                  (dolist (child child-list)
                    (pure-traverse-tree/i
                     child (list* (cons name counter) index) fn)
                    (incf counter)))))))))

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

(defmethod mapcar-children ((node node) (fn function))
  (mappend
   (lambda (child-slot &aux modifiedp)
      (let ((children
             (cl:mapcar (lambda (child)
                          (let ((new (traverse-tree child fn)))
                            (unless (eql new child) (setf modifiedp t))
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

;;; The Path should hold
;;; - a raw index into the children
;;; - a cons of child-slot and index

(defmethod slot-unbound ((class t) (f finger) (slot (eql 'cache)))
  ;; Fill in the NODE slot of finger F
  (let* ((node (node f))
         (path (path f)))
    (iter (for i in path)
          (unless (typep node 'node)
            (error "Path ~a not valid for tree rooted at ~a: ~a"
                   (path f) (node f) node))
          (destructuring-bind (slot . index)
              (etypecase i
                (cons i)
                (fixnum
                 (cond
                   ((= 1 (length (child-slots node)))
                    (if (consp (first (child-slots node)))
                        (if (>= i (cdr (first (child-slots node))))
                            (error
                             "numeric index ~a too large for child slot ~a"
                             i (first (child-slots node)))
                            (cons (car (first (child-slots node))) i))
                        (cons (first (child-slots node)) i)))
                   ((every (lambda (slot)
                             (and (consp slot)
                                  (typep (cdr slot) '(integer 1))))
                           (child-slots node))
                    (let ((index 0))
                      (or (iter (for (slot . size) in (child-slots node))
                                (when (> (+ index size) i)
                                  (return (cons slot (- i index))))
                                (incf index size))
                          (error "numeric index ~a too large for child slots ~s"
                                 i (child-slots node)))))
                   (t
                    (error "numeric index ~a used with ambiguous child slots ~s"
                           i (child-slots node))))))
            (let ((value (slot-value node slot)))
              (dolist (p (child-slots node) (error "Child slot not found: ~a" slot))
                (if (consp p)
                    (when (eql (car p) slot)
                      (return
                        (if (eql (cdr p) 1)
                            (setf node value)
                            (progn
                              (unless (and (<= 0 index) (< index (length value)))
                                (error "~a not a valid child index for ~a" index node))
                              (setf node (elt value index))))))
                    (when (eql p slot)
                      (return
                        (progn
                          (unless (and (<= 0 index) (< index (length value)))
                            (error "~a not a valid child index for ~a" index node))
                          (setf node (elt value index))))))))))

    ;; This assignment is functionally ok, since it is assigned
    ;; only once when the cache is filled
    (setf (slot-value f 'cache) node)))

(defclass path-transform ()
  ((from
    :reader from :initarg :from
    :type node
    :initform (required-argument :from))
   (transforms :initarg :transforms
               :reader transforms
               :type list
               :documentation "A list of (<path-set> <path> <status>) triples
where <path-set> is a path set, <path> is the mapping of the initial path
in that <path-set>, and <status> is one of :live :dead. These should be
sorted into non-increasing order of length of <path>.  If missing, compute
from the source/target node pair, if possible."))
  (:documentation "An object used to rewrite fingers from one
tree to another."))

(defgeneric predecessor-chain (n)
  (:documentation "REturns the list of predecessor trees of N"))

(defmethod predecessor-chain ((n node))
  (let ((tr (slot-value n 'transform)))
    (typecase tr
      (node (cons tr (predecessor-chain tr)))
      (path-transform (cons (from tr) (predecessor-chain (from tr)))))))

(defmethod from ((x null)) x)

(defgeneric transform-finger-to (f p to)
  (:documentation "Converts a finger from one tree to another."))

;;; Around method to verify pre, post conditions
(defmethod transform-finger-to :around ((f finger) (p path-transform) (to node))
  (assert (eql (node f) (from p)))
  (let ((new-finger (call-next-method)))
    (assert (typep new-finger 'finger))
    new-finger))

(defmethod transform-finger-to ((f finger) (p path-transform) (to node))
  (multiple-value-bind (new-path residue)
      (transform-path (path f) (transforms p))
    (make-instance 'finger :path new-path
                   :node to :residue residue)))

(defclass trie ()
  ((root :initarg :root :accessor root
         :type trie-node)))

(defclass trie-node ()
  ((data :initform nil :initarg :data
         :accessor data
         :documentation "Data for segments that end at this trie node,
or NIL if no such segments end here.")
   (map :initform nil :initarg :map
        :type list
        :accessor trie-map
        :documentation "Alist mapping indices to trie nodes")))

(defun make-trie ()
  (make-instance 'trie :root (make-instance 'trie-node)))

;;; TODO: make trie maps switch over to hash tables if the alist
;;;   gets too long

(defgeneric trie-insert (trie segment data)
  (:method ((trie trie) (segment list) (data t))
    ;; Find the trie node for SEGMENT
    (let ((node (root trie)))
      (iter (when (null segment)
              (setf (data node) data)
              (return))
            (let* ((map (trie-map node))
                   (i (car segment))
                   (p (assoc i (trie-map node) :test #'equal)))
              (if p
                  (setf node (cdr p)
                        segment (cdr segment))
                  (let ((child (make-instance 'trie-node)))
                    (setf (trie-map node) (cons (cons i child) map))
                    (pop segment)
                    (setf node child))))))))

(defun transforms-to-trie (transforms)
  "Construct a trie for TRANSFORMS, which is a list as described
in the transforms slot of PATH-TRANSFORMS objects."
  (let ((trie (make-trie)))
    (iter (for (segment new-initial-segment status) in transforms)
          (trie-insert trie segment (list new-initial-segment status)))
    trie))

(defgeneric transform-path (path transforms))

(defmethod transform-path ((orig-path list) (trie trie))
  (let ((node (root trie))
        (path orig-path)
        suffix
        deepest-match)
    (iter (let ((d (data node)))
            (when d
              (setf suffix path
                    deepest-match d)))
          (while path)
          (let* ((i (car path))
                 (p (assoc i (trie-map node) :test #'equal)))
            (unless p (return))
            (setf node (cdr p)
                  path (cdr path))))
    (if (null deepest-match)
        orig-path
        (destructuring-bind (new-segment status)
            deepest-match
          (ecase status
            (:live (append new-segment suffix))
            (:dead (values new-segment
                           (subseq orig-path (length new-segment)))))))))

(defmethod transform-path ((path list) (transforms list))
  (transform-path path (transforms-to-trie transforms)))

(defgeneric transform-finger (finger node &key error-p)
  (:documentation "Transforms FINGER, producing a new finger that
points through the root NODE.  NODE must be derived from the tree
that FINGER is pointed through."))

(defmethod transform-finger ((f finger) (node node) &key (error-p t))
  (declare (ignore error-p)) ;; for now

  ;;; TODO: cache PATH-TRANSFORM-OF

  ;; When placing a subtree with nonempty FINGER slot into another
  ;; tree, we may end up with paths that require brute force
  ;; computation of the path transform.  Do that if we cannot
  ;; find the transform in the predecessor chain.  TODO: cache
  ;; these with weak key hash tables to avoid recomputation.

  (flet ((%brute-force ()
           (return-from transform-finger
             (let ((node-of-f (node f)))
               #+ft-debug-transform-finger
               (progn (format t "(TRANSFORM (NODE F)) = ~a~%" (transform (node f)))
                      (format t "(TRANSFORM NODE) = ~a~%" (transform node)))
               (transform-finger-to f (path-transform-of node-of-f node) node)))))

    ;; This feature is intended for testing, and is not part of the normal
    ;; public API.  If you suspect a problem with finger/path tranform
    ;; computation enable this feature and see if your issue goes away.
    #+brute-force-transform-finger
    (%brute-force)

    #-brute-force-transform-finger
    (let* ((f f) (node-of-f (node f)))
      #+ft-debug-transform-finger
      (format t "NODE-OF-F = ~a~%" node-of-f)
      (labels ((%transform (x)
                 #+ft-debug-transform-finger
                 (format t "%transform ~a~%" x)
                 (cond
                   ((eql x node-of-f) f)
                   ((null x)
                    (%brute-force))
                   (t
                    (let ((transform (transform x)))
                      #+ft-debug-transform-finger
                      (format t "(TRANSFORM x) = ~a~%" transform)
                      (transform-finger-to
                       (%transform (from transform))
                       transform x))))))
        (%transform node)))))

(defgeneric populate-fingers (root &optional initial-rpath)
  (:documentation "Walk tree, creating fingers back to root.  RPATH
is a reversed list of nodes to be prepended to each path.")
  (:method ((root node) &optional initial-rpath)
    (do-tree (n root :index rpath :value root)
      ;; This is the only place this slot should be
      ;; assigned, which is why there's no writer method.
      (unless (finger n)
        (prog1 nil
          (setf (slot-value n 'finger)
                (make-instance 'finger :node root
                               :path (nreconc initial-rpath
                                              (reverse rpath)))))))
    root)
  (:method ((root null) &optional initial-rpath)
    (declare (ignore initial-rpath))
    nil))

;;; Computes the path leading from ROOT to NODE.
(defun path-of-node (root node)
  (unless (finger node)
    (populate-fingers root))
  (path (transform-finger (finger node) root)))

;;; To add: algorithm for extracting a  path transform from
;;; a set of rewrites (with var objects).  (Is this still relevant?)
;;  Also, conversion of the transform set to a trie.

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
  (:documentation "Check if new-node can the subtree rooted at at-node
below ROOT and produce a valid tree."))

(defmethod node-can-implant ((root node) (at-node node) (new-node node))
  (let ((serial-number-table (make-hash-table)))
    ;; Populate serial-number table
    (do-tree (n root)
      ;; Do not store serial-numbers at or below at-node
      (if (eql n at-node)
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

(defgeneric path-transform-of (from-node to-node)
  (:documentation "Produce a path transform that maps FROM-NODE to TO-NODE"))

(defclass node-heap ()
  ((heap :initform (make-array '(10))
         :type simple-vector
         :accessor node-heap/heap)
   (count :initform 0
          :type (integer 0)
          :accessor node-heap/count))
  (:documentation "Max heaps for path-transform computation"))

(defun make-node-heap ()
  (make-instance 'node-heap))

(deftype node-heap-index () '(integer 0 #.most-positive-fixnum))

(defstruct node-heap-data
  (node nil)
  (size 0)
  (path nil)
  (sn 0))

#+debug-node-heap
(defmethod check-heap ((nh node-heap))
  "Heap state consistency check"
  (let ((heap (node-heap/heap nh))
        (count (node-heap/count nh)))
    (iter (for i from 1 below count)
          (assert (node-heap-data-<
                   (aref heap i)
                   (aref heap (ash (1- i) -1)))))))

(defun node-heap-pop (nh)
  (declare (type node-heap nh))
  (nest
   (with-slots (heap count) nh)
   (if (eql count 0) nil)
   (let ((d (aref heap 0)))
     (decf count)
     (when (> count 0)
       (setf (aref heap 0) (aref heap count)
             (aref heap count) 0)
       (node-heap-sift-down heap count))
     #+debug-node-heap (check-heap nh)
     (values (node-heap-data-node d)
             (node-heap-data-size d)
             (node-heap-data-sn d)
             (node-heap-data-path d)))))

(declaim (inline node-heap-data-<))
(defun node-heap-data-< (nd1 nd2)
  (let ((s1 (node-heap-data-size nd1))
        (s2 (node-heap-data-size nd2)))
    (or (< s1 s2)
        (and (= s1 s2)
             (< (node-heap-data-sn nd1)
                (node-heap-data-sn nd2))))))

(defun node-heap-sift-down (heap count)
  (declare ; (type node-heap-index count)
           (type simple-vector heap))
  (let ((i 0)
        (n (aref heap 0)))
    (declare (type node-heap-index i))
    (iter (let ((l (1+ (the node-heap-index (+ i i)))))
            (declare (type node-heap-index l))
            (when (>= l count) (return))
            (let ((r (1+ l)))
              (declare (type node-heap-index r))
              (when (>= r count)
                (let ((ln (aref heap l)))
                  (if (node-heap-data-< n ln)
                      (setf (aref heap i) ln
                            (aref heap l) n)
                      (setf (aref heap i) n))
                  (return)))
              ;; General case
              (let ((ln (aref heap l))
                    (rn (aref heap r)))
                (when (node-heap-data-< ln rn)
                  (rotatef l r)
                  (rotatef ln rn))
                (assert (node-heap-data-< rn ln))
                (when (node-heap-data-< ln n)
                  (setf (aref heap i) n)
                  (return))
                (setf (aref heap i) ln)
                (setf (aref heap l) n)
                (setf i l))))))
  (values))

(defun node-heap-sift-up (heap i)
  (declare (type node-heap-index i)
           (type simple-vector heap))
  (let ((n (aref heap i)))
    (iter (while (> i 0))
          (let* ((p (ash (1- i) -1))
                 (pn (aref heap p)))
            (when (node-heap-data-< n pn)
              (return))
            (setf (aref heap i) pn)
            (setf i p)))
    (setf (aref heap i) n))
  (values))

(defun node-heap-insert (nh node path)
  (with-slots (heap count) nh
    (when (find node heap :key #'node-heap-data-node :end count)
      (error "Node ~a already in the heap" node))
    (let ((d (make-node-heap-data :node node :size (size node)
                                  :sn (serial-number node)
                                  :path path)))
      (when (= (length heap) count)
        (setf heap (adjust-array heap (list (+ count count))
                                 :initial-element nil)))
      (setf (aref heap count) d)
      (node-heap-sift-up heap count)
      (incf count)))
  #+debug-node-heap (check-heap nh)
  nh)
#|
(defun node-heap-add-children (nh node path)
  (iter (for i from 0)
        (for c in (children node))
        (when (typep c 'node)
          (node-heap-insert nh c (append path (list i))))))
|#

(defgeneric node-heap-add-children (nh node path)
  (:documentation "Add the children of NODE to the node heap NH.  PATH
is the path to NODE.")
  (:method ((nh t) (node node) (path list))
    (let ((child-slots (child-slots node)))
      (dolist (child-slot child-slots)
        (let ((slot (slot-spec-slot child-slot))
              (arity (slot-spec-arity child-slot)))
          (iter (for c in (child-list node child-slot))
                (for i from 0)
                (when (typep c 'node)
                  (let ((path-element
                          (cond
                            ((eql slot 'children) i)
                            ((eql arity 1)
                             (assert (eql i 0))
                             slot)
                            (t (cons slot i)))))
                    (node-heap-insert nh c
                                      (append path (list path-element)))))))))))


;;; The algorithm for computing the path transform finds all
;;; the nodes that are unique to either tree, and their immediate
;;; children.  Only the paths to these nodes need be considered
;;; when computing path transforms.  In a common case where
;;; a single node replacement has been (functionally) performed on
;;; a tree, the size of the sets is O(depth of changed node).
;;;
;;; The algorithm for computing the path transform from FROM to TO
;;; Uses two heaps to pull nodes from FROM and TO in decreasing
;;; order of size and serial number.

(defmethod path-transform-of ((orig-from node) (to node))
  (let* (;; TABLE is a mapping from serial numbers
         ;; to length 2 lists.  The elements of the list
         ;; are either NIL or a pair containing a node from the
         ;; FROM (first element) or TO (second element), along
         ;; with the path to the node.
         (table (make-hash-table))
         (from-heap (make-node-heap))
         (to-heap (make-node-heap))
         (from-size (size orig-from))
         (from-sn (serial-number orig-from))
         (from-path nil)
         (to-size (size to))
         (to-sn (serial-number to))
         (to-path nil)
         (mapping nil)
         (from orig-from)
         (to to))
    (flet ((%add-from ()
             #+ft-debug-path-transform-of
             (format t "%add-from~%")
             (let ((entry (gethash from-sn table))
                   (l (list from from-path)))
               #+ft-debug-path-transform-of
               (format t "entry = ~a~%" entry)
               (if (null entry)
                   (setf (gethash from-sn table) (list l nil))
                   (if (null (car entry))
                       (setf (car entry) l)
                       (error "Two nodes in FROM tree with same SN: ~a" from-sn)))))
           (%add-to ()
             #+ft-debug-path-transform-of
             (format t "%add-to~%")
             (let ((entry (gethash to-sn table))
                   (l (list to to-path)))
               #+ft-debug-path-transform-of
               (format t "entry = ~a~%" entry)
               (if (null entry)
                   (setf (gethash to-sn table) (list nil l))
                   (if (null (cadr entry))
                       (setf (cadr entry) l)
                       (error "Two nodes in TO tree with same SN: ~a" to-sn))))))
      ;; (declare (type fixnum from-size from-sn to-size to-sn))
      (tagbody
       again
         #+ft-debug-path-transform-of
         (progn
           (format t "from-size=~a, from-sn=~a~%" from-size from-sn)
           (format t "to-size=~a, to-sn=~a~%" to-size to-sn))
         (when (eql from to)
           #+ft-debug-path-transform-of
           (format t "eql~%")
           (%add-from)
           (%add-to)
           (go popboth))
         (when (> from-size to-size) (go advance1))
         (when (< from-size to-size) (go advance2))
         ;; sizes are eql
         (if (>= from-sn to-sn) (go advance1) (go advance2))
       popboth
         (setf (values from from-size from-sn from-path)
               (node-heap-pop from-heap))
         (setf (values to to-size to-sn to-path)
               (node-heap-pop to-heap))
         (unless (and from to) (go done))
         (go again)
       advance1
         #+ft-debug-path-transform-of
         (format t "advance1~%")
         (%add-from)
         (node-heap-add-children from-heap from from-path)
         (setf (values from from-size from-sn from-path)
               (node-heap-pop from-heap))
         (unless from (go done))
         (go again)
       advance2
         #+ft-debug-path-transform-of
         (format t "advance2~%")
         (%add-to)
         (node-heap-add-children to-heap to to-path)
         (setf (values to to-size to-sn to-path)
               (node-heap-pop to-heap))
         (unless to (go done))
         (go again)
       done
         #+ft-debug-path-transform-of
         (format t "done~%"))
      (iter (while from)
            (%add-from)
            (setf (values from from-size from-sn from-path)
                  (node-heap-pop from-heap)))
      (iter (while to)
            (%add-to)
            (setf (values to to-size to-sn to-path)
                  (node-heap-pop to-heap)))

      ;; Extract mapping from table
      (maphash
       (lambda (sn entry)
         (declare (ignore sn))
         (when (and (car entry) (cadr entry))
           (push (list (cadar entry) (cadadr entry)) mapping)))
       table)
      (setf mapping (sort mapping #'lexicographic-< :key #'car))
      #+ft-debug-path-transform-of
      (format t "Sorted mapping:~%~A~%" mapping)

      (let ((sorted-result (path-transform-compress-mapping mapping)))
        (make-instance
         'path-transform
         :from orig-from
         :transforms (cl:mapcar (lambda (p) (append p (list :live)))
                                sorted-result))))))

;;; TODO: enhance this compression so that paths that differ
;;; only in the final index are compressed into "range" paths.
(defun path-transform-compress-mapping (mapping)
  "Internal function used to remove redundancy from a set
   of path mappings."
  (let (stack result)
    (iter (for (old new) in mapping)
          #+debug
          (progn
            (format t "(old new) = ~a~%" (list old new))
            (format t "stack = ~a~%" stack)
            (format t "result = ~a~%" result))
          (iter (until (or (null stack)
                           (prefix? (caar stack) old)))
                (push (pop stack) result))
          (if (null stack)
              (push (list old new) stack)
              (let ((len (length (caar stack))))
                (if (and (prefix? (caar stack) old)
                         (equal new (append (cadr stack) (subseq old len))))
                    ;; This rewrite is subsumed by
                    ;; the one on the stack -- do nothing
                    nil
                    ;; Otherwise, push a new entry
                    (push (list old new) stack)))))
    (stable-sort (revappend stack result) #'> :key #'(lambda (x) (length (car x))))))

(defgeneric equal? (a b)
  (:documentation "Test equality of A and B.")
  (:method ((a t) (b t)) (fset:equal? a b))
  (:method ((node1 node) (node2 node))
    (and (eql (serial-number node1) (serial-number node2))
         (let ((c1 (children node1))
               (c2 (children node2)))
           (and (eql (length c1) (length c2))
                (every #'equal? c1 c2))))))


;;; Rewrite encapsulation
;;; The idea here is to allow grouping of several changes to a tree
;;; into a single change.  The intermediate changes do not need to be
;;; remembered, and the tree need not be in a consistent state during
;;; them.

(defun encapsulate (tree rewrite-fn)
  "Apply REWRITE-FN to TREE, producing a new tree.  The new
tree has its predecessor set to TREE."
  (let ((new-tree (funcall rewrite-fn tree)))
    (if (or (not (typep new-tree 'node))
            (eql tree (from (transform new-tree))))
        new-tree
        (copy new-tree :transform tree))))

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
#|     ;; If the path has a named child with an index
     (if (and (first path) (second path)
              (typep (first path) 'symbol)
              (typep (second path) 'number))
         ;; then handle them both at once.
         (lookup (lookup (lookup node (first path)) (second path)) (cddr path)) |#
     (lookup (lookup node (car path)) (cdr path)))
    ;; )
    (cons
     (destructuring-bind (slot . i) path
       (lookup (slot-value node slot) i)))))
(defmethod lookup ((node node) (finger finger))
  (let ((new-finger (transform-finger finger node)))
    (values (lookup node (path new-finger)) (residue new-finger))))
(defmethod lookup ((node node) (slot null))
  node)
(defmethod lookup ((node node) (slot symbol))
  (slot-value node slot))
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

(defmacro descend ((name &key other-args extra-args replace splice checks)
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
functions."
  (flet ((arg-values (args) (cl:mapcar #'car (cl:remove '&optional args))))
    `(progn
       (defmethod
           ,name :around ((tree node) (path t) ,@other-args ,@extra-args)
           (declare (ignorable ,@vars))
           (with-encapsulation tree (call-next-method)))
       (defmethod ,name ((tree node) (path null) ,@other-args ,@extra-args)
          (declare (ignorable ,@vars))
         ,@checks (values ,@new))
       (defmethod ,name ((tree node) (location node) ,@other-args ,@extra-args)
          (declare (ignorable ,@vars))
         ,@checks (,name tree (path-of-node tree location)
                         ,@(arg-values other-args)))
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
        (format stream "~a ~a" (serial-number obj) (convert 'list obj)))))

(defmethod print-object ((obj finger) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a~@[ ~a~]"
                (node obj) (path obj) (residue obj)))))

(defmethod print-object ((obj path-transform) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a"
                (transforms obj) (from obj)))))


;;;; FSET conversion operations
(defgeneric node-values (node)
  (:documentation "Returns multiple values that are used by
CONVERT 'LIST to append to the beginning of the list representation
of a node.")
  (:method ((node node)) (values)))

(defmethod convert ((to-type (eql 'list)) (node node)
                    &key (value-fn #'node-values) &allow-other-keys)
  "Convert NODE of type node to a list."
  (declare (optimize (speed 3)))
  (setf value-fn (coerce value-fn 'function))
  (labels ((convert- (node)
             (declare (type function value-fn))
             (if (typep node 'node)
                 (append (multiple-value-list (funcall value-fn node))
                         (cl:mapcar #'convert- (children node)))
                 node)))
    (convert- node)))

(defmethod convert ((to-type (eql 'list)) (finger finger)
                    &key &allow-other-keys)
  (let ((cached (cache finger)))
    (if (typep cached 'node)
        (convert to-type cached)
        cached)))

(defmethod convert ((to-type (eql 'alist)) (node node)
                    &key (value-fn nil value-fn-p) &allow-other-keys)
  (convert
   'list node :value-fn
   (if value-fn-p value-fn
       (let ((slots
              (nest
               (cl:remove-if
                (rcurry #'member (append '(serial-number transform finger
                                           child-slots size)
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
  (do-tree (node tree :value tree)
    (funcall function node)
    nil))

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
    (let ((predicate (coerce predicate 'function)))
      (do-seq (element seq)
        (push (funcall predicate element) result))
      (convert 'seq (nreverse result))))
  (:method (function (sequence list) &rest more)
    (apply #'cl:mapcar function sequence more)))

(defmethod mapcar (function (tree node) &rest more)
  (fset::check-two-arguments more 'mapcar 'node)
  (do-tree (node tree :rebuild t)
    (funcall function node)))

(defmethod reduce
    (fn (node node)
      &key key initial-value ;; start end from-end
      &allow-other-keys
      &aux (accumulator initial-value))
  (do-tree (node node :value accumulator)
    (setf accumulator (funcall fn accumulator (if key (funcall key node) node)))
    nil))

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
  (when key (setf key (coerce key 'function)))
  (block done
    (do-tree (node node)
      (when (funcall predicate (if key (funcall key node) node))
        (return-from done node)))))

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
  (when key (setf key (coerce key 'function)))
  (do-tree (node node :value count)
    (when (funcall predicate (if key (funcall key node) node))
      (incf count))
    nil))

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
  (when key (setf key (coerce key 'function)))
  (do-tree (node node :index index)
    (when (funcall predicate (if key (funcall key node) node))
      (return-from position-if (values (nreverse index) t)))))

(defmethod position-if-not (predicate (node node) &rest args
                            &key &allow-other-keys)
  (apply #'position-if (values (complement predicate)) node args))

(defmethod position (item (node node) &key (test #'eql test-p)
                                        (test-not nil test-not-p)
                                        (key nil key-p)
                                        &allow-other-keys)
  (test-handler position)
  (multiple-value-call #'position-if (curry test item) node
                       (if key-p (values :key key) (values))))

(defmethod remove-if (predicate (node node) &key key &allow-other-keys)
  (when key (setf key (coerce key 'function)))
  (do-tree (node node :rebuild t)
    (and (not (funcall predicate (if key (funcall key node) node)))
         node)))

(defmethod remove-if :around (predicate (node node) &key &allow-other-keys)
  ;; Ensure that we set the old node as the original for subsequent transforms.
  (when-let ((it (call-next-method))) (copy it :transform node)))

(defmethod remove-if-not (predicate (node node)
                          &key key  &allow-other-keys)
  (multiple-value-call
      #'remove-if (complement predicate) node
      (if key (values :key key) (values))))

(defmethod remove (item (node node)
                   &key (test #'eql test-p) (test-not nil test-not-p) key &allow-other-keys)
  (test-handler remove)
  (multiple-value-call #'remove-if (curry test item) node
                       (if key (values :key key) (values))))

(defmethod substitute-if (newitem predicate (node node)
                          &key (copy nil copy-p) key &allow-other-keys)
  (when copy-p (setf copy (coerce copy 'function)))
  (do-tree (node node :rebuild t)
    (if (funcall predicate (if key (funcall key node) node))
        (if copy-p (funcall copy newitem) newitem)
        node)))

(defmethod substitute-if-not (newitem predicate (node node)
                              &key key copy &allow-other-keys)
  (multiple-value-call
      #'substitute-if newitem (values (complement predicate)) node
      (if key (values :key key) (values))
      (if copy (values :copy copy) (values))))

(defmethod substitute (newitem olditem (node node)
                       &key (test #'eql test-p) (test-not nil test-not-p)
                         key &allow-other-keys)
  (test-handler substitute)
  (multiple-value-call
      #'substitute-if newitem (curry test olditem) node
      (if key (values :key key) (values))))

(defgeneric subst (new old tree &key key test test-not)
  (:documentation "If TREE is a cons, this simply calls `cl:subst'.
Also works on a functional tree node.")
  (:method (new old (tree cons)
            &key key (test nil test-p) (test-not nil test-not-p))
    (multiple-value-call #'cl:subst
      new old tree
      (if key (values :key key) (values))
      (if test-p (values :test test) (values))
      (if test-not-p (values :test-not test-not) (values))))
  (:method (new old (tree node) &rest rest &key &allow-other-keys)
    (apply #'substitute new old tree rest)))

(defgeneric subst-if (new test tree &key key)
  (:documentation "If TREE is a cons, this simply calls `cl:subst-if'.
Also works on a functional tree node.")
  (:method (new test (tree cons) &key (key nil key-p))
    (apply #'cl:subst-if new test tree (when key-p (list :key key))))
  (:method (new test (tree node) &rest rest &key &allow-other-keys)
    (apply #'substitute-if new test tree rest)))

(defgeneric subst-if-not (new test tree &key key)
  (:documentation "If TREE is a cons, this simply calls `cl:subst-if'.
Also works on a functional tree node.")
  (:method (new test tree &key (key nil key-p))
    (multiple-value-call
        #'subst-if new (complement test) tree
        (if key-p (values :key key) (values)))))
