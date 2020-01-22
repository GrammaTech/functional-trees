(defpackage :functional-trees/core
  (:nicknames :ft/core)
  (:use cl :alexandria :iterate)
  (:export children predecessor
           transform root finger path residue
           path-transform from to
           transforms transform-finger transform-finger-to
           transform-path var local-path
           value node node-with-data update-tree-at-data
           data
           path-transform-of
           remove-nodes-if
           swap-nodes
           make-node make-node* to-list to-list*
           traverse-nodes
           traverse-nodes-with-rpaths
           name
           copy update-tree update-tree*)
  (:import-from :fset :compare)
  (:import-from :uiop/utility :nest)
  (:import-from :closer-mop :slot-definition-name :class-slots)
  (:documentation "Prototype implementation of functional trees w.
finger objects"))

(in-package :functional-trees/core)

(deftype path ()
  `(and list (satisfies path-p)))

(defun path-p (list)
  (every (lambda (x)
           (typecase x
             ((integer 0) t)
             (symbol t)
             ((cons (integer 0)
                    (cons integer null))
              (<= (first x) (second x)))
             (t nil)))
         list))

(defvar *node-name-counter* 0 "Counter used to initialize the NAME slot of nodes.")

(defgeneric copy (obj &key &allow-other-keys)
  (:documentation "Like the COPY function in SEL"))

(defclass node ()
  (;; TODO: consider replacing name with the unique ID
   ;; given to objects in the Fset package
   (name :reader name :initarg :name :initform nil
         :documentation "The NAME of a node is an EQL-unique
value used in place of EQ-ness to determine when two nodes
are 'the same'.  No two nodes in the same tree should have the
same name.")
   (transform :reader transform
              :initarg :transform
              :initform nil
              :type (or null node path-transform)
              :documentation "If non-nil, is either a PATH-TRANSFORM object
to this node, or the node that led to this node.")
   (finger :reader finger
           :initform nil
           :type (or null node finger)
           :documentation "A finger back to the root of the (a?) tree.")
   (children :reader children
             :type list
             :initarg :children
             :initform nil
             :documentation "The list of children of the node,
which may be more nodes, or other values."))
  (:documentation "A node in a tree."))

(defclass node-with-data (node)
  ((data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data")))

(defmethod transform :around ((n node))
  ;; Compute the PT lazily, when TRANSFORM is a node
  (let ((tr (call-next-method)))
    (if (typep tr 'node)
        (setf (slot-value n 'transform) (path-transform-of tr n))
        tr)))

;;; There should be a way to chain together methods for COPY for
;;; classes and their superclasses, perhaps using the initialization
;;; infrastructure in CL for objects.

(defmethod copy ((node node) &rest keys)
  (nest
   (apply #'make-instance (class-name (class-of node)))
   (apply #'append keys)
   (mapcar (lambda (slot) (list (make-keyword slot) (slot-value node slot))))
   (remove 'name)
   (mapcar #'slot-definition-name (class-slots (class-of node)))))

(defmethod (setf children) (new (node node))
  (copy node :children new))

;;; TODO: make the INCF here thread safe on SBCL, using atomic
;;; increment. 
(defmethod initialize-instance :after ((node node) &key &allow-other-keys)
  (unless (name node)
    (setf (slot-value node 'name) (incf *node-name-counter*))))

(defclass finger ()
  ((node :reader node :initarg :node
         :type node
         :initform (required-argument :node)
         :documentation "The node to which this finger pertains,
considered as the root of a tree.")
   (path :reader path :initarg :path
         :type list
         :initform (required-argument :path)
         :documentation "A list of nonnegative integer values
giving a path from node down to another node.")
   (residue :reader residue :initarg :residue
            :initform nil ;; (required-argument :residue)
            :type list
            :documentation "If this finger was created from another finger
by a path-transform, some part of the path may not have been translated.
If so, this field is the part that could not be handled.  Otherwise, it is NIL.")
   (cache :accessor :node :accessor cache
         :documentation "Internal slot used to cache the lookup of
a node."))
  (:documentation "A wrapper for a path to get to a node"))

(defmethod slot-unbound ((class t) (f finger) (slot (eql 'cache)))
  ;; Fill in the NODE slot of finger F
  (let* ((node (node f))
         (path (path f)))
    (iter (for i in path)
          (unless (typep node 'node)
            (error "Path ~a not valid for tree rooted at ~a: ~a" (path f) (node f) node))
          (let ((children (children node)))
            (etypecase i
              (fixnum ;; make this an explicit range
               (unless (and (<= 0 i) (< i (length children)))
                 (error "~a not a valid child index for ~a" i node))
               (setf node (elt children i)))
              (symbol
               (setf node (slot-value node i))))))
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

(defun transform-path (path transforms)
  ;; This is inefficient, and is just for demonstration
  ;; In the real implementation, the segments are blended together
  ;; into a trie
  (let ((len (length path)))
    (iter (for (segment new-initial-segment status) in transforms)
          (when (and (>= len (length segment))
                     (every (lambda (i i-set)
                              (or (eql i i-set)
                                  (and (consp i-set)
                                       (integerp i)
                                       (<= (car i-set) i (cadr i-set)))))
                            path segment))
            (return
              (let ((new-segment
                     (loop for i in path
                        for init in new-initial-segment
                        for p in path
                        collect (if (consp i)
                                    (+ init (- p (car i)))
                                    init))))
                (if (< len (length new-initial-segment))
                    (append new-segment (subseq new-initial-segment len)
                            (subseq path (length segment)))
                    (ecase status
                      (:live (append new-segment (subseq path (length segment))))
                      (:dead (values new-segment (subseq path (length new-segment)))))))))
          (finally (return path)))))

(defgeneric transform-finger (finger node &key error-p)
  (:documentation "Transforms FINGER, producing a new finger that
points through the root NODE.  NODE must be derived from the tree
that FINGER is pointed through."))

(defmethod transform-finger ((f finger) (node node) &key (error-p t))
  (declare (ignore error-p)) ;; for now
  (let ((node-of-f (node f)))
    (labels ((%transform (x)
               (cond
                 ((eql x node-of-f) f)
                 ((null x)
                  ;; As an alternative, create a fresh path transform
                  ;; from the root for f to node, and use that instead
                  ;; However, we'd want to cache that somehow.
                  (error "Cannot find path from ~a to ~a"
                         node-of-f node))
                 (t
                  (let ((transform (transform x)))
                    (transform-finger-to
                     (%transform (from transform))
                     transform x))))))
      (%transform node))))

;;; This is an example of tree construction
;;; TODO: Remove make-* functions and replace them all with a single
;;;       from-list function.
(defun make-tree (list-form &key name transform)
  "Produce a tree from a list-form.  Uses MAKE-NODE for actual
construction, then walks it filling in the PATH attributes."
  (let ((root (make-node list-form :name name :transform transform)))
    ;; Walk tree, creating fingers back to root
    (traverse-nodes-with-rpaths
     root
     (lambda (n rpath)
       ;; This is the only place this slot should be assigned,
       ;; which is why there's no writer method
       (unless (finger n)
         (setf (slot-value n 'finger)
               (make-instance 'finger :node root :path (reverse rpath))))
       n))
    root))

(defun make-node (list-form &rest args &key name transform)
  (declare (ignorable name transform))
  (if (consp list-form)
      (if (or (typep (car list-form) 'standard-class)
              (and (symbolp (car list-form))
                   (find-class (car list-form) nil)))
          (apply #'make-node* (car list-form) (cdr list-form) args)
          (apply #'make-node* 'node list-form args))
      list-form))

(defgeneric make-node* (class vals &key &allow-other-keys)
  (:documentation "Generate a node with appropriate values"))

(defmethod make-node* ((class standard-class) vals &rest args)
  (apply #'make-node* (class-name class) vals args))

(defmethod make-node* ((class (eql 'node-with-data)) vals &key name transform)
  (make-instance 'node-with-data
    :name name
    :data (car vals)
    :transform transform
    :children (mapcar #'make-node (cdr vals))))

(defgeneric to-alist (node)
  (:documentation "Convert tree rooted at NODE into an association list.")
  (:method ((node node))
    (append
     (nest
      (apply #'append)
      (mapcar (lambda (slot)
                (when-let ((val (slot-value node slot)))
                  (list (cons (make-keyword slot) val)))))
      (remove-if (rcurry #'member '(name transform finger children)))
      (mapcar #'slot-definition-name (class-slots (class-of node))))
     (list (cons :children (mapcar #'to-alist (children node)))))))

(defgeneric from-alist (class alist)
  (:documentation "Convert from ALIST to an object of class CLASS.")
  (:method ((class symbol) alist)
    (from-alist (find-class class) alist))
  (:method ((class standard-class) (alist list))
    (apply #'make-instance class
           (apply #'append (alist-plist alist)))))

;; TODO: refactor this for better extensibility on subclasses
(defgeneric to-list (node)
  (:documentation "Convert tree rooted at NODE to list form.")
  (:method ((finger finger)) (to-list (cache finger)))
  (:method ((node node)) (to-alist node))
  (:method (node) node))

;;; Printing methods

(defmethod print-object ((obj node) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a" (to-list obj)))))

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

;;; This expensive function is used in testing
;;; Computes the path leading from ROOT to NODE, or
;;; signals an error if it cannot be found.
(defun path-of-node (root node)
  (labels ((%search (path n)
             (when (eql n node)
               (return-from path-of-node (nreverse path)))
             (typecase n
               (node
                (iter (for i from 0)
                      (for c in (children n))
                      (%search (cons i path) c))))))
    (%search nil root)
    (error "Cannot find ~a in ~a" node root)))


;;; To add: algorithm for extracting a  path transform from
;;; a set of rewrites (with var objects).  Also, conversion of the
;;; transform set to a trie.

(defgeneric traverse-nodes (root fn)
  (:documentation 
  "Apply FN at every node below ROOT, in preorder, left to right
   If FN returns NIL, stop traversal below this point.  Returns NIL."))

(defmethod traverse-nodes :around ((node node) fn)
  (when (funcall fn node)
    (call-next-method)))

(defmethod traverse-nodes ((node node) fn)
  (dolist (c (children node))
    (traverse-nodes c fn)))

(defmethod traverse-nodes ((node t) (fn t)) t)

(defgeneric traverse-nodes-with-rpaths (root fn)
  (:documentation
   "Apply FN at every node below ROOT, in preorder, left to right.
   Also pass to FN a list of indexes that is the reverse of the
   path from ROOT to the node.  If FN returns NIL, stop traversal
   below this point.  Returns NIL."))

(defmethod traverse-nodes-with-rpaths ((node node) fn)
  (traverse-nodes-with-rpaths* node fn nil))

(defgeneric traverse-nodes-with-rpaths* (root fn rpath)
  (:documentation "Internal method to implement traverse-nodes-with-rpaths"))  

(defmethod traverse-nodes-with-rpaths* :around ((node node) fn rpath)
  (when (funcall fn node rpath)
    (call-next-method)))

(defmethod traverse-nodes-with-rpaths* ((node node) fn rpath)
  (iter (for i from 0)
        (for c in (children node))
        (traverse-nodes-with-rpaths* c fn (cons i rpath)))
  nil)

(defmethod traverse-nodes-with-rpaths* ((node t) (fn t) (rpath t)) nil)

;;; To traverse fields aside from CHILDREN, write methods
;;; for the particular class for these functions that explicitly
;;; traverse those fields, then (if none returned NIL) performs
;;; (call-next-method) to the general methods for node.


(defgeneric node-valid (node)
  (:documentation "True if the tree rooted at NODE have EQL unique names,
and no node occurs on two different paths in the tree"))

(defmethod node-valid ((node node))
  (let ((name-table (make-hash-table)))
    (traverse-nodes node (lambda (n)
                           (let ((name (name n)))
                             (when (gethash name name-table)
                               (return-from node-valid nil))
                             (setf (gethash name name-table) n))))
    t))

(defun store-nodes (node table)
  (traverse-nodes node (lambda (n) (setf (gethash (name n) table) n))))

(defgeneric nodes-disjoint (node1 node2)
  (:documentation "Return true if NODE1 and NODE2 do not share
any name"))

(defmethod nodes-disjoint ((node1 node) (node2 node))
  (let ((name-table (make-hash-table)))
    ;; Populate name table
    (store-nodes node1 name-table)
    ;; Now check for collisions
    (traverse-nodes node2 (lambda (n)
                            (when (gethash (name n) name-table)
                              (return-from nodes-disjoint nil))
                            t))
    t))

(defgeneric node-can-implant (root at-node new-node)
  (:documentation "Check if new-node can the subtree rooted at at-node
below ROOT and produce a valid tree."))

(defmethod node-can-implant ((root node) (at-node node) (new-node node))
  (let ((name-table (make-hash-table)))
    ;; Populate name table
    (traverse-nodes
     root
     (lambda (n)
       ;; Do not store names at or below at-node
       (unless (eql n at-node)
         (setf (gethash (name n) name-table) n))))
    ;; Check for collisions
    (traverse-nodes
     new-node
     (lambda (n)
       (when (gethash (name n) name-table)
         (return-from node-can-implant nil))
       t))
    t))

(defun lexicographic-< (list1 list2)
  "Lexicographic comparison of lists of reals or symbols
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
            (return (eql (compare c1 c2) :less))))
         ((symbolp c2) (return nil))
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

;;; Structure used in computation of path-transform-of
(defstruct pto-data
  ;; Node in the source tree
  from
  ;; Node in the target tree
  to
  ;; Path from root of source tree to FROM node
  from-path
  ;; Path from root of target tree to TO node
  to-path)

(defmethod path-transform-of ((from node) (to node))
  (let ((table (make-hash-table)))
    (traverse-nodes-with-rpaths
     from
     (lambda (n rpath)
       (setf (gethash (name n) table) (make-pto-data :from n :from-path (reverse rpath)))))
    #+debug (format t "Table (1): ~a~%" table)
    ;; Now find nodes that are shared
    (traverse-nodes-with-rpaths
     to
     (lambda (n rpath)
       (let* ((entry (gethash (name n) table)))
         (or (not entry)
             (progn
               (setf (pto-data-to entry) n
                     (pto-data-to-path entry) (reverse rpath))
               ;; Stop recursion when this is common
               (not (eql (pto-data-from entry) n)))))))
    ;; Construct mapping
    (let (mapping)
      (maphash (lambda (n pd)
                 (declare (ignorable n))
                 #+debug (format t "Maphash ~a, ~a~%" n pd)
                 (when (pto-data-to pd)
                   (push
                    (list (pto-data-from-path pd)
                          (pto-data-to-path pd))
                    mapping)))
               table)
      #+debug (format t "Mapping:~%~A~%" mapping)
      ;; Mapping is now a list of (<old path> <new path>) lists
      ;; Sort this into increasing order of <old path>, lexicographically
      (setf mapping (sort mapping #'lexicographic-< :key #'car))
      #+debug (format t "Sorted mapping:~%~A~%" mapping)

      (let ((sorted-result (path-transform-compress-mapping mapping)))
        (make-instance
         'path-transform
         :from from
         :transforms (mapcar (lambda (p) (append p (list :live)))
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

(defgeneric compare-nodes (node1 node2)
  (:documentation "Check that two nodes are the same tree")
  (:method ((node1 node) (node2 node))
    (and (eql (name node1) (name node2))
         (let ((c1 (children node1))
               (c2 (children node2)))
           (and (eql (length c1) (length c2))
                (every #'compare-nodes c1 c2)))))
  (:method (node1 node2) (equal node1 node2)))

(defun update-tree (node fn)
  (copy (update-tree* node fn) :transform node))

(defgeneric update-tree* (node fn)
  (:documentation
  "Traverse tree rooted at NODE, in postorder, calling
FN at each node.  If FN returns a different tree, replace
the node at that point, and copy ancestors (preserving their
names.)"))

(defmethod update-tree* ((n node) fn)
  (let* ((children (children n))
         (new-children (mapcar (lambda (c) (update-tree* c fn)) children)))
    (if (every #'eql children new-children)
        n
        (let ((new-n (copy n :children new-children)))
          (assert (eql (name n) (name new-n)))
          (copy n :children new-children)))))

(defmethod update-tree* ((n t) (fn t)) n)

(defmethod update-tree* :around ((node node) fn)
  (let ((n (call-next-method)))
    (funcall fn n)))

(defun update-tree-at-data (node-with-data data)
  "Cause nodes with DATA to be copied (and all ancestors)"
  (update-tree node-with-data (lambda (n) (if (eql (data n) data) (copy n) n))))

(defun remove-nodes-if (node fn)
  "Remove nodes/leaves for which FN is true"
  ;; FIXME: Doesn't apply FN to the root.
  ;; (length (to-list (remove-if #'evenp (make-tree (iota 100))))) => 51 not 0.
  ;; FIXME: Doesn't apply to non-children fields
  (update-tree
   node
   (lambda (n)
     (let* ((c (children n))
            (new-c (remove-if fn c)))
       (if (every #'eql c new-c)
           n
           (copy n :children new-c))))))

(defun remove-nodes-randomly (root p)
  "Remove nodes from tree with probability p"
  (assert (typep p '(real 0)))
  (remove-nodes-if root (lambda (n) (declare (ignore n)) (<= (random 1.0) p))))

;; This fails if NODE1 is an ancestor of NODE2, or
;; vice versa
(defun swap-nodes (root node1 node2)
  (update-tree
   root
   (lambda (n)
     (cond
       ((eql (name n) (name node1)) node2)
       ((eql (name n) (name node2)) node1)
       (t n)))))

(defun swap-random-nodes (root)
  (let ((node1 (random-node root))
        (node2 (random-node root)))
    (if (or (is-ancestor-of node1 node2)
            (is-ancestor-of node2 node1))
        root
        (swap-nodes root node1 node2))))

(defun random-node (root)
  (let ((nodes nil))
    (traverse-nodes root (lambda (n) (push n nodes)))
    (elt nodes (random (length nodes)))))

(defun is-ancestor-of (node1 node2)
  (traverse-nodes node1 (lambda (n) (when (eql n node2)
                                      (return-from is-ancestor-of t))
                                t))
  nil)

(defun random-partition (n m)
  "Partition N into M buckets, randomly, with each
bucket getting at least 1.  Return as a list."
  (assert (typep n '(integer 1)))
  (assert (typep m '(integer 1)))
  (assert (<= m n))
  (let ((buckets (make-array (list m) :initial-element 1))
        (reps (- n m)))
    (iter (repeat reps)
          (incf (aref buckets (random m))))
    (coerce buckets 'list)))

(defun make-random-tree (size)
  "Construct a random tree of SIZE nodes."
  (declare (type fixnum size))
  (let ((leaf-bound 3)
        (child-bound 4)
        children)
    (cond
      ((< size 1)
       (error "SIZE should be a positive number: ~a" size))
      ((= size 1))
      (t ;; (> size 1)
       (let* ((n-children (1+ (random (min child-bound (1- size)))))
              (child-sizes (random-partition (1- size) n-children)))
         (setf children (mapcar #'make-random-tree child-sizes)))))
    ;; Add random set of leaf values
    (setf children
          (random-permute (append (iter (repeat (random leaf-bound))
                                        (collecting (make-random-leaf)))
                                  children)))
    (make-instance 'node-with-data :data (make-random-data)
                   :children children)))

(defun make-random-leaf () (random 100))

(defun make-random-data ()
  (let ((vals #(:a :b :c :d :e :f :g :h :i :j :k :l :m)))
    (elt vals (random (length vals)))))

(defun random-permute (seq)
  (let* ((seq (coerce seq 'vector))
         (len (length seq)))
    (iter (for i from (1- len) downto 1)
          (let ((r (random (1+ i))))
            (rotatef (aref seq i) (aref seq r))))
    (coerce seq 'list)))

