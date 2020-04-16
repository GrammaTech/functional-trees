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
  (:use :common-lisp :alexandria :iterate :gmap)
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
  (:shadow :subst :subst-if :subst-if-not :assert)
  (:shadowing-import-from :alexandria :compose)
  (:import-from :uiop/utility :nest)
  (:import-from :closer-mop
                :finalize-inheritance
                :slot-definition-name
                :slot-definition-allocation
                :slot-definition-initform
                :class-slots)
  (:export :copy
           :node :transform :child-slots :finger
           :path :transform-finger-to :residue
           :children :node-values :populate-fingers
           :map-tree
           :traverse-nodes
           :traverse-nodes-with-rpaths
           :node-equalp
           :swap)
  (:documentation
   "Prototype implementation of functional trees w. finger objects"))
(in-package :functional-trees)
;;; TODO: implement successor
;;; TODO: implement predecessor
;;; TODO: implement parent

(defmacro assert (&body body)
  ;; Copy the body of the assert so it doesn't pollute coverage reports
  `(cl:assert ,@(copy-tree body)))


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
             (t nil)))
         list))

(defgeneric copy (obj &key &allow-other-keys)
  (:documentation "Generic COPY method.") ; TODO: Extend from generic-cl?
  (:method ((obj t) &key &allow-other-keys) obj)
  (:method ((obj array) &key &allow-other-keys) (copy-array obj))
  (:method ((obj hash-table) &key &allow-other-keys) (copy-hash-table obj))
  (:method ((obj list) &key &allow-other-keys) (copy-list obj))
  (:method ((obj sequence) &key &allow-other-keys) (copy-seq obj))
  (:method ((obj symbol) &key &allow-other-keys) (copy-symbol obj)))

(defclass node (identity-ordering-mixin)
  ((transform :reader transform
              :initarg :transform
              :initform nil
              ;; TODO: change the back pointer to a weak vector
              ;; containing the pointer.
              :type (or null node path-transform)
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

;; debug macro
(defmacro dump (&body forms)
  `(progn
     ,@(iter (for form in forms)
             (collecting `(format t "~a = ~s~%"
                                  ,(format nil "~s" form)
                                  ,form)))))

;;; TODO: Also define `lookup' methods for child-slots after
;;; finalize-inheritance?

(defgeneric children (node)
  (:documentation "Return all children of NODE."))
;; Default method should never be called as the customization of
;; `finalize-inheritance' above should always define something more
;; specific.
(defmethod children ((node node))
  (error "Somehow ~S doesn't have a `children' defmethod." (type-of node)))

;;; When we finalize sub-classes of node, define a children method on
;;; that class and also define functional copying setf writers.
(defun expand-children-defmethod (class)
  `(defmethod children ((node ,class))
     ;; NOTE: For now just append everything together wrapping
     ;; singleton arity slots in `(list ...)'.  Down the line
     ;; perhaps something smarter that takes advantage of the
     ;; known size of some--maybe all--slots would be better.
     (append
      ,@(nest
         (mapcar (lambda (form)
                   (destructuring-bind (slot . arity)
                       (etypecase form
                         (symbol (cons form nil))
                         (cons form))
                     (if (and arity (= (the fixnum arity) 1))
                         `(list (slot-value node ',slot))
                         `(slot-value node ',slot)))))
         (eval) (slot-definition-initform)
         (find-if (lambda (slot)
                    (and (eql 'child-slots (slot-definition-name slot))
                         (eql :class (slot-definition-allocation slot)))))
         (class-slots class)))))

(defun expand-copying-setf-writers (class)
  ;; TODO: For every non-class-allocated slot with a accessor define a
  ;; setf method that makes it copying by default.
  (declare (ignorable class))
  nil)

(defmethod finalize-inheritance :after (class)
  (when (subtypep class 'node)
    ;; Define a custom `children' method given the value of child-slots.
    (eval (expand-children-defmethod class))
    (eval (expand-copying-setf-writers class))))

;;; NOTE: We might want to propos a patch to FSet to allow setting
;;; serial-number with an initialization argument.
(defmethod initialize-instance :after
  ((node node) &key (serial-number nil serial-number-p) &allow-other-keys)
  (when serial-number-p
    (setf (slot-value node 'serial-number) serial-number)))

(defmethod transform :around ((n node))
  ;; Compute the PT lazily, when TRANSFORM is a node
  (let ((tr (call-next-method)))
    (if (typep tr 'node)
        (setf (slot-value n 'transform) (path-transform-of tr n))
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
   (mapcar (lambda (slot) (list (make-keyword slot) (slot-value node slot))))
   (mapcar #'slot-definition-name )
   (remove-if (lambda (slot) (eql :class (slot-definition-allocation slot))))
   (class-slots (class-of node))))

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
                 (unless (= 1 (length (child-slots node)))
                   (error "numeric index ~a used with multiple child slots ~s"
                          i (child-slots node)))
                 (cons (first (child-slots node)) i)))
            (let ((children (slot-value node slot)))
              (unless (and (<= 0 index) (< index (length children)))
                (error "~a not a valid child index for ~a" index node))
              (setf node (elt children index)))))
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
                   (p (assoc i (trie-map node))))
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
                 (p (assoc i (trie-map node))))
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

  #+brute-force-transform-finger
  (let ((node-of-f (node f)))
    (transform-finger-to f (path-transform-of node-of-f node) node))

  #-brute-force-transform-finger
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

(defun populate-fingers (root)
  "Walk tree, creating fingers back to root."
  (traverse-nodes-with-rpaths
   root
   (lambda (n rpath)
     ;; This is the only place this slot should be
     ;; assigned, which is why there's no writer method.
     (unless (finger n)
       (setf (slot-value n 'finger)
             (make-instance 'finger :node root :path (reverse rpath))))
     n))
  root)

;;; This expensive function is used in testing and in FSet
;;; compatibility functions.  It computes the path leading from ROOT
;;; to NODE, or signals an error if it cannot be found.
(defun path-of-node (root node)
  (multiple-value-bind (path foundp) (position node root :key #'identity)
    (if foundp path (error "Cannot find ~a in ~a" node root))))

;;; To add: algorithm for extracting a  path transform from
;;; a set of rewrites (with var objects).  (Is this still relevant?)
;;  Also, conversion of the transform set to a trie.

(defgeneric map-tree (function tree)
  (:documentation
   "Map FUNCTION over TREE returning the result as a (potentially) new tree.")
  (:method (function (object t))
    (funcall function object))
  (:method (function (object cons))
    (funcall function object)
    (cons (map-tree function (car object))
          (when (cdr object)    ; Don't funcall on the tail of a list.
            (map-tree function (cdr object)))))
  (:method (function (node node))
    (nest
     (multiple-value-bind (value stop) (funcall function node))
     (if stop value)
     (apply #'copy value)
     (apply #'append)
     (mapcar (lambda (slot)
               (let ((slot (etypecase slot
                             (cons (car slot))
                             (symbol slot))))
                 (when-let ((it (slot-value value slot)))
                   (list (make-keyword slot)
                         (if (listp it)
                             (mapcar (curry #'map-tree function) it)
                             (map-tree function it))))))
             (child-slots value))))
  (:method :around (function (node node))
           ;; Set the transform field of the result to the old node.
           (copy (call-next-method) :transform node)))

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

(defmethod traverse-nodes-with-rpaths ((node null) fn) nil)

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
  (:documentation "True if the tree rooted at NODE have EQL unique
serial-numbers, and no node occurs on two different paths in the tree"))

(defmethod node-valid ((node node))
  (let ((serial-number-table (make-hash-table)))
    (traverse-nodes node (lambda (n)
                           (let ((serial-number (serial-number n)))
                             (when (gethash serial-number serial-number-table)
                               (return-from node-valid nil))
                             (setf (gethash serial-number serial-number-table)
                                   n))))
    t))

(defun store-nodes (node table)
  (traverse-nodes node (lambda (n) (setf (gethash (serial-number n) table) n))))

(defgeneric nodes-disjoint (node1 node2)
  (:documentation "Return true if NODE1 and NODE2 do not share
any serial-number"))

(defmethod nodes-disjoint ((node1 node) (node2 node))
  (let ((serial-number-table (make-hash-table)))
    ;; Populate serial-number table
    (store-nodes node1 serial-number-table)
    ;; Now check for collisions
    (traverse-nodes
     node2 (lambda (n)
             (when (gethash (serial-number n) serial-number-table)
               (return-from nodes-disjoint nil))
             t))
    t))

(defgeneric node-can-implant (root at-node new-node)
  (:documentation "Check if new-node can the subtree rooted at at-node
below ROOT and produce a valid tree."))

(defmethod node-can-implant ((root node) (at-node node) (new-node node))
  (let ((serial-number-table (make-hash-table)))
    ;; Populate serial-number table
    (traverse-nodes
     root
     (lambda (n)
       ;; Do not store serial-numbers at or below at-node
       (unless (eql n at-node)
         (setf (gethash (slot-value n 'serial-number) serial-number-table) n))))
    ;; Check for collisions
    (traverse-nodes
     new-node
     (lambda (n)
       (when (gethash (serial-number n) serial-number-table)
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
   (if (= count 0) nil)
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

(defun node-heap-add-children (nh node path)
  (iter (for i from 0)
        (for c in (children node))
        (when (typep c 'node)
          (node-heap-insert nh c (append path (list i))))))

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

(defgeneric node-equalp (node1 node2)
  (:documentation "Check that two nodes are the same tree")
  (:method ((node1 node) (node2 node))
    (and (eql (serial-number node1) (serial-number node2))
         (let ((c1 (children node1))
               (c2 (children node2)))
           (and (eql (length c1) (length c2))
                (every #'node-equalp c1 c2)))))
  (:method (node1 node2) (equal node1 node2)))

;;; Rewrite encapsulation
;;; The idea here is to allow grouping of several changes to a tree
;;; into a single change.  The intermediate changes do not need to be
;;; remembered, and the tree need not be in a consistent state during
;;; them.

(defun encapsulate (tree rewrite-fn)
  "Apply REWRITE-FN to TREE, producing a new tree.  The new
tree has its predecessor set to TREE."
  (let ((new-tree (funcall rewrite-fn tree)))
    (if (eql tree (from (transform new-tree)))
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
     (lookup (lookup node (car path)) (cdr path)))
    (cons
     (destructuring-bind (slot . i) path
       (elt (slot-value node slot) i)))))
(defmethod lookup ((node node) (finger finger))
    (let ((new-finger (transform-finger finger node)))
      (values (lookup node (path new-finger)) (residue new-finger))))
;; (defmethod lookup ((node node) (slot symbol))
;;   (slot-value node slot))
(defmethod lookup ((node node) (i integer))
  (elt (children node) i))

(defmacro descend ((name &key other-args extra-args replace splice checks)
                   &body new)
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
  (flet ((arg-values (args) (mapcar #'car (remove '&optional args))))
    `(progn
       (defmethod ,name ((tree node) (path null) ,@other-args ,@extra-args)
         ,@checks (values ,@new))
       (defmethod ,name ((tree node) (location node) ,@other-args ,@extra-args)
         ,@checks (,name tree (path-of-node tree location)
                         ,@(arg-values other-args)))
       (defmethod ,name ((tree node) (slot symbol) ,@other-args ,@extra-args)
         ,@checks (copy tree (make-keyword slot) ,@new))
       (defmethod ,name ((tree node) (path cons) ,@other-args ,@extra-args)
         ,@checks
         ;; At the end of the path, so act directly.
         (if (null (cdr path))
             (,name tree (car path) ,@(arg-values other-args))
             (etypecase (car path)
               (symbol
                (copy tree
                      (make-keyword (car path))
                      (,name (lookup tree (car path)) (cdr path)
                             ,@(arg-values other-args))))
               ((integer 0)
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
                 :initial-value (car path))))))
       (defmethod ,name ((tree node) (i integer) ,@other-args ,@extra-args)
         ,@checks
         (reduce (lambda (i child-slot)
                   (let* ((slot (if (consp child-slot)
                                    (car child-slot)
                                    child-slot))
                          (children (slot-value tree slot))
                          (account (cond
                                     ;; Explicit arity
                                     ((and (consp child-slot)
                                           (numberp (cdr child-slot)))
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
(defmethod size ((node node))
  (1+ (reduce #'+ (mapcar #'size (children node)))))

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
(def-gmap-arg-type :node (node)
  "Yields the nodes of NODE in preorder."
  `((list ,node)
    #'endp                              ; Check end.
    #'car                               ; Yield.
    #'(lambda (state)                        ; Update.
        (typecase (car state)
          (node (append (children (car state)) (cdr state)))
          (t (cdr state))))))

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
                         (mapcar #'convert- (children node)))
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
               (remove-if
                (rcurry #'member '(serial-number transform finger children)))
               (mapcar #'slot-definition-name (class-slots (class-of node))))))
         (lambda (node)
           (apply #'append
                  (mapcar (lambda (slot)
                            (when-let ((val (slot-value node slot)))
                              (list (cons (make-keyword slot) val))))
                          slots)))))))


;;; FSET sequence operations (+ two) for functional tree.
(defgeneric substitute-with (predicate sequence &key &allow-other-keys)
  (:documentation
   "Substitute elements of SEQUENCE with result of PREDICATE when non-nil.
If secondary return value of PREDICATE is non-nil force substitution
  with primary value even if it is nil.")
  (:method (predicate (sequence sequence) &key &allow-other-keys )
    (let ((predicate (coerce predicate 'function)))
      (map (type-of sequence)
           (lambda (element)
             (multiple-value-bind (value force)
                 (funcall predicate element)
               (if force value (or value element))))
           sequence)))
  (:method (predicate (seq seq) &key &allow-other-keys &aux result)
    (let ((predicate (coerce predicate 'function)))
      (do-seq (element seq)
        (multiple-value-bind (value force)
            (funcall predicate element)
          (push (if force value (or value element)) result)))
      (convert 'seq (nreverse result)))))

(defmethod reduce (fn (node node) &rest rest &key &allow-other-keys)
  (apply #'reduce fn (flatten (convert 'list node)) rest))

(defmacro test-handler (fn)
  "This macro is an idiom that occurs in many methods.  It handles
checking and normalization of :TEST and :TEST-NOT arguments."
  `(nest
    (if test-p (progn
                 (assert (not test-not-p) () ,(format nil "~a given both :TEST and :TEST-NOT" fn))
                 (setf test (coerce test 'function))))
    (when test-not-p (setf test (complement (coerce test-not 'function))))))

(defmethod find (item (node node)
                 &key (test #'eql test-p) (test-not nil test-not-p) (key nil key-p) &allow-other-keys)
  (test-handler find)
  (apply #'find-if (curry test item) node
         (when key-p (list :key key))))

(defmethod find-if (predicate (node node)
                    &key from-end end start key)
  (assert (notany #'identity from-end end start)
          (from-end end start)
          "TODO: implement support for ~a key in `find-if'"
          (cdr (find-if #'car
                        (mapcar #'cons
                                (list from-end end start)
                                '(from-end end start)))))
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (item) (funcall predicate (if key (funcall key item) item)))
       (find- (predicate node)
         (nest (if (check node) (return-from find-if node))
               (when (typep node 'node))
               (mapc (lambda (slot)
                       (when-let ((it (slot-value node (etypecase slot
                                                (cons (car slot))
                                                (symbol slot)))))
                         (if (listp it)
                             (mapc (curry #'find- predicate) it)
                             (find- predicate it))))
                     (child-slots node)))))
    (find- (coerce predicate 'function) node)
    nil))

(defmethod find-if-not
    (predicate (node node) &key (key nil key-p) &allow-other-keys)
  (multiple-value-call #'find-if (complement predicate) node
                       (if key-p (values :key key) (values))))

(defmethod count (item (node node) &rest rest &key &allow-other-keys)
  (apply #'count item (flatten (convert 'list node)) rest))

(defmethod count-if (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'count-if predicate (flatten (convert 'list node)) rest))

(defmethod count-if-not (predicate (node node)
                         &rest rest &key &allow-other-keys)
  (apply #'count-if-not predicate (flatten (convert 'list node)) rest))

(defmethod position (item (node node) &key (test #'eql test-p)
                                        (test-not nil test-not-p)
                                        (key nil key-p)
                                        &allow-other-keys)
  (test-handler position)
  (multiple-value-call #'position-if (curry test item) node
                       (if key-p (values :key key) (values))))

(defmethod position-if (predicate (node node)
                        &key from-end end start
                          (key nil))
  (assert (notany #'identity from-end end start)
          (from-end end start)
          "TODO: implement support for ~a key in `position-if'"
          (cdr (find-if #'car
                        (mapcar #'cons
                                (list from-end end start)
                                '(from-end end start)))))
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (item) (funcall predicate (if key (funcall key item) item)))
       (position- (predicate node path)
         (nest (if (not (typep node 'node))
                   (when (check node)
                     (return-from position-if (values (nreverse path) t))))
               (if (check node)
                   (return-from position-if (values (nreverse path) t)))
               (let* ((slots (child-slots node))
                      (single-child (= 1 (length slots)))))
               (mapc (lambda (slot)
                       (let* ((slot (etypecase slot
                                      (cons (car slot))
                                      (symbol slot)))
                              (children (slot-value node slot)))
                         (if (listp children)
                             (mapc (lambda (child index)
                                     (nest
                                      (position- predicate child)
                                      (if single-child (cons index path))
                                      (cons (cons (make-keyword slot) index)
                                            path)))
                                   children
                                   (iota (length children)))
                             (position- predicate children
                                        (cons (make-keyword slot) path)))))
                     slots))))
    (position- (coerce predicate 'function) node nil)
    (values nil nil)))

(defmethod position-if-not (predicate (node node) &rest args
                            &key &allow-other-keys)
  (apply #'position-if (values (complement predicate)) node args))

(defmethod remove (item (node node)
                   &key (test #'eql test-p) (test-not nil test-not-p) key &allow-other-keys)
  (test-handler remove)
  (multiple-value-call #'remove-if (curry test item) node
                       (if key (values :key key) (values))))

(defmethod remove-if (predicate (node node) &key key &allow-other-keys)
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (node)
         (funcall predicate (if key (funcall (the function key) node) node)))
       (remove- (predicate node)
         (nest (if (not (typep node 'node))
                   (if (check node)
                       (values nil t)
                       (values (list node) nil)))
               (if (check node) (values nil t))
               (let* ((modifiedp nil)
                      (new-children
                       (mappend
                        (lambda (slot)
                          (when-let ((children (slot-value node slot)))
                            (list (make-keyword slot)
                                  (mappend
                                   (lambda (child)
                                     (multiple-value-bind (new was-modified-p)
                                         (remove- predicate child)
                                       (when was-modified-p (setf modifiedp t))
                                       new))
                                   children))))
                        (child-slots node)))))
               (if (not modifiedp) (values (list node) nil))
               (values (list (apply #'copy node new-children)) t))))
    (car (remove- (coerce predicate 'function) node))))

(defmethod remove-if :around (predicate (node node) &key &allow-other-keys)
  ;; Ensure that we set the old node as the original for subsequent transforms.
  (when-let ((it (call-next-method))) (copy it :transform node)))

(defmethod remove-if-not (predicate (node node)
                          &key key  &allow-other-keys)
  (multiple-value-call
      #'remove-if (complement predicate) node
      (if key (values :key key) (values))))

(defmethod substitute (newitem olditem (node node)
                       &key (test #'eql test-p) (test-not nil test-not-p)
                         key &allow-other-keys)
  (test-handler substitute)
  (multiple-value-call
      #'substitute-if newitem (curry test olditem) node
      (if key (values :key key) (values))))

(defmethod substitute-if (newitem predicate (node node)
                          &key (copy nil copy-p) key &allow-other-keys)
  (when copy-p (setf copy (coerce copy 'function)))
  (setf predicate (coerce predicate 'function))
  (multiple-value-call
      #'substitute-with
    (lambda (item)
      (when (funcall predicate item)
        (values (if copy-p (funcall copy newitem) newitem) t)))
    node
    (if key (values :key key) (values))))

(defmethod substitute-if-not (newitem predicate (node node)
                              &key key copy &allow-other-keys)
  (multiple-value-call
      #'substitute-if newitem (values (complement predicate)) node
      (if key (values :key key) (values))
      (if copy (values :copy copy) (values))))

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

(defmethod substitute-with (function (node node)
                            &key key &allow-other-keys)
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (node)
         (funcall function (if key (funcall (the function key) node) node)))
       (substitute- (predicate node)
         (nest (if (not (typep node 'node))
                   (multiple-value-bind (value force) (check node)
                     (if (or force value)
                         (values (list value) t)
                         (values (list node) nil))))
               (multiple-value-bind (value force) (check node))
               (if (or force value) (values (list value) t))
               (let* ((modifiedp nil)
                      (new-children
                       (mappend
                        (lambda (slot)
                          (when-let ((children (slot-value node slot)))
                            (list (make-keyword slot)
                                  (mappend
                                   (lambda (child)
                                     (multiple-value-bind (new was-modified-p)
                                         (substitute- predicate child)
                                       (when was-modified-p (setf modifiedp t))
                                       new))
                                   children))))
                        (child-slots node))))
                 (if (not modifiedp)
                     (values (list node) nil)
                     (values (list (apply #'copy node new-children)) t))))))
    (car (substitute- (coerce function 'function) node))))

(defmethod substitute-with :around (function (node node) &key &allow-other-keys)
  ;; Ensure that we set the old node as the original for subsequent transforms.
  (when-let ((it (call-next-method))) (copy it :transform node)))
