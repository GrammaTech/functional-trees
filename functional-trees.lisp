(defpackage :functional-trees/functional-trees
  (:nicknames :ft/ft)
  (:use cl :alexandria :iterate)
  (:export tree tree-node data children predecessor
           transform root finger path residue
           path-transform from-tree to-tree
           transforms transform-finger
           transform-path var local-path
           value
           make-tree to-list)
  (:documentation "Prototype implementation of functional trees w.
finger objects"))

(in-package :functional-trees/functional-trees)

(defclass tree-node ()
  ((data :reader data :initarg :data
         :initform (required-argument :data)
         :documentation "Arbitrary data")
   (children :reader children
             :type list
             :initarg :children
             :initform (required-argument :children)
             :documentation "The list of children of the node,
which may be more tree nodes, or other values."))
  (:documentation "A simple tree node"))

(defclass tree ()
  ((predecessor :reader predecessor
                :type (or null tree)
                :initarg :predecessor
                :initform nil
                :documentation "The tree from which this tree was produced,
or NIL if this tree was created from scratch.")
   (transform :reader transform
              :type (or null path-transform)
              :initarg :transform
              :initform nil
              :documentation "A path-transform object used to convert
fingers of the predecessor tree into fingers for this tree")
   (root :reader root
         :type (or null tree-node)
         :initarg :root
         :initform (required-argument :root)
         :documentation "The root ast-node, or NIL if the tree is empty."))
  (:documentation "Base object for trees.  This is not itself
a tree node."))   

(defclass finger ()
  ((tree :reader tree :initarg :tree
         :type tree
         :initform (required-argument :tree)
         :documentation "The tree to which this finger pertains.")
   (path :reader path :initarg :path
         :type list
         :initform (required-argument :path)
         :documentation "A list of (integer 0) values, giving paths
from the root of TREE down to some node.")
   (residue :reader residue :initarg :residue
            :initform nil ;; (required-argument :residue)
            :type list
            :documentation "If this finger was created from another finger
by a path-transform, some part of the path may not have been translated.
If so, this field is the part that could not be handled.  Otherwise, it is NIL.")
   (tree-node :accessor :tree-node :accessor tree-node
              :documentation "Internal slot used to cache the lookup of
a node in the tree."))
  (:documentation "A wrapper for a path to get to a node"))

(defmethod slot-unbound ((class t) (f finger) (slot (eql 'tree-node)))
  ;; Fill in the NODE slot
  (let* ((tree (tree f))
         (path (path f))
         (node (root tree)))
    (iter (for i in path)
          (unless (typep node 'tree-node)
            (error "Path ~a not valid for tree ~a: ~a" (path f) (tree f) node))
          (let ((children (children node)))
            (unless (and (<= 0 i) (< i (length children)))
              (error "~a not a valid child index for ~a" i node))
            (setf node (elt children i))))
    (setf (slot-value f 'tree-node) node)))

(defclass path-transform ()
  ((from-tree
    :reader from-tree :initarg :from-tree
    :type tree
    :initform (required-argument :from-tree))
   (to-tree
    :reader to-tree :initarg :to-tree
    :type tree
    :initform (required-argument :to-tree))
   (transforms :initarg :transforms
               :reader transforms
               :initform (required-argument :transforms)
               :type list
               :documentation "A list of (<path> <path> <status>) triples
where each path is a list of integer indices, and <status> is one of :live
:dead. These should be sorted into non-increasing order of length of <path>."))
  (:documentation "An object used to rewrite fingers from one
tree to another."))

(defgeneric transform-finger (f p)
  (:documentation "Converts a finger from one tree to another."))

;;; Around method to verify pre, post conditions
(defmethod transform-finger :around ((f finger) (p path-transform))
  (assert (eql (tree f) (from-tree p)))
  (let ((new-finger (call-next-method)))
    (assert (typep new-finger 'finger))
    (assert (eql (tree new-finger) (to-tree p)))
    new-finger))

(defmethod transform-finger ((f finger) (p path-transform))
  (multiple-value-bind (new-path residue)
      (transform-path (path f) (transforms p))
    (make-instance 'finger :path new-path
                   :tree (to-tree p) :residue residue)))

(defun transform-path (path transforms)
  ;; This is inefficient, and is just for demonstration
  ;; In the real implementation, the segments are blended together
  ;; into a trie
  (let ((len (length path)))
    (iter (for (segment new-segment status) in transforms)
          (when (and (>= len (length segment))
                     (every #'eql path segment))
            (return
              (ecase status
                (:live (append new-segment (subseq path (length segment))))
                (:dead (values new-segment (subseq path (length new-segment)))))))
          (finally (return path)))))

(defmethod transform-finger ((f finger) (tree tree))
  (let ((tree-of-f (tree f)))
    (labels ((%transform (x)
               (cond
                 ((eql x tree-of-f) f)
                 ((null x)
                  (error "Cannot find path from ~a to ~a"
                         tree-of-f tree))
                 (t
                  (transform-finger (%transform (predecessor x))
                                    (transform x))))))
      (%transform tree))))

(defclass var ()
  ((local-path :initarg :local-path
               :type list
               :accessor local-path
               :documentation "Path in a subtree from the root of the subtree
to the value for the var.")
   (value :initarg :value
          :type t
          :accessor value
          :documentation "The tree node (or leaf value) matched by the variable."))
  (:documentation "VAR objects represent not only the value matched at a location
in an AST, but the local path it took to get there."))

(defun make-tree (list-form &key predecessor)
  (make-instance 'tree :root (make-tree-node list-form)
                 :predecessor predecessor))

(defun make-tree-node (list-form)
  (if (consp list-form)
      (make-instance 'tree-node :data (car list-form)
                     :children (mapcar #'make-tree-node (cdr list-form)))
      list-form))

(defgeneric to-list (node)
  (:method ((tree tree)) (to-list (root tree)))
  (:method ((node tree-node))
    (cons (data node) (mapcar #'to-list (children node))))
  (:method (node) node))

;;; Printing methods

(defmethod print-object ((obj tree) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a" (to-list obj)))))

(defmethod print-object ((obj tree-node) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a" (to-list obj)))))

(defmethod print-object ((obj finger) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a~@[ ~a~]"
                (tree obj) (path obj) (residue obj)))))

(defmethod print-object ((obj path-transform) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a ~a"
                (transforms obj) (from-tree obj) (to-tree obj)))))

(defmethod print-object ((obj var) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a" (local-path obj) (value obj)))))

;;; This expensive function is used in testing
;;; Computes the path leading from ROOT to NODE, or
;;; signals an error if it cannot be found.
(defun path-of-node (root node)
  (labels ((%search (path n)
             (when (eql n node)
               (return-from path-of-node (nreverse path)))
             (typecase n
               (tree-node
                (iter (for i from 0)
                      (for c in (children n))
                      (%search (cons i path) c))))))
    (%search nil root)
    (error "Cannot find ~a in ~a" node root)))

                           
;;; To add: algorithm for extracting a set of transforms from
;;; a set of rewrites (with var objects).  Also, conversion of the
;;; transform set to a trie.
