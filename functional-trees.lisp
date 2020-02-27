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
  (:shadow :subst :subst-if :subst-if-not)
  (:shadowing-import-from
   :cl :set :union :intersection :set-difference :complement)
  (:shadowing-import-from :alexandria :compose)
  (:import-from :uiop/utility :nest)
  (:import-from :closer-mop
                :finalize-inheritance
                :slot-definition-name
                :slot-definition-allocation
                :slot-definition-initform
                :class-slots)
  (:export :copy
           :node :transform :child-slots :data-slot :finger
           :path :transform-finger-to :residue
           :children :data
           :populate-fingers
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
              ;; containing the pointer.y
              :type (or null node path-transform)
              :documentation "If non-nil, is either a PATH-TRANSFORM object
to this node, or the node that led to this node.")
   (size :reader size
         :type (integer 1)
         :documentation "Number of nodes in tree rooted here.")
   (child-slots :reader child-slots
                :initform nil
                :allocation :class
                :type '(list (or symbol cons))
                :documentation
                "List of child slots with optional arity.
This field should be specified as :allocation :class if defined by a
subclass of `node'.  List of either symbols specifying a slot holding
a list of children or a cons of (symbol . number) where number
specifies a specific number of children held in the slot.")
   (data-slot :reader data-slot
              :initform nil
              :allocation :class)
   (finger :reader finger
           :initform nil
           :type (or null node finger)
           :documentation "A finger back to the root of the (a?) tree."))
  (:documentation "A node in a tree."))

(defgeneric children (node)
  (:documentation "Return all children of NODE.")
  ;; Default method should never be called as the customization of
  ;; `finalize-inheritance' above should always define something more
  ;; specific.
  (:method ((node node))
    (error "Somehow ~S doesn't have a `children' defmethod." (type-of node))))

;;; When we finalize sub-classes of node, define a children method on
;;; that class and also define functional copying setf writers.
(defun expand-children-defmethod (class)
  `(defmethod children ((node ,(class-name class)))
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

(defgeneric data (node)
  (:documentation "Return the data of NODE.
If no `data-slot' is defined on NODE return itself.")
  (:method ((non-node t)) non-node)
  (:method ((node node))
    (when (data-slot node)
      (slot-value node (data-slot node)))))

(defmethod transform :around ((n node))
  ;; Compute the PT lazily, when TRANSFORM is a node
  (let ((tr (call-next-method)))
    (if (typep tr 'node)
        (setf (slot-value n 'transform) (path-transform-of tr n))
        tr)))

(defmethod size ((obj t)) 0)
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
   (cache :accessor :node :accessor cache
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
                      (:live (append new-segment
                                     (subseq path (length segment))))
                      (:dead (values new-segment
                                     (subseq path (length new-segment)))))))))
          (finally (return path)))))

(defgeneric transform-finger (finger node &key error-p)
  (:documentation "Transforms FINGER, producing a new finger that
points through the root NODE.  NODE must be derived from the tree
that FINGER is pointed through."))

(defmethod transform-finger ((f finger) (node node) &key (error-p t))
  (declare (ignore error-p)) ;; for now

  (let ((node-of-f (node f)))
    (transform-finger-to f (path-transform-of node-of-f node) node))

  #+(or)
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
      (%transform node)))
  )

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
;;; a set of rewrites (with var objects).  Also, conversion of the
;;; transform set to a trie.

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
               (when-let ((it (slot-value node slot)))
                 (list (make-keyword slot)
                       (mapcar (curry #'map-tree function) it))))
             (child-slots node))))
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

;;; Structure used in computation of path-transform-of
(defstruct pto-data
  ;; Node in the source tree
  from
  ;; Node in the target tree
  (to nil)
  ;; Path from root of source tree to FROM node
  from-path
  ;; Path from root of target tree to TO node
  (to-path nil))

;;; The around method here runs the new algorithm and compares
;;; the result with the old algorithm.  It is an interim
;;; step until the new algorithm is used by itself.

(defmethod path-transform-of :around ((from t) (to t))
  #+(or)
  (let ((result (call-next-method)))
    (let ((new-result (new-path-transform-of from to)))
      (assert (eql (from result) (from new-result)))
      (assert (equal (transforms result) (transforms new-result))))
    result)
  (call-next-method))

;;; TODO: see if we can make PATH-TRANSFORM-OF more efficient.  The problem is
;;; that it spends time proportional to the size of the FROM tree, even if the
;;; change is much smaller
;;;
;;; Suggestion: maintain a timestamp at each node, which is the order in which
;;; it was allocated (incremented each time a new node is created).  Traverse
;;; the two trees in increasing order of timestamp, stopping the traversal on
;;; common nodes.  Serial numbers cannot be used for this.
;;;
;;; As an alternative, instead of timestamps we could use a combination of
;;; size and serial-number, using ordering based in larger size, then larger
;;; serial number if sizes are equal.   In place of "size" any function that
;;; is monotonically increasing from children to parent could be used.

(defmethod path-transform-of ((from node) (to node))
  (let ((table (make-hash-table)))
    (traverse-nodes-with-rpaths
     from
     (lambda (n rpath)
       (with-slots (serial-number) n
         (let ((pto (gethash serial-number table)))
           (assert (null pto) ()
                   "Two nodes in tree with same serial number.~%~
                    ~a~%Path1: ~a~%Path2: ~a"
                   serial-number (pto-data-from-path pto) (reverse rpath)))
         (setf (gethash serial-number table)
               (make-pto-data :from n :from-path (reverse rpath))))))
    #+debug (format t "Table (1): ~a~%" table)
    ;; Now find nodes that are shared
    (traverse-nodes-with-rpaths
     to
     (lambda (n rpath)
       (let* ((entry (gethash (serial-number n) table)))
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

(defmethod new-path-transform-of ((orig-from node) (to node))
  ;; New algorithm for computing the path transform from FROM to TO
  ;; Uses two heaps to pull nodes from FROM and TO in decreasing
  ;; order of size and serial number
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
             #+ft-debug-new-path-transform-of
             (format t "%add-from~%")
             (let ((entry (gethash from-sn table))
                   (l (list from from-path)))
               #+ft-debug-new-path-transform-of
               (format t "entry = ~a~%" entry)
               (if (null entry)
                   (setf (gethash from-sn table) (list l nil))
                   (if (null (car entry))
                       (setf (car entry) l)
                       (error "Two nodes in FROM tree with same SN: ~a" from-sn)))))
           (%add-to ()
             #+ft-debug-new-path-transform-of
             (format t "%add-to~%")
             (let ((entry (gethash to-sn table))
                   (l (list to to-path)))
               #+ft-debug-new-path-transform-of
               (format t "entry = ~a~%" entry)
               (if (null entry)
                   (setf (gethash to-sn table) (list nil l))
                   (if (null (cadr entry))
                       (setf (cadr entry) l)
                       (error "Two nodes in TO tree with same SN: ~a" to-sn))))))
      ;; (declare (type fixnum from-size from-sn to-size to-sn))
      (tagbody
       again
         #+ft-debug-new-path-transform-of
         (progn
           (format t "from-size=~a, from-sn=~a~%" from-size from-sn)
           (format t "to-size=~a, to-sn=~a~%" to-size to-sn))
         (when (eql from to)
           #+ft-debug-new-path-transform-of
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
         #+ft-debug-new-path-transform-of
         (format t "advance1~%")
         (%add-from)
         (node-heap-add-children from-heap from from-path)
         (setf (values from from-size from-sn from-path)
               (node-heap-pop from-heap))
         (unless from (go done))
         (go again)
       advance2
         #+ft-debug-new-path-transform-of
         (format t "advance2~%")
         (%add-to)
         (node-heap-add-children to-heap to to-path)
         (setf (values to to-size to-sn to-path)
               (node-heap-pop to-heap))
         (unless to (go done))
         (go again)
       done
         #+ft-debug-new-path-transform-of
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
      #+ft-debug-new-path-transform-of
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


;;;; FSet interoperability.

;;; Define `lookup' methods to work with FSet's `@' macro.
(defmethod lookup ((node t) (path null)) node)
(defmethod lookup ((node node) (path cons))
  (etypecase path
    (proper-list
     (lookup (lookup node (car path)) (cdr path)))
    (cons
     (destructuring-bind (slot . i) path
       ;; NOTE: Is there a better way to get from a keyword to a symbol?
       (elt (slot-value node (intern (symbol-name slot))) i)))))
(defmethod lookup ((node node) (finger finger))
    (let ((new-finger (transform-finger finger node)))
      (values (lookup node (path new-finger)) (residue new-finger))))
(defmethod lookup ((node node) (i integer))
  (elt (children node) i))

;;; NOTE: The following `with', `less', and `splice' are all very
;;;       formulaic.  Perhaps they could share implementation
;;;       structure with independent `descend' methods.

(defmethod with ((node node) (path t) &optional (value nil valuep))
  "Adds VALUE (value2) at PATH (value1) in NODE."
  (fset::check-three-arguments valuep 'with 'node)
  ;; Walk down the path creating new trees on the way up.
  (labels ((descend (children index path)
             (append (subseq children 0 index)
                     (list (-with (nth index children) path))
                     (subseq children (1+ index))))
           (-with (node path)
             (nest (if (emptyp path) value)
                   (let ((index (car path))))
                   (apply #'copy node)
                   (mappend (lambda (slot)
                              (when-let ((children (slot-value node slot)))
                                (list (make-keyword slot)
                                      (descend children index (cdr path)))))
                            (child-slots node)))))
    (-with node path)))

(defmethod with :around ((node node) (path t) &optional value)
  ;; Ensure that we set the old node as the original for subsequent transforms.
  (declare (ignorable value))
  (when-let ((it (call-next-method))) (copy it :transform node)))

(defmethod with ((tree node) (location node) &optional (value nil valuep))
  (fset::check-three-arguments valuep 'with 'node)
  (with tree (path-of-node tree location) value))

(defmethod less ((tree node) path &optional (arg2 nil arg2p))
  (declare (ignore arg2))
  (fset::check-two-arguments arg2p 'less 'node)
  (labels ((descend (children index path)
             (append (subseq children 0 index)
                     (unless (emptyp path)
                       (list (less- (nth index children) path)))
                     (subseq children (1+ index))))
           (less- (node path)
             (nest (let ((index (car path))))
                   (apply #'copy node)
                   (mappend (lambda (slot)
                              (when-let ((children (slot-value node slot)))
                                (list (make-keyword slot)
                                      (descend children index (cdr path)))))
                            (child-slots node)))))
    (less- tree path)))

(defmethod less ((tree node) (location node) &optional (arg2 nil arg2p))
  (declare (ignore arg2))
  (fset::check-two-arguments arg2p 'less 'node)
  (less tree (path-of-node tree location)))

(defmethod splice ((tree node) (path list) (values t))
  (insert tree path (list values)))
(defmethod splice ((tree node) (path list) (values list))
  (labels ((descend (children index path)
             (append (subseq children 0 index)
                     (if (emptyp path)
                         values
                         (list (splice- (nth index children)
                                        path)))
                     (subseq children index)))
           (splice- (node path)
             (nest (let ((index (car path))))
                   (apply #'copy node)
                   (mappend (lambda (slot)
                              (when-let ((children (slot-value node slot)))
                                (list (make-keyword slot)
                                      (descend children index (cdr path)))))
                            (child-slots node)))))
    (splice- tree path)))

(defmethod splice ((tree node) (location node) value)
  (splice tree (path-of-node tree location) value))

(defmethod insert ((tree node) (path list) value)
  (splice tree path (list value)))

(defmethod insert (tree (path node) value)
  (splice tree (path-of-node tree path) (list value)))

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
    (swap tree location-1 (path-of-node tree location-2))))

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

(defmethod convert ((to-type (eql 'list)) (node node)
                    &key (value-fn #'data) &allow-other-keys)
  "Convert NODE of type node to a list."
  (declare (optimize (speed 3)))
  (setf value-fn (coerce value-fn 'function))
  (labels ((convert- (node)
             (declare (type function value-fn))
             (if (typep node 'node)
                 (cons (funcall value-fn node)
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

(defmethod find (item (node node)
                 &key (test #'equalp) (key nil key-p) &allow-other-keys)
  (apply #'find-if (curry (coerce test 'function) item) node
         (when key-p (list :key key))))

(defmethod find-if (predicate (node node)
                    &key from-end end start test-not test key)
  (assert (notany #'identity from-end end start test-not test)
          (from-end end start test-not test)
          "TODO: implement support for ~a key in `find-if'"
          (cdr (find-if #'car
                        (mapcar #'cons
                                (list from-end end start test-not test)
                                '(from-end end start test-not test)))))
  (when key (setf key (coerce key 'function)))
  (labels
      ((check (item) (funcall predicate (if key (funcall key item) item)))
       (find- (predicate node)
         (nest (if (check node) (return-from find-if node))
               (when (typep node 'node))
               (mapc (lambda (slot)
                       (mapc (curry #'find- predicate) (slot-value node slot)))
                     (child-slots node)))))
    (find- (coerce predicate 'function) node)
    nil))

(defmethod find-if-not
    (predicate (node node) &key (key nil key-p) &allow-other-keys)
  (apply #'find-if (complement predicate) node (when key-p (list :key key))))

(defmethod count (item (node node) &rest rest &key &allow-other-keys)
  (apply #'count item (flatten (convert 'list node)) rest))

(defmethod count-if (predicate (node node) &rest rest &key &allow-other-keys)
  (apply #'count-if predicate (flatten (convert 'list node)) rest))

(defmethod count-if-not (predicate (node node)
                         &rest rest &key &allow-other-keys)
  (apply #'count-if-not predicate (flatten (convert 'list node)) rest))

(defmethod position (item (node node) &key (test #'equalp) (key nil key-p)
                                        &allow-other-keys)
  (apply #'position-if (curry (coerce test 'function) item) node
         (when key-p (list :key key))))

(defmethod position-if (predicate (node node)
                        &key from-end end start test-not test
                          (key #'data))
  (assert (notany #'identity from-end end start test-not test)
          (from-end end start test-not test)
          "TODO: implement support for ~a key in `position-if'"
          (cdr (find-if #'car
                        (mapcar #'cons
                                (list from-end end start test-not test)
                                '(from-end end start test-not test)))))
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
                       (let ((children (slot-value node slot)))
                         (mapc (lambda (child index)
                                 (nest
                                  (position- predicate child)
                                  (if single-child (cons index path))
                                  (cons (cons (make-keyword slot) index) path)))
                               children
                               (iota (length children)))))
                     slots))))
    (position- (coerce predicate 'function) node nil)
    (values nil nil)))

(defmethod position-if-not (predicate (node node)
                            &key (key nil key-p) &allow-other-keys)
  (apply #'position-if (complement predicate) node
         (when key-p (list :key key))))

(defmethod remove (item (node node)
                   &key (test #'equalp) (key nil key-p) &allow-other-keys)
  (apply #'remove-if (curry (coerce test 'function) item) node
         (when key-p (list :key key))))

(defmethod remove-if (predicate (node node) &key (key #'data) &allow-other-keys)
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
                          &key (key nil key-p) &allow-other-keys)
  (apply #'remove-if (complement predicate) node (when key-p (list :key key))))

(defmethod substitute
    (newitem olditem (node node)
     &key (test #'equalp) (key nil key-p) &allow-other-keys)
  (apply #'substitute-if newitem (curry (coerce test 'function) olditem) node
         (when key-p (list :key key))))

(defmethod substitute-if
    (newitem predicate (node node)
     &key (copy nil copy-p) (key nil key-p) &allow-other-keys)
  (when copy-p (setf copy (coerce copy 'function)))
  (setf predicate (coerce predicate 'function))
  (apply #'substitute-with
         (lambda (item)
           (when (funcall predicate item)
             (values (if copy-p (funcall copy newitem) newitem) t)))
         node (when key-p (list :key key))))

(defmethod substitute-if-not (newitem predicate (node node)
                              &key (key nil key-p) &allow-other-keys)
  (apply #'substitute-if newitem (complement predicate) node
         (when key-p (list :key key))))

(defgeneric subst (new old tree &key key test test-not)
  (:documentation "If TREE is a cons, this simply calls `cl:subst'.
Also works on a functional tree node.")
  (:method (new old (tree cons)
            &key (key nil key-p) (test nil test-p) (test-not nil test-not-p))
    (apply #'cl:subst new old tree
           `(,@(when key-p (list :key key))
               ,@(when test-p (list :test test))
               ,@(when test-not-p (list :test-not test-not)))))
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
    (apply #'subst-if new (complement test) tree (when key-p (list :key key)))))

(defmethod substitute-with (function (node node)
                            &key (key #'data) &allow-other-keys)
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
