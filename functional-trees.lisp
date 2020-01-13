(defpackage :functional-trees/functional-trees
  (:nicknames :ft/ft)
  (:use cl :alexandria :iterate)
  (:export data children predecessor
           transform root finger path residue
           path-transform from to
           transforms transform-finger transform-finger-to
           transform-path var local-path
           value node @ update-tree update-tree-at-data
           path-transform-of
           remove-nodes-if
           swap-nodes
           make-node to-list)
  (:documentation "Prototype implementation of functional trees w.
finger objects"))

(in-package :functional-trees/functional-trees)

(defvar *node-name-counter* 0 "Counter used to initialize the NAME slot of nodes.")

(defgeneric copy (obj &key &allow-other-keys)
  (:documentation "Like the COPY function in SEL"))

(defclass node ()
  ((data :reader data :initarg :data
         :initform (required-argument :data)
         :documentation "Arbitrary data")
   (name :reader name :initarg :name :initform nil)
   (transform :reader transform :initarg :transform
              :initform nil
              :type (or null path-transform)
              :documentation "If non-nil, is a PATH-TRANSFORM object
to this node.")
   (finger :reader finger
           :initform nil
           :type (or null finger)
           :documentation "A finger back to the root of the tree")
   (children :reader children
             :type list
             :initarg :children
             :initform (required-argument :children)
             :documentation "The list of children of the node,
which may be more nodes, or other values."))
  (:documentation "A node in a tree."))

(defmethod copy ((node node) &key (data (data node)) (name (name node)) (transform (transform node))
                                    (children (children node)))
  (make-instance 'node :data data :name name :transform transform :children children))


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
  ;; Fill in the NODE slot
  (let* ((node (node f))
         (path (path f)))
    (iter (for i in path)
          (unless (typep node 'node)
            (error "Path ~a not valid for tree rooted at ~a: ~a" (path f) (node f) node))
          (let ((children (children node)))
            (unless (and (<= 0 i) (< i (length children)))
              (error "~a not a valid child index for ~a" i node))
            (setf node (elt children i))))
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
               :initform (required-argument :transforms)
               :type list
               :documentation "A list of (<path-set> <path> <status>) triples
where <path-set> is a path set, <path> is the mapping of the initial path
in that <path-set>, and <status> is one of :live :dead. These should be
sorted into non-increasing order of length of <path>."))
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
                                       (<= i (car i-set) (cadr i-set)))))
                            path segment))
            (return
              (let ((new-segment
                     (loop for i in path
                        for init in new-initial-segment
                        for p in path
                        collect (if (consp i)
                                    (+ init (- p (car i)))
                                    init))))
                (ecase status
                  (:live (append new-segment (subseq path (length segment))))
                  (:dead (values new-segment (subseq path (length new-segment))))))))
          (finally (return path)))))

(defgeneric transform-finger (finger node &key error-p)
  (:documentation "Transforms FINGER, producing a new finger that
points through the root NODE.  NODE must be derived from the tree
that FINGER is pointed through."))

(defmethod transform-finger ((f finger) (node node) &key (error-p t))
  (let ((node-of-f (node f)))
    (labels ((%transform (x)
               (cond
                 ((eql x node-of-f) f)
                 ((null x)
                  (error "Cannot find path from ~a to ~a"
                         node-of-f node))
                 (t
                  (let ((transform (transform x)))
                    (transform-finger-to
                     (%transform (from transform))
                     transform x))))))
      (%transform node))))

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

(defun make-tree (list-form &key name transform)
  (let ((root (make-node list-form :name name :transform transform)))
    ;; Walk tree, creating fingers back to root
    (traverse-nodes-with-rpaths
     root
     (lambda (n rpath)
       ;; This is the only place this slot should be assigned,
       ;; which is why there's no writer method
       (setf (slot-value n 'finger)
             (make-instance 'finger :node root :path (reverse rpath)))
       n))
    root))

(defun make-node (list-form &key name transform)
  (if (consp list-form)
      (make-instance 'node :name name
                     :data (car list-form)
                     :transform transform
                     :children (mapcar #'make-node (cdr list-form)))
      list-form))

(defgeneric @ (node path &key &allow-other-keys)
    (:documentation "The node (or leaf value) at PATH below NODE."))

(defmethod @ ((node t) (path null) &key) node)
(defmethod @ ((node node) (path cons) &key)
    (let ((i (car path)))
      (unless (typep i '(integer 0))
        (error "Not a valid path index: ~a" i))
      (let* ((c (children node)))
        (iter (while (> i 0))
              (unless c (error "Path index too large: ~a (must be < ~a)"
                               (car path) (- (car path) i)))
              (pop c)
              (decf i))
        (@ (car c) (cdr path)))))
(defmethod @ ((node node) (finger finger) &key (error-p t))
    (let ((new-finger (transform-finger finger node :error-p error-p)))
      (values (@ node (path new-finger)) (residue new-finger))))

(defgeneric to-list (node)
  (:method ((finger finger))
    (to-list (cache finger)))
  (:method ((node node))
    (cons (data node) (mapcar #'to-list (children node))))
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
               (node
                (iter (for i from 0)
                      (for c in (children n))
                      (%search (cons i path) c))))))
    (%search nil root)
    (error "Cannot find ~a in ~a" node root)))


;;; To add: algorithm for extracting a  path transform from
;;; a set of rewrites (with var objects).  Also, conversion of the
;;; transform set to a trie.

(defun traverse-nodes (root fn)
  ;; Apply FN at every node below ROOT, in preorder, left to right
  ;; If FN returns NIL, stop traversal below this point.  Returns NIL.
  (labels ((%traverse (node)
             (when (and (typep node 'node)
                        (funcall fn node))
               (mapc #'%traverse (children node)))))
    (%traverse root)
    nil))

(defun traverse-nodes-with-rpaths (root fn)
  ;; Like TRAVERSE-NODES, but pass a rpath to FN as well as the node
  (labels ((%traverse (node rpath)
             (when (and (typep node 'node)
                        (funcall fn node rpath))
               (iter (for i from 0)
                     (for c in (children node))
                     (%traverse c (cons i rpath))))))
    (%traverse root nil)
    nil))


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

(defgeneric implant (root path new-node)
  (:documentation "Implants NEW-NODE at location PATH in tree rooted at ROOT"))

(defgeneric path-transform-of (from-node to-node)
  (:documentation "Produce a path transform that maps FROM-NODE to TO-NODE"))

(defstruct pto-data
  from
  to
  from-path
  to-path)

(defun lexicographic-< (list1 list2)
  (loop (cond
          ((null list1)
           (return (not (null list2))))
          ((null list2)
           (return nil))
          ((<= (car list1) (car list2))
           (return (< (car list1) (car list2))))
          (t
           (pop list1)
           (pop list2)))))

(defun prefix? (p1 p2)
  (loop (cond
          ((null p1) (return t))
          ((null p2) (return nil))
          ((eql (car p1) (car p2))
           (pop p1)
           (pop p2))
          (t (return nil)))))

(defmethod path-transform-of ((from node) (to node))
  (let ((table (make-hash-table)))
    (traverse-nodes-with-rpaths
     from
     (lambda (n rpath)
       (setf (gethash (name n) table) (make-pto-data :from n :from-path (reverse rpath)))))
    (format t "Table (1): ~a~%" table)
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
                 (format t "Maphash ~a, ~a~%" n pd)
                 (when (pto-data-to pd)
                   (push
                    (list (pto-data-from-path pd)
                          (pto-data-to-path pd))
                    mapping)))
               table)
      (format t "Mapping:~%~A~%" mapping)
      ;; Mapping is now a list of (<old path> <new path>) lists
      ;; Sort this into increasing order of <old path>, lexicographically
      (setf mapping (sort mapping #'lexicographic-< :key #'car))
      (format t "Sorted mapping:~%~A~%" mapping)

      (let ((sorted-result (path-transform-compress-mapping mapping)))
        (make-instance
         'path-transform
         :from from
         :transforms (mapcar (lambda (p) (append p (list :live)))
                             sorted-result))))))

(defun path-transform-compress-mapping (mapping)
  (let (stack result)
    (iter (for (old new) in mapping)
          (iter (until (or (null stack)
                           (prefix? (caar stack) old)))
                (push (pop stack) result))
          (if (null stack)
              (push (list old new) stack)
              (let ((len (length (caar stack))))
                (if (equal (subseq old len)
                           (subseq new len))
                    ;; This rewrite is subsumed by
                    ;; the one on the stack -- do nothing
                    nil
                    ;; Otherwise, push a new entry
                    (push (list old new) stack)))))
    (stable-sort (revappend stack result) #'> :key #'length)))

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
  "Traverse tree rooted at NODE, in postorder, calling
FN at each node.  If FN returns a different tree, replace
the node at that point, and copy ancestors (preserving their
names.)"
  (labels ((%traverse (n)
             (if (typep n 'node)
               ;; First, traverse the children
               (let* ((c (children n))
                      (new-c (mapcar #'%traverse c)))
                 (unless (every #'eql c new-c)
                   (setf n (copy n :children new-c)))
                 (funcall fn n))
               n)))
    (%traverse node)))

(defun update-tree-at-data (node data)
  "Cause nodes with DATA to be copied (and all ancestors)"
  (update-tree node (lambda (n) (if (eql (data n) data) (copy n) n))))


(defun remove-nodes-if (node fn)
  "Remove nodes/leaves for which FN is true"
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

(defun swap-nodes (root node1 node2)
  (update-tree
   root
   (lambda (n)
     (cond
       ((eql (data n) (data node1)) node2)
       ((eql (data n) (data node2)) node1)
       (t n)))))

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
      ((> size 1)
       (let* ((n-children (1+ (random (min child-bound (1- size)))))
              (child-sizes (random-partition (1- size) n-children)))
         (setf children (mapcar #'make-random-tree child-sizes)))))
    ;; Add random set of leaf values
    (setf children
          (random-permute (append (iter (repeat (random leaf-bound))
                                        (collecting (make-random-leaf)))
                                  children)))
    (make-instance 'node :data (make-random-data)
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

