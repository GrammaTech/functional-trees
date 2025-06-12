(defpackage :functional-trees/interval-trees
  (:nicknames :ft/it)
  (:use :common-lisp :alexandria :iterate)
  (:shadowing-import-from :fset :convert)
  (:export
    :colliding-intervals
    :colliding-trees
    :interval-collision-error
    :intervals-of-itree
    :itree
    :itree-add-intervals
    :itree-delete
    :itree-delete-node
    :itree-find
    :itree-find-node
    :itree-find-node-path
    :itree-glb
    :itree-glb-node
    :itree-insert
    :itree-lub
    :itree-lub-node
    :itree-merge-root-nodes
    :itree-remove-interval
    :itree-remove-intervals
    :itree-root
    :itree-size
    :node
    :node-data
    :node-hi
    :node-key
    :node-left
    :node-lo
    :node-right
    :node-size)
  (:documentation "Functional implementation of splay trees
for integer intervals."))

(in-package :functional-trees/interval-trees)

;;; Interval trees here represent sets of disjoint intervals
;;; of integers

(deftype bound ()
  "The type of endpoints of the intervals"
  '(integer 0 (#.(1- (ash 1 61)))))

(deftype key-type ()
  "The type of keys in the interval tree, which should subsume BOUND"
  '(integer -1 #.(1- (ash 1 61))))

(declaim
 (inline make-node
         itree-find-node-splay
         itree-find-node-path))

(declaim (inline make-node))
(defstruct node
  (left nil :type (or null node) :read-only t)
  (right nil :type (or null node) :read-only t)
  (lo (error "No lo!") :type bound :read-only t)
  (hi (error "No hi!") :type bound :read-only t)
  (data nil :type t :read-only t))

(defun node-key (node)
  (let ((lo (node-lo node))
        (hi (node-hi node)))
    (if (eql lo hi) lo (cons lo hi))))

(defun interval-range (interval)
  (etypecase interval
    (integer (values interval interval))
    (cons (values (car interval) (cdr interval)))))

(defstruct itree
  (root nil :type (or null node))
  (size 0 :type bound :read-only t))

(defgeneric nodes (tree)
  (:documentation "Returns the nodes in TREE")
  (:method ((obj itree)) (nodes (itree-root obj)))
  (:method ((obj null)) nil)
  (:method ((obj node))
    (append (nodes (node-left obj)) (list obj) (nodes (node-right obj)))))

(defmethod print-object ((obj itree) s)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj s)
        (let ((node-strings
                (mapcar (lambda (node)
                          (let ((lo (node-lo node))
                                (hi (node-hi node)))
                            (if (eql lo hi)
                                (format nil "~a=>~a" lo (node-data node))
                                (format nil "[~a,~a]=>~a" lo hi (node-data node)))))
                        (nodes obj))))
          (format s "~{~a~^,~:_~}" node-strings)))))

(defmethod print-object ((node node) s)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (node s)
        (let ((lo (node-lo node))
              (hi (node-hi node))
              (data (node-data node)))
          (format s "~a" (if (eql lo hi) lo (list lo hi)))
          (unless (eql data t)
            (format s " ~a" data))
          (format s " ~a ~a" (node-left node) (node-right node))))))

(define-condition interval-collision-error (error)
  ((lo1 :reader lo1 :initarg :lo1)
   (hi1 :reader hi1 :initarg :hi1)
   (lo2 :reader lo2 :initarg :lo2)
   (hi2 :reader hi2 :initarg :hi2)
   (data :reader data :initarg :data)
   (node :accessor node :initform nil)
   (colliding-trees :accessor colliding-trees :initform nil))
  (:default-initargs :data nil)
  (:documentation "Error thrown when an inserted interval overlaps an existing interval")
  (:report
   (lambda (cnd s)
     (format s "Interval collision~@[ inserting into ~a~]~@[ of ~a~]: ~
[~a,~a] intersects [~a,~a]~
~@[~%The following trees contain colliding intervals:~%~{  ~a~^~%~}~]"
             (data cnd)
             (node cnd)
             (lo1 cnd) (hi1 cnd) (lo2 cnd) (hi2 cnd)
             (colliding-trees cnd)))))

(defmethod colliding-intervals ((self interval-collision-error))
  (with-slots (lo1 hi1 lo2 hi2) self
    (values (cons lo1 hi1)
            (cons lo2 hi2))))

;;; TODO -- in the itree-find... functions, move the found node
;;; (or last node in the path) to the root.  This will involve
;;; modifying the itree object, but this is ok as it is still
;;; a representation of the same map
(defun itree-find-node (tree key)
  "Return the NODE whose interval contains KEY, or NIL if none.
Also return the depth of the node (or the NIL leaf) in the tree."
  (declare (type key-type key)
           (type itree tree))
  (let ((node (itree-root tree))
        (depth 0))
    (declare (type bound depth))
    (iter (while node)
          (cond
            ((< key (node-lo node))
             (incf depth)
             (setf node (node-left node)))
            ((> key (node-hi node))
             (incf depth)
             (setf node (node-right node)))
            (t
             (return-from itree-find-node (values node depth)))))
    (values nil depth)))

(defun itree-find-node-path (tree key)
  "Return the NODE whose interval contains KEY, or NIL if none,
and the reversed path to that node (or NIL leaf).  Also return
the depth of the node, which is the length of the path."
  ;; TODO -- also return the GLB and LUB nodes, and return
  ;; their reversed paths as well (these will be suffixes of the
  ;; reversed path to the NIL leaf itself.)
  (declare (type key-type key)
           (type itree tree)
           (optimize speed))
  (let ((node (itree-root tree))
        (path nil)
        (depth 0))
    (declare ((and unsigned-byte fixnum) depth))
    (iter (while node)
          (cond
            ((< key (node-lo node))
             (incf depth)
             (push node path)
             (setf node (node-left node)))
            ((> key (node-hi node))
             (incf depth)
             (push node path)
             (setf node (node-right node)))
            (t
             (return-from itree-find-node-path
               (values node path depth)))))
    (values nil path depth)))

(defun itree-find-node-splay (tree key)
  "Find the node in TREE that has the interval containing KEY,
or NIL if none.  At the same time, splay that node to the root
of TREE.  The structure TREE is modified, but the tree is updated
functionally."
  (declare (optimize speed))
  (multiple-value-bind (node rpath depth)
      (itree-find-node-path tree key)
    (declare (ignore depth))
    (when node
      (setf (itree-root tree) (insert-node node rpath))
      (itree-root tree))))

(defun itree-find (tree key)
  "Find the interval in TREE containing KEY.  Returns three values:
the lo key, the hi key (giving the interval [lo,hi]) and the datum.
If no such interval is found, return NIL."
  (when-let ((node (itree-find-node tree key)))
    (values (node-lo node) (node-hi node) (node-data node))))

(defun itree-glb-node (tree key)
  "Find the highest interval in TREE for which KEY is >= LO, or NIL
if none."
  (declare (type key-type key)
           (type itree tree))
  (let ((node (itree-root tree))
        (glb nil))
    (iter (while node)
          (let ((lo (node-lo node)))
            (cond
              ((< key lo)
               (setf node (node-left node)))
              ((> key lo)
               (setf glb node)
               (setf node (node-right node)))
              (t (setf glb node)
                 (return)))))
    glb))

(defun itree-glb (tree key)
  (when-let ((node (itree-glb-node tree key)))
    (values (node-lo node) (node-hi node) (node-data node))))

(defun itree-lub-node-path (tree key)
   "Find the lowest interval in TREE for which KEY is <= HI, or NIL
if none.  Returns the path to the node (list of ancestors of node,
in decreasing order of depth) if it exists."
  (declare (type key-type key)
           (type itree tree))
  (let ((node (itree-root tree))
        (lub nil)
        (lub-path nil)
        (path nil))
    (iter (while node)
          (let ((hi (node-hi node)))
            (cond
              ((< key hi)
               (setf lub-path path)
               (setf lub node)
               (push node path)
               (setf node (node-left node)))
              ((> key hi)
               (push node path)
               (setf node (node-right node)))
              (t (setf lub-path path)
                 (setf lub node)
                 (return)))))
    (if lub (values lub lub-path) nil)))

(defun itree-lub-node (tree key)
  (values (itree-lub-node-path tree key)))

(defun itree-lub (tree key)
  (when-let ((node (itree-lub-node-path tree key)))
    (values (node-lo node) (node-hi node) (node-data node))))

(defun move-node (node left right)
  "Copy a node, changing its left and right children."
  (declare (type node node))
  (make-node :left left
             :right right
             :lo (node-lo node)
             :hi (node-hi node)
             :data (node-data node)))

(defun intervals-of-itree (itree)
  "Return a fresh list of all the intervals in ITREE"
  (let ((intervals nil))
    (labels ((%walk (node)
               (iter (while node)
                     (%walk (node-right node))
                     (push (cons (node-lo node) (node-hi node)) intervals)
                     (setf node (node-left node)))))
      (%walk (itree-root itree)))
    intervals))

(defun itree-replace-node (itree new-node path &optional (size-delta 0))
  "Replaces the node that was reached by PATH in ITREE with new-node.
SIZE-DELTA is the change in size of the itree"
  (declare (type bound size-delta))
  (make-itree :root (insert-node new-node path)
              :size (+ (itree-size itree) size-delta)))

(defun insert-node (x rpath)
  "Given a node X that has been inserted at the end of RPATH,
rebalance nodes back along that reversed path.  Returns the root node."
  (declare (type node x) (type list rpath))
  ;; RPATH is the reversed path down to X, but X is not on RPATH
  ;; Because nodes are reallocated during ascent, we cannot
  ;; compare nodes vs. node-left to determine the position of
  ;; a child under its parent.  So, compare keys instead.
  (flet ((%less (a b)
           (< (node-hi a) (node-lo b))))
    (iter (while rpath)
      (let ((p (car rpath))
            (pp (cadr rpath)))
        (declare (type node p))
        (unless pp
          ;; Final step
          (if (%less x p)
              (setf x (move-node x
                                 (node-left x)
                                 (move-node p (node-right x) (node-right p))))
              (setf x (move-node x
                                 (move-node p (node-left p) (node-left x))
                                 (node-right x))))
          (return))
        (locally (declare (type node pp))
            ;; Four cases
          (setf x
                (if (%less x p)
                    (if (%less p pp)
                        ;; zig-zig
                        (move-node x (node-left x)
                                   (move-node p (node-right x)
                                              (move-node pp (node-right p)
                                                         (node-right pp))))
                        ;; zag zig
                        (move-node x (move-node pp (node-left pp) (node-left x))
                                   (move-node p (node-right x) (node-right p))))
                    (if (%less p pp)
                        ;; zig zag
                        (move-node x (move-node p (node-left p) (node-left x))
                                   (move-node pp (node-right x) (node-right pp)))
                        ;; zig zig
                        (move-node x (move-node p (move-node pp (node-left pp)
                                                             (node-left p))
                                                (node-left x))
                                   (node-right x))))
                rpath (cddr rpath))))))
  x)

(defun next-node (path)
  "Find the next node in the tree after the last node in PATH,
where PATH is a (reversed) list of nodes from the root down to
some node.  Return NIL if there is no next node."
  (assert path)
  (assert (null (node-right (car path))))
  (let ((node (pop path)))
    (iter (while path)
      (when (eql node (node-left (car path)))
        (if-let ((rnode (node-right (car path))))
          (progn
            (iter (while (node-left rnode))
              (setf rnode (node-left rnode)))
            (return rnode))
          (return (car path))))
      (setf node (pop path)))))

(defun max-node (node)
  "Returns the rightmost node in tree rooted at NODE, and the rpath to it"
  (let ((rpath nil))
    (iter (while (node-right node))
          (push node rpath)
          (setf node (node-right node)))
    (values node rpath)))

(defun min-node (node)
  "Returns the leftmost node in tree rooted at NODE, and the rpath to it"
  (let ((rpath nil))
    (iter (while (node-left node))
          (push node rpath)
          (setf node (node-left node)))
    (values node rpath)))

(declaim (ftype (function (t t t t) nil) collision))

(defun collision (node lo hi data)
  (error (make-condition 'interval-collision-error
                         :data data
                         :lo1 lo :hi1 hi
                         :lo2 (node-lo node) :hi2 (node-hi node))))

(defun merge-intervals (interval-list)
  "Combine intervals with the same datum.  Assumes INTERVAL-LIST
is fresh and can be modified."
  (declare (list interval-list))
  (setf interval-list (sort interval-list #'< :key #'caar))
  (when interval-list 
    (destructuring-bind ((lo . hi) datum) (car interval-list)
      (declare (type bound lo hi))
      (nconc
       (iter (for interval in (cdr interval-list))
         (destructuring-bind ((next-lo . next-hi) next-datum)
             interval
           (if (and (eql next-lo (the bound (1+ hi)))
                    (eql next-datum datum))
               (setf hi next-hi)
               (progn
                 (collecting (list (cons lo hi) datum))
                 (setf lo next-lo
                       hi next-hi
                       datum next-datum)))))
       (list (list (cons lo hi) datum))))))

(defgeneric itree-merge-root-nodes (tree &key test)
  (:documentation
  "Merge the root node with preceding or following
nodes if they (1) have abutting intervals, and (2)
have data satisfying the TEST comparison function.")
  (:method ((tree itree) &key (test #'eql))
    ;; Merge before root
    (let ((root (itree-root tree))
          (size (itree-size tree))
          (test (ensure-function test)))
      (if root
          (let ((root-data (node-data root))
                (root-lo (node-lo root))
                (root-hi (node-hi root))
                (root-left (node-left root))
                (root-right (node-right root)))
            (declare (type bound root-lo root-hi size))
            (block nil
              (labels ((%max-left (n &optional moves)
                         (declare (optimize (debug 0))) ;tail recursion
                         (unless n (return))
                         (if (null (node-right n))
                             (progn
                               (when (or (< (1+ (node-hi n)) root-lo)
                                         (not (funcall test (node-data n) root-data)))
                                 (return))
                               ;; Merge this node into root
                               (decf size)
                               (setf root-lo (node-lo n))
                               (reduce
                                (lambda (right move)
                                  (move-node move
                                             (node-left move)
                                             right))
                                moves
                                :initial-value (node-left n)))
                             (%max-left (node-right n) (cons n moves)))))
                (setf root-left (%max-left root-left))))
            (block nil
              (labels ((%max-right (n &optional moves)
                         (declare (optimize (debug 0))) ;tail recursion
                         (unless n (return))
                         (if (null (node-left n))
                             (progn
                               (when (or (< (1+ root-hi) (node-lo n))
                                         (not (funcall test root-data (node-data n))))
                                 (return))
                               ;; Merge this node into root
                               (decf size)
                               (setf root-hi (node-hi n))
                               (reduce
                                (lambda (left move)
                                  (move-node move
                                             left
                                             (node-right move)))
                                moves
                                :initial-value (node-right n)))
                             (%max-right (node-left n) (cons n moves)))))
                (setf root-right (%max-right root-right))))
            (if (< size (itree-size tree))
                (let ((new-root (make-node :data root-data
                                           :lo root-lo
                                           :hi root-hi
                                           :left root-left :right root-right)))
                  (make-itree :root new-root :size size))
              tree))
          tree))))

(defun itree-insert (tree lo hi data
                          &aux (new-node
                                (make-node :lo lo :hi hi
                                           :data data)))
  "Insert an interval [lo,hi] mapping to data into tree.
Return the new tree.  If the interval overlaps an interval
already in the tree signal an error"
  (declare (type bound lo hi))
  (multiple-value-bind (node path)
      (itree-find-node-path tree lo)
    (when node
      (collision node lo hi data))
    (when path
      (when-let ((next (and (< (node-hi (car path)) lo)
                            (next-node path))))
        (when (<= (node-lo next) hi)
          (collision next lo hi data))))
    (itree-merge-root-nodes
     (make-itree :root (insert-node new-node path)
                 :size (1+ (itree-size tree))))))

(defun itree-insert* (tree lo hi data &key (test #'eql))
  "Like ITREE-INSERT, but also merge any compatible nodes that
abut the newly inserted node."
  (itree-merge-root-nodes (itree-insert tree lo hi data) :test test))

(defun itree-delete (tree val &key error)
  (multiple-value-bind (node path)
      (itree-find-node-path tree val)
    (cond
      (node (itree-delete-node tree node path))
      (error (error "Attempted to delete a value not in the tree: ~a" val))
      (t tree))))

(defun itree-delete-node (tree node path)
  "Delete NODE from end of PATH in TREE.  Returns a new tree."
  ;; If NODE has more than one child, lift the least larger node
  ;; below it into its place
  (cond
    ((and (node-left node) (node-right node))
     (multiple-value-bind (new-node new-right)
         (lift-least-node (node-right node))
       (setf node (move-node new-node (node-left node) new-right))))
    ((node-left node)
     (setf node (node-left node)))
    ((node-right node)
     (setf node (node-right node)))
    ;; NODE has no children
    ((null path)
     (return-from itree-delete-node (make-itree))) ;; empty tree
    (t
     (let ((p (pop path)))
       (if (< (node-hi node) (node-lo p))
           (setf node (move-node p nil (node-right p)))
           (setf node (move-node p (node-left p) nil))))))
  (make-itree :root (insert-node node path) :size (1- (itree-size tree))))

(defun lift-least-node (node)
  "Rotate the least node of the tree rooted at NODE to the root."
  (let ((path nil))
    (iter (while (node-left node))
      (push node path)
      (setf node (node-left node)))
    (if (null path)
        (values node (node-right node)) ;; already in the desired form
        (values node (insert-node
                      (move-node (car path) (node-right node)
                                 (node-right (car path)))
                      (cdr path))))))

(defun itree-add-intervals (itree intervals)
  "Add interval -> data mappings itree.  Fails if any interval
overlaps one already in the tree."
  (iter (for (interval datum) in intervals)
        (setf itree
              (multiple-value-call
                  #'itree-insert
                itree
                (interval-range interval)
                datum)))
  itree)

(defun itree-remove-intervals (itree intervals)
  "Removes the intervals in INTERVALS from ITREE"
  (iter (for interval in intervals)
        (setf itree
              (multiple-value-call
                  #'itree-remove-interval
                itree
                (interval-range interval))))
  itree)

(defun itree-remove-interval (itree lo hi)
  "Remove the interval [LO,HI] from ITREE"
  (declare (type bound lo hi))
  (iter (while (<= lo hi))
        (multiple-value-bind (node path) (itree-lub-node-path itree lo)
          (while node)
          (let ((n-lo (node-lo node))
                (n-hi (node-hi node)))
            (cond
              ((< n-lo lo)
               ;; Should only happen on first iteration, if then
               (if (> n-hi hi)
                   ;; remove internal interval
                   (let* ((new2 (make-node :left nil :right (node-right node)
                                           :lo (1+ hi) :hi n-hi
                                           :data (node-data node)))
                          (new1 (make-node :left (node-left node)
                                           :right new2
                                           :lo n-lo :hi (1- lo)
                                           :data (node-data node))))
                     (setf itree (itree-replace-node itree new1 path 1))
                     (return))
                   ;; Move the overlapping node (on the low end)
                   ;; completely out of the interval.
                   (let ((new (make-node :left (node-left node)
                                         :right (node-right node)
                                         :data (node-data node)
                                         :lo n-lo :hi (1- lo))))
                     (setf itree (itree-replace-node itree new path))
                     (return))))
              ;; (>= n-lo lo)
              ((> n-hi hi)
               ;; Final iteration. Move the overlapping node (on the
               ;; high end) out of the interval.
               (let ((new (make-node :left (node-left node)
                                     :right (node-right node)
                                     :data (node-data node)
                                     :lo (1+ hi) :hi n-hi)))
                 (setf itree (itree-replace-node itree new path)))
               (return))
              (t
               ;; Common case -- remove entire node
               (setf itree (itree-delete-node itree node path))
               (setf lo (1+ n-hi)))))))
  itree)

;;; utility functions

(defmethod convert ((to-type (eql 'list)) (tree itree) &key)
  (convert 'list (itree-root tree)))

(defmethod convert ((to-type (eql 'list)) (node node) &key)
  (append (convert 'list (node-left node))
          (list (list (node-key node) (node-data node)))
          (convert 'list (node-right node))))

(defmethod convert ((to-type (eql 'itree)) (list list) &key)
  (let ((tree (make-itree)))
    (dolist (i list)
      (etypecase i
        (bound (setf tree (itree-insert tree i i t)))
        ((cons bound (cons t null))
         (setf tree (itree-insert tree (car i) (car i) (cadr i))))
        ((cons (cons bound bound) (cons t null))
         (setf tree (itree-insert tree (caar i) (cdar i) (cadr i))))))
    tree))
