(defpackage :functional-trees/interval-trees
  (:nicknames :ft/it)
  (:use :common-lisp :alexandria :iterate)
  (:shadowing-import-from :fset :convert)
  (:export itree itree-root itree-size
           node node-left node-right node-key node-lo
           node-hi node-data node-size
           itree-find-node itree-find-node-path
           itree-find
           itree-glb-node itree-glb
           itree-lub-node itree-lub
           itree-insert itree-delete-node
           itree-delete)
  (:documentation "Functional implementation of splay trees
for integer intervals."))

(in-package :functional-trees/interval-trees)

;;; Interval trees here represent sets of disjoint intervals
;;; of integers

(deftype bound ()
  "The type of endpoints of the intervals"
  'integer)

(defstruct node
  (left nil :type (or null node))
  (right nil :type (or null node))
  ;; Key is either an integer (representing the interval
  ;; containing just that integer) or a cons (representing
  ;; the interval [car,cdr]).
  (key nil :type (or null bound (cons bound bound)))
  (data nil :type t))

(defun node-lo (node)
  (let ((key (node-key node)))
    (if (consp key) (car key) key)))

(defun node-hi (node)
  (let ((key (node-key node)))
    (if (consp key) (cdr key) key)))

(defstruct itree
  (root nil :type (or null node))
  (size 0 :type (integer 0)))

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

(declaim (ftype (function (bound itree) (or null node))
                itree-find-node
                itree-glb-node
                itree-lub-node)
         (ftype (function (bound itree) (values (or null node) list))))

(defun itree-find-node (key tree)
  "Return the NODE whose interval contains KEY, or NIL if none."
  (declare (type bound key)
           (type itree tree))
  (let ((node (itree-root tree)))
    (iter (while node)
          (cond
            ((< key (node-lo node))
             (setf node (node-left node)))
            ((> key (node-hi node))
             (setf node (node-right node)))
            (t
             (return node))))))

(defun itree-find-node-path (key tree)
  "Return the NODE whose interval contains KEY, or NIL if none,
and the reversed path to that node (or NIL leaf)."
  (declare (type bound key)
           (type itree tree))
  (let ((node (itree-root tree))
        (path nil))
    (iter (while node)
          (cond
            ((< key (node-lo node))
             (push node path)
             (setf node (node-left node)))
            ((> key (node-hi node))
             (push node path)
             (setf node (node-right node)))
            (t
             (return-from itree-find-node-path (values node path)))))
    (values nil path)))

(defun itree-find (key tree)
  "Find the interval in TREE containins KEY.  Returns three values:
the lo key, the hi key (giving the interval [lo,hi]) and the datum.
If no such interval is found, return NIL."
  (when-let ((node (itree-find-node key tree)))
    (values (node-lo node) (node-hi node) (node-data node))))

(defun itree-glb-node (key tree)
  "Find the highest interval in TREE for which KEY is >= LO, or NIL
if none."
  (declare (type bound key)
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

(defun itree-glb (key tree)
  (when-let ((node (itree-lub-node key tree)))
    (values (node-lo node) (node-hi node) (node-data node))))

(defun itree-lub-node (key tree)
   "Find the lowest interval in TREE for which KEY is <= HI, or NIL
if none."
  (declare (type bound key)
           (type itree tree))
  (let ((node (itree-root tree))
        (lub nil))
    (iter (while node)
          (let ((hi (node-hi node)))
            (cond
              ((< key hi)
               (setf lub node) 
               (setf node (node-left node)))
              ((> key hi)
               (setf node (node-right node)))
              (t (setf lub node)
                 (return)))))
    lub))

(defun itree-lub (key tree)
  (when-let ((node (itree-lub-node key tree)))
    (values (node-lo node) (node-hi node) (node-data node))))

(defun move-node (node left right)
  "Copy a node, changing its left and right children."
  (declare (type node node))
  (make-node :left left
             :right right
             :key (node-key node)
             :data (node-data node)))

(defun insert-node (x path)
  "Given a node X that has been inserted at the end of PATH
, rebalance nodes back along that path.  Returns the root node."
  (declare (type node x) (type list path))
  ;; X is not actually on PATH
  ;; Because nodes are reallocated during ascent, we cannot
  ;; compare nodes vs. node-left to determine the position of
  ;; a child under its parent.  So, compare keys instead.
  (flet ((%less (a b)
           (< (node-hi a) (node-lo b))))
    (iter (while path)
      (let ((p (car path))
            (pp (cadr path)))
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
                path (cddr path))))))
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

(declaim (ftype (function (t t t t) nil) collision))

(defun collision (node lo hi data)
  (declare (ignore data))
  (error "Interval collision in ITREE-INSERT: [~a,~a] intersects [~a,~a]"
         lo hi (node-lo node) (node-hi node)))

(defun itree-insert (tree lo hi data
                          &aux (new-node
                                (make-node :key (if (eql lo hi) lo (cons lo hi))
                                           :data data)))
  "Insert an interval [lo,hi] mapping to data into tree.
Return the new tree.  If the interval overlaps an interval
already in the tree signal an error"
  (multiple-value-bind (node path)
      (itree-find-node-path lo tree)
    (when node
      (collision node lo hi data))
    (when path
      (when-let ((next (and (< (node-hi (car path)) lo)
                            (next-node path))))
        (when (<= (node-lo next) hi)
          (collision next lo hi data))))
    (make-itree :root (insert-node new-node path)
                :size (1+ (itree-size tree)))))

(defun itree-delete (tree val &key error)
  (multiple-value-bind (node path)
      (itree-find-node-path val tree)
    (cond
      (node (itree-delete-node tree node path))
      (error (error "Attempted to delete a value not in the tree: ~a" val))
      (t tree))))

(defun itree-delete-node (tree node path)
  "Delete NODE from end of PATH in TREE.  Returns a new tree."
  (declare (ignorable tree node))
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
        (values node (insert-node (move-node (car path) (node-right node) (node-right (car path)))
                                  (cdr path)))))) 
    
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

      
                                            
                    
          
         
