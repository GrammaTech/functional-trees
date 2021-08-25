;;;; test.lisp --- Unit tests for the functional-trees package.
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
(defpackage :functional-trees/test
  (:nicknames :ft/test)
  (:use :common-lisp
        :functional-trees
        :alexandria
        :named-readtables
        :curry-compose-reader-macros
        :stefil+
        :iterate
        :cl-store
        #+gt :testbot)
  (:import-from :uiop/utility :nest)
  (:import-from :uiop/stream :with-temporary-file)
  (:shadowing-import-from :functional-trees
                          :equal?
                          :dump
                          :lexicographic-<
                          :make-node-heap-data
                          :mapc
                          :mapcar
                          :node
                          :node-can-implant
                          :node-heap-data
                          :node-heap-data-<
                          :node-valid
                          :nodes-disjoint
                          :path-of-node
                          :path-p
                          :path-transform
                          :path-transform-compress-mapping
                          :path-transform-of
                          :prefix?
                          :serial-number
                          :subst
                          :subst-if
                          :subst-if-not
                          :transform-finger
                          :with-encapsulation
                          :root-info
                          :set-transform)
  (:shadowing-import-from :fset
                          :@ :convert :less :splice :insert :lookup :alist
                          :map :set :partition :alist :size
                          :range :compose :unionf :appendf :with :removef
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
                          :some :every :notany :notevery)
  #+gt (:shadowing-import-from :testbot :batch-test)
  (:export :test))
(in-package :ft/test)
(in-readtable :curry-compose-reader-macros)

;;;; Additional infrastructure on node for testing.
(defclass node-with-data (node)
  ((children :reader children
             :type list
             :initarg :children
             :initarg children
             :initform nil
             :documentation "The list of children of the node,
which may be more nodes, or other values.")
   (child-slots :initform '(children) :allocation :class)
   (child-slot-specifiers :allocation :class)
   (data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data")))

(defmethod print-object ((obj node-with-data) stream)
  (if *print-readably*
      (call-next-method)
      (print-unreadable-object (obj stream :type t)
        (format stream "~a ~a" (serial-number obj)
                (convert 'list obj)))))

(defmethod convert ((to-type (eql 'node-with-data)) (sequence list)
                    &key &allow-other-keys)
  (labels ((make-node (list-form)
             (when list-form
               (if (consp list-form)
                   (make-instance 'node-with-data
                     :data (car list-form)
                     :children (mapcar #'make-node (cdr list-form)))
                   (make-instance 'node-with-data :data list-form)))))
    (ft::populate-fingers (make-node sequence))))

(defmethod convert ((to-type (eql 'list)) (node node-with-data)
                    &key (value-fn 'data) &allow-other-keys)
  ;; This is wonky, but it sort of looks like what you might want.
  ;; The whole `node-with-data' data structure isn't great.
  (if (children node)
      (cons (funcall value-fn node)
            (mapcar (lambda (child)
                      (if (typep child 'node)
                          (convert 'list child :value-fn value-fn)
                          child))
                    (children node)))
      (funcall value-fn node)))

(defmethod convert ((to-type (eql 'node-with-data)) (from node-with-data)
                    &key &allow-other-keys)
  from)

(define-node-class node-cons (node)
  ((head :reader head
         :initarg :head
         :initarg head
         :initform nil)
   (tail :reader tail
         :initarg :tail
         :initarg tail
         :initform nil)
   (child-slots :initform '((head . 1) (tail . 1)) :allocation :class))
  (:documentation "Functional replacement for cons."))

(define-node-class node-cons2 (node)
  ((head :reader head
         :initarg :head
         :initarg head
         :initform nil)
   (tail :reader tail
         :initarg :tail
         :initarg tail
         :initform nil)
   (child-slots :initform '((head . 1) (tail . 0)) :allocation :class))
  (:documentation "Like node-cons, but the tail is a list of children.
This is form testing . 0 child slots."))

(define-node-class node-list (node)
  ((child-slots :initform '(child-list) :allocation :class)
   (child-list :reader node-list-child-list
               :initarg :child-list
               :initarg child-list
               :initform nil))
  (:documentation "Functional replacement for LIST."))

(define-node-class node-list2 (node)
  ((child-slots :initform '((body . 0)) :allocation :class)
   (body :reader node-list2-body :initarg :body :initarg body :initform nil))
  (:documentation "A single named child that is a list of arbitrary length"))

(defun cconvert (class val)
  (typecase val
    (cons (convert class val))
    (t val)))

(defun lconvert (val)
  (if (typep val 'node) (convert 'list val) val))

(defmethod convert ((to-type (eql 'node-cons)) (sequence list)
                    &key &allow-other-keys)
  (flet ((next (it) (cconvert 'node-cons it)))
    (when sequence
      (make-instance 'node-cons
        :head (next (car sequence))
        :tail (next (cdr sequence))))))
(defmethod convert ((to-list (eql 'list)) (node node-cons)
                    &key &allow-other-keys)
  (cons (lconvert (head node)) (lconvert (tail node))))

(defmethod convert ((to-type (eql 'node-cons2)) (sequence list)
                    &key &allow-other-keys)
  (flet ((next (it) (cconvert 'node-cons2 it)))
    (when sequence
      (make-instance 'node-cons2
                     :head (next (car sequence))
                     :tail (cl:mapcar #'next (cdr sequence))))))
(defmethod convert ((to-type (eql 'list)) (node node-cons2)
                    &key &allow-other-keys)
  (cons (lconvert (head node))
        (cl:mapcar #'lconvert (tail node))))

(defmethod convert ((to-type (eql 'node-list)) (value t) &key) value)
(defmethod convert ((to-type (eql 'node-list)) (sequence list) &key)
  (make-instance 'node-list :child-list (mapcar {convert 'node-list} sequence)))
(defmethod convert ((to-type (eql 'list)) (node node-list) &key)
  (mapcar (lambda (x) (if (typep x 'node) (convert 'list x) x))
          (node-list-child-list node)))

(defmethod convert ((to-type (eql 'node-list2)) (value t) &key) value)
(defmethod convert ((to-type (eql 'node-list2)) (sequence list) &key)
  (make-instance 'node-list2 :body (mapcar {convert 'node-list2} sequence)))
(defmethod convert ((to-type (eql 'list)) (node node-list2) &key)
  (mapcar (lambda (x) (if (typep x 'node) (convert 'list x) x))
          (node-list2-body node)))

(define-node-class node-with-fields (node)
  ((child-slots :initform '((a . 1) (b . 1)) :allocation :class)
   (a :reader node-a
      :initarg :a
      :initarg a
      :initform nil
      :type (or null node-with-fields)
      :documentation "Example of a node field")
   (b :reader node-b
      :initarg :b
      :initarg b
      :initform nil
      :type (or null node-with-fields)
      :documentation "Example of a node field")
   (data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data"))
  (:documentation "Example class with two fields, a and b,
that are made available (in addition to children) as links
to subtrees."))


(defmethod node-values ((node node-with-fields)) (data node))

(defmethod lookup ((node node-with-fields) (i (eql :data))) (data node))

(defmethod convert ((to-type (eql 'node-with-fields)) (sequence list)
                    &key &allow-other-keys)
  (labels ((safe-getf (list-form key)
             (ignore-errors (getf list-form key)))
           (make-node (list-form)
             (if (consp list-form)
                 (nest
                  (apply #'make-instance 'node-with-fields)
                  (apply #'append)
                  (cons (when-let ((it (safe-getf list-form :data)))
                          (list :data it)))
                  (cons (when-let ((it (safe-getf list-form :a)))
                          (list :a (make-node it))))
                  (cons (when-let ((it (safe-getf list-form :b)))
                          (list :b (make-node it))))
                  nil)
                 list-form)))
    (ft::populate-fingers (make-node sequence))))

(defmethod convert ((to-type (eql 'list)) (node node-with-fields)
                    &key &allow-other-keys)
  "Convert NODE of type node to a list."
  (declare (optimize (speed 3)))
  (labels ((to-plist (node) (when-let ((it (data node))) (list :data it)))
           (convert- (node)
             (if (typep node 'node)
                 (append (to-plist node)
                         (mappend (lambda (child-slot)
                                    (assert (consp child-slot))
                                    (destructuring-bind
                                          (slot . size) child-slot
                                      (assert (eql size 1))
                                      (when-let ((children
                                                  (slot-value node slot)))
                                        (list (make-keyword slot)
                                              (convert 'list children)))))
                                  (child-slots node)))
                 node)))
    (convert- node)))


(define-node-class node-with-arity2 (node)
  ((child-slots :initform '((a . 2)) :allocation :class)
   (a :reader node-a
      :initarg :a
      :initarg a
      :initform '(nil nil)
      :type list
      :documentation "Example of a field of arity 2")
   (data :reader data
         :initarg :data
         :initform nil
         :documentation "Data that is attached to the node"))
  (:documentation "Example of a class with a single child slot of arity 2"))

(define-node-class node-with-arity2/2 (node)
  ((child-slots :initform '((a . 2) (b . 2)) :allocation :class)
   (a :reader node-a
      :initarg :a
      :initarg a
      :initform '(nil nil)
      :type list
      :documentation "Example of a field of arity 2")
   (b :reader node-b
      :initarg :b
      :initarg b
      :initform '(nil nil)
      :type list
      :documentation "Example of a field of arity 2"))
  (:documentation "Example of a class with two child slots of arity 2"))


(defmethod convert ((to-type (eql 'node-with-arity2)) (seq list) &key &allow-other-keys)
  (if (null seq)
      (call-next-method)
      (progn
        (assert (consp (cdr seq)))
        (make-instance 'node-with-arity2 :a (list (convert 'node-with-arity2 (car seq))
                                                  (convert 'node-with-arity2 (cadr seq)))
                       :data (cddr seq)))))

(defmethod convert ((to-type (eql 'node-with-arity2)) x &key &allow-other-keys) x)

(defmethod convert ((to-type (eql 'list)) (node node-with-arity2) &key &allow-other-keys)
  (append (mapcar (lambda (c)
                    (if (typep c 'node) (convert 'list c) c))
                  (slot-value node 'a))
          (slot-value node 'data)))

(defmethod convert ((to-type (eql 'node-with-arity2/2)) (seq list) &key &allow-other-keys)
  (if (null seq)
      (call-next-method)
      (progn
        (assert (consp (cdr seq)))
        (make-instance 'node-with-arity2/2
                       :a (mapcar {convert 'node-with-arity2/2} (car seq))
                       :b (mapcar {convert 'node-with-arity2/2} (cadr seq))))))

(defmethod convert ((to-type (eql 'node-with-arity2/2)) x &key &allow-other-keys) x)

(defmethod convert ((to-type (eql 'list)) (node node-with-arity2/2) &key &allow-other-keys)
  (list (mapcar (lambda (c)
                  (if (typep c 'node) (convert 'list c) c))
                (slot-value node 'a))
        (mapcar (lambda (c)
                  (if (typep c 'node) (convert 'list c) c))
                (slot-value node 'b))))

(defun swap-random-nodes (root)
  (let ((node1 (random-node root))
        (node2 (random-node root)))
    (if (or (is-ancestor-of node1 node2)
            (is-ancestor-of node2 node1))
        root
        (swap root node1 node2))))

(defun random-node (root)
  (let ((nodes nil))
    (do-tree (n root) (prog1 nil (push n nodes)))
    (elt nodes (random (length nodes)))))

(defun is-ancestor-of (node1 node2)
  (do-tree (n node1 :value nil)
    (prog1 nil
      (when (eql n node2)
        (return-from is-ancestor-of t)))))

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

(defun plist-drop-keys (keys plist)
  (iter (for e on plist by #'cddr)
        (unless (member (car e) keys)
          (collecting (car e))
          (when (cdr e)
            (collecting (cadr e))))))


;;;; Test suite.
(defroot test)
(defsuite test "Functional trees top-level test suite.")

;;; Simple Copy Tests
(deftest simple-copy-tests ()
  (flet ((copy-is-equal (it)
           (dolist (fn '(copy tree-copy))
             (is (funcall (typecase it
                            (symbol (lambda (a b)
                                      (string= (symbol-name a) (symbol-name b))))
                            (t #'equalp))
                          it (funcall fn it))))))
    (every #'copy-is-equal
           (list 0
                 #(1 2 3 4)
                 (let ((it (make-hash-table))) (setf (gethash :x it) 10) it)
                 '(1 2 3 4)
                 'foo))))

(deftest lexicographic-<.1 ()
  (is (not (lexicographic-< nil nil)))
  (is (not (lexicographic-< '(1) nil)))
  (is (not (lexicographic-< '(1) '(0))))
  (is (not (lexicographic-< '(1 2 3 0) '(1 2 3))))
  (is (not (lexicographic-< '(1) '(1))))
  (is (lexicographic-< nil '(1)))
  (is (lexicographic-< '(0) '(1)))
  (is (lexicographic-< '(1 2 3) '(1 2 3 0)))
  (is (lexicographic-< '(a) '(b)))
  (is (not (lexicographic-< '(b) '(a))))
  (is (lexicographic-< '(a) '(0)))
  (is (not (lexicographic-< '(0) '(a))))
  (is (not (lexicographic-< '(a) '(a))))
  (is (lexicographic-< '((a . 1)) '(2)))
  (is (lexicographic-< '((a . 1)) '((a . 2))))
  (is (not (lexicographic-< '((a . 2)) '((a . 1)))))
  (is (lexicographic-< '((a . 1) 3) '((a . 1) 10)))
  (is (if (eql (fset:compare 'a 'b) :less)
          (lexicographic-< '((a . 1)) '((b . 0)))
          (not (lexicographic-< '((a . 1)) '((b . 0))))))
  (is (not (lexicographic-< '(1) '((a . 0))))))

(deftest make-node.1 ()
  (is (not (convert 'node-cons nil)))
  (is (typep (convert 'node-cons '(:a)) 'node))
  (is (null (transform (convert 'node-cons '(:b (:c))))))
  (is (equal (convert 'list (convert 'node-cons '(:a))) '(:a)))
  (is (eql 4 (serial-number (make-instance 'node :serial-number 4)))))

(deftest finger.1 ()
  (let* ((init-list '(:a "ab" (:b) "xy" (:c (:d) #\Z (:e "!"))))
         (node (convert 'node-cons init-list)))
    (is (equal (convert 'list node) init-list))
    (flet ((%f (path)
             (convert 'list (make-instance 'finger :node node
                                     :path path :residue nil))))
      (is (equal (%f nil) init-list))
      (is (equal (%f '(0)) (car init-list)))
      (is (equal (%f '(1 0)) (cadr init-list)))
      (is (equal (%f '(1 1 0)) (caddr init-list)))
      (is (equal (%f '(1 1 1 1 0 1 0)) (second (fifth init-list)))))))

(deftest transform-path.1 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:x))))
         (node1 (convert 'node-cons l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((1) (2) :live))))
         (node2 (convert 'node-cons l2)))
    (set-transform node2 pt)

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (convert 'list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (convert 'list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(1 0))))
      (is (equal (path f3) '(1 0)))
      (is (equal (convert 'list f3) (cadr l1)))
      (ignore-errors
        (let ((f4 (transform-finger-to f3 pt node2)))
          (is (equal (path f4) '(2 0)))
          (is (null (residue f4)))
          (is (equal (convert 'list f4) (cadr l2))))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1 1 0))))
      (is (equal (path f5) '(1 1 0)))
      (is (equal (convert 'list f5) (third l1)))
      (ignore-errors
        (let ((f6 (transform-finger-to f5 pt node2)))
          (is (equal (path f6) '(2 1 0)))
          (is (null (residue f6)))
          (is (equal (convert 'list f6) (fourth l2))))))))

(deftest transform-path.2 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:c (:x))))
         (node1 (convert 'node-list l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((1) nil :dead)
                                          ((2) (1) :live))))
         (node2 (convert 'node-list l2)))
    (set-transform node2 pt)

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (convert 'list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (convert 'list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(2 1))))
      (is (equal (path f3) '(2 1)))
      (is (equal (convert 'list f3) (second (third l1))))

      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '(1 1)))
        (is (null (residue f4)))
        (is (equal (convert 'list f4) (second (second l2))))))

    (let ((f5 (make-instance 'finger :node node1 :path '(2 1))))
      (is (equal (path f5) '(2 1)))
      (is (equal (convert 'list f5) (second (third l1))))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(1 1)))
        (is (null (residue f6)))
        (is (equal (convert 'list f6) (second (second l2))))))))

(deftest transform-path.3 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:z) (:x) (:y))))
         (node1 (convert 'node-list l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((2 1) (2 0) :live)
                                          ((2) (3) :live))))
         (node2 (convert 'node-list l2)))
    (set-transform node2 pt)

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (convert 'list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (convert 'list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(2 1))))
      (is (equal (path f3) '(2 1)))
      (is (equal (convert 'list f3) (second (third l1))))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '(2 0)))
        (is (null (residue f4)))
        (is (equal (convert 'list f4) (first (third l2))))))

    (let ((f5 (make-instance 'finger :node node1 :path '(2 0))))
      (is (equal (path f5) '(2 0)))
      (is (equal (convert 'list f5) (first (third l1))))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(3 0)))
        (is (null (residue f6)))
        (is (equal (convert 'list f6) (first (fourth l2))))))))

(deftest transform-path.not-error ()
  (let* ((l1 '(:a 1))
         (l2 '(:b 2))
         (node1 (convert 'node-cons l1))
         (node2 (convert 'node-cons l2))
         (f1 (make-instance 'finger :node node1 :path nil)))
    (is (handler-case
            (progn (transform-finger f1 node2) t)
          (error () nil)))))

(deftest transform-path.named-children ()
  ;; Tests of path transforms on nodes with named child slots
  (let* ((l1 '((a b 1) (c d 2) 3))
         (node1 (convert 'node-with-arity2 l1))
         (l2 `((a b 1) (e ,(second (node-a node1)) 4) 3))
         (node2 (convert 'node-with-arity2 l2))
         (f1 (make-instance 'finger :node node1 :path nil))
         (f2 (make-instance 'finger :node node1 :path '((a . 0))))
         (f3 (make-instance 'finger :node node1 :path '((a . 1))))
         )
    (is (equal (convert 'list node2)
               '((a b 1) (e (c d 2) 4) 3)))
    (is (null (path f1)))
    (is (equal (convert 'list f1) l1))
    (is (equal (convert 'list (lookup node1 '((a . 0)))) '(a b 1)))
    (is (equal (convert 'list (lookup node1 '((a . 1)))) '(c d 2)))
    (is (equal (convert 'list f1) l1))
    (is (equal (convert 'list f2) (car l1)))
    (is (equal (convert 'list f3) (cadr l1)))
    (let ((pt (path-transform-of node1 node2)))
      ;; (is (equal (transform-path nil pt) nil))
      ;; (is (equal (transform-path '(:a 0) pt) '(:a 0)))
      (is (eql (ft::from pt) node1))
      (is (equal (ft::transforms pt)
                 '((((a . 1)) ((a . 1) (a . 1)) :live))))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '((a . 1) (a . 1))))))))

;;; Tests of path-transform-of, mapcar
(deftest mapcar.0 ()
  (is (eql (mapcar #'identity 1) 1))
  (is (eql (mapcar #'1+ 1) 2))
  (is (equalp (mapcar (lambda (x) (if (integerp x) (1+ x) x)) '(0 1 (2 . 3)))
              ;; Because we call cl:mapcar on regular lists.
              '(1 2 (2 . 3)))))

(deftest mapcar.1 ()
    (let* ((n1 (convert 'node-cons '(:a (:b) (:c) (:d))))
           (n2 (mapcar (lambda (n)
                         (if (eql :c (head n))
                             (make-instance 'node-cons :head :c)
                             n))
                       n1)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n1) (convert 'list n2)))))

(deftest mapcar.2 ()
    (let* ((n1 (convert 'node-cons '(:a (:b) (:c) (:d))))
           (n2 (mapcar (lambda (n)
                         (if (eql :c (head n))
                             (make-instance 'node-cons :head :c)
                             n))
                         n1)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n1) (convert 'list n2)))))

(deftest remove-if.3 ()
  (let* ((n1 (convert 'node-cons '(:a (:b) (:c) (:d))))
         (n2 (remove-if (lambda (it)
                          (and (typep (head it) 'node-cons)
                               (eql :c (head (head it)))))
                        n1)))
    (is (not (eql n1 n2)))
    (is (equal (convert 'list n2) '(:a (:b))))))

(deftest swap.4 ()
  (let* ((n1 (convert 'node-cons '(:a (:b) (:c) (:d))))
         (n2 (@ n1 '(:tail :head)))
         (n3 (@ n1 '(:tail :tail :tail :head)))
         (n4 (swap n1 n2 n3)))
    (is (not (eql n1 n4)))
    (is (equal (convert 'list n4) '(:a (:d) (:c) (:b))))))

(deftest setf-slot-accessor.1 ()
  (let* ((n1 (convert 'node-cons '(:a :b)))
         (sn1 (serial-number n1)))
    (is (eql (@ n1 :head) :a))
    (is (equal (convert 'list (@ n1 :tail)) '(:b)))
    (is (eql (setf (@ n1 :head) :c) :c))
    (is (eql (handler-case (setf (head n1) :d)
               (error () :good))
             :good))
    (is (equal (convert 'list n1) '(:c :b)))
    (is (equal sn1 (serial-number n1)))))

(deftest setf-slot-accessor.2 ()
  (let* ((n1 (convert 'node-cons '(:a :b)))
         (n2 (convert 'node-cons '(:c :d))))
    (setf (@ n1 :tail) n2)
    (is (eql (serial-number n2) (serial-number (tail n1))))))

(deftest @.error ()
  (is (handler-case (progn (@ (convert 'node-cons '(:a)) '(:bad)) nil)
        (error () t)))
  (is (handler-case (progn (@ (convert 'node-cons '(:a)) '(-1)) nil)
        (error () t))))

(deftest path-of-node.1 ()
  (let ((n1 (convert 'node-cons '(:a)))
        (n2 (convert 'node-cons '(:a (:b) (:b (:c) (:d) (:e)) (:d)))))
    (is (handler-case (progn (path-of-node n2 n1) nil)
          (error () t)))
    (is (equal (path-of-node n2 (second (children n2))) '(tail)))
    (is (equal (path-of-node n1 n1) nil))
    (is (equal (path-of-node n2 (head (tail n2))) '(tail head)))))

(deftest node-can-implant.1 ()
  (let* ((n1 (convert 'node-cons '(:a (:b) (:b (:c) (:d) (:e)) (:d))))
         (n2 (tail n1))
         (n3 (head (tail (tail n1)))))
    (is (node-can-implant n1 n1 n1))
    (is (node-can-implant n1 n2 n2))
    (is (not (node-can-implant n1 n2 n1)))
    (is (not (node-can-implant n1 n3 n2)))))

(deftest path-p.1 ()
  (is (path-p '()))
  (is (path-p '((1 2))))
  (is (not (path-p '((2 1)))))
  (is (path-p '(0 1 2)))
  (is (not (path-p '(-1))))
  (is (not (path-p '(-1 1)))))

(deftest path.1 ()
  (is (typep '() 'path))
  (is (typep '((1 2)) 'path))
  (is (not (typep '((2 1)) 'path)))
  (is (typep '(0 1 2) 'path))
  (is (not (typep '(-1) 'path)))
  (is (not (typep '(-1 1) 'path))))

(deftest node-valid.1 ()
  (is (node-valid (convert 'node-cons '(:a))))
  (is (node-valid (convert 'node-cons '(:a (:a) (:b)))))
  (is (not (node-valid
            (let ((n (convert 'node-cons '(:a))))
              (convert 'node-cons `(:b ,n ,n)))))))

(deftest nodes-disjoint.1 ()
  (is (nodes-disjoint (convert 'node-cons '(:a))
                          (convert 'node-cons '(:b))))
  (is (nodes-disjoint (convert 'node-cons '(:a))
                          (convert 'node-cons '(:a))))
  (is (nodes-disjoint (convert 'node-cons '(:a (:b)))
                          (convert 'node-cons '(:a (:b)))))
  (let ((n (convert 'node-cons '(:a))))
    (is (not (nodes-disjoint n n))))
  (let ((n (convert 'node-cons '(:a))))
    (is (not (nodes-disjoint (convert 'node-cons `(:b ,n))
                             (convert 'node-cons `(:c ,n))))))
  (let* ((n (convert 'node-cons '(:a)))
         (n2 (copy n :data :b)))
    (is (not (nodes-disjoint (convert 'node-cons `(:c ,n))
                             (convert 'node-cons `(:d ,n2)))))))

(deftest tree-copy.1 ()
  (let* ((l '(:a (:b) ((:c) :d . :e)))
         (n (convert 'node-cons l))
         (n2 (tree-copy n))
         (nodes nil)
         (nodes2 nil))
    (do-tree (x n) (push x nodes))
    (do-tree (x n2) (push x nodes2))
    (is (null (intersection nodes nodes2)))
    (is (equal (convert 'list n) l))
    (is (equal (convert 'list n2) l))
    (is (nodes-disjoint n n2))))

(deftest node-equal?.1 ()
  (is (equal? nil nil))
  (is (equal? 1 1))
  (is (equal? '(1) '(1)))
  (is (not (equal? 1 2)))
  (let ((n (convert 'node-cons '(:a))))
    (is (equal? n n))
    (is (equal? n (copy n :data :b)))
    (is (not (equal? n (convert 'node-cons '(:a)))))
    (is (not (equal? n (convert 'node-cons '(:a (:b))))))
    (let ((it (convert 'node-cons '(:b))))
      (is (not (equal? n (copy n :head (head it) :tail (tail it))))))))

(deftest print.1 ()
  (let ((*print-readably* nil)
        (n1 (convert 'node-cons '(:a)))
        (t1 (convert 'node-cons '(:a))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (convert 'node-cons '(:a)) s))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (path-transform-of n1 n1) s))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (finger t1) s))))))

(deftest print.2 ()
  (let ((*print-readably* t)
        (n1 (convert 'node-cons '(:a)))
        (t1 (convert 'node-cons '(:a))))
    (declare (ignorable t1))
    (flet ((%e (v)
             (handler-case (progn (prin1 v) nil)
               (error () t))))
      (is (%e (convert 'node-cons '(:a))))
      (is (%e (path-transform-of n1 n1))))))

(deftest print.3 ()
  (let* ((init-list '(:a "ab" (:b) "xy" (:c (:d) #\Z (:e "!"))))
         (node (convert 'node-cons init-list))
         (f (make-instance 'finger :node node
                           :path '(1 0)))
         (*print-readably* t))
    (is (handler-case (progn (prin1 f) nil)
          (error () t)))))

(defun random-test-check (n1 n2)
  (when (and n1 n2)
    (let ((pt (path-transform-of n1 n2))
          (serial-numbers nil))
      (handler-case
          (progn
            (do-tree (n n2)
              (prog1 nil
                (push (serial-number n) serial-numbers)))
            ;; (format t "SERIAL-NUMBERS = ~a~%" serial-numbers)
            (do-tree (n n1 :index rpath)
              (prog1 nil
                (when (member (serial-number n) serial-numbers)
                  (let* ((f (make-instance 'finger
                              :node n1 :path (reverse rpath)))
                         (n3 (@ n2 f)))
                    ;; (format t "n = ~a~% n3 = ~a~%" n n3)
                    (when (typep n3 'node)
                      (unless (eql (serial-number n)
                                   (serial-number n3))
                        (return-from random-test-check
                          (list n1 n2 n3 n (serial-number n)
                                (serial-number n3)
                                f)))))))))
        (error (e)
          (return-from random-test-check
            (list n1 n2 pt e))))))
  nil)

(defun random-test (size reps mutate-fn)
  "For REPS repetitions, generate a random tree of size
SIZE, mutate it with MUTATE-FN, then check that the path
transform from the former to the latter correctly maps
paths to the right nodes.  Return NIL on success or
diagnostic information on error or failure."
  (iter (repeat reps)
        (let* ((n1 (make-random-tree size))
               (n2 (funcall mutate-fn n1))
               (result (random-test-check n1 n2)))
          (when result (return result)))))

(defun remove-nodes-randomly (root p)
  "Remove nodes from tree with probability p"
  (assert (typep p '(real 0)))
  (remove-if (lambda (n) (declare (ignore n)) (<= (random 1.0) p)) root))

(deftest swap.1 ()
  ;; Swap (:d 26) and (:b 54 84)
  (let* ((l1 '(:i 17 17 (:d 26) (:m (:b 54 84))))
         (n1 (convert 'node-cons l1))
         (p2 '(:tail :tail :tail :head))
         (n2 (@ n1 p2))
         (f2 (make-instance 'finger :node n1 :path p2))
         (p3 '(:tail :tail :tail :tail :head :tail :head))
         (n3 (@ n1 p3))
         (f3 (make-instance 'finger :node n1 :path p3))
         (n4 (swap n1 n2 n3)))
    (is (equal (transform n1) nil))
    (is (typep (transform n4) 'path-transform))
    (is (equal (convert 'list n1) l1))
    (is (equal (convert 'list n2) '(:d 26)))
    (is (equal (convert 'list n3) '(:b 54 84)))
    (is (equal (convert 'list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    ;; Swap moves the nodes as expected.
    (is (eql (serial-number (@ n1 p2)) (serial-number (@ n4 p3))))
    (is (eql (@ n1 p2) (@ n4 p3)))
    (is (eql n2 (@ n4 p3)))
    (is (eql n3 (@ n4 p2)))
    ;; Fingers find original nodes in original.
    (is (eql n2 (@ n1 f2)))
    (is (eql n3 (@ n1 f3)))
    ;; Fingers find the new nodes at the new locations.
    ;; This does not work yet, as path transforms are not working
    ;; on non-numeric path entries
    #+broken (is (equal n2 (@ n4 f2)))
    #+broken (is (equal n3 (@ n4 f3)))
    ))

;; Same as swap.1, but with 0/1 in place of :head/:tail
(deftest swap.2 ()
  ;; Swap (:d 26) and (:b 54 84)
  (let* ((l1 '(:i 17 17 (:d 26) (:m (:b 54 84))))
         (n1 (convert 'node-cons l1))
         (p2 '(tail tail tail head))
         ;; (p2 '((tail . 0) (tail . 0) (tail . 0) (head . 0)))
         (n2 (@ n1 p2))
         (f2 (make-instance 'finger :node n1 :path p2))
         ;; (p3 '(:tail :tail :tail :tail :head :tail :head))
         ;; (p3 '(1 1 1 1 0 1 0))
         (p3 '(tail tail tail tail head tail head))
         ; (p3 '((tail . 0) (tail . 0) (tail . 0) (tail . 0) (head . 0) (tail . 0) (head . 0)))
         (n3 (@ n1 p3))
         (f3 (make-instance 'finger :node n1 :path p3))
         (n4 (swap n1 n2 n3)))
    (is (equal (transform n1) nil))
    (is (typep (transform n4) 'path-transform))
    (is (equal (convert 'list n1) l1))
    (is (equal (convert 'list n2) '(:d 26)))
    (is (equal (convert 'list n3) '(:b 54 84)))
    (is (equal (convert 'list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    ;; Swap moves the nodes as expected.
    (is (eql (serial-number (@ n1 p2)) (serial-number (@ n4 p3))))
    (is (eql (@ n1 p2) (@ n4 p3)))
    (is (eql n2 (@ n4 p3)))
    (is (eql n3 (@ n4 p2)))
    ;; Fingers find original nodes in original.
    (is (eql n2 (@ n1 f2)))
    (is (eql n3 (@ n1 f3)))
    ;; Fingers find the new nodes at the new locations.
    (is (equal n2 (@ n4 f2)))
    (is (equal n3 (@ n4 f3)))
    ))

(deftest path-of-node.0 ()
  (let ((it (convert 'node-cons '(:i 17 17 (:d 26) (:m (:b 54 84))))))
    (is (equalp (path-of-node it (@ it '(tail tail tail))) '(tail tail tail)))))

(deftest size.0 ()
  (let ((it (convert 'node-cons '(:i 17 17 (:d 26) (:m (:b 54 84))))))
    (is (eql 12 (size it)))))

(deftest mapcar.3 ()
  (is (equalp (mapcar (lambda (n) (case n (3 :eric) (t n))) '(1 2 3 4))
              '(1 2 :eric 4)))
  (is (equalp (mapcar (lambda (n) (case n (3 :eric) (t n))) (fset:seq 1 2 3 4))
              (fset::seq 1 2 :eric 4))))

;; Test that came up in random testing
#+nil
(deftest remove-second-child ()
  (let* ((n (convert 'node-with-data '(a b c d)))
         (n2 (remove (@ n 1) n)))
    ))

(deftest random.1 ()
  ;; Randomized test of path transforms
  (is (equal (random-test 20 200 (lambda (n) (remove-nodes-randomly n 0.2))) nil)))

(deftest random.2 ()
  (let ((result :pass)
        (size 50))
    (dotimes (n 1000)
      (let ((root (make-random-tree size)))
        (do-tree (n root :index rpath)
          (prog1 nil
            (let ((p (reverse rpath)))
              (macrolet ((is (e)
                           `(unless ,e
                              (setf result (list :fail ',e p n root))
                              (return))))
                ;; TODO: Iterate needs to be taught how to walk `is'.
                (is (path-p p))
                (is (typep p 'path))
                (is (eql (@ root p) n))
                (is (equal (path-of-node root n) p))))))))
    (is (equal result :pass))))

(deftest random.3a ()
  (is (equal (random-test 5 1000 #'swap-random-nodes)
             nil)))

(deftest random.3 ()
  (is (equal (random-test 5 1000 (lambda (n)
                                   (iter (repeat (1+ (random 4)))
                                         (setf n (swap-random-nodes n)))
                                   n))
             nil)))

(defun tree-has-null-data-node (n)
  (typecase n
    (node-cons (or (null (data n))
                        (some #'tree-has-null-data-node (children n))))
    (t nil)))

(deftest new/old.path-transform.1 ()
  ;; Likely related to symbolic paths not working in path transforms
  #+broken
  (let* ((l1 '(a 65 (g 39 82) 23 (a 68 51)))
         (n1 (convert 'node-cons l1))
         (c (children n1))
         (l2 `(a 65 ,(elt c 1) 23 ,(elt c 0)))
         (n2 (copy (convert 'node-cons l2) :root-info (make-instance 'root-info :transform n1))))
    (is (null (random-test-check n1 n2)))))

(deftest path-transform-compress-mapping.1 ()
  (let ((mapping '((nil nil) ((0) (2 0)) ((1) (0 1))
                   ((2) (2)) ;; This is dominated by (nil nil)
                   ((2 0) (0)) ((2 0 1) (1)))))
    (is (equal (path-transform-compress-mapping mapping)
               '(((2 0 1) (1))
                 ((2 0) (0))
                 ((1) (0 1))
                 ((0) (2 0))
                 (nil nil))))))

;;; Tests of subclass of NODE with discrete fields

(deftest node-with-fields.1 ()
  (let ((n (make-instance 'node-with-fields :data :foo
                          :a (make-instance 'node-with-fields :data 1)
                          :b (make-instance 'node-with-fields :data 2))))
    (is (equal (convert 'list n) '(:data :foo :a (:data 1) :b (:data 2))))
    (is (equal (@ n '(:a :data)) 1))
    (is (equal (@ n '(:b :data)) 2))))

(deftest node-with-fields.2 ()
  (let ((n (convert 'node-with-fields '(nil))))
    (is (typep n 'node-with-fields))
    (is (equal (node-a n) nil))
    (is (equal (node-b n) nil))))

(deftest node-with-fields.3 ()
  (let ((n (convert 'node-with-fields '(:data :foo :a (:data 1) :b (:data 2)))))
    (is (equal (data (node-a n)) 1))
    (is (equal (data (node-b n)) 2))))

(deftest node-with-fields.4 ()
  (let* ((n1 (convert 'node-with-fields '(:data :foo
                                          :a (:data :bar)
                                          :b (:data :baz))))
         (n2 (mapcar (lambda (n)
                         (if (eql :bar (data n))
                             (make-instance 'node-with-fields :data :qux)
                             n))
                       n1))
         (n3 (convert 'node-with-fields '(:data :quux)))
         (n4 (mapcar (lambda (n) (if (eql :baz (data n)) n3 n))
                       n1)))
    (is (equal (convert 'list n1) '(:data :foo
                                    :a (:data :bar)
                                    :b (:data :baz))))
    (is (equal (convert 'list n2) '(:data :foo
                                    :a (:data :qux)
                                    :b (:data :baz))))
    (is (equal (convert 'list n4) '(:data :foo
                                    :a (:data :bar)
                                    :b (:data :quux))))))

(deftest reduce-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (is (eql (reduce #'+ (iota 10))
             (reduce (lambda (acc node)
                       (+ (or (data node) 0)
                          (reduce #'+ (remove-if {typep _ 'node} (children node)))
                          acc))
                     tree :initial-value 0)))))

(deftest find-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (is (eql (data (find 4 tree :key #'data)) 4))
    (is (not (find 10 tree))))
  (let ((tree (convert 'node-with-arity2 '((a b 1) (c d 2) 3))))
    (is (equal (convert 'list (find 1 tree :key [#'car #'data])) '(a b 1)))
    (is (equal (convert 'list (find 2 tree :key [#'car #'data])) '(c d 2)))
    (is (equal (convert 'list (find 3 tree :key [#'car #'data])) '((a b 1) (c d 2) 3)))
    (is (null (convert 'list (find 0 tree :key [#'car #'data]))))))

(deftest find-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (declare (optimize (speed 0)))
    (is (eql (data (find-if «and #'integerp [#'zerop {mod _ 3}] {< 4 }» tree :key #'data)) 6))
    (is (not (find-if (constantly nil) tree :key #'data)))
    (is (not (find-if (constantly nil) tree))))
  (let ((tree (convert 'node-with-arity2 '((a b 1) (c d 2) 3))))
    (is (equal (data (find-if #'evenp tree :key [#'car #'data])) '(2)))
    (is (null (find-if {< 4} tree :key [#'car #'data])))))

(deftest find-if-not-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (declare (optimize (speed 0)))
    (is (eql (data (find-if-not [#'not «and #'integerp [#'zerop {mod _ 3}] {< 4 }»] tree :key #'data)) 6))
    (is (not (find-if-not (constantly t) tree :key #'data)))
    (is (not (find-if-not #'identity tree)))))

(deftest find-returns-a-node ()
  (let ((tree (convert 'node-with-fields '(:data :foo
                                           :a (:data :bar)
                                           :b (:data :baz)))))
    (flet ((%f (v) (find v tree :key #'data)))
      (is (null (%f :qux)))
      (is (typep (%f :foo) 'node-with-fields))
      (is (equalp (%f :foo) tree))
      (is (typep (%f :bar) 'node-with-fields))
      (is (typep (%f :baz) 'node-with-fields))
      (is (equalp (%f :baz)
                  (@ tree (position :baz tree :key #'data)))))))

(deftest count-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (is (eql (count 3 tree :key #'data) 1))))

(deftest count-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (declare (optimize (speed 0)))
    (is (= (count-if [#'zerop {mod _ 3}] tree :key #'data) 3))
    (is (zerop (count-if (constantly nil) tree :key #'data)))))

(deftest count-if-not-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (declare (optimize (speed 0)))
    (is (= (count-if-not [#'zerop {mod _ 3}] tree :key #'data) 6))
    (is (not (zerop (count-if-not (constantly nil) tree :key #'data))))))

(deftest position-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (is (equalp (position 4 tree :key #'data) '((children . 2))))
    (is (equalp (position 11 tree :key #'data) '((children . 4) (children . 0)
                                                 (children . 0))))
    (is (not (position 12 tree :key #'data)))))

(deftest position-tree-w-named-children ()
  (is (equalp (position 1 (convert 'node-with-fields
                                   '(:data :foo :a (:data 1) :b (:data 2)))
                        :key #'data)
              '(a))))

(deftest position-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (declare (optimize (speed 0)))
    (is (= (data (@ tree (position-if «and [#'zerop {mod _ 3}] {< 4 }» tree
                                      :key #'data)))
           6))
    (is (not (position-if (constantly nil) tree)))
    (is (not (position-if #'identity tree :key (constantly nil))))))

(deftest position-if-tree.named-children ()
    (let* ((l1 '((a b . 1) (c d . 2) . 3))
           (node (convert 'node-with-arity2 l1)))
      (is (equal (position-if #'evenp node :key #'data)
                 '((a . 1))))))

(deftest position-if-not-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (declare (optimize (speed 0)))
    (is (= (data (@ tree (position-if-not
                          [#'not «and [#'zerop {mod _ 3}] {< 4 }»]
                          tree :key #'data)))
           6))
    (is (not (position-if-not (constantly t) tree)))
    (is (not (position-if-not #'not tree :key (constantly nil))))))

(deftest child-position-tree ()
  (let ((tree (convert 'node-list '(4 7 19 21))))
    (is (equal (child-position-if (lambda (c) (eql c 19)) tree) '((child-list . 2))))
    (is (equal (child-position-if #'evenp tree :key #'1+) '((child-list . 1))))
    (is (equal (child-position 0 tree) nil))
    (is (equal (child-position 4 tree) '((child-list . 0))))
    (is (equal (child-position 4 tree :key (lambda (c) (- c 3))) '((child-list . 1))))))

(deftest remove-tree ()
  (declare (optimize (speed 0)))
  (is (= (size (remove 24 (convert 'node-with-data (iota 100)) :key #'data))
         99))
  (is (transform (remove 24 (convert 'node-with-data (iota 100)) :key #'data)))
  (is (equal (convert 'list (remove 3 (convert 'node-with-data (iota 6))
                                    :key #'data))
             '(0 1 2 4 5)))
  (is (equal (convert 'list (remove 3 (convert 'node-with-data (iota 6))
                                    :key [#'1+ #'data]))
             '(0 1 3 4 5)))
  (is (equal (convert 'list (remove 3 (convert 'node-with-data (iota 6))
                                    :key #'data))
             '(0 1 2 4 5))))

(deftest remove-tree-if ()
  ;; NOTE: Counterintuitively, because the "0" node is the parent of
  ;; the rest of the tree.
  (is (zerop (length (convert 'list (remove-if #'evenp (convert 'node-with-data
                                                                (iota 100))
                                               :key #'data)))))
  (is (= 50 (length (convert 'list (remove-if #'oddp (convert 'node-with-data
                                                              (iota 100))
                                              :key #'data))))))

(deftest remove-tree-if-not ()
  (is (= 50 (length (convert 'list
                             (remove-if-not #'evenp
                                            (convert 'node-with-data
                                                     (iota 100))
                                            :key #'data)))))
  (is (equal (convert 'list (remove-if-not (lambda (a)
                                             (or (not (integerp a))
                                                 (<= 2 a 4)))
                                           (convert 'node-with-data (cons :a (iota 6)))
                                           :key #'data))
             '(:a 2 3 4)))
  (is (equal (convert 'list (remove-if-not #'not
                                           (convert 'node-with-data (iota 6))
                                           :key [{member _ '(2 3 4)} #'data]))
             '(0 1 5))))

(deftest substitute-test ()
  (let ((no-twenty (substitute
                    (make-instance 'node-with-data :data 40) 20
                    (convert 'node-with-data (iota 100)) :key #'data)))
    (is (= 0 (count 20 no-twenty :key #'data)))
    (is (= 2 (count 40 no-twenty :key #'data)))
    (is (transform no-twenty)))
  (let ((it (convert 'node-with-data (iota 6))))
    (is (equal (convert 'list (substitute
                               (make-instance 'node-with-data :data :x) nil it
                               :key [{typep _ '(not (integer 2 4))} #'data]))
               '(0 1 :x :x :x 5)))))

(deftest substitute-if-test ()
  (let ((no-odd (substitute-if (make-instance 'node-with-data :data :odd)
                               #'oddp (convert 'node-with-data (iota 100))
                               :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data)))
    (let ((it (convert 'node-with-data '(0 2 3 3 4)))
          (n (convert 'node-with-data '(:z 18))))
      (let ((c1 (substitute-if n #'oddp it :key #'data)))
        (is (eql (@ c1 '(1)) (@ c1 '(2)))))
      (let ((c1 (substitute-if n #'oddp it :copy 'copy :key #'data)))
        (is (not (eql (@ c1 '(1)) (@ c1 '(2)))))))))

(deftest substitute-if-not-test ()
  (let ((no-odd
         (substitute-if-not (make-instance 'node-with-data :data :odd)
                            #'evenp
                            (convert 'node-with-data (iota 100))
                            :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data)))
    (let ((it (convert 'node-with-data (iota 6))))
      (is (equal (convert 'list (substitute-if-not
                                 (make-instance 'node-with-data :data :x)
                                 #'null it
                                 :key [{typep _ '(integer 2 4)} #'data]))
                 '(0 1 :x :x :x 5))))
    (let ((it (convert 'node-with-data '(0 2 3 3 4)))
          (n (convert 'node-with-data '(:z 18))))
      (let ((c1 (substitute-if-not n «or (complement #'numberp) #'evenp» it
                                   :key #'data)))
        (is (eql (@ c1 '(1)) (@ c1 '(2)))))
      (let ((c1 (substitute-if-not n #'evenp it :copy 'copy
                                   :key #'data)))
        (is (not (eql (@ c1 '(1)) (@ c1 '(2)))))))))

(deftest subst-test ()
  (let ((no-twenty (subst (make-instance 'node-with-data :data 40)
                          20 (convert 'node-with-data (iota 100))
                          :key #'data)))
    (is (= 0 (count 20 no-twenty :key #'data)))
    (is (= 2 (count 40 no-twenty :key #'data)))
    (is (transform no-twenty)))
  (is (equal (subst :y :x '(:a :x :y :z))
             '(:a :y :y :z)))
  (is (equal (subst :y t '(0 1 2 3 4) :key {typep _ '(eql 2)})
             '(0 1 :y 3 4)))
  (is (equal (subst :y '(1) '(0 1 2 3 4) :test #'equal :key #'list)
             '(0 :y 2 3 4)))
  (is (equal (subst :y '(1) '(0 1 2 3 4) :test-not (complement #'equal) :key #'list)
             '(0 :y 2 3 4)))
  (is (= (subst 10 20 20) 10)) ; when tree is an atom
  (let ((it (subst (make-instance 'node-with-data :data :x)
                   4 (convert 'node-with-data '(:a 1 (:b 2) 3 (:c (:d 4) 5) (:e 4) 7))
                   :key #'data)))
    (is (equal (convert 'list it)
               '(:a 1 (:b 2) 3 (:c (:d :x) 5) (:e :x) 7))))
  (let ((it (subst (make-instance 'node-with-data :data 17)
                   :c (convert 'node-with-data '(:a 1 (:b 2) (:c 3) (:d 4)))
                   :key #'data)))
    (is (equal (convert 'list it) '(:a 1 (:b 2) 17 (:d 4)))))
  (let ((it (subst (make-instance 'node-with-data :data 17)
                   :c (convert 'node-with-data '(:a 1 (:b 2) (:c 3) (:d 4)))
                   :key #'data)))
    (is (equal (convert 'list it) '(:a 1 (:b 2) 17 (:d 4))))))

(deftest subst-if-test ()
  (let ((no-odd (subst-if (make-instance 'node-with-data :data :odd)
                          #'oddp (convert 'node-with-data (iota 100))
                          :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data))))
  (is (= (subst-if 10 (lambda (x) (= x 20)) 20) 10)) ; when tree is an atom
  (let ((it (subst-if (make-instance 'node-with-data :data :odd)
                      «and #'numberp #'oddp»
                      (convert 'node-with-data '(:a 1 2 3))
                      :key #'data)))
    (is (equal (convert 'list it) '(:a :odd 2 :odd))))
  (is (equal (subst-if :x #'zerop '(1 2) :key #'size)
             '(:x :x . :x))))

(deftest subst-if-not-test ()
  (let ((no-odd
         (subst-if-not (make-instance 'node-with-data :data :odd)
                       #'evenp (convert 'node-with-data (iota 100))
                       :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data))))
  (is (= (subst-if-not 10 (lambda (x) (= x 20)) 20) 20)) ; when tree is an atom
  (let ((it (subst-if-not (make-instance 'node-with-data :data :odd)
                          (complement «and #'numberp #'oddp»)
                          (convert 'node-with-data '(:a 1 2 3))
                          :key #'data)))
    (is (equal (convert 'list it) '(:a :odd 2 :odd))))
  (is (equal (subst-if-not :x #'plusp '(1 2) :key #'size)
             '(:x :x . :x))))

(deftest with-test ()
  (let ((two-fives (with (convert 'node-with-data (iota 10)) '(2)
                         (make-instance 'node-with-data :data 5))))
    (is (= 2 (count 5 two-fives :key #'data)))
    (is (zerop (count 3 two-fives :key #'data))))
  ;; Should replace (5 6 7 8) with :TOUCHED.
  (is (nest
       (= 6)
       (length)
       (flatten)
       (convert 'list)
       (with (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9))) '(3)
             (make-instance 'node-with-data :data :touched))))
  ;; Should replace 6 with :TOUCHED.
  (is (nest (= 9)
            (length)
            (flatten)
            (convert 'list)
            (with (convert 'node-with-data
                           '(1 2 3 4 (5 6 7 8) (9)))
                  '(3 0) (make-instance 'node-with-data :data :touched))))
  (let* ((r (convert 'node-with-data '(:a 1 2 (:b 3 4) 5)))
         (n (@ r '(2))))
    (is (equal (nest (flatten)
                     (convert 'list)
                     (with r n)
                     (make-instance 'node-with-data :data :removed))
               '(:a 1 2 :removed 5))))
  ;; Should replace '(:data 2) with :TOUCHED.
  (let ((tree (convert 'node-with-fields '(:data :foo :a (:data 1)
                                            :b (:data 2)))))
    (is (equal (nest (flatten)
                     (convert 'list)
                     (with tree '(1))
                     (make-instance 'node-with-fields :data :touched))
               '(:data :foo :a :data 1 :b :data :touched)))))

(deftest lookup-node-index-test ()
  (let ((r (convert 'node-with-fields '(:data :foo :a (:data 1)
                                        :b (:data 2)))))
    (is (equalp (@ r :a) (@ r (@ r :a))))))

(deftest less-test ()
  (let ((no-threes (less (convert 'node-with-data (iota 10)) '(2))))
    (is (zerop (count 3 no-threes)))
    (is (= 9 (length (convert 'list no-threes)))))
  (let* ((r (convert 'node-with-data '(:a 1 (:b 2) (:c 3) 4)))
         (n (@ r 2)))
    (is (equal (flatten (convert 'list (less r n)))
               '(:a 1 :b 2 4))))
  (let* ((r (convert 'node-with-fields '(:data :foo :a (:data 1)
                                         :b (:data 2)))))

    (is (equal (flatten (convert 'list (less r (@ r 1))))
               '(:data :foo :a :data 1)))
    (is (equal (flatten (convert 'list (less r (@ r :b))))
               '(:data :foo :a :data 1)))))

(deftest less.named-children ()
  (let* ((l1 '((a b) (c d) e))
         (n1 (convert 'node-cons2 l1))
         (n2 (car (tail n1))))
    (is (equal (convert 'list (less n1 n2))
               '((a b) e)))
    (let* ((l1 '((a b) (y (c d)) e))
           (n1 (convert 'node-cons2 l1))
           (n2 (first (tail (first (tail n1))))))
      (is (equal (convert 'list (less n1 n2))
                 '((a b) (y) e))))))

(deftest insert-named-children ()
  (let* ((l1 '((a b) (c d)))
         (n1 (convert 'node-list2 l1))
         (l2 '(f g))
         (n2 (convert 'node-list2 l2))
         (n3 (insert n1 '((body . 1)) n2)))
    (is (equal (convert 'list n3) '((a b) (f g) (c d))))))

(deftest @-test ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9)))))
    (let ((it (copy tree)))
      (setf (@ it '(3 0)) :deleted)
      (is (zerop (count 6 it))))))

(deftest more-less-tests ()
  (let ((it (convert 'node-with-data '(defun euclids-gcd (a b)
                         (if (= a 0)
                             b)
                         (do ()
                             ((= b 0) a)
                           (if (> a b)
                               (setf a (- a b))
                               (setf b (- b a))))))))
    (is (= 1 (nest (count 'defun)
                   (flatten)
                   (convert 'list)
                   (less it)
                   (position '= it :key #'data))))))

(deftest splice-test ()
  (flet ((to-node (it)
           (make-instance 'node-with-data :data it)))
    (let ((it (convert 'node-with-data '(0 1 2 3 4))))
      (is (equalp (convert 'list (splice it '(1)
                                         (mapcar #'to-node '(:a :b :c))))
                  '(0 1 :a :b :c 2 3 4))))
    (let ((it (convert 'node-with-data '(0 1 2 3 4)))
          (n (mapcar #'to-node '(:a 5))))
      (is (equal (convert 'list (splice it '(1) n))
                 `(0 1 :a 5 2 3 4))))
    (let ((it (convert 'node-with-data '(:a (:b 1) (:c (:d 2) (:e 3) 4) 5))))
      (is (equal (convert 'list (splice it '(1 0) (mapcar #'to-node '(:new))))
                 '(:a (:b 1) (:c :new (:d 2) (:e 3)  4) 5)))
      (is (equal (convert 'list (splice it (@ it '(1 1))
                                        (mapcar #'to-node '(:new))))
                 '(:a (:b 1) (:c (:d 2) :new (:e 3) 4) 5))))
    (let ((it (convert 'node-with-fields '(:data :x :a (1) :b (2)))))
      (is (handler-case (progn (splice it '(:a) (to-node :what)) nil)
            (error () t))))))

(deftest insert-test ()
  (flet ((to-node (it)
           (make-instance 'node-with-data :data it)))
    (let ((it (convert 'node-with-data '(0 1 2 3 4))))
      (is (equalp (convert 'list (insert it '(1) (to-node :a)))
                  '(0 1 :a 2 3 4))))
    (let* ((it (convert 'node-with-data '(:a (:b 1) (:c 2 3 (:d 4) 5) 6)))
           (n (@ it '(1 2))))
      (is (equal (convert 'list (insert it '(1 2) (to-node :new)))
                 '(:a (:b 1) (:c 2 3 :new (:d 4) 5) 6)))
      (is (equal (convert 'list (insert it n (to-node :new)))
                 '(:a (:b 1) (:c 2 3 :new (:d 4) 5) 6))))
    (nest
     (let* ((it (convert 'node-with-fields '(:data :foo :a (:data 1))))))
     (is (equal (nest (convert 'list)
                      (insert it '(1))
                      (make-instance 'node-with-fields :data 3))
                '(:data :foo :a (:data 1) :b (:data 3))))
     (is (equal (nest (convert 'list)
                      (insert it '(:b))
                      (make-instance 'node-with-fields :data 3))
                '(:data :foo :a (:data 1) :b (:data 3)))))))

(deftest conversion-to-node-with-data ()
  (is (= 10 (nest (count :data)
                  (flatten)
                  (convert 'alist)
                  (convert 'node-with-data)
                  '(1 2 3 4 (5 6 7 8) (9 10))))))

(deftest mapcar-works ()
  (is (equalp (nest (convert 'list)
                    (mapcar
                     (lambda (it)
                       (if (eql (head it) :c)
                           (convert 'node-cons '(:foo))
                           it)))
                    (convert 'node-cons)
                    '(:a (:b) (:b (:c) (:d) (:e)) (:d)))
              '(:a (:b) (:b (:foo) (:d) (:e)) (:d)))))

(deftest mapcar-keeps-on-nil ()
  (is (equalp (nest (convert 'list)
                    (mapcar
                     (lambda (it)
                       (when (eql (head it) :c)
                         (convert 'node-cons '(:foo)))))
                    (convert 'node-cons)
                    '(:a (:b) (:b (:c) (:d) (:e)) (:d)))
              '(:a (:b) (:b (:foo) (:d) (:e)) (:d)))))

(deftest bad-tree ()
  ;; Test where a tree has a node twice
  (flet ((%f (f x y)
           (is
            (handler-case
                (progn (funcall f x y) nil)
              (error (e) (declare (ignorable e))
                     ;; (format t "Expected error: ~a~%" e)
                     t))
            "PATH-TRANSFORM-OF on tree with duplicate SN did not signal an error: ~a, ~a"
            x y)))
    (let* ((sn 261237163)
           (n1 (convert 'node-list '(:a 1)))
           (n1a (copy n1 :serial-number sn))
           (n2 (convert 'node-list '(:b 2)))
           (n2a (copy n2 :serial-number sn))
           (good (convert 'node-list`(:c ,n1 ,n2)))
           (bad (convert 'node-list`(:c ,n1a ,n2a))))
      (%f #'path-transform-of good bad)
      (%f #'path-transform-of bad good))))

(deftest prefix?.1 ()
  (is (prefix? nil nil))
  (is (prefix? nil '(a)))
  (is (prefix? '(a) '(a)))
  (is (prefix? '(a) '(a b)))
  (is (not (prefix? '(a) nil)))
  (is (not (prefix? '(a) '(b))))
  (is (not (prefix? '(a a) '(a b))))
  (is (not (prefix? '(a a) '(a)))))

(deftest node-heap-data-test ()
  (let ((all (iter (for sz from 1 to 2)
                   (appending
                    (iter (for sn from 1 to 2)
                          (collecting
                           (make-node-heap-data :size sz :sn sn)))))))
    (declare (notinline node-heap-data-<)) ;; so coverage hits the def
    (iter (for e on all)
          (let ((n1 (car e)))
            (is (not (node-heap-data-< n1 n1)))
            (iter (for n2 in (cdr e))
                  (is (node-heap-data-< n1 n2))
                  (is (not (node-heap-data-< n2 n1))))))))

;;; SBCL nonstandard sequence extension
#+sbcl
(progn
  (defclass my-sequence (standard-object sequence)
    ((actual :type list :initarg :actual :initform nil
	     :accessor my-sequence-actual))
    (:documentation "An example of an SBCL user-defined sequence class"))
  (defmethod sb-sequence:length ((obj my-sequence))
    (cl:length (my-sequence-actual obj)))
  (defmethod sb-sequence:elt ((obj my-sequence) index)
    (elt (my-sequence-actual obj) index))
  (defmethod (setf sb-sequence:elt) (val (obj my-sequence) index)
    (setf (elt (my-sequence-actual obj) index) val))
  (defmethod sb-sequence:adjust-sequence ((obj my-sequence) len &rest args)
    (setf (my-sequence-actual obj)
	  (apply #'sb-sequence:adjust-sequence (my-sequence-actual obj) len args))
    obj)
  (defmethod sb-sequence:make-sequence-like ((obj my-sequence) len &rest args)
    (let ((new-contents
	   (apply #'sb-sequence:make-sequence-like (my-sequence-actual obj) len args)))
      (make-instance 'my-sequence :actual new-contents)))
  )

#+sbcl
(deftest copy-custom-sequence-test ()
  (let ((s (make-instance 'my-sequence :actual (list 'a 'b 'c))))
    (is (equal (my-sequence-actual (copy s)) '(a b c)))))

(deftest dump-test ()
  (is (equal (with-output-to-string (*standard-output*)
               (eval '(let ((x 1)) (dump x))))
             (concatenate 'string "X = 1" (string #\Newline)))))

(deftest encapsulate-test ()
  (let ((t3
         (eval
          '(let ((tree (convert 'node-with-data '(:a 1 2)))
                 (t2 nil))
            (with-encapsulation (setf t2 (with-encapsulation tree tree)) t2))))
        (t4
         (eval
          '(let ((tree (convert 'node-with-data '(:a 1 2))))
            (with-encapsulation tree tree)))))
    (is (transform t3))
    (is (transform t4))
    (is (not (equal (transform t3) t3)))
    (is (not (equal (transform t4) t4))))
  (is (transform
       (eval '(let ((t1 (convert 'node-with-data '(:a 1 2))))
               (with-encapsulation t1 (copy t1 :root-info (make-instance 'root-info :transform t1))))))))

(deftest assert-test ()
  (is (null (eval '(ft::assert t)))))

(deftest mapcar-right-children-test ()
  (is (equal '(1 2 3)
             (children
              (mapcar (lambda (node)
                          (if (typep node 'node-with-data)
                             (make-instance 'node-with-data
                                 :children (reverse (children node)))
                             node))
                      (make-instance 'node-with-data
                                     :children '(3 2 1)))))))

(deftest serialization-test ()
  (with-temporary-file (:pathname store-file)
    (let ((tree (make-random-tree 5)))
      (store tree store-file)
      (is (equal? tree (restore store-file))))))

;;; Named children test.
(defclass js-block-statement (node)
  ((acorn-slot-name :initform :block-statement :allocation :class)
   (child-slots :initform '((js-body . 0)) :allocation :class)
   (child-slot-specifiers :allocation :class)
   (js-body :reader js-body :initform nil :initarg :js-body :initarg js-body :type list))
  (:documentation "javascript ast node class for block-statement acorn asts."))

(deftest test-index-into-named-child ()
  (let ((it (make-instance 'js-block-statement
                           :js-body (list 1 2 3))))
    (is (equal? (@ it '(js-body)) '(1 2 3)))
    (is (equal? (@ it '((js-body . 0))) 1))
    (is (equal? (js-body (less it '((js-body . 0))))
                '(2 3)))))

(deftest index-into-child-test ()
  (let ((it (make-instance 'js-block-statement
                           :js-body (list 1 2 3))))
    (is (equal? (children (less it 0)) '(2 3)))))

(deftest path-later-p.basics ()
  (let ((n (convert 'node-list '((:a :b :c) (:d :e :f) (:g :h :i)))))
    (is (not (path-later-p n nil nil)))
    (is (not (path-later-p n nil '(1))))
    (is (path-later-p n '(1) nil))
    (is (path-later-p n '(1 2) '(1)))
    (is (not (path-later-p n '(1) '(1 2))))
    (is (path-later-p n '(2) '(1)))
    (is (not (path-later-p n '(1) '(2))))
    (is (not (path-later-p n '(1) '(1))))))

(deftest path-later-p.named-children ()
  (let ((n (convert 'node-with-arity2/2 '((x y)(u v)))))
    (is (path-later-p n '((a . 1)) '((a . 0))))
    (is (not (path-later-p n '((a . 1)) '((a . 1)))))
    (is (not (path-later-p n '((a . 0)) '((a . 1)))))
    (is (path-later-p n '((b . 0)) '((a . 1))))
    (is (not (path-later-p n '(a) '(a))))))

(deftest path-of-node.named-children ()
  (let* ((n1 (convert 'node-with-arity2/2 '((a b)(c d))))
         (n2 (convert 'node-with-arity2/2 '((e f)(g h))))
         (n3 (convert 'node-with-arity2/2 '((i j)(k l))))
         (n4 (convert 'node-with-arity2/2 '((m n)(o p))))
         (n (convert 'node-with-arity2/2 `((,n1 ,n2)(,n3 ,n4)))))
    (is (equal (path-of-node n n) nil))
    (is (equal (path-of-node n (first (children n))) '((a . 0))))
    (is (equal (path-of-node n (second (children n))) '((a . 1))))
    (is (equal (path-of-node n (third (children n))) '((b . 0))))
    (is (equal (path-of-node n (fourth (children n))) '((b . 1))))
    (is (equal (children n) (list n1 n2 n3 n4)))))

(deftest define-node-class.bad-initarg-detected ()
  (progn
    (setf (find-class 'bad-node-class) nil)
    (is (handler-case
            (progn (eval '(define-node-class bad-node-class (node)
                           ;; Node C does not have :C  as an initarg
                           ((c :initarg :z :initform nil)
                            (child-slots :allocation :class
                                         :initform '(c)))))
                   nil)
          (error () t)))))

(deftest children-alist.cons-and-list-nodes ()
  (is (equal (children-alist (convert 'node-cons '(a . b)))
             '((head a) (tail b))))
  (is (equal (children-alist (convert 'node-cons2 '(a b)))
             '((head a) (tail b))))
  (is (equal (children-alist (convert 'node-list '(a b c)))
               '((child-list a b c))))
  (is (equal (children-alist (convert 'node-list2 '(a b c)))
             '((body a b c)))))

(deftest children-alist.nodes ()
  (is (equal (mapcar #'(lambda (p)
                         (list* (car p) (convert 'list (cadr p)) (cddr p)))
                     (children-alist
                      (convert 'node-with-fields
                               '(:data 17 :a (:data 1) :b (:data 2)))))
             '((a (:data 1)) (b (:data 2)))))
  (is (equal (children-alist (convert 'node-with-arity2
                                      '(17 32)))
             '((a 17 32))))
  (is (equal (children-alist (convert 'node-with-arity2/2
                                      '((4 7) (6 19))))
             '((a 4 7) (b 6 19)))))

(deftest copy-with-children-alist.cons-and-list-nodes ()
  (let ((n (convert 'node-cons '(a . b))))
    (is (equal (convert 'list
                        (copy-with-children-alist
                         n
                         '((head z))
                         :head :ignore))
               '((z) . b)))
    (is (equal (convert 'list
                        (copy-with-children-alist
                         (convert 'node-cons '(a . b))
                         `((,(ft::slot-specifier-for-slot n 'head) z))
                         :head :ignore))
               '(z . b))))
  (is (equal (convert 'list
                      (copy-with-children-alist
                       (convert 'node-cons2 '(a b))
                       '((tail z))
                       :head 'c))
             '(c z))))

(defclass triggers-unbound-slot-error (node)
  ((slot1 :initarg :slot1)
   (slot2 :initarg :slot2)))

(defmethod slot-unbound ((class t)
                         (obj triggers-unbound-slot-error)
                         (slot-name (eql 'slot2)))
  (error "Should not be called"))

(deftest copy-ignores-unbound-slots ()
  (let* ((node (make-instance 'triggers-unbound-slot-error :slot1 'x)))
    (is (slot-boundp node 'slot1))
    (is (not (slot-boundp node 'slot2)))
    (signals error
      (slot-value node 'slot2))
    (let ((copy (finishes (copy node))))
      (is (slot-boundp copy 'slot1))
      (is (not (slot-boundp copy 'slot2))))
    (let ((copy (finishes (tree-copy node))))
      (is (slot-boundp copy 'slot1))
      (is (not (slot-boundp copy 'slot2))))))

(deftest parent-nil-on-self ()
  (let ((root-and-node (convert 'node-list '(a b c))))
    (populate-fingers root-and-node)
    (is (null (parent root-and-node root-and-node)))))

(deftest parent-nil-on-unrelated-root ()
  (let ((node (convert 'node-list '(a b c)))
        (root (convert 'node-list '(d e f))))
    (populate-fingers root)
    (populate-fingers node)
    (is (null (parent root node)))))

(deftest parent-works-on-actual-child ()
  (let ((root (convert 'node-list '(a b (c d)))))
    (populate-fingers root)
    (is (not (null (parent root (@ root '(2))))))))

(deftest predecessor-works-on-actual-child ()
  (let ((root (convert 'node-list '(a b (c d) e))))
    (populate-fingers root)
    (is (not (null (predecessor root (@ root '(2))))))))

(deftest successor-works-on-actual-child ()
  (let ((root (convert 'node-list '(a b (c d) e))))
    (populate-fingers root)
    (is (not (null (successor root (@ root '(2))))))))

;;;; Tests of interval trees

(defsuite interval-trees "Interval trees tests")

(defun random-permute (seq)
  (let ((len (length seq)))
    (setf seq (copy-seq seq))
    (iter (for i from len downto 1)
          (let ((r (random len)))
            (rotatef (elt seq r) (elt seq (1- i)))))
    seq))

(deftest it.1 ()
  (macrolet ((%check (lst)
               (assert (typep lst 'list))
               (assert (every #'integerp lst))
               (let ((len (length lst)))
                 `(let ((itree (convert 'ft/it:itree ',lst)))
                    (is (eql (ft/it:itree-size itree) ,len))
                    (is (equal (mapcar #'car (convert 'list itree)) ',(sort (copy-seq lst) #'<)))
                    (is (eql (ft/it:itree-find-node ,(1- (reduce #'min lst :initial-value 0)) itree) nil))
                    (is (eql (ft/it:itree-find-node ,(1+ (reduce #'max lst :initial-value 0)) itree) nil))
                    ,@(iter (for i in lst)
                            (collect
                                `(let ((node (ft/it:itree-find-node ,i itree)))
                                   (is (typep node 'ft/it:node))
                                   (is (eql (ft/it:node-data node) t)))))))))
    (%check nil)
    (%check (1))
    (%check (1 2))
    (%check (3 2 1))))

(deftest it.delete ()
  (macrolet ((%check (inserts deletes)
               (assert (equal (sort (copy-seq inserts) #'<)
                              (sort (copy-seq deletes) #'<)))
               (let ((len (length inserts))
                     (initial (sort (copy-seq inserts) #'<)))
                 `(let ((itree (convert 'ft/it:itree ',inserts)))
                    (is (equal (mapcar #'car (convert 'list itree))
                               ',initial))
                    ,@(iter (for i in deletes)
                            (setq initial (remove i initial))
                            (collect
                                `(multiple-value-bind (node path)
                                     (ft/it:itree-find-node-path ,i itree)
                                   (is (typep node 'ft/it:node))
                                   (setq itree (ft/it:itree-delete-node itree node path))
                                   (is (equal (mapcar #'car (convert 'list itree))
                                              ',initial)))))))))
    (%check (1) (1))
    (%check (1 2) (1 2))
    (%check (1 2) (2 1))
    (%check (1 2 3) (3 2 1))
    (%check (1 3 2 0) (1 3 0 2))
    (%check (0 3 2 1) (1 2 0 3))
    ))

(deftest it.2 ()
  (let* ((vals (iota 20))
         (result
           (iter (repeat 100)
                 (let* ((seq (random-permute vals))
                        (itree (convert 'ft/it:itree seq))
                        (lst (mapcar #'car (convert 'list itree))))
                   (unless (equal vals lst)
                     (return (list seq lst)))))))
    (is (eql result nil))))

(deftest it.3 ()
  (let* ((vals (iota 20))
         (result
           (iter (repeat 1000)
                 (let* ((seq1 (random-permute vals))
                        (seq2 (random-permute vals))
                        (vals-left (copy-seq vals))
                        (itree (convert 'ft/it:itree seq1)))
                   (iter (for i in seq2)
                         (multiple-value-bind (node path)
                             (ft/it:itree-find-node-path i itree)
                           (assert node)
                           (setq itree (ft/it:itree-delete-node itree node path))
                           (setq vals-left (remove i vals-left))
                           (assert (equal (mapcar #'car (convert 'list itree)) vals-left))))))))
    (is (eql result niL))))
  
                        
