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
  (:shadowing-import-from
   :functional-trees
   :dump
   :equal?
   :lexicographic-<
   :mapc
   :mapcar
   :node
   :node-can-implant
   :node-valid
   :nodes-disjoint
   :path-of-node
   :path-p
   :prefix?
   :serial-number
   :subst
   :subst-if
   :subst-if-not
   :with-encapsulation)

  (:shadowing-import-from
   :functional-trees/attrs
   :def-attr-fun
   :*attrs*
   :with-attr-table
   :attr-missing
   :attrs-root
   :subroot
   :subroot?)
   
  (:shadowing-import-from
   :fset
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
(defclass parent (node)
  ((children :reader children
             :type list
             :initarg :children
             :initarg children
             :initform nil
             :documentation "The list of children of the node,
which may be more nodes, or other values.")
   (child-slots :initform '(children) :allocation :class)
   (child-slot-specifiers :allocation :class)))

(defclass node-with-data (parent)
  ((data :reader data :initarg :data :initform nil
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
    (make-node sequence)))

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
    (make-node sequence)))

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
(defsuite ft-test "Functional trees top-level test suite.")

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
  (is (equal (convert 'list (convert 'node-cons '(:a))) '(:a)))
  (is (eql 4 (serial-number (make-instance 'node :serial-number 4)))))

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

(deftest mapc.1 ()
  (let ((result nil))
    (mapc #'(lambda (x) (push (convert 'list x) result)) (convert 'node-list2 '(a (b c) d)))
    (is (equal result '((b c) (a (b c) d))))))

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
    (is (handler-case (progn (path-of-node n2 n1 :error t) nil)
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
      (is (not (equal? n (copy n :head (head it) :tail (tail it)))))))
  (is (not (equal? (convert 'node-list2 '(a b))
                   (convert 'node-list2 '(a b c)))))
  (let* ((n1 (convert 'node-list2 '(a b)))
         (n2 (copy n1 :body nil)))
    (is (not (equal? n1 n2)))))

(deftest print.1 ()
  (let ((*print-readably* nil)
        (n1 (convert 'node-cons '(:a)))
        (t1 (convert 'node-cons '(:a))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (convert 'node-cons '(:a)) s))))))

(deftest print.2 ()
  (let ((*print-readably* t)
        (n1 (convert 'node-cons '(:a)))
        (t1 (convert 'node-cons '(:a))))
    (declare (ignorable t1))
    (flet ((%e (v)
             (handler-case (progn (prin1 v) nil)
               (error () t))))
      (is (%e (convert 'node-cons '(:a))))
      )))

;; TODO -- reimplement this to not involve fingers
(defun random-test-check (n1 n2)
  (when (and n1 n2)
    (let ((serial-numbers nil))
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
            (list n1 n2 e))))))
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
         (p3 '(:tail :tail :tail :tail :head :tail :head))
         (n3 (@ n1 p3))
         (n4 (swap n1 n2 n3)))
    (is (equal (convert 'list n1) l1))
    (is (equal (convert 'list n2) '(:d 26)))
    (is (equal (convert 'list n3) '(:b 54 84)))
    (is (equal (convert 'list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    ;; Swap moves the nodes as expected.
    (is (eql (serial-number (@ n1 p2)) (serial-number (@ n4 p3))))
    (is (eql (@ n1 p2) (@ n4 p3)))
    (is (eql n2 (@ n4 p3)))
    (is (eql n3 (@ n4 p2)))
    ))

;; Same as swap.1, but with 0/1 in place of :head/:tail
(deftest swap.2 ()
  ;; Swap (:d 26) and (:b 54 84)
  (let* ((l1 '(:i 17 17 (:d 26) (:m (:b 54 84))))
         (n1 (convert 'node-cons l1))
         (p2 '(tail tail tail head))
         ;; (p2 '((tail . 0) (tail . 0) (tail . 0) (head . 0)))
         (n2 (@ n1 p2))
         ;; (p3 '(:tail :tail :tail :tail :head :tail :head))
         ;; (p3 '(1 1 1 1 0 1 0))
         (p3 '(tail tail tail tail head tail head))
         ; (p3 '((tail . 0) (tail . 0) (tail . 0) (tail . 0) (head . 0) (tail . 0) (head . 0)))
         (n3 (@ n1 p3))
         (n4 (swap n1 n2 n3)))
    (is (equal (convert 'list n1) l1))
    (is (equal (convert 'list n2) '(:d 26)))
    (is (equal (convert 'list n3) '(:b 54 84)))
    (is (equal (convert 'list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    ;; Swap moves the nodes as expected.
    (is (eql (serial-number (@ n1 p2)) (serial-number (@ n4 p3))))
    (is (eql (@ n1 p2) (@ n4 p3)))
    (is (eql n2 (@ n4 p3)))
    (is (eql n3 (@ n4 p2)))
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
#|
(deftest random.1 ()
  ;; Randomized test of path transforms
  (is (equal (random-test 20 200 (lambda (n) (remove-nodes-randomly n 0.2))) nil)))
|#

(deftest random.2 (&optional (size 50))
  (let ((result :pass))
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

#+nil
(deftest random.3a ()
  (is (equal (random-test 5 1000 #'swap-random-nodes)
             nil)))

#+nil
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
  (is (emptyp (convert 'list (remove-if #'evenp (convert 'node-with-data
                                                         (iota 100))
                                        :key #'data))))
  (is (length= 50 (convert 'list (remove-if #'oddp (convert 'node-with-data
                                                            (iota 100))
                                            :key #'data)))))

(deftest remove-tree-if-not ()
  (is (length= 50 (convert 'list
                           (remove-if-not #'evenp
                                          (convert 'node-with-data
                                                   (iota 100))
                                          :key #'data))))
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
    (is (= 2 (count 40 no-twenty :key #'data))))
  ;; This test is no good, since the subtree is being inserted more than once
  #+nil
  (let ((it (convert 'node-with-data (iota 6))))
    (is (equal (convert 'list (substitute
                               (make-instance 'node-with-data :data :x) nil it
                               :key [{typep _ '(not (integer 2 4))} #'data]))
               '(0 1 :x :x :x 5)))))

(deftest substitute-if-test ()
  (let ((no-odd (substitute-if (make-instance 'node-with-data :data :odd)
                               #'oddp (convert 'node-with-data (iota 100))
                               :copy 'tree-copy
                               :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data))))
  (let ((it (convert 'node-with-data '(0 2 3 3 4)))
        (n (convert 'node-with-data '(:z 18))))
    (is (eql (handler-case (substitute-if n #'oddp it :key #'data)
               (error () :error))
             :error))
    (let ((c1 (substitute-if n #'oddp it :copy 'tree-copy :key #'data)))
      (is (equal (convert 'list c1) '(0 2 (:z 18) (:z 18) 4)))
      (is (not (eql (@ c1 '(1)) (@ c1 '(2))))))))

(deftest substitute-if-not-test ()
  (let ((no-odd
         (substitute-if-not (make-instance 'node-with-data :data :odd)
                            #'evenp
                            (convert 'node-with-data (iota 100))
                            :copy 'tree-copy
                            :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data))))
  (let ((it (convert 'node-with-data (iota 6))))
    (is (equal (convert 'list (substitute-if-not
                               (make-instance 'node-with-data :data :x)
                               #'null it
                               :copy 'tree-copy
                               :key [{typep _ '(integer 2 4)} #'data]))
               '(0 1 :x :x :x 5))))
  (let ((it (convert 'node-with-data '(0 2 3 3 4)))
        (n (convert 'node-with-data '(:z 18))))
    (is (eql (handler-case
                 (substitute-if-not n «or (complement #'numberp) #'evenp» it
                                    :key #'data)
               (error () :error))
             :error))
    (let ((c1 (substitute-if-not n #'evenp it :copy 'tree-copy
                                              :key #'data)))
      (is (not (eql (@ c1 '(1)) (@ c1 '(2))))))))

(deftest subst-test ()
  (let ((no-twenty (subst (make-instance 'node-with-data :data 40)
                          20 (convert 'node-with-data (iota 100))
                          :copy 'tree-copy
                          :key #'data)))
    (is (= 0 (count 20 no-twenty :key #'data)))
    (is (= 2 (count 40 no-twenty :key #'data))))
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
                   :copy 'tree-copy
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
                          :copy 'tree-copy
                          :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data))))
  (is (= (subst-if 10 (lambda (x) (= x 20)) 20) 10)) ; when tree is an atom
  (let ((it (subst-if (make-instance 'node-with-data :data :odd)
                      «and #'numberp #'oddp»
                      (convert 'node-with-data '(:a 1 2 3))
                      :copy 'tree-copy
                      :key #'data)))
    (is (equal (convert 'list it) '(:a :odd 2 :odd))))
  (is (equal (subst-if :x #'zerop '(1 2) :key #'size)
             '(:x :x . :x))))

(deftest subst-if-not-test ()
  (let ((no-odd
         (subst-if-not (make-instance 'node-with-data :data :odd)
                       #'evenp (convert 'node-with-data (iota 100))
                       :copy 'tree-copy
                       :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd :key #'data)))
    (is (= 50 (count :odd no-odd :key #'data))))
  (is (= (subst-if-not 10 (lambda (x) (= x 20)) 20) 20)) ; when tree is an atom
  (let ((it (subst-if-not (make-instance 'node-with-data :data :odd)
                          (complement «and #'numberp #'oddp»)
                          (convert 'node-with-data '(:a 1 2 3))
                          :copy 'tree-copy
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
       (length= 6)
       (flatten)
       (convert 'list)
       (with (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9))) '(3)
             (make-instance 'node-with-data :data :touched))))
  ;; Should replace 6 with :TOUCHED.
  (is (nest (length= 9)
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
    (is (length= 9 (convert 'list no-threes))))
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

(deftest error-tests ()
  (let* ((it (convert 'node-with-data '(:a (:b 1) (:c 2 3 (:d 4) 5) 6)))
         (n (convert 'node-with-data '(:f 17))))
    (is (handler-case (progn (with it (convert 'node-with-data '(:e 10)) n)
                             nil)
          (error () t)))
    (is (handler-case (progn (less it (convert 'node-with-data '(:e 10)))
                             nil)
          (error () t)))
    (is (handler-case (progn (splice it (convert 'node-with-data '(:e 10))
                                     (list n))
                             nil)
          (error () t)))
    (is (handler-case (progn (insert it (convert 'node-with-data '(:e 10)) n)
                             nil)
          (error () t)))))   

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

(deftest prefix?.1 ()
  (is (prefix? nil nil))
  (is (prefix? nil '(a)))
  (is (prefix? '(a) '(a)))
  (is (prefix? '(a) '(a b)))
  (is (not (prefix? '(a) nil)))
  (is (not (prefix? '(a) '(b))))
  (is (not (prefix? '(a a) '(a b))))
  (is (not (prefix? '(a a) '(a)))))

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
    (is (null (parent root-and-node root-and-node)))))

(deftest parent-nil-on-unrelated-root ()
  (let ((node (convert 'node-list '(a b c)))
        (root (convert 'node-list '(d e f))))
    (is (null (parent root node)))))

(deftest parent-works-on-actual-child ()
  (let ((root (convert 'node-list '(a b (c d)))))
    (is (not (null (parent root (@ root '(2))))))))

(deftest predecessor-works-on-actual-child ()
  (let ((root (convert 'node-list '(a b (c d) e))))
    (is (not (null (predecessor root (@ root '(2))))))))

(deftest successor-works-on-actual-child ()
  (let ((root (convert 'node-list '(a b (c d) e))))
    (is (not (null (successor root (@ root '(2))))))))

;;;; Tests of interval trees

(defsuite interval-trees "Interval trees tests")

(defun mapcar-car (x) (mapcar #'car x))

(eval-when (:load-toplevel :compile-toplevel)
  (defun seq-to-intervals (seq)
    (setf seq (sort (copy-seq seq) #'<))
    (iter (for i in (ft/it::merge-intervals (mapcar (lambda (i) (list (cons i i) t)) seq)))
          (destructuring-bind ((lo . hi) val) i
            (collect (if (eql lo hi) lo (car i)))))))

(deftest it.1 ()
  (macrolet ((%check (lst)
               (assert (typep lst 'list))
               (assert (every #'integerp lst))
               (let* ((intervals (ft/it::merge-intervals (mapcar (lambda (i) (list (cons i i) t)) lst)))
                      (len (length intervals)))
                 `(let ((itree (convert 'ft/it:itree ',lst)))
                    (is (eql (ft/it:itree-size itree) ,len))
                    (is (equal (mapcar-car (convert 'list itree)) ',(seq-to-intervals lst)))
                    (is (eql (ft/it:itree-find-node itree ,(1- (reduce #'min lst :initial-value 0))) nil))
                    (is (eql (ft/it:itree-find-node itree ,(1+ (reduce #'max lst :initial-value 0))) nil))
                    ,@(iter (for i in lst)
                            (collect
                                `(let ((node (ft/it:itree-find-node itree ,i)))
                                   (is (typep node 'ft/it:node))
                                   (is (eql (ft/it:node-data node) t)))))))))
    (%check nil)
    (%check (1))
    (%check (1 2))
    (%check (3 2 1))))

(deftest it.delete-node ()
  (macrolet ((%check (inserts deletes)
               (assert (equal (sort (copy-seq inserts) #'<)
                              (sort (copy-seq deletes) #'<)))
               (let ((len (length inserts))
                     (initial (sort (copy-seq inserts) #'<)))
                 `(let ((itree (convert 'ft/it:itree ',inserts)))
                    (is (equal (mapcar-car (convert 'list itree))
                               ',initial))
                    ,@(iter (for i in deletes)
                            (setq initial (remove i initial))
                            (collect
                                `(multiple-value-bind (node path)
                                     (ft/it:itree-find-node-path itree ,i)
                                   (is (typep node 'ft/it:node))
                                   (setq itree (ft/it:itree-delete-node itree node path))
                                   (is (equal (mapcar-car (convert 'list itree))
                                              ',initial)))))))))
    (%check (1) (1))
    (%check (1 3) (1 3))
    (%check (1 3) (3 1))
    (%check (1 3 5) (5 3 1))
    (%check (3 7 5 1) (3 7 1 5))
    (%check (1 7 5 3) (3 5 1 7))))

(deftest it.delete ()
  (let ((itree (convert 'ft/it:itree '(((1 . 3) :a) ((5 . 5) :b) ((6 . 10) :c)))))
    (is (equal (convert 'list (ft/it:itree-delete itree 0))
               '(((1 . 3) :a) (5 :b) ((6 . 10) :c))))
    (is (equal
         (handler-case (ft/it:itree-delete itree 0 :error t)
           (error () :good))
         :good))
    (is (equal (convert 'list (ft/it:itree-delete itree 1))
               '((5 :b) ((6 . 10) :c))))
    (is (equal (convert 'list (ft/it:itree-delete itree 2))
               '((5 :b) ((6 . 10) :c))))
    (is (equal (convert 'list (ft/it:itree-delete itree 3))
               '((5 :b) ((6 . 10) :c))))
    ))

(deftest it.insert* ()
  (let ((itree (convert 'ft/it:itree nil)))
    (setf itree (ft/it::itree-insert* itree 0 0 :a))
    (is (equal (convert 'list itree) '((0 :a))))
    (setf itree (ft/it::itree-insert* itree 10 11 :b))
    (is (equal (convert 'list itree) '((0 :a) ((10 . 11) :b))))
    (setf itree (ft/it::itree-insert* itree 5 5 :c))
    (is (equal (convert 'list itree) '((0 :a) (5 :c) ((10 . 11) :b))))))

(deftest it.2 ()
  (let* ((vals (iota 20))
         (result
           (iter (repeat 100)
                 (let* ((seq (random-permute vals))
                        (itree (convert 'ft/it:itree seq))
                        (lst (mapcar-car (convert 'list itree))))
                   (unless (equal '((0 . 19)) lst)
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
                         (setq itree (ft/it:itree-remove-interval itree i i))
                         (setq vals-left (remove i vals-left))
                         (assert (equal (mapcar-car (convert 'list itree)) (seq-to-intervals vals-left))))))))
    (is (eql result niL))))

(deftest it.4 ()
  (let ((itree (convert 'ft/it:itree '(((1 . 2) :a) ((3 . 4) :b) (5 :c)))))
    (is (equal (ft/it:itree-size itree) 3))
    (is (null (ft/it:itree-find itree 0)))
    (is (equal (multiple-value-list (ft/it:itree-find itree 1)) '(1 2 :a)))
    (is (equal (multiple-value-list (ft/it:itree-find itree 2)) '(1 2 :a)))
    (is (equal (multiple-value-list (ft/it:itree-find itree 3)) '(3 4 :b)))
    (is (equal (multiple-value-list (ft/it:itree-find itree 4)) '(3 4 :b)))
    (is (equal (multiple-value-list (ft/it:itree-find itree 5)) '(5 5 :c)))
    (is (null (ft/it:itree-find itree 6)))))

(defun intervals-of-list (vals)
  (let ((vals (sort (copy-seq vals) #'<)))
    (iter (while vals)
          (let* ((start (pop vals))
                 (end start))
            (iter (while (and vals (eql (car vals) (1+ end))))
                  (setf end (pop vals)))
            (collecting (cons start end))))))

(defun random-integers (size p)
  (declare (type (integer 1) size)
           (type (real 0 1) p))
  (iter (for i from 0 below size)
        (when (< (random 1.0) p)
          (collecting i))))
        
(deftest it.intervals-of-itree (&key (reps 1000) (size 20) (p 0.5))
  (let ((result
          (iter (repeat reps)
                (let* ((vals (random-integers size p))
                       (sorted-intervals (intervals-of-list vals))
                       (intervals (random-permute sorted-intervals))
                       (itree (convert 'ft/it:itree nil)))
                  (setf itree (ft/it:itree-add-intervals
                               itree
                               (mapcar (lambda (x) (list x t)) intervals)))
                  (let ((ints-of-tree (ft/it:intervals-of-itree itree)))
                    (unless (equal sorted-intervals ints-of-tree)
                      (return (list intervals sorted-intervals ints-of-tree))))))))
    (is (null result))))

        
(deftest it.intervals-of-itree.2 (&key (reps 1000) (size 20) (p 0.5))
  (let ((result
          (iter (repeat reps)
                (let* ((vals (random-integers size p))
                       (other-vals (set-difference (iota size) vals))
                       (sorted-intervals (intervals-of-list vals))
                       (sorted-other-intervals (intervals-of-list other-vals))
                       (intervals (random-permute sorted-intervals))
                       (itree (convert 'ft/it:itree (list (list (cons 0 (1- size)) t)))))
                  (setf itree (ft/it:itree-remove-intervals
                               itree
                               intervals))
                  (let ((ints-of-tree (ft/it:intervals-of-itree itree)))
                    (unless (equal sorted-other-intervals ints-of-tree)
                      (return (list intervals sorted-other-intervals ints-of-tree))))))))
    (is (null result))))

(deftest it.intervals-of-itree.3 ()
  (let ((itree (ft/it:itree-add-intervals (convert 'ft/it::itree nil) '((1 :a) (5 :b) (9 :c)))))
    (is (equal (ft/it:intervals-of-itree itree)
               '((1 . 1) (5 . 5) (9 . 9))))))

(deftest it.itree-merge-root-nodes (&key (reps 1000) (size 20) (p 0.5))
  (let ((result
          (iter (repeat reps)
                (let* ((vals (random-permute (random-integers size p)))
                       (itree (make-instance 'ft/it:itree)))
                  (iter (for val in vals)
                        (setf itree (ft/it:itree-insert itree val val nil))
                        (setf itree (ft/it:itree-merge-root-nodes itree)))
                  (unless (iter (for i from 0 below size)
                                (always (if (member i vals)
                                            (ft/it:itree-find-node itree i)
                                            (not (ft/it:itree-find-node itree i)))))
                    (return (list vals (convert 'list itree))))))))
    (is (null result))))

(deftest it.insert.collision ()
  (let ((itree (convert 'ft/it:itree '(((1 . 3) :a)))))
    (is (null (ft/it:itree-find itree 0)))
    (is (null (ft/it:itree-find itree 4)))
    (iter (for i from 1 to 3)
          (is (eql (handler-case (progn (ft/it:itree-insert itree i i t) :bad1)
                     (ft/it:interval-collision-error () :good))
                   :good))))
  (let ((itree (convert 'ft/it:itree '(((1 . 2) :a) ((5 . 6) :c)))))
    (is (eql (handler-case (progn (ft/it:itree-insert itree 3 5 :b) :bad2)
               (ft/it:interval-collision-error () :good))
             :good)))
  (is (equal (with-standard-io-syntax
               (with-output-to-string (s)
                 (write (make-condition 'ft/it:interval-collision-error :lo1 1 :hi1 4 :lo2 2 :hi2 3)
                        :escape nil :stream s)))
             "Interval collision: [1,4] intersects [2,3]")))

(deftest it.print ()
  (is (equal (format nil "~a" (convert 'ft/it:itree '((1 2)))) "#<1=>2>"))
  (is (equal (format nil "~a" (convert 'ft/it:itree '(((1 . 3) 2)))) "#<[1,3]=>2>"))
  (is (equal (format nil "~a" (ft/it:itree-root (convert 'ft/it:itree '((1 2))))) "#<1 2 NIL NIL>"))
  (is (equal (format nil "~a" (ft/it:itree-root (convert 'ft/it:itree '((1 t))))) "#<1 NIL NIL>"))
  (is (equal (format nil "~a" (ft/it:itree-root (convert 'ft/it:itree '(((1 . 3) 2))))) "#<(1 3) 2 NIL NIL>")))

(deftest it.glb.1 ()
  (let ((itree (convert 'ft/it:itree '(((1 . 2) :a) (4 :b) ((6 . 8) :c)))))
    (iter (for i from -1 to 0)
          (is (equal (multiple-value-list (ft/it:itree-glb itree i)) '(nil))))
    (iter (for i from 1 to 3)
          (is (equal (multiple-value-list (ft/it:itree-glb itree i))
                     '(1 2 :a))))
    (iter (for i from 4 to 5)
          (is (equal (multiple-value-list (ft/it:itree-glb itree i))
                     '(4 4 :b))))
    (iter (for i from 6 to 10)
          (is (equal (multiple-value-list (ft/it:itree-glb itree i)) '(6 8 :c))))))

(deftest it.lub.1 ()
  (let ((itree (convert 'ft/it:itree '(((1 . 2) :a) (4 :b) ((6 . 8) :c)))))
    (iter (for i from 0 to 2)
          (is (equal (multiple-value-list (ft/it:itree-lub itree i))
                     '(1 2 :a))))
    (iter (for i from 3 to 4)
          (is (equal (multiple-value-list (ft/it:itree-lub itree i))
                     '(4 4 :b))))
    (iter (for i from 5 to 8)
          (is (equal (multiple-value-list (ft/it:itree-lub itree i)) '(6 8 :c))))
    (iter (for i from 9 to 10)
          (is (equal (multiple-value-list (ft/it:itree-lub itree i)) '(nil))))))

(deftest it.min/max-node ()
    (let ((root (ft/it:itree-root (convert 'ft/it:itree '(1 11 4 9)))))
      (multiple-value-bind (node rpath) (ft/it::max-node root)
        (is (equal (convert 'list node) '((11 t))))
        (is (equal (convert 'list (car rpath)) '((1 t) (4 t) (9 t) (11 t))))
        (is (null (cdr rpath))))
      (multiple-value-bind (node rpath) (ft/it::min-node root)
        (is (equal (convert 'list node) '((1 t))))
        (is (equal (convert 'list (car rpath)) '((1 t) (4 t))))
        (is (equal (convert 'list (cadr rpath)) '((1 t) (4 t) (9 t) (11 t))))
        (is (null (cddr rpath))))))

;;; Tests of attribute functions

(defclass data-root (attrs-root node-with-data)
  ())

(defclass data-subroot (subroot node-with-data)
  ())

(defmethod convert ((to-type (eql 'data-root))
                    in &key)
  "Convert IN into a data-root with data-subroots for children."
  (let ((in (change-class (copy (convert 'node-with-data in)) 'data-root)))
    (copy in
          :children
          (mapc (lambda (child)
                  (change-class child 'data-subroot))
                (children in)))))

(defmethod convert ((to-type (eql 'data-subroot))
                    (in node-with-data) &key)
  (change-class (copy in) 'data-subroot))

(defmethod convert ((to-type (eql 'data-subroot))
                    in &key)
  (convert 'data-subroot (convert 'node-with-data in)))

(deftest attr.1 ()
  (def-attr-fun attr.1-fn (parent)
    "Label each node with its parent"
    (:method ((node node) &optional parent)
      (mapc {attr.1-fn _ node} (children node))
      parent))
  (let ((t1 (convert 'data-root '(a b c)))
        at)
    (with-attr-table t1
      (setf at *attrs*)
      (is (eql (attr.1-fn t1 nil) nil))
      (is (eql (attr.1-fn t1) nil))
      (is (eql (attr.1-fn (first (children t1))) t1))
      (is (eql (attr.1-fn (second (children t1))) t1)))
    (with-attr-table at
      (is (eql (attr.1-fn t1 nil) nil))
      (is (eql (attr.1-fn t1) nil))
      (is (eql (attr.1-fn (first (children t1))) t1))
      (is (eql (attr.1-fn (second (children t1))) t1)))))

(deftest attr.2 ()
  (def-attr-fun attr.2-fun ()
    "Size function"
    (:method ((node node))
      (reduce #'+ (children node) :key #'attr.2-fun :initial-value 1)))
  (let ((t1 (convert 'data-root '(a (b c) (d e)))))
    (with-attr-table t1
      (is (eql (attr.2-fun t1) 5))
      (is (eql (attr.2-fun t1) 5)))))

(deftest attr-circular ()
  (def-attr-fun attr.3-fn ()
    (:method ((node node)) (attr.3-fn node)))
  (let ((t1 (convert 'data-root '(a))))
    (with-attr-table t1
      (is (handler-case (progn (attr.3-fn t1) nil)
            (error () t))))))

(deftest attr.4 ()
  (def-attr-fun attr.4-fn (parent)
    (:method ((node node) &optional parent)
      (mapc {attr.4-fn _ node} (children node))
      parent))
  (defmethod ft/attrs:attr-missing ((fn-name (eql 'attr.4-fn)) (node node))
    (let ((root (attrs-root *attrs*)))
      (attr.4-fn root nil)))
  (let* ((r (convert 'data-root '(a b (c d))))
         (n1 (first (children r)))
         (n2 (second (children r)))
         (n3 (first (children n2))))
    (with-attr-table r
      (is r)
      (is n1)
      (is n2)
      (is n3)
      (is (eql (attr.4-fn n3) n2))
      (is (eql (attr.4-fn n2) r))
      (is (eql (attr.4-fn n1) r))
      (is (eql (attr.4-fn r) nil)))))

(defvar *attr-run* nil)

(deftest attr.5 ()
  "Incrementalization without dependencies."
  (def-attr-fun attr.5-fun ()
    "Size function"
    (:method ((node node))
      (setf *attr-run* t)
      (reduce #'+ (children node) :key #'attr.5-fun :initial-value 1)))
  (let ((t1 (convert 'data-root '((a b) (c d) (e f)))))
    (is (children t1))
    (with-attr-table t1
      (let ((*attr-run*))
        (is (eql (attr.5-fun t1) 5))
        (is *attr-run*)))
    (let* ((t2 (with t1
                     (second (children t1))
                     (convert 'data-subroot '(g h)))))
      (is (not (eql t1 t2)))
      (with-attr-table t2
        (let ((*attr-run*))
          (is (subroot? (first (children t1))))
          (is (eql (first (children t1))
                   (first (children t2))))
          (attr.5-fun (first (children t2)))
          ;; The attribute was not recomputed for the unchanged
          ;; subroot.
          (is (null *attr-run*))
          (attr.5-fun (second (children t2)))
          (is *attr-run*)
          (is (eql 5 (attr.5-fun t2)))))
      t2)))

(defclass project (parent attrs-root)
  ())

(defmethod print-object ((self project) stream)
  (print-unreadable-object (self stream :type t :identity t)))

(defclass file (node)
  ((name :initarg :name :type string :reader name)
   (exports :initarg :exports :type list :reader exports)))

(defmethod print-object ((self file) stream)
  (print-unreadable-object (self stream :type t :identity t)
    (format stream "~a" (name self))))

(defclass impl-file (file subroot)
  ((deps :initarg :deps :type list :reader deps)))

(defclass header-file (file subroot)
  ())

(defun find-dep (p name)
  (or (find name (children p) :key #'name :test #'equal)
      (error "No such dependency: ~a" name)))

(def-attr-fun trivial-symbol-table (in)
  (:method ((h header-file) &optional in)
    (copy-list (append in (exports h))))
  (:method ((p project) &optional in)
    (copy-list
     (reduce (lambda (in2 child)
               (trivial-symbol-table child in2))
             (let ((children (children p)))
               (append
                (remove-if-not (of-type 'impl-file) children)
                (remove-if-not (of-type 'header-file) children)))
             :initial-value in)))
  (:method ((f impl-file) &optional in)
    (copy-list
     (append
      (reduce (lambda (in2 dep)
                (trivial-symbol-table dep in2))
              (mapcar (lambda (d)
                        (find-dep (ft/attrs:attrs-root*) d))
                      (deps f))
              :initial-value in)
      (exports f)))))

(defmethod attr-missing ((fn-name (eql 'trivial-symbol-table)) (node t))
  (trivial-symbol-table (ft/attrs:attrs-root*) nil))

(defun symbol-table-alist (project)
  ;; TODO Should work without.
  (trivial-symbol-table project)
  (iter (for file in (children project))
        (collect (cons (name file)
                       (trivial-symbol-table file)))))

(defun eql-for-key (key alist1 alist2)
  (eql (cdr (is (assoc key alist1 :test #'equal)))
       (cdr (is (assoc key alist2 :test #'equal)))))

(deftest attr-project ()
  (let* ((cc-file-1
           (make-instance 'impl-file
             :name "my_class.cc"
             :deps (list "my_class.h")
             :exports (list "my_class::do_something()")))
         (cc-file-2
           (make-instance 'impl-file
             :name "my_program.cc"
             :deps (list "my_class.h" "other_class.h")
             :exports (list "main")))
         (cc-file-3
           (make-instance 'impl-file
             :name "other_class.cc"
             :deps (list "other_class.h")
             :exports (list "other_class::do_something()")))
         (header-file-1
           (make-instance 'header-file
             :name "my_class.h"
             :exports (list "my_class")))
         (header-file-2
           (make-instance 'header-file
             :name "other_class.h"
             :exports (list "other_class")))
         (project
           (make-instance 'project
             :children (list
                        cc-file-1
                        cc-file-2
                        cc-file-3
                        header-file-1
                        header-file-2))))
    ;; Test that changing one .cc file doesn't change them all.
    (let* ((old-alist
             (with-attr-table project
               (symbol-table-alist project)))
           (new-cc-file (tree-copy cc-file-1))
           (new-project
             (with project
                   cc-file-1
                   new-cc-file))
           (new-alist
             (with-attr-table new-project
               (symbol-table-alist new-project))))
      (is (not (eql new-project project))
          "The project must have changed")
      (is (not (eql cc-file-1
                    (is (find (name cc-file-1)
                              (children new-project)
                              :key #'name))))
          "The cc file must have changed")
      (dolist (file (list cc-file-2 cc-file-3 header-file-1 header-file-2))
        (is (eql (is (cdr (assoc (name file) old-alist :test #'equal)))
                 (is (cdr (assoc (name file) new-alist :test #'equal))))
            "Unchanged files must have the same symbol table"))
      (is (not (eql-for-key (name cc-file-1) old-alist new-alist))
          "Changed files must have new symbol tables"))
    (let* ((old-alist
             (with-attr-table project
               (symbol-table-alist project)))
           (new-header-file (tree-copy header-file-1))
           (new-project
             (with project header-file-1 new-header-file))
           (new-alist
             (with-attr-table new-project
               (symbol-table-alist new-project))))
      (is (not (eql new-project project))
          "The project must have changed")
      (is (not (eql header-file-1
                    (is (find (name header-file-1)
                              (children new-project)
                              :key #'name))))
          "The header file must have changed")
      (is (path-of-node new-project new-header-file))
      (is (not (path-of-node new-project header-file-1)))
      (dolist (file (list cc-file-3 header-file-2))
        (is (eql-for-key (name file) old-alist new-alist)
            "Unrelated symbol tables must be left alone."))
      (dolist (file (list header-file-1))
        (is (not (eql-for-key (name file) old-alist new-alist))
            "The header file must be recalculated."))
      (dolist (file (list cc-file-1 cc-file-2))
        (is (not (eql-for-key (name file) old-alist new-alist))
            "The dependencies must be recalculated.")))))
