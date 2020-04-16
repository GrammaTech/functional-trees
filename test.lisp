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
        :gmap
        :alexandria
        :named-readtables
        :curry-compose-reader-macros
        :stefil
        :iterate
        #+gt :testbot)
  (:import-from :uiop/utility :nest)
  (:shadowing-import-from :functional-trees
                          :dump
                          :lexicographic-<
                          :make-node-heap-data
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
                          :substitute-with
                          :transform-finger
                          :traverse-nodes-with-rpaths
                          :with-encapsulation)
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
  (:export test))
(in-package :ft/test)
(in-readtable :curry-compose-reader-macros)

#-gt
(progn
  ;;; External replacement for GT-specific test submission helpers
  (defvar *success* nil "Variable indicating test success or failure.")
  (defun batch-test (test project branch &optional args)
    "Run tests in 'batch' mode, printing results as a string."
    (declare (ignorable project branch args))

    (let* ((stefil::*test-progress-print-right-margin* (expt 2 20))
           (failures (coerce (stefil::failure-descriptions-of
                              (without-debugging (funcall test)))
                             'list)))
      (setf *success*
            (if failures
                (prog1 nil
                  (format *error-output* "FAILURES~%")
                  (mapc [{format *error-output* "  ~a~%"}
                         #'stefil::name-of
                         #'stefil::test-of
                         #'car #'stefil::test-context-backtrace-of]
                        failures))
                (prog1 t
                  (format *error-output* "SUCCESS~%")))))))

(defun run-batch (&rest a)
  (declare (ignorable a))
  #+ccl (setf ccl::*interactive-streams-initialized* nil)
  (batch-test #'test "functional-trees" "master"))


;;;; Additional infrastructure on node for testing.
(defclass node-with-data (node)
  ((children :reader children
             :type list
             :initarg :children
             :initform nil
             :documentation "The list of children of the node,
which may be more nodes, or other values.")
   (child-slots :initform '(children) :allocation :class)
   (data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data")))

(defmethod node-values ((node node-with-data)) (data node))
(defmethod data (val) val)

(defmethod convert ((to-type (eql 'node-with-data)) (sequence list)
                    &key &allow-other-keys)
  (labels ((make-node (list-form)
             (if (consp list-form)
                 (make-instance 'node-with-data
                   :data (car list-form)
                   :children (mapcar #'make-node (cdr list-form)))
                 list-form)))
    (populate-fingers (make-node sequence))))

(defmethod convert ((to-type (eql 'node-with-data)) (from node-with-data)
                    &key &allow-other-keys)
  from)

(defclass node-with-fields (node)
  ((child-slots :initform '((a . 1) (b . 1)) :allocation :class)
   (a :reader node-a
      :initarg :a
      :initform nil
      :type (or null node-with-fields)
      :documentation "Example of a node field")
   (b :reader node-b
      :initarg :b
      :initform nil
      :type (or null node-with-fields)
      :documentation "Example of a node field")
   (data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data"))
  (:documentation "Example class with two fields, a and b,
that are made available (in addition to children) as links
to subtrees."))

(defmethod node-values ((node node-with-fields)) (data node))

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
    (populate-fingers (make-node sequence))))

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
                                      (assert (= size 1))
                                      (when-let ((children
                                                  (slot-value node slot)))
                                        (list (make-keyword slot)
                                              (convert 'list children)))))
                                  (child-slots node)))
                 node)))
    (convert- node)))

(defun swap-random-nodes (root)
  (let ((node1 (random-node root))
        (node2 (random-node root)))
    (if (or (is-ancestor-of node1 node2)
            (is-ancestor-of node2 node1))
        root
        (swap root node1 node2))))

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

(defmethod lookup ((node node-with-fields) (i (eql :a))) (node-a node))
(defmethod lookup ((node node-with-fields) (i (eql :b))) (node-b node))
(defmethod lookup ((node node-with-fields) (i (eql :data))) (data node))

(defun plist-drop-keys (keys plist)
  (iter (for e on plist by #'cddr)
        (unless (member (car e) keys)
          (collecting (car e))
          (when (cdr e)
            (collecting (cadr e))))))


;;;; Test suite.
(defsuite test)
(in-suite test)

;;; Simple Copy Tests
(deftest simple-copy-tests ()
  (flet ((copy-is-equal (it)
           (is (funcall (typecase it
                          (symbol (lambda (a b)
                                    (string= (symbol-name a) (symbol-name b))))
                          (t #'equalp))
                        it (copy it)))))
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
  (is (not (lexicographic-< '(a) '(a)))))

(deftest make-node.1 ()
  (is (not (convert 'node-with-data nil)))
  (is (typep (convert 'node-with-data '(:a)) 'node))
  (is (null (transform (convert 'node-with-data '(:b (:c))))))
  (is (equal (convert 'list (convert 'node-with-data '(:a))) '(:a)))
  (is (= 4 (serial-number (make-instance 'node :serial-number 4)))))

(deftest finger.1 ()
  (let* ((init-list '(:a "ab" (:b) "xy" (:c (:d) #\Z (:e "!"))))
         (node (convert 'node-with-data init-list)))
    (is (equal (convert 'list node) init-list))
    (flet ((%f (path)
             (convert 'list (make-instance 'finger :node node
                                     :path path :residue nil))))
      (is (equal (%f nil) init-list))
      (is (equal (%f '(0)) (cadr init-list)))
      (is (equal (%f '(1)) (caddr init-list)))
      (is (equal (%f '(3 0)) (second (fifth init-list))))
      )))

(deftest transform-path.1 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:x))))
         (node1 (convert 'node-with-data l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((1) (2) :live))))
         (node2 (convert 'node-with-data l2)))
    (setf (slot-value node2 'transform) pt)

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (convert 'list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (convert 'list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (convert 'list f3) (cadr l1)))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '(0)))
        (is (null (residue f4)))
        (is (equal (convert 'list f4) (cadr l2)))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1))))
      (is (equal (path f5) '(1)))
      (is (equal (convert 'list f5) (third l1)))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(2)))
        (is (null (residue f6)))
        (is (equal (convert 'list f6) (fourth l2)))))))

(deftest transform-path.2 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:c (:x))))
         (node1 (convert 'node-with-data l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((0) nil :dead)
                                          ((1) (0) :live))))
         (node2 (convert 'node-with-data l2)))
    (setf (slot-value node2 'transform) pt)

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (convert 'list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (convert 'list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (convert 'list f3) (cadr l1)))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (null (path f4)))
        (is (equal (residue f4) '(0)))
        (is (equal (convert 'list f4) l2))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1))))
      (is (equal (path f5) '(1)))
      (is (equal (convert 'list f5) (third l1)))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(0)))
        (is (null (residue f6)))
        (is (equal (convert 'list f6) (second l2)))))))

(deftest transform-path.3 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:z) (:x) (:y))))
         (node1 (convert 'node-with-data l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((1 0) (2 1) :live)
                                          ((1) (2) :live))))
         (node2 (convert 'node-with-data l2)))
    (setf (slot-value node2 'transform) pt)

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (convert 'list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (convert 'list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (convert 'list f3) (cadr l1)))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '(0)))
        (is (null (residue f4)))
        (is (equal (convert 'list f4) (cadr l2)))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1 0))))
      (is (equal (path f5) '(1 0)))
      (is (equal (convert 'list f5) (second (third l1))))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(2 1)))
        (is (null (residue f6)))
        (is (equal (convert 'list f6) (third (fourth l2))))))))

(deftest transform-path.error ()
  (let* ((l1 '(:a 1))
         (l2 '(:b 2))
         (node1 (convert 'node-with-data l1))
         (node2 (convert 'node-with-data l2))
         (f1 (make-instance 'finger :node node1 :path nil)))
    (is (handler-case
            (progn (transform-finger f1 node2) nil)
          (error () t)))))        

;;; Tests of path-transform-of, map-tree
(deftest map-tree.0 ()
  (is (= (map-tree #'identity 1) 1))
  (is (= (map-tree #'1+ 1) 2))
  (is (equalp (map-tree (lambda (x) (if (integerp x) (1+ x) x)) '(0 1 (2 . 3)))
              '(1 2 (3 . 4)))))

(deftest map-tree.1 ()
    (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
           (n2 (map-tree (lambda (n)
                           (if (eql :c (data n))
                               (make-instance 'node-with-data :data :c)
                               n))
                         n1)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n1) (convert 'list n2)))))

(deftest map-tree.2 ()
    (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
           (n2 (map-tree (lambda (n)
                           (if (eql :c (data n))
                               (make-instance 'node-with-data :data :c)
                               n))
                         n1)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n1) (convert 'list n2)))))

(deftest map-tree.3 ()
  (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
         (n2 (remove-if
              (lambda (n)
                (etypecase n
                  (node-with-data (eql (data n) :c))
                  (symbol (eql n :c)))) n1)))
    (is (not (eql n1 n2)))
    (is (equal (convert 'list n2) '(:a (:b) (:d))))))

(deftest map-tree.4 ()
  (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
         (n2 (@ n1 '(1)))
         (n3 (@ n1 '(2)))
         (n4 (swap n1 n2 n3)))
    (is (not (eql n1 n4)))
    (is (equal (convert 'list n4) '(:a (:b) (:d) (:c))))))

(deftest @.error ()
  (is (handler-case (progn (@ (convert 'node-with-data '(:a)) '(:bad)) nil)
        (error () t)))
  (is (handler-case (progn (@ (convert 'node-with-data '(:a)) '(-1)) nil)
        (error () t)))
  (is (handler-case (progn (@ (convert 'node-with-data '(:a (:b))) '(1)) nil)
        (error () t))))

(deftest path-of-node.1 ()
  (let ((n1 (convert 'node-with-data '(:a)))
        (n2 (convert 'node-with-data '(:a (:b) (:b (:c) (:d) (:e)) (:d)))))
    (is (handler-case (progn (path-of-node n2 n1) nil)
          (error () t)))
    (is (equal (path-of-node n2 (second (children n2))) '(1)))
    (is (equal (path-of-node n1 n1) nil))
    (is (equal (path-of-node n2 (third (children (second (children n2)))))
               '(1 2)))))

(deftest node-can-implant.1 ()
  (let* ((n1 (convert 'node-with-data '(:a (:b) (:b (:c) (:d) (:e)) (:d))))
         (n2 (second (children n1)))
         (n3 (third (children n1))))
    (is (node-can-implant n1 n1 n1))
    (is (node-can-implant n1 n2 n2))
    (is (not (node-can-implant n1 n2 n1)))
    (is (not (node-can-implant n1 n2 n3)))))

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
  (is (node-valid (convert 'node-with-data '(:a))))
  (is (node-valid (convert 'node-with-data '(:a (:a) (:b)))))
  (is (not (node-valid
            (let ((n (convert 'node-with-data '(:a))))
              (convert 'node-with-data `(:b ,n ,n)))))))

(deftest nodes-disjoint.1 ()
  (is (nodes-disjoint (convert 'node-with-data '(:a))
                          (convert 'node-with-data '(:b))))
  (is (nodes-disjoint (convert 'node-with-data '(:a))
                          (convert 'node-with-data '(:a))))
  (is (nodes-disjoint (convert 'node-with-data '(:a (:b)))
                          (convert 'node-with-data '(:a (:b)))))
  (let ((n (convert 'node-with-data '(:a))))
    (is (not (nodes-disjoint n n))))
  (let ((n (convert 'node-with-data '(:a))))
    (is (not (nodes-disjoint (convert 'node-with-data `(:b ,n))
                             (convert 'node-with-data `(:c ,n))))))
  (let* ((n (convert 'node-with-data '(:a)))
         (n2 (copy n :data :b)))
    (is (not (nodes-disjoint (convert 'node-with-data `(:c ,n))
                             (convert 'node-with-data `(:d ,n2)))))))

(deftest node-equalp.1 ()
  (is (node-equalp nil nil))
  (is (node-equalp 1 1))
  (is (node-equalp '(1) '(1)))
  (is (not (node-equalp 1 2)))
  (let ((n (convert 'node-with-data '(:a))))
    (is (node-equalp n n))
    (is (node-equalp n (copy n :data :b)))
    (is (not (node-equalp n (convert 'node-with-data '(:a)))))
    (is (not (node-equalp n (convert 'node-with-data '(:a (:b))))))
    (is (not (node-equalp n (copy n :children
                                  (list (convert 'node-with-data '(:b))))))))
  (let ((n (convert 'node-with-data '(:a (:b)))))
    (is (node-equalp n
                       (copy n
                             :children
                             (list (copy (car (children n))
                                         :data :c)))))
    (is (not (node-equalp n (copy n :children
                                  (list (convert 'node-with-data '(:c)))))))))

(deftest print.1 ()
  (let ((*print-readably* nil)
        (n1 (convert 'node-with-data '(:a)))
        (t1 (convert 'node-with-data '(:a))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (convert 'node-with-data '(:a)) s))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (path-transform-of n1 n1) s))))
    (is (stringp (with-output-to-string (s)
                   (prin1 (finger t1) s))))))

(deftest print.2 ()
  (let ((*print-readably* t)
        (n1 (convert 'node-with-data '(:a)))
        (t1 (convert 'node-with-data '(:a))))
    (flet ((%e (v)
             (handler-case (progn (prin1 v) nil)
               (error () t))))
    (is (%e (convert 'node-with-data '(:a))))
    (is (%e (path-transform-of n1 n1)))
    (is (%e (finger t1))))))

(defun random-test-check (n1 n2)
  (when (and n1 n2)
    (let ((pt (path-transform-of n1 n2))
          (serial-numbers nil))
      (handler-case
          (progn
            (traverse-nodes n2 (lambda (n) (push (serial-number n)
                                                 serial-numbers)))
            ;; (format t "SERIAL-NUMBERS = ~a~%" serial-numbers)
            (traverse-nodes-with-rpaths
             n1
             (lambda (n rpath)
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
                               (serial-number n3)))))))
               t)))
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
  (let* ((l1 '(:i 17 17 (:d 26) (:m (:b 54 84))))
         (n1 (convert 'node-with-data l1))
         (n2 (@ n1 '(2)))
         (f2 (make-instance 'finger :node n1 :path '(2)))
         (n3 (@ n1 '(3 0)))
         (f3 (make-instance 'finger :node n1 :path '(3 0)))
         (n4 (swap n1 n2 n3)))
    (is (equal (transform n1) nil))
    (is (typep (transform n4) 'path-transform))
    (is (equal (convert 'list n1) l1))
    (is (equal (convert 'list n2) '(:d 26)))
    (is (equal (convert 'list n3) '(:b 54 84)))
    (is (equal (convert 'list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    ;; Swap moves the nodes as expected.
    (is (eql (serial-number (@ n1 '(2))) (serial-number (@ n4 '(3 0)))))
    (is (eql (@ n1 '(2)) (@ n4 '(3 0))))
    (is (eql n2 (@ n4 '(3 0))))
    (is (eql n3 (@ n4 '(2))))
    ;; Fingers find original nodes in original.
    (is (eql n2 (@ n1 f2)))
    (is (eql n3 (@ n1 f3)))
    ;; Fingers find the new nodes at the new locations.
    #+broken (is (equal n2 (@ n4 f2)))
    #+broken (is (equal n3 (@ n4 f3)))))

(deftest path-of-node.0 ()
  (let ((it (convert 'node-with-data '(:i 17 17 (:d 26) (:m (:b 54 84))))))
    (is (equalp (path-of-node it (@ it '(3 0))) '(3 0)))))

(deftest size.0 ()
  (let ((it (convert 'node-with-data '(:i 17 17 (:d 26) (:m (:b 54 84))))))
    (is (= 4 (size it)))))

(deftest substitute-with.0 ()
  (is (equalp (substitute-with (lambda (n) (case n (3 :eric))) '(1 2 3 4))
              '(1 2 :eric 4)))
  (is (equalp (substitute-with (lambda (n) (case n (3 :eric))) (fset:seq 1 2 3 4))
              (fset::seq 1 2 :eric 4))))

(deftest random.1 ()
  ;; Randomized test of path transforms
  (is (equal (random-test 20 200 (lambda (n) (remove-nodes-randomly n 0.2))) nil)))

(deftest random.2 ()
  (let ((result :pass)
        (size 50))
    (dotimes (n 1000)
      (let ((root (make-random-tree size)))
        (traverse-nodes-with-rpaths
         root
         (lambda (n rpath)
           (let ((p (reverse rpath)))
             (macrolet ((is (e)
                          `(unless ,e
                             (setf result (list :fail ',e p n root))
                             (return))))
               ;; TODO: Iterate needs to be taught how to walk `is'.
               (is (path-p p))
               (is (typep p 'path))
               (is (eql (@ root p) n))
               (is (equal (path-of-node root n) p))))
           t))))
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
    (node-with-data (or (null (data n))
                        (some #'tree-has-null-data-node (children n))))
    (t nil)))

(deftest new/old.path-transform.1 ()
  (let* ((l1 '(a 65 (g 39 82) 23 (a 68 51)))
         (n1 (convert 'node-with-data l1))
         (c (children n1))
         (l2 `(a 65 ,(elt c 3) 23 ,(elt c 1)))
         (n2 (copy (convert 'node-with-data l2) :transform n1)))
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
  (let ((n (convert 'node-with-fields '(:data 12))))
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
         (n2 (map-tree (lambda (n)
                         (if (eql :bar (data n))
                             (make-instance 'node-with-fields :data :qux)
                             n))
                       n1))
         (n3 (convert 'node-with-fields '(:data :quux)))
         (n4 (map-tree (lambda (n)
                         (if (eql :baz (data n))
                             n3
                             n))
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
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (reduce #'+ (iota 10)) (reduce #'+ tree)))))

(deftest find-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find 4 tree) 4))
    (is (not (find 10 tree)))))

(deftest find-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find-if «and #'integerp [#'zerop {mod _ 3}] {< 4 }» tree) 6))
    (is (not (find-if (constantly nil) tree)))
    (is (not (find-if (constantly nil) tree :key #'identity)))))

(deftest find-if-not-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find-if-not [#'not «and #'integerp [#'zerop {mod _ 3}] {< 4 }»] tree) 6))
    (is (not (find-if-not (constantly t) tree)))
    (is (not (find-if-not #'identity tree :key #'identity)))))

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
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count 3 tree) 1))))

(deftest count-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count-if [#'zerop {mod _ 3}] tree) 3))
    (is (zerop (count-if (constantly nil) tree)))))

(deftest count-if-not-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count-if-not [#'zerop {mod _ 3}] tree) 6))
    (is (not (zerop (count-if-not (constantly nil) tree))))))

(deftest position-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (is (equalp (position 4 tree) '(2)))
    (is (equalp (position 11 tree :key #'data) '(4 0 0)))
    (is (not (position 12 tree)))))

(deftest position-tree-w-named-children ()
  (is (equalp (position 1 (convert 'node-with-fields
                                   '(:data :foo :a (:data 1) :b (:data 2)))
                        :key #'data)
              '(:a))))

(deftest position-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (is (= (@ tree (position-if «and [#'zerop {mod _ 3}] {< 4 }» tree
                                :key #'data))
           6))
    (is (not (position-if (constantly nil) tree)))
    (is (not (position-if #'identity tree :key (constantly nil))))))

(deftest position-if-not-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (is (= (@ tree (position-if-not [#'not «and [#'zerop {mod _ 3}] {< 4 }»]
                                    tree :key #'data))
           6))
    (is (not (position-if-not (constantly t) tree)))
    (is (not (position-if-not #'not tree :key (constantly nil))))))

(deftest remove-tree ()
  (is (= (length (convert 'list (remove 24 (convert 'node-with-data
                                                    (iota 100)))))
         99))
  (is (transform (remove 24 (convert 'node-with-data (iota 100)))))
  (is (equal (convert 'list (remove 3 (convert 'node-with-data (iota 6))))
             '(0 1 2 4 5)))
  (is (equal (convert 'list (remove 3 (convert 'node-with-data (iota 6))
                                    :key (lambda (a) (if (numberp a) (1+ a) a))))
             '(0 1 3 4 5)))
  (is (equal (convert 'list (remove 3 (convert 'node-with-data (iota 6)) :key 'identity))
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
                                           (convert 'node-with-data (cons :a (iota 6)))))
             '(:a 2 3 4)))
  (is (equal (convert 'list (remove-if-not #'not
                                           (convert 'node-with-data (iota 6))
                                           :key {member _ '(2 3 4)}))
             '(0 1 5))))

(deftest substitute-test ()
  (let ((no-twenty (substitute 40 20 (convert 'node-with-data (iota 100)))))
    (is (= 0 (count 20 no-twenty)))
    (is (= 2 (count 40 no-twenty)))
    (is (transform no-twenty)))
  (let ((it (convert 'node-with-data (iota 6))))
    (is (equal (convert 'list (substitute :x nil it
                                          :key {typep _ '(not (integer 2 4))}))
               '(0 1 :x :x :x 5)))))

(deftest substitute-if-test ()
  (let ((no-odd (substitute-if :odd #'oddp (convert 'node-with-data
                                                    (iota 100))
                               :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd)))
    (is (= 50 (count :odd no-odd)))
    (let ((it (convert 'node-with-data '(0 2 3 3 4)))
          (n (convert 'node-with-data '(:z 17))))
      (let ((c1 (substitute-if n #'oddp it :key #'data)))
        (is (eql (@ c1 '(1)) (@ c1 '(2)))))
      (let ((c1 (substitute-if n #'oddp it :copy 'copy :key #'data)))
        (is (not (eql (@ c1 '(1)) (@ c1 '(2)))))))))

(deftest substitute-if-not-test ()
  (let ((no-odd
         (substitute-if-not :odd #'evenp
                            (convert 'node-with-data (iota 100))
                            :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd)))
    (is (= 50 (count :odd no-odd)))
    (let ((it (convert 'node-with-data (iota 6))))
      (is (equal (convert 'list (substitute-if-not :x #'null it
                                                   :key {typep _ '(integer 2 4)}))
                 '(0 1 :x :x :x 5))))
    (let ((it (convert 'node-with-data '(0 2 3 3 4)))
          (n (convert 'node-with-data '(:z 17))))
      (let ((c1 (substitute-if-not n «or (complement #'numberp) #'evenp» it)))
        (is (eql (@ c1 '(1)) (@ c1 '(2)))))
      (let ((c1 (substitute-if-not n #'evenp it :copy 'copy :key #'data)))
        (is (not (eql (@ c1 '(1)) (@ c1 '(2)))))))))

(deftest subst-test ()
  (let ((no-twenty (subst 40 20 (convert 'node-with-data (iota 100)))))
    (is (= 0 (count 20 no-twenty)))
    (is (= 2 (count 40 no-twenty)))
    (is (transform no-twenty)))
  (is (equal (subst :y :x '(:a :x :y :z)) '(:a :y :y :z)))
  (is (equal (subst :y t '(0 1 2 3 4) :key {typep _ '(eql 2)})
             '(0 1 :y 3 4)))
  (is (equal (subst :y '(1) '(0 1 2 3 4) :test #'equal
                    :key #'list)
             '(0 :y 2 3 4)))
  (is (equal (subst :y '(1) '(0 1 2 3 4) :test-not (complement #'equal)
                    :key #'list)
             '(0 :y 2 3 4)))
  (let ((it (subst :x 4 (convert 'node-with-data '(:a 1 (:b 2) 3 (:c (:d 4) 5) (:e 4) 7)))))
    (is (equal (convert 'list it)
               '(:a 1 (:b 2) 3 (:c (:d :x) 5) (:e :x) 7))))
  (let ((it (subst 17 :c (convert 'node-with-data '(:a 1 (:b 2) (:c 3) (:d 4))))))
    (is (equal (convert 'list it) '(:a 1 (:b 2) (:c 3) (:d 4)))))
  (let ((it (subst 17 :c (convert 'node-with-data '(:a 1 (:b 2) (:c 3) (:d 4)))
                   :key #'data)))
    (is (equal (convert 'list it) '(:a 1 (:b 2) 17 (:d 4))))))

(deftest subst-if-test ()
  (let ((no-odd (subst-if :odd #'oddp (convert 'node-with-data (iota 100))
                          :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd)))
    (is (= 50 (count :odd no-odd))))
  (let ((it (subst-if :odd «and #'numberp #'oddp» (convert 'node-with-data '(:a 1 2 3)))))
    (is (equal (convert 'list it) '(:a :odd 2 :odd))))
  (is (equal (subst-if :x #'zerop '(1 2) :key #'size)
             '(:x :x . :x))))

(deftest subst-if-not-test ()
  (let ((no-odd
         (subst-if-not :odd #'evenp (convert 'node-with-data (iota 100))
                       :key #'data)))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd)))
    (is (= 50 (count :odd no-odd))))
  (let ((it (subst-if-not :odd (complement «and #'numberp #'oddp»)
                          (convert 'node-with-data '(:a 1 2 3)))))
    (is (equal (convert 'list it) '(:a :odd 2 :odd))))
  (is (equal (subst-if-not :x #'plusp '(1 2) :key #'size)
             '(:x :x . :x))))

(deftest with-test ()
  (let ((two-fives (with (convert 'node-with-data (iota 10)) '(2) 5)))
    (is (= 2 (count 5 two-fives)))
    (is (zerop (count 3 two-fives))))
  ;; Should replace (5 6 7 8) with :TOUCHED.
  (is (= 6 (length (flatten (convert 'list
                             (with (convert 'node-with-data
                                            '(1 2 3 4 (5 6 7 8) (((9)))))
                                   '(3) :touched))))))
  ;; Should replace 6 with :TOUCHED.
  (is (= 9 (length (flatten (convert 'list
                             (with (convert 'node-with-data
                                            '(1 2 3 4 (5 6 7 8) (((9)))))
                                   '(3 0) :touched))))))
  (let* ((r (convert 'node-with-data '(:a 1 2 (:b 3 4) 5)))
         (n (@ r '(2))))
    (is (equal (flatten (convert 'list (with r n :removed)))
               '(:a 1 2 :removed 5)))))

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

(deftest @-test ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (let ((it (copy tree)))
      (setf (@ it '(3 0)) :deleted)
      (is (zerop (count 6 it)))))
  (nest
   (ignore-errors)
   (with-expected-failures)
   (let ((tree (convert 'node-with-fields '(:data :foo :a (:data 1)
                                            :b (:data 2))))))
   (is (equal (flatten (convert 'list (@ tree '(1) 3)))
              '(:data :foo :a :data 1 :b 3)))))

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
  (let ((it (convert 'node-with-data '(0 1 2 3 4))))
    (is (equalp (convert 'list (splice it '(1) '(:a :b :c)))
                '(0 1 :a :b :c 2 3 4)))
    (is (handler-case (progn (splice it nil '(1)) nil)
          (error () t)))
    (is (handler-case (progn (splice it it '(1)) nil)
          (error () t))))
  #|
  (let ((it (convert 'node-with-data '(0 1 2 3 4)))
        (n (convert 'node-with-data '(:a 5))))
    (is (equal (convert 'list (splice it '(1) n))
               `(0 1 ,n 2 3 4))))
  |#
  (let ((it (convert 'node-with-data '(:a (:b 1) (:c (:d 2) (:e 3) 4) 5))))
    (is (equal (convert 'list (splice it '(1 0) '(:new)))
               '(:a (:b 1) (:c :new (:d 2) (:e 3)  4) 5)))
    (is (equal (convert 'list (splice it (@ it '(1 1)) '(:new)))
               '(:a (:b 1) (:c (:d 2) :new (:e 3) 4) 5))))
  #|
  (let ((it (convert 'node-with-fields '(:data :x :a (1) :b (2)))))
    (is (handler-case (progn (splice it '(:a) :what) nil)
          (error () t))))
  |#
  )

(deftest insert-test ()
  (let ((it (convert 'node-with-data '(0 1 2 3 4))))
    (is (equalp (convert 'list (insert it '(1) ':a))
                '(0 1 :a 2 3 4)))
    (is (handler-case (progn (insert it nil :what) nil)
          (error () t)))
    (is (handler-case (progn (insert it it :what) nil)
          (error () t))))
  (let* ((it (convert 'node-with-data '(:a (:b 1) (:c 2 3 (:d 4) 5) 6)))
         (n (@ it '(1 2))))
    (is (equal (convert 'list (insert it '(1 2) :new))
               '(:a (:b 1) (:c 2 3 :new (:d 4) 5) 6)))
    (is (equal (convert 'list (insert it n :new))
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
              '(:data :foo :a (:data 1) :b (:data 3))))))

(deftest conversion-to-node-with-data ()
  (is (= 3 (nest (count :data)
                 (flatten)
                 (convert 'alist)
                 (convert 'node-with-data)
                 '(1 2 3 4 (5 6 7 8) (9 10))))))

(deftest map-tree-works ()
  (is (equalp (nest (convert 'list)
                    (map-tree
                     (lambda (it)
                       (if (eql (data it) :c)
                           (convert 'node-with-data '(:foo))
                           it)))
                    (convert 'node-with-data)
                    '(:a (:b) (:b (:c) (:d) (:e)) (:d)))
              '(:a (:b) (:b (:foo) (:d) (:e)) (:d)))))

(deftest gmap-tree-works ()
  (let* ((node (convert 'node-with-data '(:i 17 17 (:d 26) (:m (:b 54 84)))))
         (list (gmap :list #'identity (:node node))))
    (is (equalp node (car list)))
    (is (find (@ node '(3 0)) list))
    (is (find 26 list))
    (is (= (length list) 9))))

(deftest bad-tree ()
  ;; Test where a tree has a node twice
  (flet ((%f (f x y)
           (assert
            (handler-case
                (progn (funcall f x y) nil)
              (error (e) (declare (ignorable e))
                     ;; (format t "Expected error: ~a~%" e)
                     t))
            ()
            "PATH-TRANSFORM-OF on tree with duplicate SN did not signal an error: ~a, ~a"
            x y)))
    (let* ((sn 261237163)
           (n1 (convert 'node-with-data '(:a 1)))
           (n1a (copy n1 :serial-number sn))
           (n2 (convert 'node-with-data '(:b 2)))
           (n2a (copy n2 :serial-number sn))
           (good (convert 'node-with-data `(:c ,n1 ,n2)))
           (bad (convert 'node-with-data `(:c ,n1a ,n2a))))
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
               (with-encapsulation t1 (copy t1 :transform t1)))))))

(deftest assert-test ()
  (is (null (eval '(ft::assert t)))))

(deftest map-tree-right-children-test ()
  (is (equal '(1 2 3)
             (children
              (map-tree (lambda (node)
                          (if (typep node 'node-with-data)
                              (make-instance 'node-with-data
                                             :children (reverse (children node)))
                              node))
                        (make-instance 'node-with-data
                                       :children '(3 2 1)))))))
