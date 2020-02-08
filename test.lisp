(defpackage :functional-trees/test
  (:nicknames :ft/test)
  (:use :common-lisp
        :functional-trees
        :gmap
        :alexandria
        :named-readtables
        :curry-compose-reader-macros
        :software-evolution-library/stefil-plus
        :iterate)
  (:import-from :uiop/utility :nest)
  (:shadowing-import-from :fset
                          :@ :convert :less :splice :insert
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


;;;; Additional infrastructure on node for testing.
(defclass node-with-data (node)
  ((children :reader children
             :type list
             :initarg :children
             :initform nil
             :documentation "The list of children of the node,
which may be more nodes, or other values.")
   (child-slots :initform '(children) :allocation :class)
   (data-slot :initform 'data :allocation :class)
   (data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data")))

(defmethod convert ((to-type (eql 'node-with-data)) (sequence list)
                    &key &allow-other-keys)
  (labels ((make-node (list-form)
             (if (consp list-form)
                 (make-instance 'node-with-data
                   :data (car list-form)
                   :children (mapcar #'make-node (cdr list-form)))
                 list-form)))
    (populate-fingers (make-node sequence))))

(defclass node-with-fields (node-with-data)
  ((a :reader node-a
      :initarg :a
      :documentation "Example of a node field")
   (b :reader node-b
      :initarg :b
      :documentation "Example of a node field"))
  (:documentation "Example class with two fields, a and b,
that are made available (in addition to children) as links
to subtrees."))

(defun update-tree (node fn)
  (copy (update-tree* node fn) :transform node))

(defgeneric update-tree* (node fn)
  (:documentation
  "Traverse tree rooted at NODE, in postorder, calling
FN at each node.  If FN returns a different tree, replace
the node at that point, and copy ancestors (preserving their
serial-numbers.)"))

(defmethod update-tree* ((n node) fn)
  (let* ((children (children n))
         (new-children (mapcar (lambda (c) (update-tree* c fn)) children)))
    (if (every #'eql children new-children)
        n
        (let ((new-n (copy n :children new-children)))
          (assert (eql (ft::serial-number n) (ft::serial-number new-n)))
          (copy n :children new-children)))))

(defmethod update-tree* ((n t) (fn t)) n)

(defmethod update-tree* :around ((node node) fn)
  (let ((n (call-next-method)))
    (funcall fn n)))

;; This fails if NODE1 is an ancestor of NODE2, or
;; vice versa
(defun swap-nodes (root node1 node2)
  (update-tree
   root
   (lambda (n)
     (cond
       ((eql (ft::serial-number n) (ft::serial-number node1)) node2)
       ((eql (ft::serial-number n) (ft::serial-number node2)) node1)
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

(defmethod lookup ((node node-with-fields) (i (eql :a))) (node-a node))
(defmethod lookup ((node node-with-fields) (i (eql :b))) (node-b node))

(defun plist-drop-keys (keys plist)
  (iter (for e on plist by #'cddr)
        (unless (member (car e) keys)
          (collecting (car e))
          (when (cdr e)
            (collecting (cadr e))))))

(defun update-tree-at-data (node-with-data data)
  "Cause nodes with DATA to be copied (and all ancestors)"
  (update-tree node-with-data (lambda (n) (if (eql (data n) data) (copy n) n))))


;;;; Test suite.
(defroot test)
(defsuite ft-tests "Functional tree tests")

(deftest lexicographic-<.1 ()
  (is (not (ft::lexicographic-< nil nil)))
  (is (not (ft::lexicographic-< '(1) nil)))
  (is (not (ft::lexicographic-< '(1) '(0))))
  (is (not (ft::lexicographic-< '(1 2 3 0) '(1 2 3))))
  (is (not (ft::lexicographic-< '(1) '(1))))
  (is (ft::lexicographic-< nil '(1)))
  (is (ft::lexicographic-< '(0) '(1)))
  (is (ft::lexicographic-< '(1 2 3) '(1 2 3 0)))
  (is (ft::lexicographic-< '(a) '(b)))
  (is (not (ft::lexicographic-< '(b) '(a))))
  (is (ft::lexicographic-< '(a) '(0)))
  (is (not (ft::lexicographic-< '(0) '(a))))
  (is (not (ft::lexicographic-< '(a) '(a)))))

(deftest make-node.1 ()
  (is (not (convert 'node-with-data nil)))
  (is (typep (convert 'node-with-data '(:a)) 'node))
  (is (null (transform (convert 'node-with-data '(:b (:c))))))
  (is (equal (convert 'list (convert 'node-with-data '(:a))) '(:a))))

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
         (pt (make-instance 'ft::path-transform
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
        (is (equal (convert 'list f6) (fourth l2)))))

    ))

(deftest transform-path.2 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:c (:x))))
         (node1 (convert 'node-with-data l1))
         (pt (make-instance 'ft::path-transform
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
        (is (equal (convert 'list f6) (second l2)))))
    ))


(deftest transform-path.3 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:z) (:x) (:y))))
         (node1 (convert 'node-with-data l1))
         (pt (make-instance 'ft::path-transform
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
        (is (equal (convert 'list f6) (third (fourth l2))))))
    ))

;;; Tests of ft::path-transform-of, update-tree

(deftest update-tree.1 ()
    (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
           (n2 (update-tree-at-data n1 :c)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n1) (convert 'list n2)))))

(deftest update-tree.2 ()
    (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
           (n2 (update-tree-at-data n1 :c)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n1) (convert 'list n2)))))

(deftest update-tree.3 ()
    (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
           (n2 (remove-if
                (lambda (n)
                  (etypecase n
                    (node-with-data (eql (data n) :c))
                    (symbol (eql n :c)))) n1)))
      (is (not (eql n1 n2)))
      (is (equal (convert 'list n2) '(:a (:b) (:d))))))

(deftest update-tree.4 ()
    (let* ((n1 (convert 'node-with-data '(:a (:b) (:c) (:d))))
           (n2 (@ n1 '(1)))
           (n3 (@ n1 '(2)))
           (n4 (swap-nodes n1 n2 n3)))
      (is (not (eql n1 n4)))
      (is (equal (convert 'list n4) '(:a (:b) (:d) (:c))))
      ))

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
    (is (handler-case (progn (ft::path-of-node n2 n1) nil)
          (error () t)))
    (is (equal (ft::path-of-node n2 (second (children n2))) '(1)))
    (is (equal (ft::path-of-node n1 n1) nil))
    (is (equal (ft::path-of-node n2 (third (children (second (children n2)))))
               '(1 2)))))

(deftest node-can-implant.1 ()
  (let* ((n1 (convert 'node-with-data '(:a (:b) (:b (:c) (:d) (:e)) (:d))))
         (n2 (second (children n1)))
         (n3 (third (children n1))))
    (is (ft::node-can-implant n1 n1 n1))
    (is (ft::node-can-implant n1 n2 n2))
    (is (not (ft::node-can-implant n1 n2 n1)))
    (is (not (ft::node-can-implant n1 n2 n3)))))

(deftest path-p.1 ()
  (is (ft::path-p '()))
  (is (ft::path-p '((1 2))))
  (is (not (ft::path-p '((2 1)))))
  (is (ft::path-p '(0 1 2)))
  (is (not (ft::path-p '(-1))))
  (is (not (ft::path-p '(-1 1)))))

(deftest path.1 ()
  (is (typep '() 'path))
  (is (typep '((1 2)) 'path))
  (is (not (typep '((2 1)) 'path)))
  (is (typep '(0 1 2) 'path))
  (is (not (typep '(-1) 'path)))
  (is (not (typep '(-1 1) 'path))))

(deftest node-valid.1 ()
  (is (ft::node-valid (convert 'node-with-data '(:a))))
  (is (ft::node-valid (convert 'node-with-data '(:a (:a) (:b)))))
  (is (not (ft::node-valid
            (let ((n (convert 'node-with-data '(:a))))
              (convert 'node-with-data `(:b ,n ,n)))))))

(deftest nodes-disjoint.1 ()
  (is (ft::nodes-disjoint (convert 'node-with-data '(:a)) (convert 'node-with-data '(:b))))
  (is (ft::nodes-disjoint (convert 'node-with-data '(:a)) (convert 'node-with-data '(:a))))
  (is (ft::nodes-disjoint (convert 'node-with-data '(:a (:b))) (convert 'node-with-data '(:a (:b)))))
  (let ((n (convert 'node-with-data '(:a))))
    (is (not (ft::nodes-disjoint n n))))
  (let ((n (convert 'node-with-data '(:a))))
    (is (not (ft::nodes-disjoint (convert 'node-with-data `(:b ,n))
                             (convert 'node-with-data `(:c ,n))))))
  (let* ((n (convert 'node-with-data '(:a)))
         (n2 (copy n :data :b)))
    (is (not (ft::nodes-disjoint (convert 'node-with-data `(:c ,n))
                             (convert 'node-with-data `(:d ,n2)))))))

;;; Note that NODE-EQUALP is comparing by ft::serial-number, not by data
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
    (is (not (node-equalp n (copy n :children (list (convert 'node-with-data '(:b))))))))
  (let ((n (convert 'node-with-data '(:a (:b)))))
    (is (node-equalp n
                       (copy n
                             :children
                             (list (copy (car (children n))
                                         :data :c)))))
    (is (not (node-equalp n
                            (copy n :children (list (convert 'node-with-data '(:c)))))))))


(deftest print.1 ()
  (let ((*print-readably* nil)
        (n1 (convert 'node-with-data '(:a)))
        (t1 (convert 'node-with-data '(:a))))
    (is (stringp (with-output-to-string (s) (prin1 (convert 'node-with-data '(:a)) s))))
    (is (stringp (with-output-to-string (s) (prin1 (ft::path-transform-of n1 n1) s))))
    (is (stringp (with-output-to-string (s) (prin1 (finger t1) s))))))

(deftest print.2 ()
  (let ((*print-readably* t)
        (n1 (convert 'node-with-data '(:a)))
        (t1 (convert 'node-with-data '(:a))))
    (flet ((%e (v)
             (handler-case (progn (prin1 v) nil)
               (error () t))))
    (is (%e (convert 'node-with-data '(:a))))
    (is (%e (ft::path-transform-of n1 n1)))
    (is (%e (finger t1))))))

(defun random-test (size reps mutate-fn)
  "For REPS repetitions, generate a random tree of size
SIZE, mutate it with MUTATE-FN, then check that the path
transform from the former to the latter correctly maps
paths to the right nodes.  Return NIL on success or
diagnostic information on error or failure."
  (iter (repeat reps)
        (let* ((n1 (make-random-tree size))
               (n2 (funcall mutate-fn n1)))
          ;; FIXME: It is possible to delete the root returning a tree
          ;;        for n2 that is just nil.
          (when (and n1 n2)
            (let ((pt (ft::path-transform-of n1 n2))
                  (serial-numbers nil))
              (handler-case
                  (progn
                    (traverse-nodes n2 (lambda (n) (push (ft::serial-number n)
                                                    serial-numbers)))
                    ;; (format t "SERIAL-NUMBERS = ~a~%" serial-numbers)
                    (ft::traverse-nodes-with-rpaths
                     n1
                     (lambda (n rpath)
                       (when (member (ft::serial-number n) serial-numbers)
                         (let* ((f (make-instance 'finger
                                     :node n1 :path (reverse rpath)))
                                (n3 (@ n2 f)))
                           ;; (format t "n = ~a~% n3 = ~a~%" n n3)
                           (when (typep n3 'node)
                             (unless (eql (ft::serial-number n)
                                          (ft::serial-number n3))
                               (return-from random-test
                                 (list n1 n2 n3 n (ft::serial-number n)
                                       (ft::serial-number n3)))))))
                       t)))
                (error (e)
                  (return-from random-test
                    (list n1 n2 pt e))))))))
  nil)

(defun remove-nodes-randomly (root p)
  "Remove nodes from tree with probability p"
  (assert (typep p '(real 0)))
  (remove-if (lambda (n) (declare (ignore n)) (<= (random 1.0) p)) root))

(deftest swap.1 ()
  (let* ((l1 '(:i 17 17 (:d 26) (:m (:b 54 84))))
         (n1 (convert 'node-with-data l1))
         (n2 (@ n1 '(2)))
         (n3 (@ n1 '(3 0)))
         (n4 (swap-nodes n1 n2 n3)))
    (is (equal (transform n1) nil))
    (is (typep (transform n4) 'ft::path-transform))
    (is (equal (convert 'list n1) l1))
    (is (equal (convert 'list n2) '(:d 26)))
    (is (equal (convert 'list n3) '(:b 54 84)))
    (is (equal (convert 'list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    (let ((f1 (make-instance 'finger :node n1 :path '(2))))
      ;; (format t "(@ n4 f1) ==> ~a~%" (@ n4 f1))
      ;; (format t "n2 ==> ~a~%" n2)
      (is (equal (ft::serial-number (@ n4 f1)) (ft::serial-number n2))))
    (let ((f2 (make-instance 'finger :node n1 :path'(3 0))))
      (is (equal (ft::serial-number (@ n4 f2)) (ft::serial-number n3))))
    ))

#+known-failure  ; TODO: Can't handle deleted root node (whole tree).
(deftest random.1 ()
  ;; Randomized test of path transforms
  (is (equal (random-test 20 200 (lambda (n) (remove-nodes-randomly n 0.2))) nil)))

(deftest random.2 ()
  (let ((result :pass)
        (size 50))
    (iter (repeat 1000)
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
                   (is (ft::path-p p))
                   (is (typep p 'path))
                   (is (eql (@ root p) n))
                   (is (equal (ft::path-of-node root n) p))))
               t))))
      (is (equal result :pass))))

(deftest random.3 ()
  (is (equal (random-test 20 1000 (lambda (n)
                                    (iter (repeat (1+ (random 4)))
                                          (setf n (swap-random-nodes n)))
                                    n))
             nil)))

(deftest path-transform-compress-mapping.1 ()
  (let ((mapping '((nil nil) ((0) (2 0)) ((1) (0 1))
                   ((2) (2)) ;; This is dominated by (nil nil)
                   ((2 0) (0)) ((2 0 1) (1)))))
    (is (equal (ft::path-transform-compress-mapping mapping)
               '(((2 0 1) (1))
                 ((2 0) (0))
                 ((1) (0 1))
                 ((0) (2 0))
                 (nil nil))))))

;;; Tests of subclass of NODE with discrete fields

(deftest node-with-fields.1 ()
  (let ((n (make-instance 'node-with-fields :a 1 :b 2 :data :foo
                          :children '(3))))
    (is (equal (convert 'list n) '((:data :foo :a 1 :b 2) 3)))
    (is (equal (@ n :a) 1))
    (is (equal (@ n :b) 2))
    (is (equal (@ n 0) 3))))

(deftest node-with-fields.2 ()
  (let ((n (convert 'node-with-fields '(1))))
    (is (equal (node-a n) nil))
    (is (equal (node-b n) nil))
    (is (equal (children n) nil))))

(deftest node-with-fields.3 ()
  (let ((n (convert 'node-with-fields '(:foo :a 1 :b 2 3 4 5))))
    (is (equal (node-a n) 1))
    (is (equal (node-b n) 2))
    (is (equalp (children n) '(3 4 5)))))

(deftest node-with-fields.4 ()
  (let* ((n (convert 'node-with-fields '(:foo
                         :a (:bar :a :n2 :b 1)
                         :b (:baz :a :n3 :b 2))))
         (n4 (update-tree-at-data n :bar))
         (n5 (convert 'node-with-fields '(:qux :n5 5)))
         (n6 (update-tree n (lambda (x)
                              (if (and (typep x 'node) (eql (node-a x) :n3)) n5 x)))))
    (is (equal (convert 'list n) '((:data :foo
                                    :a ((:data :bar :a :n2 :b 1))
                                    :b ((:data :baz :a :n3 :b 2))))))
    (is (equal (convert 'list n4) '((:data :foo
                                     :a ((:data :bar :a :n2 :b 1))
                                     :b ((:data :baz :a :n3 :b 2))))))
    (is (equal (convert 'list n6) '((:data :foo :a
                                     ((:data :bar :a :n2 :b 1)) :b
                                     ((:data :qux) :n5 5)))))))

(defsuite ft-fset-tests "Functional tree FSET tests")

(deftest reduce-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (reduce #'+ (iota 10)) (reduce #'+ tree)))))

(deftest find-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find 4 tree) 4))
    (is (not (find 10 tree)))))

(deftest find-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find-if «and [#'zerop {mod _ 3}] {< 4 }» tree) 6))
    (is (not (find-if (constantly nil) tree)))))

(deftest count-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count 3 tree) 1))))

(deftest count-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count-if [#'zerop {mod _ 3}] tree) 3))
    (is (zerop (count-if (constantly nil) tree)))))

(deftest position-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (is (equalp (position 4 tree) '(2)))
    (is (equalp (position 11 tree) '(4 0 0)))
    (is (not (position 12 tree)))))

(deftest position-if-tree ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
    (is (= (@ tree (position-if «and [#'zerop {mod _ 3}] {< 4 }» tree)) 6))
    (is (not (position-if (constantly nil) tree)))))

(deftest remove-tree ()
  (is (= (length (convert 'list (remove 24 (convert 'node-with-data (iota 100)))))
         99)))

(deftest remove-tree-if ()
  ;; NOTE: Counterintuitively, because the "0" node is the parent of
  ;; the rest of the tree.
  (is (zerop (length (convert 'list (remove-if #'evenp (convert 'node-with-data (iota 100)))))))
  (is (= 50 (length (convert 'list (remove-if #'oddp (convert 'node-with-data (iota 100))))))))

(deftest substitute-test ()
  (let ((no-twenty (substitute 40 20 (convert 'node-with-data (iota 100)))))
    (is (= 0 (count 20 no-twenty)))
    (is (= 2 (count 40 no-twenty)))))

(deftest substitute-if-test ()
  (let ((no-odd (substitute-if :odd #'oddp (convert 'node-with-data (iota 100)))))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd)))
    (is (= 50 (count :odd no-odd)))))

(deftest with-test ()
  (let ((two-fives (with (convert 'node-with-data (iota 10)) '(2) 5)))
    (is (= 2 (count 5 two-fives)))
    (is (zerop (count 3 two-fives))))
  ;; Should replace (5 6 7 8) with :TOUCHED.
  (is (= 6 (length (flatten (convert 'list
                             (with (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))
                                   '(3) :touched))))))
  ;; Should replace 6 with :TOUCHED.
  (is (= 9 (length (flatten (convert 'list
                             (with (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))
                                   '(3 0) :touched)))))))

(deftest less-test ()
  (let ((no-threes (less (convert 'node-with-data (iota 10)) '(2))))
    (is (zerop (count 3 no-threes)))
    (is (= 9 (length (convert 'list no-threes))))))

(deftest @-test ()
  (let ((tree (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (((9)))))))
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
                   (position '= it))))))

(deftest splice-test ()
  (let ((it (convert 'node-with-data '(0 1 2 3 4))))
    (is (equalp (convert 'list (splice it '(1) '(:a :b :c)))
                '(0 1 :a :b :c 2 3 4)))))

(deftest insert-test ()
  (let ((it (convert 'node-with-data '(0 1 2 3 4))))
    (is (equalp (convert 'list (insert it '(1) ':a))
                '(0 1 :a 2 3 4)))))

(deftest conversion-to-node-with-data ()
  (is (= 3 (nest (count :data)
                 (flatten)
                 (convert 'alist)
                 (convert 'node-with-data)
                 '(1 2 3 4 (5 6 7 8) (9 10))))))
