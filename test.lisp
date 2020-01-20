(defpackage :functional-trees/test
  (:nicknames :ft/test)
  (:use :cl :functional-trees/functional-trees
        :alexandria
        :named-readtables
        :curry-compose-reader-macros
        :software-evolution-library/stefil-plus
        :iterate)
  (:import-from :fset :@)
  (:import-from :functional-trees/functional-trees
                :copy :finger :make-tree
                :make-random-tree
                :remove-nodes-randomly
                :swap-random-nodes
                :path-of-node
                :path :path-p :node-valid
                :nodes-disjoint
                :lexicographic-<
                :compare-nodes
                :node-can-implant
                :path-transform-compress-mapping)
  (:shadowing-import-from :functional-trees/fset
                          :with :less
                          :reduce
                          :find :find-if :find-if-not
                          :count :count-if :count-if-not
                          :position :position-if :position-if-not
                          :remove :remove-if :remove-if-not
                          :substitute :substitute-if :substitute-if-not)
  (:export test))
(in-package :ft/test)
(in-readtable :curry-compose-reader-macros)

(defroot test)
(defsuite ft-tests "Functional tree tests")

(deftest lexicographic-<.1 ()
  (is (not (lexicographic-< nil nil)))
  (is (not (lexicographic-< '(1) nil)))
  (is (not (lexicographic-< '(1) '(0))))
  (is (not (lexicographic-< '(1 2 3 0) '(1 2 3))))
  (is (not (lexicographic-< '(1) '(1))))
  (is (lexicographic-< nil '(1)))
  (is (lexicographic-< '(0) '(1)))
  (is (lexicographic-< '(1 2 3) '(1 2 3 0))))

(deftest make-node.1 ()
  (is (not (make-node nil)))
  (is (typep (make-node '(:a)) 'node))
  (is (null (transform (make-node '(:b (:c))))))
  (is (equal (to-list (make-node '(:a))) '(:a))))

(deftest finger.1 ()
  (let* ((init-list '(:a "ab" (:b) "xy" (:c (:d) #\Z (:e "!"))))
         (node (make-node init-list)))
    (is (equal (to-list node) init-list))
    (flet ((%f (path)
             (to-list (make-instance 'finger :node node
                                     :path path :residue nil))))
      (is (equal (%f nil) init-list))
      (is (equal (%f '(0)) (cadr init-list)))
      (is (equal (%f '(1)) (caddr init-list)))
      (is (equal (%f '(3 0)) (second (fifth init-list))))
      )))

(deftest transform-path.1 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:x))))
         (node1 (make-node l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((1) (2) :live))))
         (node2 (make-node l2 :transform pt)))

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (to-list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (to-list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (to-list f3) (cadr l1)))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '(0)))
        (is (null (residue f4)))
        (is (equal (to-list f4) (cadr l2)))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1))))
      (is (equal (path f5) '(1)))
      (is (equal (to-list f5) (third l1)))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(2)))
        (is (null (residue f6)))
        (is (equal (to-list f6) (fourth l2)))))

    ))

(deftest transform-path.2 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:c (:x))))
         (node1 (make-node l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((0) nil :dead)
                                          ((1) (0) :live))))
         (node2 (make-node l2 :transform pt)))

    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (to-list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (to-list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (to-list f3) (cadr l1)))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (null (path f4)))
        (is (equal (residue f4) '(0)))
        (is (equal (to-list f4) l2))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1))))
      (is (equal (path f5) '(1)))
      (is (equal (to-list f5) (third l1)))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(0)))
        (is (null (residue f6)))
        (is (equal (to-list f6) (second l2)))))
    ))


(deftest transform-path.3 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:z) (:x) (:y))))
         (node1 (make-node l1))
         (pt (make-instance 'path-transform
                            :from node1
                            :transforms '(((1 0) (2 1) :live)
                                          ((1) (2) :live))))
         (node2 (make-node l2 :transform pt)))
    (let ((f1 (make-instance 'finger :node node1 :path nil)))
      (is (null (path f1)))
      (is (equal (to-list f1) l1))
      (let ((f2 (transform-finger-to f1 pt node2)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (to-list f2) l2))))

    (let ((f3 (make-instance 'finger :node node1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (to-list f3) (cadr l1)))
      (let ((f4 (transform-finger-to f3 pt node2)))
        (is (equal (path f4) '(0)))
        (is (null (residue f4)))
        (is (equal (to-list f4) (cadr l2)))))

    (let ((f5 (make-instance 'finger :node node1 :path '(1 0))))
      (is (equal (path f5) '(1 0)))
      (is (equal (to-list f5) (second (third l1))))
      (let ((f6 (transform-finger-to f5 pt node2)))
        (is (equal (path f6) '(2 1)))
        (is (null (residue f6)))
        (is (equal (to-list f6) (third (fourth l2))))))
    ))

;;; Tests of path-transform-of, update-tree

(deftest update-tree.1 ()
    (let* ((n1 (make-node '(:a (:b) (:c) (:d))))
           (n2 (update-tree-at-data n1 :c)))
      (is (not (eql n1 n2)))
      (is (equal (to-list n1) (to-list n2)))))

(deftest update-tree.2 ()
    (let* ((n1 (make-node '(:a (:b) (:c) (:d))))
           (n2 (update-tree-at-data n1 :c)))
      (is (not (eql n1 n2)))
      (is (equal (to-list n1) (to-list n2)))))

(deftest update-tree.3 ()
    (let* ((n1 (make-node '(:a (:b) (:c) (:d))))
           (n2 (remove-nodes-if n1 (lambda (n) (eql (data n) :c)))))
      (is (not (eql n1 n2)))
      (is (equal (to-list n2) '(:a (:b) (:d))))
      ))


(deftest update-tree.4 ()
    (let* ((n1 (make-node '(:a (:b) (:c) (:d))))
           (n2 (@ n1 '(1)))
           (n3 (@ n1 '(2)))
           (n4 (swap-nodes n1 n2 n3)))
      (is (not (eql n1 n4)))
      (is (equal (to-list n4) '(:a (:b) (:d) (:c))))
      ))

(deftest @.error ()
  (is (handler-case (progn (@ (make-node '(:a)) '(:bad)) nil)
        (error () t)))
  (is (handler-case (progn (@ (make-node '(:a)) '(-1)) nil)
        (error () t)))
  (is (handler-case (progn (@ (make-node '(:a (:b))) '(1)) nil)
        (error () t))))

(deftest path-of-node.1 ()
  (let ((n1 (make-node '(:a)))
        (n2 (make-node '(:a (:b) (:b (:c) (:d) (:e)) (:d)))))
    (is (handler-case (progn (path-of-node n2 n1) nil)
          (error () t)))
    (is (equal (path-of-node n2 (second (children n2))) '(1)))
    (is (equal (path-of-node n1 n1) nil))
    (is (equal (path-of-node n2 (third (children (second (children n2)))))
               '(1 2)))))

(deftest node-can-implant.1 ()
  (let* ((n1 (make-node '(:a (:b) (:b (:c) (:d) (:e)) (:d))))
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
  (is (node-valid (make-node '(:a))))
  (is (node-valid (make-node '(:a (:a) (:b)))))
  (is (not (node-valid
            (let ((n (make-node '(:a))))
              (make-node `(:b ,n ,n)))))))

(deftest nodes-disjoint.1 ()
  (is (nodes-disjoint (make-node '(:a)) (make-node '(:b))))
  (is (nodes-disjoint (make-node '(:a)) (make-node '(:a))))
  (is (nodes-disjoint (make-node '(:a (:b))) (make-node '(:a (:b)))))
  (let ((n (make-node '(:a))))
    (is (not (nodes-disjoint n n))))
  (let ((n (make-node '(:a))))
    (is (not (nodes-disjoint (make-node `(:b ,n))
                             (make-node `(:c ,n))))))
  (let* ((n (make-node '(:a)))
         (n2 (copy n :data :b)))
    (is (not (nodes-disjoint (make-node `(:c ,n))
                             (make-node `(:d ,n2)))))))

;;; Note that COMPARE-NODES is comparing by name, not by data
(deftest compare-nodes.1 ()
  (is (compare-nodes nil nil))
  (is (compare-nodes 1 1))
  (is (compare-nodes '(1) '(1)))
  (is (not (compare-nodes 1 2)))
  (let ((n (make-node '(:a))))
    (is (compare-nodes n n))
    (is (compare-nodes n (copy n :data :b)))
    (is (not (compare-nodes n (make-node '(:a)))))
    (is (not (compare-nodes n (make-node '(:a (:b))))))
    (is (not (compare-nodes n (copy n :children (list (make-node '(:b))))))))
  (let ((n (make-node '(:a (:b)))))
    (is (compare-nodes n
                       (copy n
                             :children
                             (list (copy (car (children n))
                                         :data :c)))))
    (is (not (compare-nodes n
                            (copy n :children (list (make-node '(:c)))))))))
  

(deftest print.1 ()
  (let ((*print-readably* nil)
        (n1 (make-node '(:a)))
        (t1 (make-tree '(:a))))
    (is (stringp (with-output-to-string (s) (prin1 (make-node '(:a)) s))))
    (is (stringp (with-output-to-string (s) (prin1 (path-transform-of n1 n1) s))))
    (is (stringp (with-output-to-string (s) (prin1 (finger t1) s))))))

(deftest print.2 ()
  (let ((*print-readably* t)
        (n1 (make-node '(:a)))
        (t1 (make-tree '(:a))))
    (flet ((%e (v)
             (handler-case (progn (prin1 v) nil)
               (error () t))))
    (is (%e (make-node '(:a))))
    (is (%e (path-transform-of n1 n1)))
    (is (%e (finger t1))))))

(defun random-test (size reps mutate-fn)
  "For REPS repetitions, generate a random tree of size
SIZE, mutate it with MUTATE-FN, then check that the path
transform from the former to the latter correctly maps
paths to the right nodes.  Return NIL on success or
diagnostic information on error or failure."
  (iter (repeat reps)
        (let* ((n1 (make-random-tree size))
               (n2 (funcall mutate-fn n1))
               (pt (path-transform-of n1 n2))
               (names nil))
          (handler-case
              (progn
                (traverse-nodes n2 (lambda (n) (push (name n) names)))
                ;; (format t "NAMES = ~a~%" names)
                (traverse-nodes-with-rpaths
                 n1
                 (lambda (n rpath)
                   (when (member (name n) names)
                     (let* ((f (make-instance 'finger
                                              :node n1 :path (reverse rpath)))
                            (n3 (@ n2 f)))
                       ;; (format t "n = ~a~% n3 = ~a~%" n n3)
                       (when (typep n3 'node)
                         (unless (eql (name n) (name n3))
                           (return-from random-test (list n1 n2 n3 n (name n) (name n3)))))))
                   t)))
            (error (e)
              (return-from random-test
                (list n1 n2 pt e))))))
  nil)

(deftest swap.1 ()
  (let* ((l1 '(:i 17 17 (:d 26) (:m (:b 54 84))))
         (n1 (make-node l1))
         (n2 (@ n1 '(2)))
         (n3 (@ n1 '(3 0)))
         (n4 (swap-nodes n1 n2 n3)))
    (is (equal (transform n1) nil))
    (is (typep (transform n4) 'path-transform))
    (is (equal (to-list n1) l1))
    (is (equal (to-list n2) '(:d 26)))
    (is (equal (to-list n3) '(:b 54 84)))
    (is (equal (to-list n4) '(:i 17 17 (:b 54 84) (:m (:d 26)))))
    (let ((f1 (make-instance 'finger :node n1 :path '(2))))
      ;; (format t "(@ n4 f1) ==> ~a~%" (@ n4 f1))
      ;; (format t "n2 ==> ~a~%" n2)
      (is (equal (name (@ n4 f1)) (name n2))))
    (let ((f2 (make-instance 'finger :node n1 :path'(3 0))))
      (is (equal (name (@ n4 f2)) (name n3))))
    ))

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
                   (is (path-p p))
                   (is (typep p 'path))
                   (is (eql (@ root p) n))
                   (is (equal (path-of-node root n) p))))
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
    (is (equal (path-transform-compress-mapping mapping)
               '(((2 0 1) (1))
                 ((2 0) (0))
                 ((1) (0 1))
                 ((0) (2 0))
                 (nil nil))))))

(defsuite ft-fset-tests "Functional tree FSET tests")

;;; TODO:
;;; 1. Implement simple tests of FSET functions.
;;;    > DONE.
;;; 2. Switch FSET implementation to using `update-tree' and `remove-node-if'.
;;;    > Actually keep implementations in fset.lisp because they have
;;;    > different semantics that might more closely match fset
;;;    > semantics.
;;; 3. Implement `with' and `less' and test both.
;;; 4. Ensure that `(setf @)' works as expected on a functional tree.

(deftest reduce-tree ()
  (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (reduce #'+ (iota 10)) (reduce #'+ tree)))))

(deftest find-tree ()
  (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find 4 tree) 4))
    (is (not (find 10 tree)))))

(deftest find-if-tree ()
  (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (find-if «and [#'zerop {mod _ 3}] {< 4 }» tree) 6))
    (is (not (find-if (constantly nil) tree)))))

(deftest count-tree ()
  (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count 3 tree) 1))))

(deftest count-if-tree ()
  (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
    (is (= (count-if [#'zerop {mod _ 3}] tree) 3))
    (is (zerop (count-if (constantly nil) tree)))))

;; (deftest position-tree ()
;;   (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
;;     (is (equalp (position 4 tree) '(2)))
;;     (is (not (position 10 tree)))))

;; (deftest position-if-tree ()
;;   (let ((tree (make-tree '(1 2 3 4 (5 6 7 8) (((9)))))))
;;     (is (= (position-if «and [#'zerop {mod _ 3}] {< 4 }» tree) 6))
;;     (is (not (position-if (constantly nil) tree)))))

(deftest remove-tree ()
  (is (= (length (to-list (remove 24 (make-tree (iota 100)))))
         99)))

(deftest remove-tree-if ()
  ;; NOTE: Counterintuitively, because the "0" node is the parent of
  ;; the rest of the tree.
  (is (zerop (length (to-list (remove-if #'evenp (make-tree (iota 100)))))))
  (is (= 50 (length (to-list (remove-if #'oddp (make-tree (iota 100))))))))

(deftest substitute-test ()
  (let ((no-twenty (substitute 40 20 (make-tree (iota 100)))))
    (is (= 0 (count 20 no-twenty)))
    (is (= 2 (count 40 no-twenty)))))

(deftest substitute-if-test ()
  (let ((no-odd (substitute-if :odd #'oddp (make-tree (iota 100)))))
    (is (= 0 (count-if «and #'numberp #'oddp» no-odd)))
    (is (= 50 (count :odd no-odd)))))

(deftest with-test ()
  (let ((two-fives (with (make-tree (iota 10)) '(2) 5)))
    (is (= 2 (count 5 two-fives)))
    (is (zerop (count 3 two-fives)))))

(deftest less-test ()
  (let ((no-threes (less (make-tree (iota 10)) '(2))))
    (is (zerop (count 3 no-threes)))
    (is (= 9 (length (to-list no-threes))))))
