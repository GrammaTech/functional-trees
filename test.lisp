(defpackage :functional-trees/test
  (:nicknames :ft/test)
  (:use :cl :functional-trees/functional-trees
        :software-evolution-library/stefil-plus
        :iterate)
  (:export test))

(in-package :ft/test)

(defroot test)
(defsuite ft-tests "Functional tree tests")

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

(deftest random.1 ()
  ;; Randomized test of path transforms
  (iter (repeat 100)
        (let* ((n1 (ft/ft::make-random-tree 10))
               (n2 (ft/ft::remove-nodes-randomly n1 0.1))
               (pt (path-transform-of n1 n2))
               (names nil))
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
                   (is (eql (name n) (name n3))))))
             t)))))
