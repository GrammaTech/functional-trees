(defpackage :functional-trees/test
  (:nicknames :ft/test)
  (:use :cl :functional-trees/functional-trees
        :software-evolution-library/stefil-plus)
  (:export))

(in-package :ft/test)

(defroot test)
(defsuite ft-tests "Functional tree tests")

(deftest make-tree.1 ()
  (is (typep (make-tree nil) 'tree))
  (is (typep (make-tree 1) 'tree))
  (is (typep (make-tree '(:a)) 'tree))
  (is (null (predecessor (make-tree '(:b (:c))))))
  (is (null (transform (make-tree '(:a)))))
  (is (equal (to-list (root (make-tree '(:a)))) '(:a))))

(deftest finger.1 ()
  (let* ((init-list '(:a "ab" (:b) "xy" (:c (:d) #\Z (:e "!"))))
         (tree (make-tree init-list)))
    (is (equal (to-list (root tree)) init-list))
    (flet ((%f (path)
             (to-list (tree-node (make-instance 'finger :tree tree
                                                :path path :residue nil)))))
      (is (equal (%f nil) init-list))
      (is (equal (%f '(0)) (cadr init-list)))
      (is (equal (%f '(1)) (caddr init-list)))
      (is (equal (%f '(3 0)) (second (fifth init-list))))
      )))

(deftest transform-path.1 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:x))))
         (tree1 (make-tree l1))
         (tree2 (make-tree l2 :predecessor tree1))
         (pt (make-instance 'path-transform
                            :from-tree tree1 :to-tree tree2
                            :transforms '(((1) (2) :live)))))
                            
    (let ((f1 (make-instance 'finger :tree tree1 :path nil)))
      (is (null (path f1)))
      (is (equal (to-list (tree-node f1)) l1))
      (let ((f2 (transform-finger f1 pt)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (to-list (tree-node f2)) l2))))

    (let ((f3 (make-instance 'finger :tree tree1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (to-list (tree-node f3)) (cadr l1)))
      (let ((f4 (transform-finger f3 pt)))
        (is (equal (path f4) '(0)))
        (is (null (residue f4)))
        (is (equal (to-list (tree-node f4)) (cadr l2)))))

    (let ((f5 (make-instance 'finger :tree tree1 :path '(1))))
      (is (equal (path f5) '(1)))
      (is (equal (to-list (tree-node f5)) (third l1)))
      (let ((f6 (transform-finger f5 pt)))
        (is (equal (path f6) '(2)))
        (is (null (residue f6)))
        (is (equal (to-list (tree-node f6)) (fourth l2)))))

    ))

(deftest transform-path.2 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:c (:x))))
         (tree1 (make-tree l1))
         (tree2 (make-tree l2 :predecessor tree1))
         (pt (make-instance 'path-transform
                            :from-tree tree1 :to-tree tree2
                            :transforms '(((0) nil :dead)
                                          ((1) (0) :live)))))
    (let ((f1 (make-instance 'finger :tree tree1 :path nil)))
      (is (null (path f1)))
      (is (equal (to-list (tree-node f1)) l1))
      (let ((f2 (transform-finger f1 pt)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (to-list (tree-node f2)) l2))))

    (let ((f3 (make-instance 'finger :tree tree1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (to-list (tree-node f3)) (cadr l1)))
      (let ((f4 (transform-finger f3 pt)))
        (is (null (path f4)))
        (is (equal (residue f4) '(0)))
        (is (equal (to-list (tree-node f4)) l2))))

    (let ((f5 (make-instance 'finger :tree tree1 :path '(1))))
      (is (equal (path f5) '(1)))
      (is (equal (to-list (tree-node f5)) (third l1)))
      (let ((f6 (transform-finger f5 pt)))
        (is (equal (path f6) '(0)))
        (is (null (residue f6)))
        (is (equal (to-list (tree-node f6)) (second l2)))))
    ))
    
                            
(deftest transform-path.3 ()
  (let* ((l1 '(:a (:b) (:c (:x))))
         (l2 '(:a (:b) (:d) (:c (:z) (:x) (:y))))
         (tree1 (make-tree l1))
         (tree2 (make-tree l2 :predecessor tree1))
         (pt (make-instance 'path-transform
                            :from-tree tree1 :to-tree tree2
                            :transforms '(((1 0) (2 1) :live)
                                          ((1) (2) :live)))))
    (let ((f1 (make-instance 'finger :tree tree1 :path nil)))
      (is (null (path f1)))
      (is (equal (to-list (tree-node f1)) l1))
      (let ((f2 (transform-finger f1 pt)))
        (is (null (path f2)))
        (is (null (residue f2)))
        (is (equal (to-list (tree-node f2)) l2))))

    (let ((f3 (make-instance 'finger :tree tree1 :path '(0))))
      (is (equal (path f3) '(0)))
      (is (equal (to-list (tree-node f3)) (cadr l1)))
      (let ((f4 (transform-finger f3 pt)))
        (is (equal (path f4) '(0)))
        (is (null (residue f4)))
        (is (equal (to-list (tree-node f4)) (cadr l2)))))

    (let ((f5 (make-instance 'finger :tree tree1 :path '(1 0))))
      (is (equal (path f5) '(1 0)))
      (is (equal (to-list (tree-node f5)) (second (third l1))))
      (let ((f6 (transform-finger f5 pt)))
        (is (equal (path f6) '(2 1)))
        (is (null (residue f6)))
        (is (equal (to-list (tree-node f6)) (third (fourth l2))))))
    ))
    
    

    
           
                 


