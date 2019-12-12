(defpackage :functional-trees/test
  (:nicknames :ft/test)
  (:use :cl :functional-trees/functional-trees
        :software-evolution-library/stefil-plus)
  (:export))

(in-package :ft/test)

(defixture f1
    (:setup (setf *tree1* 
  
