(defpackage :functional-trees/sel-attributes-test
  (:nicknames :ft/sel-attributes-test :ft/sel-attrs-test)
  (:use
   :common-lisp
   :functional-trees/sel-attributes
   :alexandria
   :iterate
   :software-evolution-library/software/tree-sitter
   :software-evolution-library/software/c
   :functional-trees
   :functional-trees/attrs
   :named-readtables
   :curry-compose-reader-macros
   :named-readtables
   :stefil+)
  (:export test)
  (:shadowing-import-from
   :fset
   :map
   :convert
   :empty-map)
  (:shadowing-import-from
   :functional-trees
   :equal?
   :mapc
   :mapcar
   :subst
   :subst-if
   :subst-if-not))

(in-package :functional-trees/sel-attributes-test)
(in-readtable :curry-compose-reader-macros)

(defroot test)
(defsuite test "Tests of functional-trees/attributes on SEL trees")

(deftest sel-attrs.1 ()
  (let ((root (convert 'c-ast "int x; int y; char z;")))
    (with-attr-table root
      (is (equal? (st root (empty-map))
                  (convert 'map '(("x" . "int") ("y" . "int") ("z" . "char")))))
      (is (equal? (st root)
                  (convert 'map '(("x" . "int") ("y" . "int") ("z" . "char")))))
      (is (equal? (st (first (children root))) (empty-map)))
      (is (equal? (defs (first (children root)))
                  (convert 'map '(("x" . "int")))))
      (is (equal? (st (second (children root)))
                  (convert 'map '(("x" . "int")))))
      (is (equal? (defs (second (children root)))
                  (convert 'map '(("y" . "int")))))
      (is (equal? (st (third (children root)))
                  (convert 'map '(("x" . "int") ("y" . "int")))))
      (is (equal? (defs (third (children root)))
                  (convert 'map '(("z" . "char"))))))))


