(defsystem "functional-trees"
  :author "GrammaTech"
  :licence "GPL V3"
  :description "prototype for functional manipulation of trees"
  :long-description "Prototype for a system that allows walking
and rewriting of parts of trees in a functional manner, along
with translation of references to internal nodes that can be carried
from one tree to its successors"
  :version "0.0.0"
  :depends-on (functional-trees/functional-trees)
  :class :package-inferred-system
  :defsystem-depends-on (:asdf-package-system)
  :in-order-to ((test-op (test-op "functional-trees/test"))))

(register-system-packages
 "functional-trees/functional-trees"
 '(:functional-trees))

;;;; Tests and binaries.
(defsystem "functional-trees/test"
  :author "GrammaTech"
  :licence "GPL V3"
  :description "Test the FUNCTIONAL-TREES package."
  :version "0.0.0"
  :perform
  (test-op (o c) (symbol-call :functional-trees/test '#:run-batch)))
