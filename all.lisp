(uiop/package:define-package :functional-trees/all
    (:nicknames :functional-trees :ft)
  (:use-reexport :functional-trees/core :functional-trees/fset :fset)
  (:shadowing-import-from :fset :some :every :notany :notevery))
