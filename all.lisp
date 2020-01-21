(uiop/package:define-package :functional-trees/all
    (:nicknames :functional-trees :ft)
  (:use-reexport :functional-trees/core :functional-trees/fset :fset)
  (:shadowing-import-from :functional-trees/fset :map)
  (:shadowing-import-from :fset :some :every :notany :notevery))

;;; To include this library the following (admittedly way too verbose)
;;; `defpackage' form should serve as a model.  You probably want
;;; everything in the below included in your `defpackage' form.
;;;
;;; NOTE: I wish there was a way to define a macro or something to
;;; avoid having to copy/paste all of this boilerplate.
#+example
(defpackage :ft/user
  (:use :common-lisp :functional-trees)
  (:shadowing-import-from :functional-trees/all
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
			  :some :every :notany :notevery))
