(defpackage :functional-trees/sel-attributes
  (:nicknames :ft/sel-attributes :ft/sel-attrs)
  (:use
   :gt/full
   :software-evolution-library/software/tree-sitter
   :software-evolution-library/software/c
   :functional-trees
   :functional-trees/attrs
   :named-readtables
   :curry-compose-reader-macros
   :named-readtables)
  (:shadowing-import-from :software-evolution-library/software/parseable
                          :source-text :text)
  (:shadowing-import-from :fset :set :map :union :empty-set :empty-map
                          :restrict)
  (:export :st :defs :uses)
  (:documentation "Package for integration of SEL with FT attributes."))

(in-package :functional-trees/sel-attributes)
(in-readtable :curry-compose-reader-macros)

;;; Define a simple propagator for type information on C terms

(defun st-union (st1 st2) (fset:map-union st1 st2))
(defun st-add (st key value)
  (if key (fset:with st key value) st))

;;; There are three attr functions in this example.
;;; The first, st, is the symbol table map coming into the node.
;;; The second, defs, is the map of definitions produced by and
;;; exported by the node.
;;; The third, uses, is a set of names that occur in a subtree.

(def-attr-fun st (in)
  "Compute the symbol table at this node."
  ;; Default method: propagate down
  (:method ((node node) &optional in)
    ;; This passes the full ST down to the subtree
    ;; (mapc-attrs-children #'st (list in) node)
    ;; but this prunes off all the symbols not used in the subtree,
    ;; which may make incrementalization easier.
    (mapc (lambda (n) (st n (restrict in (uses n))))
          (children node))
    in)
  ;; Perhaps include a superclass that means definitions propagate across
  ;; the children
  (:method ((node c-compound-statement) &optional in)
    ;; Propagate across children
    (reduce (lambda (in2 child) (st-union (st child in2) (defs child)))
            (children node)
            :initial-value in)
    in)
  (:method ((node c-translation-unit) &optional in)
    ;; Propagate across children
    (reduce (lambda (in2 child) (st-union (st child in2) (defs child)))
            (children node)
            :initial-value in))
  )

(def-attr-fun defs (in)
  "Map of definitions from a node"
  (:method ((node node) &optional in)
    (empty-map))
  (:method ((node c-declaration) &optional in)
    (decl-map node))
  )

(def-attr-fun uses ()
  "Set of names that occur in a subtree"
  (:method ((node node))
    (reduce #'union (children node)
            :key #'uses :initial-value (fset:empty-set)))
  (:method ((node c-identifier))
    (fset:set (text node))))

(defgeneric decl-map (node)
  (:documentation "Construct a map that gives the declarations produced by NODE")
  ;; This is a very simple prototype, handling only simple declarations
  
  (:method ((node c-declaration))
    (let* ((type (c-type node))
           (alist
             (iter (for declarator in (c-declarator node))
                   (when-let ((name declarator))
                     (collect (cons (text name) (text type)))))))
      (convert 'fset:map alist))))
