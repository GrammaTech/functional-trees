(defpackage :functional-trees/sel-attributes
  (:nicknames :ft/sel-attributes :ft/sel-attrs)
  (:use
   :gt/full
   :functional-trees
   :functional-trees/attrs)
  (:shadowing-import-from :fset :set :map :union :empty-set :empty-map
                          :restrict)
  (:export
    :c-ast
    :c-compound-statement
    :c-declaration
    :c-identifier
    :c-primitive-type
    :c-translation-unit
    :c-type
    :st
    :defs
    :uses)
  (:documentation "Package for integration of SEL with FT attributes."))

(in-package :functional-trees/sel-attributes)

;;; Minimal AST implementation.

(define-node-class c-ast (node attrs-root)
  ((child-slots
    :allocation :class
    :initform '(children))
   (children
    :initarg :children
    :initform nil)
   (text :initarg :text :reader text)))

(define-node-class c-compound-statement (c-ast)
  ())

(define-node-class c-declaration (c-ast)
  ;; TODO Defining :c-declarator or :c-type would claim the keyword
  ;; globally for this package's symbol. See `ft::store-actual-slot'.
  ((c-declarator*
    :initarg :c-declarator*
    :reader c-declarator)
   (c-type*
    :initarg :c-type*
    :reader c-type)
   (child-slots
    :allocation :class
    :initform '(c-declarator* (c-type* . 1)))))

(define-node-class c-identifier (c-ast)
  ())

(define-node-class c-primitive-type (c-ast)
  ())

(define-node-class c-translation-unit (c-ast)
  ())

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
  (:bottom (empty-map))
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
            :initial-value in)))

(def-attr-fun defs ()
  "Map of definitions from a node"
  (:bottom (empty-map))
  (:method ((node node))
    (empty-map))
  (:method ((node c-declaration))
    (decl-map node)))

(def-attr-fun uses ()
  "Set of names that occur in a subtree"
  (:bottom (empty-set))
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
