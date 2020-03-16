Functional Trees
================

A system that allows walking and rewriting of parts of trees in a
functional manner, along with translation of references to internal
nodes that can be carried from one tree to its successors.

Implemented in a manner that is compatible with and depends upon FSet.

## Design and Usage

### Sub-classing the `node` class
In most cases it is likely that one would subclass the `node` class
provided by this package.  Any subclass of `node` can specify which of
its slots might hold subtrees by defining a `child-slots` slot which
should be initialized to hold the names of these fields and should be
allocated on the class itself.  See the following example.

```lisp
(defclass if-then-else-node (node)
  ((child-slots :initform '((then . 1) else) :allocation :class)
   (then :reader then :type node)
   (else :reader else :type '(list node)))
  (:documentation "An if-then-else subtree of a program AST."))
```

Each child slot should hold children nodes.  Child slots may hold a
single node or multiple nodes.  It is possible to specify the arity of
a child slot using the `child-slots` class-level field.  This changes
the behavior of relevant generic functions.  E.g., the `then` slot in
`if-then-else-node` above holds a single node child while the `else`
slot may hold a list of any number of children.

In addition to customizing the functional-tree generic functions to
traverse your tree appropriately, defining `child-slots` will cause
the generic `children` function to be defined to return all children
of a newly defined node subclass--this is done by hooking the MOP
sub-class finalization process for sub-classes of `node`.

### Default data access
In some cases it may be useful to identify a slot which by default
holds the data for a node.  This can be specified by defining the
`data-slot` slot on your node subclass, which similarly should be
stored on the class instance.

```lisp
(defclass node-with-data (node)
  ((children :reader children
             :type list
             :initarg :children
             :initform nil
             :documentation "The list of children of the node,
which may be more nodes, or other values.")
   (child-slots :initform '(children) :allocation :class)
   (data-slot :initform 'data :allocation :class)
   (data :reader data :initarg :data :initform nil
         :documentation "Arbitrary data")))
```

By defining `data-slot` the generic `data` function will operate on
the defined subclass.

```lisp
(let ((it (convert 'node-with-data '(1 2 3 4 (5 6 7 8) (9 (10 (11)))))))
  (list (position 8 it :key #'data)
        (@ (position 8 it :key #'data) it)))
```

## Tasks
- [X] Eliminate hard-coded children.
- [X] Address all FIXMEs
- [X] Address all #+broken
- [X] Find should return the subtree.
- [X] Define replacements for `cl:subst` and friends.
- [X] Integrate with FSet.
- [X] Define a map-tree function.
- [X] Replace `update-tree` with `map-tree`
- [X] Ensure tests provide good coverage.
- [X] Integrate with GMap.
- [ ] Automatically define `convert` methods for subclasses of node.
- [X] Consider hooking into the class definition mechanisms with the
      MOP to define copy-based setf setters for all fields on any
      child of a node.
- [X] Eliminate 'data' as default key in trees.
- [X] Make default equality test in tree methods be EQL, as on sequences.
- [ ] Add :START, :END for tree methods, where these are paths not integers.
- [ ] Back pointer to previous tree versions should be weak, if that is supported.
- [ ] Define copying setf expanders for non-class-allocated slots of node subclasses.
- [ ] Make trie maps switch to hash tables if the branching is too large (efficiency.)
- [ ] Cache PATH-TRANSFORM-OF.
- [ ] Enhance path transform compression so paths that differ only in the final
      index  are compressed into "range" paths.
- [ ] Splice should report error on nodes of fixed arity.