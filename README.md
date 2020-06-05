Functional Trees
================

A system that allows walking and rewriting of parts of trees in a
functional manner, along with translation of references to internal
nodes that can be carried from one tree to its successors.

Implemented in a manner that is compatible with and depends upon FSet.

## Design and Usage

To start, load this library (system name `:functional-trees`) using Quicklisp:

```lisp
(ql:quickload :functional-trees)
```

This library defines one package, `:functional-trees`, which we will refer to by
its nickname `:ft`. The main thing provided by `:ft` is the `node` class, an
object of which represents a node in a tree. Here are its slots:

```lisp
(describe (make-instance 'ft:node))
```
```
#<FUNCTIONAL-TREES:NODE 0 NIL>
  [standard-object]

Slots with :CLASS allocation:
  CHILD-SLOTS                    = NIL
Slots with :INSTANCE allocation:
  SERIAL-NUMBER                  = 0
  TRANSFORM                      = NIL
  SIZE                           = #<unbound slot>
  FINGER                         = NIL
```

The `:class`-allocated `child-slots` slot holds a list of the slots that
actually hold children. Thus, since it holds the value `nil` here, we see that
the raw `ft:node` class can only really represent leaf nodes. Next we'll address
this by defining our own node class that can hold children. Afterward, we'll
discuss the other `ft:node` slots.

### Sub-classing the `node` class
In most cases it is likely that one would subclass the `node` class
provided by this package.  Any subclass of `node` can specify which of
its slots might hold subtrees by defining a `child-slots` slot which
should be initialized to hold the names of these fields and should be
allocated on the class itself.  See the following example.

```lisp
(defclass if-then-else-node (ft:node)
  ((ft:child-slots :initform '((then . 1) else) :allocation :class)
   (then :reader then :type ft:node)
   (else :reader else :type '(list ft:node)))
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

Thus if we create a node using our new class and give values to its
`child-slots`, the `children` function will return the list of those children
according to the the order of the `child-slots` list:

```lisp
(let ((my-node (make-instance 'if-then-else-node)))
  (setf (slot-value my-node 'else) '(:foo :bar))
  (setf (slot-value my-node 'then) :baz)
  (ft:children my-node))
```
```
(:BAZ :FOO :BAR)
```

(In this particular example we eschewed the `:type` annotations on the child
slots, for simplicity.)

### "Functional" and "applicative"

The word "functional" usually means multiple things:

1. Objects cannot be modified after they have been created (immutability).
2. Functions always return the same results when given the same inputs
   (referential transparency).

(Note that the second condition implies the first.) This library satisfies the
first condition but not the second, which is why we will sometimes use the word
"applicative" instead of "functional". Also, we slightly relax our definition of
immutability: because slots can be unbound, we do not consider an assignment to
an unbound slot to be a mutation of the object. So rather than immutability
meaning that the object never changes, it instead means that the object can only
ever go upward in a lattice ordered by boundness of slots.

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
- [ ] Make path transform algorithm more efficient with very long child lists.
