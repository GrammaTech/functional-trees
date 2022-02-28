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
  CHILD-SLOT-SPECIFIERS          = #<unbound slot>
Slots with :INSTANCE allocation:
  DESCENDANT-MAP                 = #<unbound slot>
  SERIAL-NUMBER                  = 0
  SIZE                           = #<unbound slot>
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
(ft:define-node-class if-then-else-node (ft:node)
  ((ft:child-slots :initform '((then . 1) else) :allocation :class)
   (then :reader then :initarg :then :type ft:node)
   (else :reader else :initarg :else :type list))
  (:documentation "An if-then-else subtree of a program AST."))
```

Note that we used `ft:define-node-class` instead of just `defclass`. The latter
would work, but the former also sets up some additional useful infrastructure
for our new `node` subclass. This infrastructure is already defined generically
for all nodes, but the `ft:define-node-class` macro defines it more efficiently
for a specific class of nodes.

Note also that the `:initarg` keywords for `then` and `else` are necessary, as
they are used by automatic tree-copying functions in this library. If they are
omitted, many functions (including the FSet generic sequence transformation
functions described below) will not work properly.

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
according to the order of the `child-slots` list:

```lisp
(ft:children (make-instance 'if-then-else-node
                            :else '(:foo :bar)
                            :then :baz))
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

The reason we don't have referential transparency is that each newly created
`node` has a unique serial number:

```lisp
(ft::serial-number (make-instance 'ft:node))
```
```
2
```

These serial numbers increase monotonically, and are used internally in the
library for various algorithmic tasks. One important thing to note is that these
serial numbers must be unique in any given tree in addition to being unique per
node. That is, if you transform a tree by copying one of its subtrees to another
location in the tree, you must clone that entire subtree to ensure that the new
tree does not contain any duplicate serial numbers.

### Constructing trees

As the above examples show, `make-instance` is fairly barebones: it sets the
`serial-number` but not much else. Because this library incorporates FSet,
though, we can extend the generic `convert` function to provide an easier way to
construct our nodes:

```lisp
(defmethod fset:convert ((to-type (eql 'if-then-else-node)) (sequence list)
                         &key &allow-other-keys)
  (labels ((construct (form)
             (etypecase form
               (cons
                (make-instance 'if-then-else-node
                  :then (construct (first form))
                  :else (mapcar #'construct (rest form))))
               (atom
                (make-instance 'ft:node)))))
    (construct sequence)))
```

This method may be used to easily create a functional tree from a list.
```lisp
(progn (defvar my-node (fset:convert 'if-then-else-node '((nil) nil)))
       (describe my-node))
```
```
#<IF-THEN-ELSE-NODE 6 (#<IF-THEN-ELSE-NODE 4 (#1=#<NODE 3 NIL>)> #1#..
  [standard-object]

Slots with :CLASS allocation:
  CHILD-SLOTS                    = ((THEN . 1) ELSE)
  CHILD-SLOT-SPECIFIERS          = #<unbound slot>
Slots with :INSTANCE allocation:
  DESCENDANT-MAP                 = #<unbound slot>
  SERIAL-NUMBER                  = 6
  SIZE                           = #<unbound slot>
  THEN                           = #<IF-THEN-ELSE-NODE 4 (#<NODE 3 NIL>)>
  ELSE                           = (#<FUNCTIONAL-TREES:NODE 5 NIL>)
```

Now we can round-trip from a `list` to an `if-then-else-node` and
back, because this library already defines an `fset:convert` method to
convert from nodes to lists, essentially a recursive version of
`ft:children`.

```lisp
(ft::convert 'list my-node)
```
```
(#<IF-THEN-ELSE-NODE 6 (#<IF-THEN-ELSE-NODE 4 (#<NODE 3 NIL>)> #<NODE 3 NIL>
                        #<NODE 5 NIL>)>
 #<IF-THEN-ELSE-NODE 4 (#<NODE 3 NIL>)> #<FUNCTIONAL-TREES:NODE 3 NIL>
 #<FUNCTIONAL-TREES:NODE 5 NIL>)
 ```

The convert functions to and from lists may be specialized for a
particular subclass of node to achieve translation to and from
functional trees which don't lose information.  However, doing that in
general is not possible without specific knowledge of the desired tree
structure -- namely how the tree stores list *values* vs list
*strucure*.

### Transformations

This library provides `ft:node` implementations for the following generic
sequence functions from FSet:

- `reduce`
- `find-if`
- `find-if-not`
- `find`
- `count-if`
- `count-if-not`
- `count`
- `position-if`
- `position-if-not`
- `position`
- `remove-if`
- `remove-if-not`
- `remove`
- `substitute-if`
- `substitute-if-not`
- `substitute`

It also provides a couple additional generic methods, also with implementations
for `ft:node`:

- `mapc` takes as arguments a function and a node, respectively. It calls the
  given function on every node in the tree of the given node, and then returns
  `nil`.

- `mapcar` does the same thing as `mapc`, except that it constructs a new tree
  from the results of all those function calls, and returns the newly
  constructed tree.

  For example, we could expand an `if-then-else-node` by adding an extra
  `ft:node` to every `else` branch:

  ```lisp
  (progn
    (defvar expanded
      (ft:mapcar (lambda (n)
                   (if (typep n 'if-then-else-node)
                       (make-instance 'if-then-else-node
                                      :then (then n)
                                      :else (list* (make-instance 'ft:node)
                                                   (else n)))
                       n))
                 my-node))
    (describe expanded))
  ```
  ```
  #<IF-THEN-ELSE-NODE 8 (#<IF-THEN-ELSE-NODE 10 (#1=#<NODE 3 NIL>..
    [standard-object]

  Slots with :CLASS allocation:
    CHILD-SLOTS                    = ((THEN . 1) ELSE)
    CHILD-SLOT-SPECIFIERS          = (#<FUNCTIONAL-TREES::SLOT-SPECIFIER THEN 1>..
  Slots with :INSTANCE allocation:
    DESCENDANT-MAP                 = #<3=>THEN,5=>ELSE,7=>ELSE,8=>NIL,[9,10]=>THEN>
    SERIAL-NUMBER                  = 8
    SIZE                           = #<unbound slot>
    THEN                           = #<IF-THEN-ELSE-NODE 10 (#<NODE 3 NIL> #<NODE 9 NIL>)>
    ELSE                           = (#<FUNCTIONAL-TREES:NODE 7 NIL> #<FUNCTIONAL-TREES:NODE 5 NIL>)
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
- [ ] Automatically define `convert` methods for subclasses of node.
- [X] Consider hooking into the class definition mechanisms with the
      MOP to define copy-based setf setters for all fields on any
      child of a node.
- [X] Eliminate 'data' as default key in trees.
- [X] Make default equality test in tree methods be EQL, as on sequences.
- [ ] Add :START, :END for tree methods, where these are paths not integers.
- [ ] Define copying setf expanders for non-class-allocated slots of node subclasses.
- [ ] Make trie maps switch to hash tables if the branching is too large (efficiency.)
- [ ] Splice should report error on nodes of fixed arity.
