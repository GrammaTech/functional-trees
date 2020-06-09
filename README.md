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
(ft:define-node-class if-then-else-node (ft:node)
  ((ft:child-slots :initform '((then . 1) else) :allocation :class)
   (then :reader then :initarg :then :type ft:node)
   (else :reader else :initarg :else :type '(list ft:node)))
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
according to the the order of the `child-slots` list:

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

There is one exception to this definition of immutability: fingers. As shown by
our first `node` example, the `finger` slot is initially set to `nil` when a
node is created, and should only be set by the `ft:populate-fingers` function
(see below). Thus, a more accurate version of our definition of immutability
would replace "unbound" with "`nil`" in the case of the `finger` slot.

The reason we don't have referential transparency is that each newly created
`node` has a unique serial number:

```lisp
(ft::serial-number (make-instance 'ft:node))
```
```
3
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
construct our nodes (we will discuss `ft:populate-fingers` in the next section):

```lisp
(defmethod fset:convert ((to-type (eql 'if-then-else-node)) (sequence list)
                         &key &allow-other-keys)
  (labels ((construct (form)
             (if (consp form)
                 (make-instance 'if-then-else-node
                                :then (construct (first form))
                                :else (mapcar #'construct (rest form)))
                 (make-instance 'ft:node))))
    (ft:populate-fingers (construct sequence))))
```

Now we can round-trip from a `list` to an `if-then-else-node` and back, because
this library already defines an `fset:convert` method to convert from nodes to
lists, essentially a recursive version of `ft:children`:

```lisp
(progn
  (defvar my-node (fset:convert 'if-then-else-node '((nil) nil)))
  (describe my-node)
  (fset:convert 'list my-node))
```
```
#<IF-THEN-ELSE-NODE 7 ((NIL) NIL)>
  [standard-object]

Slots with :CLASS allocation:
  CHILD-SLOTS                    = ((THEN . 1) ELSE)
Slots with :INSTANCE allocation:
  SERIAL-NUMBER                  = 7
  TRANSFORM                      = NIL
  SIZE                           = #<unbound slot>
  FINGER                         = #<FUNCTIONAL-TREES:FINGER #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)> NIL>
  THEN                           = #<IF-THEN-ELSE-NODE 5 (NIL)>
  ELSE                           = (#<FUNCTIONAL-TREES:NODE 6 NIL>)
((NIL) NIL)
```

### Fingers

In the previous example, we constructed a small tree and then called
`ft:populate-fingers` on it. Let's take a look at one of these fingers:

```lisp
(progn
  (defvar finger1 (ft:finger (then (then my-node))))
  (describe finger1))
```
```
#<FUNCTIONAL-TREES:FINGER #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)> (THEN THE..
  [standard-object]

Slots with :INSTANCE allocation:
  NODE                           = #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)>
  PATH                           = (:THEN :THEN)
  RESIDUE                        = NIL
  CACHE                          = #<unbound slot>
```

From this we can see that a finger includes a pointer to the root of a tree (in
`node`) and a `path` to another node in that tree. From these two pieces, it is
straightforward to follow `path`, starting from the root `node`, to find the
original node which held this `finger`; once this lookup has been computed once,
finger can store the resulting `node` in its `cache` slot. The `residue` relates
to path transformations, which we will discuss in the next section.

Now let's look at one more finger:

```lisp
(progn
  (defvar finger2 (ft:finger (first (else my-node))))
  (describe finger2))
```
```
#<FUNCTIONAL-TREES:FINGER #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)> (ELSE 0)>
  [standard-object]

Slots with :INSTANCE allocation:
  NODE                           = #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)>
  PATH                           = (ELSE 0)
  RESIDUE                        = NIL
  CACHE                          = #<unbound slot>
```

Because these two fingers were both created in the context of the same tree,
they both point to the same root `node`. However, this one has a different
`path` to it: we took the first node in the the `else` branch.

The `ft:populate-fingers` function produces fingers whose paths follow a
somewhat different format from the paths used in other parts of the library; see
the next section, for instance. Specifically, an `ft:populate-fingers` path is a
list where

- a keyword (e.g. `:then`) means to follow the child whose slot name is the same
  as that keyword;
- a number means that there is only one slot, so follow the child with that
  index in that one slot; and
- a non-keyword symbol followed by a number means to follow the child with the
  given number as its index, in the slot whose name is the given symbol.


Using the particular `child-slots` of our `if-then-else-node` class, we could
write a function to translate these `ft:populate-fingers` paths to simple lists
of child indices:

```lisp
(defun simplify-path (path)
  (mapcar (lambda (x)
            (if (eq x :then)
                0
                (1+ x)))
          (remove 'else path)))
```

We could then also write a function that transforms entire finger objects to use
this alternate path format:

```lisp
(defun simplify (finger)
  (with-accessors ((node ft:node)
                   (path ft:path)
                   (residue ft:residue))
      finger
    (let ((simplified (make-instance 'ft:finger
                                     :node node
                                     :path (simplify-path path)
                                     :residue residue)))
      (when (slot-boundp finger 'ft::cache)
        (setf (ft::cache simplified) (ft::cache finger)))
      simplified)))
```

A couple examples, using our existing fingers:

```lisp
(values-list (mapcar (alexandria:compose #'ft:path #'simplify)
                     (list finger1 finger2)))
```
```
(0 0)
(1)
```

Note of course that these functions would not work for `ft:populate-fingers`
paths in other node subclasses besides `if-then-else-node`.

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
  #<IF-THEN-ELSE-NODE 9 ((NIL NIL) NIL NIL)>
    [standard-object]

  Slots with :CLASS allocation:
    CHILD-SLOTS                    = ((THEN . 1) ELSE)
  Slots with :INSTANCE allocation:
    SERIAL-NUMBER                  = 9
    TRANSFORM                      = #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)>
    SIZE                           = #<unbound slot>
    FINGER                         = NIL
    THEN                           = #<IF-THEN-ELSE-NODE 11 (NIL NIL)>
    ELSE                           = (#<FUNCTIONAL-TREES:NODE 8 NIL> #<FUNCTIONAL-TREES:NODE 6 NIL>)
  ```

### Path transforms

This library differs from a naive implementation of functional trees by
efficiently handling the relationship between transformations on trees and
transformations on paths.

When you transform a tree into another tree using this library, the latter
retains knowledge of the relationship to the former (its "predecessor") via its
`transform` slot:

```lisp
(describe (ft:transform expanded))
```
```
#<FUNCTIONAL-TREES::PATH-TRANSFORM (((0 0) (0 0) LIVE) ((1) (2) LIVE))..
  [standard-object]

Slots with :INSTANCE allocation:
  FROM                           = #<IF-THEN-ELSE-NODE 7 ((NIL) NIL)>
  TRANSFORMS                     = (((0 0) (0 0) :LIVE) ((1) (2) :LIVE))
```

Here we see that `expanded` knows which tree it originally came `from` (the
predecessor), and also stores some additional `transforms` information. Since
`expanded` shares some structure with `my-node`, these `transforms` enable us to
take a path (that is, a finger) to a node in the `my-node` tree and translate it
into a path (finger) to the same node in the `expanded` tree:

```lisp
(defun show-expanded-finger (finger)
  (describe (ft:transform-finger-to (simplify finger)
                                    (ft:transform expanded)
                                    expanded)))
```

Here's an example:

```lisp
(show-expanded-finger finger1)
```
```
#<FUNCTIONAL-TREES:FINGER #<IF-THEN-ELSE-NODE 9 ((NIL NIL) NIL NIL)> (..
  [standard-object]

Slots with :INSTANCE allocation:
  NODE                           = #<IF-THEN-ELSE-NODE 9 ((NIL NIL) NIL NIL)>
  PATH                           = (0 0)
  RESIDUE                        = NIL
  CACHE                          = #<unbound slot>
```

That example isn't particularly exciting, because the path to this node is the
same as it was before: it's still just the first child of the first child. We do
see that the root `node` of the finger was changed to our new tree, though. But
we can also translate other paths:

```lisp
(show-expanded-finger finger2)
```
```
#<FUNCTIONAL-TREES:FINGER #<IF-THEN-ELSE-NODE 9 ((NIL NIL) NIL NIL)> (..
  [standard-object]

Slots with :INSTANCE allocation:
  NODE                           = #<IF-THEN-ELSE-NODE 9 ((NIL NIL) NIL NIL)>
  PATH                           = (2)
  RESIDUE                        = NIL
  CACHE                          = #<unbound slot>
```

This path actually did change, because we added an extra `ft:node` in the else
branch right before it.

This library is able to very efficiently compute these path transform objects:
it only takes time _O_(_n_ log _n_), where _n_ is the number of newly allocated
nodes in the transformed tree.

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
