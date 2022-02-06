# Attributes

This is a description of a new scheme for computing attributes
on functional trees.  The new scheme relies less on explicit
representation of attributes and more on functions that compute
the values of attributes.  Attribute values will be the cached
values of these functions.  The result should be easier to use
and understand than the previous scheme, which required too much
low level plumbing.

## Overall Design

The design centers around **attribute functions**.  These are
functions on nodes that have the following properties:

- The first argument is the node to which the attribute belongs.
- The remaining arguments are optional.
- The optional arguments are values that are passed in from other nodes that are then used to compute the value of the attribute.
- The value also depends on a special variable `*root*`, which is the root of the tree in which the node resides.
- For any given value of `*root*` and any given node, the function may only be called with one set of values of its optional arguments.
- After that, calling the function returns the value(s) computed in that call (they have been cached.)
- Calling the function with no optional arguments before that is an error.
- If a function has no optional arguments, then the first time it is called
  it will be computed, and the cached value computed will be used thereafter.

## Dependencies

Attribute functions will be implemented by forms that invoke other
attribute functions -- some on the current node, and some on
descendants of the node.  The whole process is kicked off by invoking
an attribute function at the root.  For example, if we have an
attribute function returning a symbol table, we ask for the symbol
table after the root.

## Recomputation

An ultimate design goal for these attribute systems is to accelerate
recomputation of attributes.  That is, suppose we've computed the
values of some attribute functions over a tree with root R1 (which I
will just call R1 for short).  We then construct a new tree that
shares much structure with this one, and has root R2 (I will call this
tree R2).  We now want to compute the attribute functions on R2,
exploiting the computations we've already done on R1.

If an attribute is purely synthetic (is independent of anything above
the node) then its value can be reused.  Otherwise, we want to be able
to efficiently evaluate the bodies of attribute functions using knowledge
of changes in the input values.   A design goal is to support this:
the forms in the bodies should support incremental recomputation.

One way we might do this is to record, when computing some function f,
which part of one of its optional arguments it depends on.  As a
concrete example: when computing the type of an expression using a
symbol table, we record not only the type, but also what part of the
symbol table that value depends on.  When recomputing for the new tree,
if the symbol table there did not change on that part, we can skip the
recomputation on the nodes in that subtree.

## Handling of Child Slots of Arbitrary Arity

Here, we want to compute attribute functions not just on nodes, but on
cons cells of the child lists of child slots with list arity.  Here,
values computed on the car of suffix of the list can be passed to the
cdr of the list.  Special attribute functions will be defined that
take the parent node, the child slot name, and the cons cell (or null)
as required arguments (along with what optional arguments are needed.)

## Example

See sel-attributes.lisp and sel-attributes-test.lisp for a toy example
of using attributes to propagate type declarations in a very simple subset
of C.