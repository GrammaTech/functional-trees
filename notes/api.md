Comments on API for CL-like functions in Functional Trees
=========================================================

Data of nodes should not be what is handled by the functions, but
rather the nodes themselves.   This is consistent with what functions
like SUBST do on cons cell trees.   (AGREED)

-   :FROM-END

    should be interpreted as traversing the tree from right to left
    instead of the default left-to-right.   (AGREED)

-   :START
-   :END

    could be interpreted as path arguments.  Traverse all nodes/leaves
    on paths from START (inclusive) to END (exclusive).  (DELAY)

-   :KEY
-   :TEST
-   :TEST-NOT

    have the usual meanings.  All should be called on internal nodes,
    not data of internal nodes.

Additional keyword arguments:

-   :RESTRICT

    A function that is called to determine if the traversal should be
    applied to this node.  Special values are :LEAF, :NODE, T (meaning
    all, the default).  If the traversal is not applied, it may be
    applied to descendants of this node.

-   :CONTINUE

    A function that is evaluated at each internal node to determine
    if traversal should continue below it (default is (constantly t)).

-   :ORDER

    Set the order of the traversal (preorder or postorder).  Is :PRE
    or :POST (:PRE default).

Other functions
---------------

There should be a function for mapping over a tree.  Perhaps MAP but
with one argument?  I suggest it have a new name, but also apply to CL
sequences.

Invoking CL Functions
---------------------

Methods for CL classes would have a `&rest` parameter, and invoke the
CL version passing the keyword arguments that way.  Even better, in
SBCL we might want to have a `defknown` that would call the CL
function directly if the argument is known to be of the correct type.
This would eliminate performance penalty.


Additional issues for discussion
--------------------------------

When traversing a tree, we may want not just a reference to the node,
but the path to get to that node (or, a finger, which is a path +
root).

In preorder traversal, the path is no longer necessarily a good path
for the original tree, but there is not yet a root for the partially
rewritten tree.  This may mean we want to make postorder the default
(or even the only traversal mode.)

We may want to make the path in the original tree available.

Early termination of a traversal could be a good thing.  I suggest
there be a function that can be called that would do this.  It would
still allow the functional updates performed so far to be included
in the result.