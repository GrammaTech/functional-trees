# Proposal

This file describes a proposed redesign to simplify and improve
functional-trees.  The basic idea is to have the set of serial
numbers below each node be available at that node.  Getting this
to work efficiently require some work, which I will describe.

## Basic Idea

At each node n, there will be a set or map (desc n), which is the set
of all nodes in the tree, indexed by their serial numbers.  We may
attach additional information here (so the set is a map).

## Benefits

We can determine if a node with a given serial number is already
in a subtree rooted at any other given node.

Given a serial number, we can find the path from the root to
the node with that serial number repeatedly finding the child
of the current node that has that serial number in its desc set.
Therefore, there is no need to have retain and transform paths.
Fingers are not needed.

## Obstacles

The sets cannot be updated destructively if old versions of the trees
are to be retained (that is, if they are functional).

Transplanting and entire subtree may cause O(size of subtree) updates
to the sets of all the ancestors.  It would be very helpful if these
updates can commonly be done in less time than that.

## Design

The map at each node will be from serial number to a child label of
the subtree that has that serial number.  The serial number of the
root of the subtree is not included in the map, but can be found
directly from the node.

It will often be the case that the serial numbers of nodes in a
subtree are consecutive integers.  In particular, in a freshly
allocated or copied tree this will be true for all subtrees (including
the entire tree).  Therefore, the representation will be optimized so
that subsequences that map to the same child label will be stored as a
single thing.  This can be done with balanced trees, and balanced
trees can be implemented functionally.

(Possible alternative: map to the serial number of a child, not to the
child label.  This would make changing the tree possibly faster, but
would slow down the case of looking up a node in the tree.  I feel
this is likely not a good tradeoff.)

If a subtree is sufficiently small, don't store these sets at all, and
do the operations by just traversing the tree.  This can save most of
the space needed to represent these sets, and won't cost very much
because traversing small subtrees is relatively cheap.  There will be
a size cutoff constant indicating when this happens.

(As implemented, instead of omitting subtrees for small nodes, we uses a different representation for them – a sorted vector. Entirely omitting an index is undesirable, because we want to be able to do fast collision checking when copying a node. Using sorted vectors enables both fast lookups, using bisection, and fast collision checks.)

Even without the size cutoff, if all labels are sequentially (in a
newly allocated tree) then the set at a given node will have size
proportional to its number of children.  The total extra size over the
tree will be proportional to the number of nodes.  So, this increases
the memory used by a constant factor.  The memory used increases if
changes to the tree begin to break sequentiality, but the extra space
will be O((depth)(number of new node serial number sequences)) added,
which should be small.  Copying a tree (getting new serial numbers)
will reset the space back to zero, at the cost of losing connection to
the previous serial numbers.

Note that a subtree is entirely self contained.

## Operations to be Performed During Tree Updates

When a node is replaced with another node:

- Find the serial number intervals for the old node, and the new node.

- Compute the serial number intervals that were removed, and the
  intervals added.

- Copy all the ancestors, updating their maps to remove the removed
  intervals and add the added intervals.  This will take time
  O((depth)(#of changed intervals) log(# of children)).

- If, during this process, we find any serial number in an added
  interval maps to two different child labels, or is equal to the
  serial number of an ancestor, then we have found a duplicate serial
  number and will signal an error.

- When a duplicate is found after a replacement, there should be a
  way to change the replacement subtree to copy the duplicated nodes
  and restart with the cleansed tree.

When a node is inserted or deleted, we may also have to change some of
the child labels in the parent's map.

The map at a node will, in the initial case, have size (in number of
intervals stored) equal to the number of children of the node.  In
most cases, it's likely to be efficient to just store it as a list or
vector.  For nodes with many children, a balanced tree can be used.

## Path Stuff Goes Away

Paths will remain as arguments to @ and lookup, but otherwise will
have no place in the internals.  Instead, nodes will be looked up
by their serial numbers.







