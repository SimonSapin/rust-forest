rust-forest
===========

Various implementation strategies for “DOM-like” tree data structures in Rust.

“DOM-like” here means that data structures can be used to represent
the parsed content of an HTML or XML document,
like [*the* DOM](https://dom.spec.whatwg.org/) does,
but don’t necessarily have the exact same API as the DOM.
That is:

* A tree is made up of nodes.
* Each node has zero or more *child* nodes, which are ordered.
* Each node has a no more than one *parent*, the node that it is a *child* of.
* A node without a *parent* is called a *root*.
* As a consequence, each node may also have *siblings*: its *parent*’s other *children*, if any.
* From any given node, access to its
  parent, previous sibling, next sibling, first child, and last child (if any)
  can take no more than *O(1)* time.
* Each node also has data associated to it,
  which for the purpose of this project is purely generic.
  For an HTML document, the data would be either the text of a text node,
  or the name and attributes of an element node.
* The tree is mutable:
  nodes (with their sub-trees) can be inserted or removed anywhere in the tree.

In particular, the need to access parents means we can not use the obvious structure
of child nodes being *owned* directly by their parent:

```rust
struct Node<T> {
    data: T,
    children: Vec<Node<T>>,
    parent: /* ??? */
}
```

More generally, a tree with parent and sibling relationships (in addition to children relationships)
can be viewed as a graph of aspecial kind, but still a graph that contains cycles.
And Rust’s default ownership model does not support cycles easily.
Therefore, we need a more involved strategy to manage the lifetime of nodes.

In [Servo](https://github.com/servo/servo/),
[DOM nodes are managed by the JavaScript garbage collector](
https://blog.mozilla.org/research/2014/08/26/javascript-servos-only-garbage-collector/).
Rust however currently does not have a tracing garbage collector of its own,
and many Rust projects might want to manipulate DOM-like trees
without embedding an entire JavaScript virtual machine.

This repository contains multiple crates that each implement a DOM-like data structure
with a different approach and different trade-offs.


`rctree`
--------

The lifetime of nodes is managed through *reference counting*.
To avoid reference cycles which would cause memory leaks, the tree is *asymmetric*:
each node holds optional *strong references* to its next sibling and first child,
but only optional *weak references* to its parent, previous sibling, and last child.

Nodes are destroyed as soon as there is no strong reference left to them.
The structure is such that holding a reference to the root
is sufficient to keep the entire tree alive.
However, if for example the only reference that exists from outside the tree
is one that you use to traverse it,
you will not be able to go back “up” the tree to ancestors and previous siblings after going “down”,
as those nodes will have been destroyed.

Weak references to destroyed nodes are treated as if they were not set at all.
(E.g. a node can become a root when its parent is destroyed.)

Since nodes are *aliased* (have multiple references to them),
[`RefCell`](http://doc.rust-lang.org/std/cell/index.html) is used for interior mutability.

Advantages:

* A single `NodeRef` user-visible type to manipulate the tree, with methods
* Memory is freed as soon as it becomes unused (if parts of the tree are removed).

Disadvantages:

* The tree can only be accessed from the thread is was created in.
* Any tree manipulation, including read-only traversals,
  requires incrementing and decrementing reference counts,
  which causes run-time overhead
* Nodes are allocated individually, which may cause memory fragmentation and hurt performance.


`arena-tree`
------------

The lifetime of nodes is managed through an *arena allocator*.

Nodes are tied, through `&'a T` references, to the lifetime of the arena
and are destroyed all at once when the arena is destroyed.
The links between nodes are also `&'a T` references internally.

Since nodes are *aliased* (have multiple references to them),
`RefCell` is used for interior mutability.

Advantages:

* Nodes still have methods,
  the arena can largely be ignored during tree manipulation (as long as it’s kept alive).
* Less runtime overhead. (Allocation is fast, no reference count to increment or decrement.)
* Nodes are allocated in large, continuous chunks of memory. This helps memory cache performance.

Disadvantages:

* There is one more object (the arena) to keep around.
* The tree can only be accessed from the thread is was created in.
* Memory “leaks” when nodes are removed from the tree before the arena is destroyed.
  This can be alleviated by maintaining a *free list*
  of nodes that are not used anymore and can be reused,
  but only if these nodes have been freed explicitly.
  (Whereas reference counting and garbage collection would free unused nodes automatically.)
  But then nothing prevents references to freed nodes to be kept around.
  Another explicit mechanism (like tracking a *generation number* in each node)
  can be added to prevent (mostly) such references and accessing a freed or re-allocated node.


`idtree`
--------

Similar to `arena-tree`, buth the arena is simplified to a single `Vec`
and numerical identifiers (indices in the vector) are used instead of `&'a T` references.

Advantages:

* There is no `RefCell`, mutability is handled in a way much more idiomatic to Rust
  through unique (`&mut`) access to the arena.
* The tree can be sent or shared across threads like a `Vec`.
  This enables e.g. parallel tree traversals.

Disadvantages:

* Every access requires going through the arena, which can be cumbersome.
* There is some runtime overhead over `arena-tree` because of bound checks.
* A node ID from a given arena can be used in a different arena,
  which is likely to not cause an error and access an unrelated node.
