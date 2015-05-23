extern crate typed_arena;

use std::cell::{self, RefCell};
use std::fmt;
use std::ops::{Deref, DerefMut};


/// A reference to a node holding a value of type `T`. Nodes form a tree.
///
/// Internally, this uses `std::cell::RefCell` for interior mutability.
///
/// **Note:** Cloning a `NodeRef` only copies a pointer. It does not copy the data.
pub struct NodeRef<'a, T: 'a>(&'a RefCell<Node<'a, T>>);

struct Node<'a, T: 'a> {
    parent: Link<'a, T>,
    previous_sibling: Link<'a, T>,
    next_sibling: Link<'a, T>,
    first_child: Link<'a, T>,
    last_child: Link<'a, T>,
    data: T,
}

type Link<'a, T> = Option<&'a RefCell<Node<'a, T>>>;


/// An arena allocators for tree nodes.
///
/// Nodes are only freed when the arena is.
/// Multiple trees can be in the same arena.
pub struct Arena<'a, T: 'a>(typed_arena::Arena<RefCell<Node<'a, T>>>);

impl<'a, T> Arena<'a, T> {
    pub fn new() -> Arena<'a, T> {
        Arena(typed_arena::Arena::new())
    }

    /// Create a new node from its associated data.
    pub fn new_node(&'a self, data: T) -> NodeRef<'a, T> {
        NodeRef(self.0.alloc(RefCell::new(Node {
            parent: None,
            first_child: None,
            last_child: None,
            previous_sibling: None,
            next_sibling: None,
            data: data,
        })))
    }
}

fn same_ref<T>(a: &T, b: &T) -> bool {
    a as *const T == b as *const T
}


impl<'a, T> Copy for NodeRef<'a, T> {}

/// Cloning a node reference does not clone the node itself, it only copies a pointer.
impl<'a, T> Clone for NodeRef<'a, T> {
    fn clone(&self) -> NodeRef<'a, T> { *self }
}

impl<'a, T: fmt::Debug> fmt::Debug for NodeRef<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&*self.borrow(), f)
    }
}

impl<'a, T> NodeRef<'a, T> {
    /// Return a reference to the parent node, unless this node is the root of the tree.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn parent(self) -> Option<NodeRef<'a, T>> {
        self.0.borrow().parent.map(NodeRef)
    }

    /// Return a reference to the first child of this node, unless it has no child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn first_child(self) -> Option<NodeRef<'a, T>> {
        self.0.borrow().first_child.map(NodeRef)
    }

    /// Return a reference to the last child of this node, unless it has no child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn last_child(self) -> Option<NodeRef<'a, T>> {
        self.0.borrow().last_child.map(NodeRef)
    }

    /// Return a reference to the previous sibling of this node, unless it is a first child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn previous_sibling(self) -> Option<NodeRef<'a, T>> {
        self.0.borrow().previous_sibling.map(NodeRef)
    }

    /// Return a reference to the previous sibling of this node, unless it is a first child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn next_sibling(self) -> Option<NodeRef<'a, T>> {
        self.0.borrow().next_sibling.map(NodeRef)
    }

    /// Return a shared reference to this node’s data
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn borrow(self) -> Ref<'a, T> {
        Ref { _ref: self.0.borrow() }
    }

    /// Return a unique/mutable reference to this node’s data
    ///
    /// # Panics
    ///
    /// Panics if the node is currently borrowed.
    pub fn borrow_mut(self) -> RefMut<'a, T> {
        RefMut { _ref: self.0.borrow_mut() }
    }

    /// Returns whether two references point to the same node.
    pub fn same_node(self, other: NodeRef<'a, T>) -> bool {
        same_ref(self.0, other.0)
    }

    /// Return an iterator of references to this node and its ancestors.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn ancestors(self) -> Ancestors<'a, T> {
        Ancestors(Some(self))
    }

    /// Return an iterator of references to this node and the siblings before it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn preceding_siblings(self) -> PrecedingSiblings<'a, T> {
        PrecedingSiblings(Some(self))
    }

    /// Return an iterator of references to this node and the siblings after it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn following_siblings(self) -> FollowingSiblings<'a, T> {
        FollowingSiblings(Some(self))
    }

    /// Return an iterator of references to this node’s children.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn children(self) -> Children<'a, T> {
        Children(self.first_child())
    }

    /// Return an iterator of references to this node’s children, in reverse order.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn reverse_children(self) -> ReverseChildren<'a, T> {
        ReverseChildren(self.last_child())
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    ///
    /// Parent nodes appear before the descendants.
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn descendants(self) -> Descendants<'a, T> {
        Descendants(self.traverse())
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn traverse(self) -> Traverse<'a, T> {
        Traverse {
            root: self,
            next: Some(NodeEdge::Start(self)),
        }
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn reverse_traverse(self) -> ReverseTraverse<'a, T> {
        ReverseTraverse {
            root: self,
            next: Some(NodeEdge::End(self)),
        }
    }

    /// Detach a node from its parent and siblings. Children are not affected.
    ///
    /// # Panics
    ///
    /// Panics if the node or one of its adjoining nodes is currently borrowed.
    pub fn detach(self) {
        self.0.borrow_mut().detach();
    }

    /// Append a new child to this node, after existing children.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new child, or one of their adjoining nodes is currently borrowed.
    pub fn append(self, new_child: NodeRef<'a, T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_child_borrow = new_child.0.borrow_mut();
        new_child_borrow.detach();
        new_child_borrow.parent = Some(self.0);
        if let Some(last_child) = self_borrow.last_child.take() {
            new_child_borrow.previous_sibling = Some(last_child);
            debug_assert!(last_child.borrow().next_sibling.is_none());
            last_child.borrow_mut().next_sibling = Some(new_child.0);
        } else {
            debug_assert!(self_borrow.first_child.is_none());
            self_borrow.first_child = Some(new_child.0);
        }
        self_borrow.last_child = Some(new_child.0);
    }

    /// Prepend a new child to this node, before existing children.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new child, or one of their adjoining nodes is currently borrowed.
    pub fn prepend(self, new_child: NodeRef<'a, T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_child_borrow = new_child.0.borrow_mut();
        new_child_borrow.detach();
        new_child_borrow.parent = Some(self.0);
        if let Some(first_child) = self_borrow.first_child.take() {
            debug_assert!(first_child.borrow().previous_sibling.is_none());
            first_child.borrow_mut().previous_sibling = Some(new_child.0);
            new_child_borrow.next_sibling = Some(first_child);
        } else {
            debug_assert!(self_borrow.first_child.is_none());
            self_borrow.last_child = Some(new_child.0);
        }
        self_borrow.first_child = Some(new_child.0);
    }

    /// Insert a new sibling after this node.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new sibling, or one of their adjoining nodes is currently borrowed.
    pub fn insert_after(self, new_sibling: NodeRef<'a, T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_sibling_borrow = new_sibling.0.borrow_mut();
        new_sibling_borrow.detach();
        new_sibling_borrow.parent = self_borrow.parent;
        new_sibling_borrow.previous_sibling = Some(self.0);
        if let Some(next_sibling) = self_borrow.next_sibling.take() {
            debug_assert!(same_ref(next_sibling.borrow().previous_sibling.unwrap(), self.0));
            next_sibling.borrow_mut().previous_sibling = Some(new_sibling.0);
            new_sibling_borrow.next_sibling = Some(next_sibling);
        } else if let Some(parent) = self_borrow.parent {
            debug_assert!(same_ref(parent.borrow().last_child.unwrap(), self.0));
            parent.borrow_mut().last_child = Some(new_sibling.0);
        }
        self_borrow.next_sibling = Some(new_sibling.0);
    }

    /// Insert a new sibling before this node.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new sibling, or one of their adjoining nodes is currently borrowed.
    pub fn insert_before(self, new_sibling: NodeRef<'a, T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_sibling_borrow = new_sibling.0.borrow_mut();
        new_sibling_borrow.detach();
        new_sibling_borrow.parent = self_borrow.parent;
        new_sibling_borrow.next_sibling = Some(self.0);
        if let Some(previous_sibling) = self_borrow.previous_sibling.take() {
            new_sibling_borrow.previous_sibling = Some(previous_sibling);
            debug_assert!(same_ref(previous_sibling.borrow().next_sibling.unwrap(), self.0));
            previous_sibling.borrow_mut().next_sibling = Some(new_sibling.0);
        } else if let Some(parent) = self_borrow.parent {
            debug_assert!(same_ref(parent.borrow().first_child.unwrap(), self.0));
            parent.borrow_mut().first_child = Some(new_sibling.0);
        }
        self_borrow.previous_sibling = Some(new_sibling.0);
    }
}

/// Wraps a `std::cell::Ref` for a node’s data.
pub struct Ref<'a, T: 'a> {
    _ref: cell::Ref<'a, Node<'a, T>>
}

/// Wraps a `std::cell::RefMut` for a node’s data.
pub struct RefMut<'a, T: 'a> {
    _ref: cell::RefMut<'a, Node<'a, T>>
}

impl<'a, T> Deref for Ref<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { &self._ref.data }
}

impl<'a, T> Deref for RefMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { &self._ref.data }
}

impl<'a, T> DerefMut for RefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T { &mut self._ref.data }
}


impl<'a, T> Node<'a, T> {
    fn detach(&mut self) {
        let parent = self.parent.take();
        let previous_sibling = self.previous_sibling.take();
        let next_sibling = self.next_sibling.take();

        if let Some(next_sibling) = next_sibling {
            next_sibling.borrow_mut().previous_sibling = previous_sibling;
        } else if let Some(parent) = parent {
            parent.borrow_mut().last_child = previous_sibling;
        }

        if let Some(previous_sibling) = previous_sibling {
            previous_sibling.borrow_mut().next_sibling = next_sibling;
        } else if let Some(parent) = parent {
            parent.borrow_mut().first_child = next_sibling;
        }
    }
}


macro_rules! impl_node_iterator {
    ($name: ident, $next: expr) => {
        impl<'a, T> Iterator for $name<'a, T> {
            type Item = NodeRef<'a, T>;

            /// # Panics
            ///
            /// Panics if the node about to be yielded is currently mutability borrowed.
            fn next(&mut self) -> Option<NodeRef<'a, T>> {
                match self.0.take() {
                    Some(node) => {
                        self.0 = $next(node);
                        Some(node)
                    }
                    None => None
                }
            }
        }
    }
}

/// An iterator of references to the ancestors a given node.
pub struct Ancestors<'a, T: 'a>(Option<NodeRef<'a, T>>);
impl_node_iterator!(Ancestors, |node: NodeRef<'a, T>| node.parent());

/// An iterator of references to the siblings before a given node.
pub struct PrecedingSiblings<'a, T: 'a>(Option<NodeRef<'a, T>>);
impl_node_iterator!(PrecedingSiblings, |node: NodeRef<'a, T>| node.previous_sibling());

/// An iterator of references to the siblings after a given node.
pub struct FollowingSiblings<'a, T: 'a>(Option<NodeRef<'a, T>>);
impl_node_iterator!(FollowingSiblings, |node: NodeRef<'a, T>| node.next_sibling());

/// An iterator of references to the children of a given node.
pub struct Children<'a, T: 'a>(Option<NodeRef<'a, T>>);
impl_node_iterator!(Children, |node: NodeRef<'a, T>| node.next_sibling());

/// An iterator of references to the children of a given node, in reverse order.
pub struct ReverseChildren<'a, T: 'a>(Option<NodeRef<'a, T>>);
impl_node_iterator!(ReverseChildren, |node: NodeRef<'a, T>| node.previous_sibling());


/// An iterator of references to a given node and its descendants, in tree order.
pub struct Descendants<'a, T: 'a>(Traverse<'a, T>);

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = NodeRef<'a, T>;

    /// # Panics
    ///
    /// Panics if the node about to be yielded is currently mutability borrowed.
    fn next(&mut self) -> Option<NodeRef<'a, T>> {
        loop {
            match self.0.next() {
                Some(NodeEdge::Start(node)) => return Some(node),
                Some(NodeEdge::End(_)) => {}
                None => return None
            }
        }
    }
}


#[derive(Debug, Clone)]
pub enum NodeEdge<T> {
    /// Indicates that start of a node that has children.
    /// Yielded by `Traverse::next` before the node’s descendants.
    /// In HTML or XML, this corresponds to an opening tag like `<div>`
    Start(T),

    /// Indicates that end of a node that has children.
    /// Yielded by `Traverse::next` after the node’s descendants.
    /// In HTML or XML, this corresponds to a closing tag like `</div>`
    End(T),
}


/// An iterator of references to a given node and its descendants, in tree order.
pub struct Traverse<'a, T: 'a> {
    root: NodeRef<'a, T>,
    next: Option<NodeEdge<NodeRef<'a, T>>>,
}

impl<'a, T> Iterator for Traverse<'a, T> {
    type Item = NodeEdge<NodeRef<'a, T>>;

    /// # Panics
    ///
    /// Panics if the node about to be yielded is currently mutability borrowed.
    fn next(&mut self) -> Option<NodeEdge<NodeRef<'a, T>>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    NodeEdge::Start(ref node) => {
                        match node.first_child() {
                            Some(first_child) => Some(NodeEdge::Start(first_child)),
                            None => Some(NodeEdge::End(node.clone()))
                        }
                    }
                    NodeEdge::End(ref node) => {
                        if node.same_node(self.root) {
                            None
                        } else {
                            match node.next_sibling() {
                                Some(next_sibling) => Some(NodeEdge::Start(next_sibling)),
                                None => match node.parent() {
                                    Some(parent) => Some(NodeEdge::End(parent)),

                                    // `node.parent()` here can only be `None`
                                    // if the tree has been modified during iteration,
                                    // but silently stoping iteration
                                    // seems a more sensible behavior than panicking.
                                    None => None
                                }
                            }
                        }
                    }
                };
                Some(item)
            }
            None => None
        }
    }
}

/// An iterator of references to a given node and its descendants, in reverse tree order.
pub struct ReverseTraverse<'a, T: 'a> {
    root: NodeRef<'a, T>,
    next: Option<NodeEdge<NodeRef<'a, T>>>,
}

impl<'a, T> Iterator for ReverseTraverse<'a, T> {
    type Item = NodeEdge<NodeRef<'a, T>>;

    /// # Panics
    ///
    /// Panics if the node about to be yielded is currently mutability borrowed.
    fn next(&mut self) -> Option<NodeEdge<NodeRef<'a, T>>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    NodeEdge::End(ref node) => {
                        match node.last_child() {
                            Some(last_child) => Some(NodeEdge::End(last_child)),
                            None => Some(NodeEdge::Start(node.clone()))
                        }
                    }
                    NodeEdge::Start(ref node) => {
                        if node.same_node(self.root) {
                            None
                        } else {
                            match node.previous_sibling() {
                                Some(previous_sibling) => Some(NodeEdge::End(previous_sibling)),
                                None => match node.parent() {
                                    Some(parent) => Some(NodeEdge::Start(parent)),

                                    // `node.parent()` here can only be `None`
                                    // if the tree has been modified during iteration,
                                    // but silently stoping iteration
                                    // seems a more sensible behavior than panicking.
                                    None => None
                                }
                            }
                        }
                    }
                };
                Some(item)
            }
            None => None
        }
    }
}


#[test]
fn it_works() {
    struct DropTracker<'a>(&'a cell::Cell<u32>);
    impl<'a> Drop for DropTracker<'a> {
        fn drop(&mut self) {
            self.0.set(self.0.get() + 1);
        }
    }

    let drop_counter = cell::Cell::new(0);
    {
        let mut new_counter = 0;
        let arena = Arena::new();
        let mut new = || {
            new_counter += 1;
            arena.new_node((new_counter, DropTracker(&drop_counter)))
        };

        let a = new();  // 1
        a.append(new());  // 2
        a.append(new());  // 3
        a.prepend(new());  // 4
        let b = new();  // 5
        b.append(a.clone());
        a.insert_before(new());  // 6
        a.insert_before(new());  // 7
        a.insert_after(new());  // 8
        a.insert_after(new());  // 9
        let c = new();  // 10
        b.append(c.clone());

        assert_eq!(drop_counter.get(), 0);
        c.previous_sibling().unwrap().detach();
        assert_eq!(drop_counter.get(), 0);

        assert_eq!(b.descendants().map(|node| {
            let borrow = node.borrow();
            borrow.0
        }).collect::<Vec<_>>(), [
            5, 6, 7, 1, 4, 2, 3, 9, 10
        ]);
    }

    assert_eq!(drop_counter.get(), 10);
}
