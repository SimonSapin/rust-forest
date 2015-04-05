#![feature(alloc)]

use std::cell::{self, RefCell};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::rc::{Rc, Weak};


/// A reference to a node holding a value of type `T`. Nodes form a tree.
///
/// Internally, this uses reference counting for lifetime tracking
/// and `std::cell::RefCell` for interior mutability.
pub struct NodeRef<T>(Rc<RefCell<Node<T>>>);

struct Node<T> {
    parent: WeakLink<T>,
    first_child: Link<T>,
    last_child: WeakLink<T>,
    previous_sibling: WeakLink<T>,
    next_sibling: Link<T>,
    data: T,
}

type Link<T> = Option<Rc<RefCell<Node<T>>>>;
type WeakLink<T> = Option<Weak<RefCell<Node<T>>>>;


fn same_rc<T>(a: &Rc<T>, b: &Rc<T>) -> bool {
    let a: *const T = &**a;
    let b: *const T = &**b;
    a == b
}


impl<T> Clone for NodeRef<T> {
    fn clone(&self) -> NodeRef<T> {
        NodeRef(self.0.clone())
    }
}


impl<T> NodeRef<T> {
    /// Create a new node from its associated data.
    pub fn new(data: T) -> NodeRef<T> {
        NodeRef(Rc::new(RefCell::new(Node {
            parent: None,
            first_child: None,
            last_child: None,
            previous_sibling: None,
            next_sibling: None,
            data: data,
        })))
    }

    /// Return a reference to the parent node, unless this node is the root of the tree.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn parent(&self) -> Option<NodeRef<T>> {
        self.0.borrow().parent.as_ref().map(|weak| NodeRef(weak.upgrade().unwrap()))
    }

    /// Return a reference to the first child of this node, unless it has no child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn first_child(&self) -> Option<NodeRef<T>> {
        self.0.borrow().first_child.as_ref().map(|strong| NodeRef(strong.clone()))
    }

    /// Return a reference to the last child of this node, unless it has no child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn last_child(&self) -> Option<NodeRef<T>> {
        self.0.borrow().last_child.as_ref().map(|weak| NodeRef(weak.upgrade().unwrap()))
    }

    /// Return a reference to the previous sibling of this node, unless it is a first child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn previous_sibling(&self) -> Option<NodeRef<T>> {
        self.0.borrow().previous_sibling.as_ref().map(|weak| NodeRef(weak.upgrade().unwrap()))
    }

    /// Return a reference to the previous sibling of this node, unless it is a first child.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn next_sibling(&self) -> Option<NodeRef<T>> {
        self.0.borrow().next_sibling.as_ref().map(|strong| NodeRef(strong.clone()))
    }

    /// Return a shared reference to this node’s data
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn data(&self) -> DataRef<T> {
        DataRef(self.0.borrow())
    }

    /// Return a unique/mutable reference to this node’s data
    ///
    /// # Panics
    ///
    /// Panics if the node is currently borrowed.
    pub fn data_mut(&self) -> DataRefMut<T> {
        DataRefMut(self.0.borrow_mut())
    }

    /// Returns whether two references point to the same node.
    pub fn same_node(&self, other: &NodeRef<T>) -> bool {
        same_rc(&self.0, &other.0)
    }

    /// Return an iterator of references to this node and its ancestors.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn ancestors(&self) -> Ancestors<T> {
        Ancestors(Some(self.clone()))
    }

    /// Return an iterator of references to this node and the siblings before it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn preceding_siblings(&self) -> PrecedingSiblings<T> {
        PrecedingSiblings(Some(self.clone()))
    }

    /// Return an iterator of references to this node and the siblings after it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn following_siblings(&self) -> FollowingSiblings<T> {
        FollowingSiblings(Some(self.clone()))
    }

    /// Return an iterator of references to this node’s children.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn children(&self) -> Children<T> {
        Children(self.first_child())
    }

    /// Return an iterator of references to this node’s children, in reverse order.
    ///
    /// # Panics
    ///
    /// Panics if the node is currently mutability borrowed.
    pub fn reverse_children(&self) -> ReverseChildren<T> {
        ReverseChildren(self.last_child())
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    ///
    /// Parent nodes appear before the descendants.
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn descendants(&self) -> Descendants<T> {
        Descendants {
            root: self.clone(),
            next: Some(self.clone()),
        }
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn traverse(&self) -> Traverse<T> {
        Traverse {
            root: self.clone(),
            next: Some(Item::Open(self.clone())),
        }
    }

    /// Detach a node from its parent and siblings. Children are not affected.
    ///
    /// # Panics
    ///
    /// Panics if the node or one of its adjoining nodes is currently borrowed.
    pub fn detach(&self) {
        self.0.borrow_mut().detach();
    }

    /// Append a new child to this node, after existing children.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new child, or one of their adjoining nodes is currently borrowed.
    pub fn append(&self, new_child: NodeRef<T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_child_borrow = new_child.0.borrow_mut();
        new_child_borrow.detach();
        new_child_borrow.parent = Some(self.0.downgrade());
        match mem::replace(&mut self_borrow.last_child, Some(new_child.0.downgrade())) {
            Some(last_child_weak) => {
                let last_child_strong = last_child_weak.upgrade().unwrap();
                new_child_borrow.previous_sibling = Some(last_child_weak);
                let mut last_child_borrow = last_child_strong.borrow_mut();
                debug_assert!(last_child_borrow.next_sibling.is_none());
                // FIXME: Can we avoid this clone?
                last_child_borrow.next_sibling = Some(new_child.0.clone());
            }
            None => {
                debug_assert!(self_borrow.first_child.is_none());
                // FIXME: Can we avoid this clone?
                self_borrow.first_child = Some(new_child.0.clone());
            }
        }
    }

    /// Prepend a new child to this node, before existing children.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new child, or one of their adjoining nodes is currently borrowed.
    pub fn prepend(&self, new_child: NodeRef<T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_child_borrow = new_child.0.borrow_mut();
        new_child_borrow.detach();
        new_child_borrow.parent = Some(self.0.downgrade());
        // FIXME: Can we avoid this clone?
        match mem::replace(&mut self_borrow.first_child, Some(new_child.0.clone())) {
            Some(first_child_strong) => {
                {
                    let mut first_child_borrow = first_child_strong.borrow_mut();
                    debug_assert!(first_child_borrow.previous_sibling.is_none());
                    first_child_borrow.previous_sibling = Some(new_child.0.downgrade());
                }
                new_child_borrow.next_sibling = Some(first_child_strong);
            }
            None => {
                debug_assert!(self_borrow.first_child.is_none());
                self_borrow.last_child = Some(new_child.0.downgrade());
            }
        }
    }

    /// Insert a new sibling after this node.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new sibling, or one of their adjoining nodes is currently borrowed.
    pub fn insert_after(&self, new_sibling: NodeRef<T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_sibling_borrow = new_sibling.0.borrow_mut();
        new_sibling_borrow.detach();
        new_sibling_borrow.parent = self_borrow.parent.clone();
        new_sibling_borrow.previous_sibling = Some(self.0.downgrade());
        // FIXME: Can we avoid this clone?
        match mem::replace(&mut self_borrow.next_sibling, Some(new_sibling.0.clone())) {
            Some(next_sibling_strong) => {
                {
                    let mut next_sibling_borrow = next_sibling_strong.borrow_mut();
                    debug_assert!({
                        let weak = next_sibling_borrow.previous_sibling.as_ref().unwrap();
                        same_rc(&weak.upgrade().unwrap(), &self.0)
                    });
                    next_sibling_borrow.previous_sibling = Some(new_sibling.0.downgrade());
                }
                new_sibling_borrow.next_sibling = Some(next_sibling_strong);
            }
            None => {
                // FIXME: Is it OK to insert after a root element?
                if let Some(parent_ref) = self_borrow.parent.as_ref() {
                    let parent_strong = parent_ref.upgrade().unwrap();
                    let mut parent_borrow = parent_strong.borrow_mut();
                    parent_borrow.last_child = Some(new_sibling.0.downgrade());
                }
            }
        }
    }

    /// Insert a new sibling before this node.
    ///
    /// # Panics
    ///
    /// Panics if the node, the new sibling, or one of their adjoining nodes is currently borrowed.
    pub fn insert_before(&self, new_sibling: NodeRef<T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_sibling_borrow = new_sibling.0.borrow_mut();
        new_sibling_borrow.detach();
        new_sibling_borrow.parent = self_borrow.parent.clone();
        // FIXME: Can we avoid this clone?
        new_sibling_borrow.next_sibling = Some(self.0.clone());
        match mem::replace(&mut self_borrow.previous_sibling, Some(new_sibling.0.downgrade())) {
            Some(previous_sibling_weak) => {
                let previous_sibling_strong = previous_sibling_weak.upgrade().unwrap();
                new_sibling_borrow.previous_sibling = Some(previous_sibling_weak);
                let mut previous_sibling_borrow = previous_sibling_strong.borrow_mut();
                debug_assert!({
                    let rc = previous_sibling_borrow.next_sibling.as_ref().unwrap();
                    same_rc(rc, &self.0)
                });
                // FIXME: Can we avoid this clone?
                previous_sibling_borrow.next_sibling = Some(new_sibling.0.clone());
            }
            None => {
                // FIXME: Is it OK to insert before a root element?
                if let Some(parent_ref) = self_borrow.parent.as_ref() {
                    let parent_strong = parent_ref.upgrade().unwrap();
                    let mut parent_borrow = parent_strong.borrow_mut();
                    // FIXME: Can we avoid this clone?
                    parent_borrow.first_child = Some(new_sibling.0.clone());
                }
            }
        }
    }
}

/// Wraps a `std::cell::Ref` for a node’s data.
pub struct DataRef<'a, T: 'a>(cell::Ref<'a, Node<T>>);

/// Wraps a `std::cell::RefMut` for a node’s data.
pub struct DataRefMut<'a, T: 'a>(cell::RefMut<'a, Node<T>>);

impl<'a, T> Deref for DataRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0.data }
}

impl<'a, T> Deref for DataRefMut<'a, T> {
    type Target = T;
    fn deref(&self) -> &T { &self.0.data }
}

impl<'a, T> DerefMut for DataRefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T { &mut self.0.data }
}


impl<T> Node<T> {
    /// Detach a node from its parent and siblings. Children are not affected.
    fn detach(&mut self) {
        let parent_strong = match self.parent.take() {
            Some(parent_weak) => parent_weak.upgrade().unwrap(),
            None => {
                debug_assert!(self.previous_sibling.is_none());
                debug_assert!(self.next_sibling.is_none());
                return
            }
        };
        let mut parent_borrow = parent_strong.borrow_mut();

        let previous_sibling_weak = self.previous_sibling.take();
        let next_sibling_strong = self.next_sibling.take();

        if let Some(next_sibling_ref) = next_sibling_strong.as_ref() {
            let mut next_sibling_borrow = next_sibling_ref.borrow_mut();
            // FIXME: Can we avoid this clone?
            next_sibling_borrow.previous_sibling = previous_sibling_weak.clone();
        } else {
            // FIXME: Can we avoid this clone?
            parent_borrow.last_child = previous_sibling_weak.clone();
        }

        if let Some(previous_sibling_ref) = previous_sibling_weak.as_ref() {
            let previous_sibling_strong = previous_sibling_ref.upgrade().unwrap();
            let mut previous_sibling_borrow = previous_sibling_strong.borrow_mut();
            previous_sibling_borrow.next_sibling = next_sibling_strong;
        } else {
            parent_borrow.first_child = next_sibling_strong;
        }
    }
}


macro_rules! impl_node_iterator {
    ($name: ident, $next: expr) => {
        impl<T> Iterator for $name<T> {
            type Item = NodeRef<T>;

            /// # Panics
            ///
            /// Panics if the node about to be yielded is currently mutability borrowed.
            fn next(&mut self) -> Option<NodeRef<T>> {
                match self.0.take() {
                    Some(node) => {
                        self.0 = $next(&node);
                        Some(node)
                    }
                    None => None
                }
            }
        }
    }
}

/// An iterator of references to the ancestors a given node.
pub struct Ancestors<T>(Option<NodeRef<T>>);
impl_node_iterator!(Ancestors, |node: &NodeRef<T>| node.parent());

/// An iterator of references to the siblings before a given node.
pub struct PrecedingSiblings<T>(Option<NodeRef<T>>);
impl_node_iterator!(PrecedingSiblings, |node: &NodeRef<T>| node.previous_sibling());

/// An iterator of references to the siblings after a given node.
pub struct FollowingSiblings<T>(Option<NodeRef<T>>);
impl_node_iterator!(FollowingSiblings, |node: &NodeRef<T>| node.next_sibling());

/// An iterator of references to the children of a given node.
pub struct Children<T>(Option<NodeRef<T>>);
impl_node_iterator!(Children, |node: &NodeRef<T>| node.next_sibling());

/// An iterator of references to the children of a given node, in reverse order.
pub struct ReverseChildren<T>(Option<NodeRef<T>>);
impl_node_iterator!(ReverseChildren, |node: &NodeRef<T>| node.previous_sibling());


/// An iterator of references to a given node and its descandants, in tree order.
pub struct Descendants<T> {
    root: NodeRef<T>,
    next: Option<NodeRef<T>>,
}

impl<T> Iterator for Descendants<T> {
    type Item = NodeRef<T>;

    /// # Panics
    ///
    /// Panics if the node about to be yielded is currently mutability borrowed.
    fn next(&mut self) -> Option<NodeRef<T>> {
        match self.next.take() {
            Some(node) => {
                self.next = descandants_next(&node, &self.root);
                Some(node)
            }
            None => None
        }
    }
}

fn descandants_next<T>(node: &NodeRef<T>, root: &NodeRef<T>) -> Option<NodeRef<T>> {
    let mut parent;
    {
        let node_borrow = node.0.borrow();

        if let Some(first_child) = node_borrow.first_child.as_ref() {
            return Some(NodeRef(first_child.clone()))

        } else if let Some(next_sibling) = node_borrow.next_sibling.as_ref() {
            return Some(NodeRef(next_sibling.clone()));

        } else if let Some(parent_weak) = node_borrow.parent.as_ref() {
            parent = parent_weak.upgrade().unwrap();

        } else {
            return None
        }
    }

    loop {
        if same_rc(&parent, &root.0) {
            return None
        }
        let next_parent;
        {
            let parent_borrow = parent.borrow();

            if let Some(next_sibling) = parent_borrow.next_sibling.as_ref() {
                return Some(NodeRef(next_sibling.clone()));

            } else if let Some(parent_weak) = parent_borrow.parent.as_ref() {
                next_parent = parent_weak.upgrade().unwrap();

            } else {
                return None
            }
        }
        parent = next_parent;
    }
}


/// An iterator of references to a given node and its descandants, in tree order.
pub struct Traverse<T> {
    root: NodeRef<T>,
    next: Option<Item<T>>,
}

pub enum Item<T> {
    /// Indicates that start of a node that has children.
    /// Yielded by `Traverse::next` before the node’s descandants.
    /// In HTML or XML, this corresponds to an opening tag like `<div>`
    Open(NodeRef<T>),

    /// Indicates that end of a node that has children.
    /// Yielded by `Traverse::next` after the node’s descandants.
    /// In HTML or XML, this corresponds to a closing tag like `</div>`
    Close(NodeRef<T>),
}

impl<T> Iterator for Traverse<T> {
    type Item = Item<T>;

    /// # Panics
    ///
    /// Panics if the node about to be yielded is currently mutability borrowed.
    fn next(&mut self) -> Option<Item<T>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    Item::Open(ref node) => {
                        match node.first_child() {
                            Some(first_child) => Some(Item::Open(first_child)),
                            None => Some(Item::Close(node.clone()))
                        }
                    }
                    Item::Close(ref node) => {
                        if node.same_node(&self.root) {
                            None
                        } else {
                            match node.next_sibling() {
                                Some(next_sibling) => Some(Item::Open(next_sibling)),
                                None => match node.parent() {
                                    Some(parent) => Some(Item::Close(parent)),

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
