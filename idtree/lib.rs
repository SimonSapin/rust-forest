use std::cell::{self, RefCell};
use std::fmt;
use std::ops::{Index, IndexMut};


/// A reference to a node holding a value of type `T`. Nodes form a tree.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub struct NodeId {
    index: usize,  // FIXME: use NonZero to optimize the size of Option<NodeId>
}

#[derive(Clone)]
pub struct Node<T> {
    parent: Option<NodeId>,
    previous_sibling: Option<NodeId>,
    next_sibling: Option<NodeId>,
    first_child: Option<NodeId>,
    last_child: Option<NodeId>,
    pub data: T,
}


#[derive(Clone)]
pub struct Arena<T> {
    nodes: Vec<Node<T>>,
}

impl<T> Arena<T> {
    pub fn new() -> Arena<T> {
        Arena {
            nodes: Vec::new(),
        }
    }

    /// Create a new node from its associated data.
    pub fn new_node(&mut self, data: T) -> NodeId {
        let next_index = self.nodes.len();
        self.nodes.push(Node {
            parent: None,
            first_child: None,
            last_child: None,
            previous_sibling: None,
            next_sibling: None,
            data: data,
        });
        NodeId {
            index: next_index,
        }
    }
}

impl<T> Index<NodeId> for Arena<T> {
    type Output = Node<T>;

    fn index(&self, node: NodeId) -> &Node<T> {
        &self.nodes[node.index]
    }
}

impl<T> IndexMut<NodeId> for Arena<T> {
    fn index_mut(&mut self, node: NodeId) -> &mut Node<T> {
        &mut self.nodes[node.index]
    }
}


impl<T> Node<T> {
    /// Return the ID of the parent node, unless this node is the root of the tree.
    pub fn parent(&self) -> Option<NodeId> { self.parent }

    /// Return the ID of the first child of this node, unless it has no child.
    pub fn first_child(&self) -> Option<NodeId> { self.first_child }

    /// Return the ID of the last child of this node, unless it has no child.
    pub fn last_child(&self) -> Option<NodeId> { self.last_child }

    /// Return the ID of the previous sibling of this node, unless it is a first child.
    pub fn previous_sibling(&self) -> Option<NodeId> { self.previous_sibling }

    /// Return the ID of the previous sibling of this node, unless it is a first child.
    pub fn next_sibling(&self) -> Option<NodeId> { self.previous_sibling }
}


impl<T> Arena<T> {
    /// Return an iterator of references to this node and its ancestors.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn ancestors(&self, node: NodeId) -> Ancestors<T> {
        Ancestors {
            arena: self,
            node: Some(node),
        }
    }

    /// Return an iterator of references to this node and the siblings before it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn preceding_siblings(&self, node: NodeId) -> PrecedingSiblings<T> {
        PrecedingSiblings {
            arena: self,
            node: Some(node),
        }
    }

    /// Return an iterator of references to this node and the siblings after it.
    ///
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn following_siblings(&self, node: NodeId) -> FollowingSiblings<T> {
        FollowingSiblings {
            arena: self,
            node: Some(node),
        }
    }

    /// Return an iterator of references to this node’s children.
    pub fn children(&self, node: NodeId) -> Children<T> {
        Children {
            arena: self,
            node: self[node].first_child,
        }
    }

    /// Return an iterator of references to this node’s children, in reverse order.
    pub fn reverse_children(&self, node: NodeId) -> ReverseChildren<T> {
        ReverseChildren {
            arena: self,
            node: self[node].last_child,
        }
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    ///
    /// Parent nodes appear before the descendants.
    /// Call `.next().unwrap()` once on the iterator to skip the node itself.
    pub fn descendants(&self, node: NodeId) -> Descendants<T> {
        Descendants(self.traverse(node))
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn traverse(&self, node: NodeId) -> Traverse<T> {
        Traverse {
            arena: self,
            root: node,
            next: Some(NodeEdge::Start(node)),
        }
    }

    /// Return an iterator of references to this node and its descendants, in tree order.
    pub fn reverse_traverse(&self, node: NodeId) -> ReverseTraverse<T> {
        ReverseTraverse {
            arena: self,
            root: node,
            next: Some(NodeEdge::End(node)),
        }
    }

    /// Detach a node from its parent and siblings. Children are not affected.
    pub fn detach(&mut self, node: NodeId) {
        let (parent, previous_sibling, next_sibling) = {
            let node = &mut self[node];
            (node.parent.take(), node.previous_sibling.take(), node.next_sibling.take())
        };

        if let Some(next_sibling) = next_sibling {
            self[next_sibling].previous_sibling = previous_sibling;
        } else if let Some(parent) = parent {
            self[parent].last_child = previous_sibling;
        }

        if let Some(previous_sibling) = previous_sibling {
            self[previous_sibling].next_sibling = next_sibling;
        } else if let Some(parent) = parent {
            self[parent].first_child = next_sibling;
        }
    }

    /// Append a new child to this node, after existing children.
    pub fn append(&mut self, node: NodeId, new_child: NodeId) {
        self.detach(new_child);


//        let mut self_borrow = self.0.borrow_mut();
//        let mut new_child_borrow = new_child.0.borrow_mut();
//        new_child_borrow.detach();
//        new_child_borrow.parent = Some(&self.0);
//        if let Some(last_child) = self_borrow.last_child.take() {
//            new_child_borrow.previous_sibling = Some(last_child);
//            debug_assert!(last_child.borrow().next_sibling.is_none());
//            last_child.borrow_mut().next_sibling = Some(new_child.0);
//        } else {
//            debug_assert!(&self_borrow.first_child.is_none());
//            self_borrow.first_child = Some(new_child.0);
//        }
//        self_borrow.last_child = Some(new_child.0);
    }

    /// Prepend a new child to this node, before existing children.
    pub fn prepend(&mut self, node: NodeId, new_child: NodeId) {
//        let mut self_borrow = self.0.borrow_mut();
//        let mut new_child_borrow = new_child.0.borrow_mut();
//        new_child_borrow.detach();
//        new_child_borrow.parent = Some(&self.0);
//        if let Some(first_child) = self_borrow.first_child.take() {
//            debug_assert!(first_child.borrow().previous_sibling.is_none());
//            first_child.borrow_mut().previous_sibling = Some(new_child.0);
//            new_child_borrow.next_sibling = Some(first_child);
//        } else {
//            debug_assert!(&self_borrow.first_child.is_none());
//            self_borrow.last_child = Some(new_child.0);
//        }
//        self_borrow.first_child = Some(new_child.0);
    }

    /// Insert a new sibling after this node.
    pub fn insert_after(&mut self, node: NodeId, new_sibling: NodeId) {
//        let mut self_borrow = self.0.borrow_mut();
//        let mut new_sibling_borrow = new_sibling.0.borrow_mut();
//        new_sibling_borrow.detach();
//        new_sibling_borrow.parent = self_borrow.parent;
//        new_sibling_borrow.previous_sibling = Some(&self.0);
//        if let Some(next_sibling) = self_borrow.next_sibling.take() {
//            debug_assert!(same_ref(next_sibling.borrow().previous_sibling.unwrap(), self.0));
//            next_sibling.borrow_mut().previous_sibling = Some(new_sibling.0);
//            new_sibling_borrow.next_sibling = Some(next_sibling);
//        } else if let Some(parent) = self_borrow.parent {
//            debug_assert!(same_ref(parent.borrow().last_child.unwrap(), self.0));
//            parent.borrow_mut().last_child = Some(new_sibling.0);
//        }
//        self_borrow.next_sibling = Some(new_sibling.0);
    }

    /// Insert a new sibling before this node.
    pub fn insert_before(&mut self, node: NodeId, new_sibling: NodeId) {
//        let mut self_borrow = self.0.borrow_mut();
//        let mut new_sibling_borrow = new_sibling.0.borrow_mut();
//        new_sibling_borrow.detach();
//        new_sibling_borrow.parent = self_borrow.parent;
//        new_sibling_borrow.next_sibling = Some(&self.0);
//        if let Some(previous_sibling) = self_borrow.previous_sibling.take() {
//            new_sibling_borrow.previous_sibling = Some(previous_sibling);
//            debug_assert!(same_ref(previous_sibling.borrow().next_sibling.unwrap(), self.0));
//            previous_sibling.borrow_mut().next_sibling = Some(new_sibling.0);
//        } else if let Some(parent) = self_borrow.parent {
//            debug_assert!(same_ref(parent.borrow().first_child.unwrap(), self.0));
//            parent.borrow_mut().first_child = Some(new_sibling.0);
//        }
//        self_borrow.previous_sibling = Some(new_sibling.0);
    }
}


macro_rules! impl_node_iterator {
    ($name: ident, $next: expr) => {
        impl<'a, T> Iterator for $name<'a, T> {
            type Item = NodeId;

            fn next(&mut self) -> Option<NodeId> {
                match self.node.take() {
                    Some(node) => {
                        self.node = $next(&self.arena[node]);
                        Some(node)
                    }
                    None => None
                }
            }
        }
    }
}

/// An iterator of references to the ancestors a given node.
pub struct Ancestors<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(Ancestors, |node: &Node<T>| node.parent);

/// An iterator of references to the siblings before a given node.
pub struct PrecedingSiblings<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(PrecedingSiblings, |node: &Node<T>| node.previous_sibling);

/// An iterator of references to the siblings after a given node.
pub struct FollowingSiblings<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(FollowingSiblings, |node: &Node<T>| node.next_sibling);

/// An iterator of references to the children of a given node.
pub struct Children<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(Children, |node: &Node<T>| node.next_sibling);

/// An iterator of references to the children of a given node, in reverse order.
pub struct ReverseChildren<'a, T: 'a> {
    arena: &'a Arena<T>,
    node: Option<NodeId>,
}
impl_node_iterator!(ReverseChildren, |node: &Node<T>| node.previous_sibling);


/// An iterator of references to a given node and its descendants, in tree order.
pub struct Descendants<'a, T: 'a>(Traverse<'a, T>);

impl<'a, T> Iterator for Descendants<'a, T> {
    type Item = NodeId;

    fn next(&mut self) -> Option<NodeId> {
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
    arena: &'a Arena<T>,
    root: NodeId,
    next: Option<NodeEdge<NodeId>>,
}

impl<'a, T> Iterator for Traverse<'a, T> {
    type Item = NodeEdge<NodeId>;

    fn next(&mut self) -> Option<NodeEdge<NodeId>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    NodeEdge::Start(node) => {
                        match self.arena[node].first_child {
                            Some(first_child) => Some(NodeEdge::Start(first_child)),
                            None => Some(NodeEdge::End(node.clone()))
                        }
                    }
                    NodeEdge::End(node) => {
                        if node == self.root {
                            None
                        } else {
                            match self.arena[node].next_sibling {
                                Some(next_sibling) => Some(NodeEdge::Start(next_sibling)),
                                None => match self.arena[node].parent {
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
    arena: &'a Arena<T>,
    root: NodeId,
    next: Option<NodeEdge<NodeId>>,
}

impl<'a, T> Iterator for ReverseTraverse<'a, T> {
    type Item = NodeEdge<NodeId>;

    fn next(&mut self) -> Option<NodeEdge<NodeId>> {
        match self.next.take() {
            Some(item) => {
                self.next = match item {
                    NodeEdge::End(node) => {
                        match self.arena[node].last_child {
                            Some(last_child) => Some(NodeEdge::End(last_child)),
                            None => Some(NodeEdge::Start(node.clone()))
                        }
                    }
                    NodeEdge::Start(node) => {
                        if node == self.root {
                            None
                        } else {
                            match self.arena[node].previous_sibling {
                                Some(previous_sibling) => Some(NodeEdge::End(previous_sibling)),
                                None => match self.arena[node].parent {
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
            self.0.set(&self.0.get() + 1);
        }
    }

    let drop_counter = cell::Cell::new(0);
    {
        let mut new_counter = 0;
        let mut arena = Arena::new();
        macro_rules! new {
            () => {
                {
                    new_counter += 1;
                    arena.new_node((new_counter, DropTracker(&drop_counter)))
                }
            }
        };

        let a = new!();  // 1
        let tmp = new!(); arena.append(a, tmp);  // 2
        let tmp = new!(); arena.append(a, tmp);  // 3
        let tmp = new!(); arena.prepend(a, tmp);  // 4
        let b = new!();  // 5
        arena.append(b, a);
        let tmp = new!(); arena.insert_before(a, tmp);  // 6
        let tmp = new!(); arena.insert_before(a, tmp);  // 7
        let tmp = new!(); arena.insert_after(a, tmp);  // 8
        let tmp = new!(); arena.insert_after(a, tmp);  // 9
        let c = new!();  // 10
        arena.append(b, c);

        assert_eq!(drop_counter.get(), 0);
        let tmp = arena[c].previous_sibling().unwrap();
        arena.detach(tmp);
        assert_eq!(drop_counter.get(), 0);

        assert_eq!(arena.descendants(b).map(|node| arena[node].data.0).collect::<Vec<_>>(), [
            5, 6, 7, 1, 4, 2, 3, 9, 10
        ]);
    }

    assert_eq!(drop_counter.get(), 10);
}
