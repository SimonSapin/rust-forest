#![feature(alloc)]

use std::cell::{self, RefCell};
use std::mem;
use std::ops::{Deref, DerefMut};
use std::rc::{Rc, Weak};


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


impl<T> NodeRef<T> {
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

    pub fn parent(&self) -> Option<NodeRef<T>> {
        self.0.borrow().parent.as_ref().map(|weak| NodeRef(weak.upgrade().unwrap()))
    }

    pub fn first_child(&self) -> Option<NodeRef<T>> {
        self.0.borrow().first_child.as_ref().map(|strong| NodeRef(strong.clone()))
    }

    pub fn last_child(&self) -> Option<NodeRef<T>> {
        self.0.borrow().last_child.as_ref().map(|weak| NodeRef(weak.upgrade().unwrap()))
    }

    pub fn previous_sibling(&self) -> Option<NodeRef<T>> {
        self.0.borrow().previous_sibling.as_ref().map(|weak| NodeRef(weak.upgrade().unwrap()))
    }

    pub fn next_sibling(&self) -> Option<NodeRef<T>> {
        self.0.borrow().next_sibling.as_ref().map(|strong| NodeRef(strong.clone()))
    }

    pub fn data(&self) -> DataRef<T> {
        DataRef(self.0.borrow())
    }

    pub fn data_mut(&self) -> DataRefMut<T> {
        DataRefMut(self.0.borrow_mut())
    }

    // Detach a node from its parent and siblings. Children are not affected.
    pub fn detach(&self) {
        self.0.borrow_mut().detach();
    }

    pub fn append(&self, new_child: NodeRef<T>) {
        let mut self_borrow = self.0.borrow_mut();
        let mut new_child_borrow = new_child.0.borrow_mut();
        new_child_borrow.detach();
        new_child_borrow.parent = Some(self.0.downgrade());
        match mem::replace(&mut self_borrow.last_child, Some(new_child.0.downgrade())) {
            Some(last_child_weak) => {
                let last_child_strong = last_child_weak.upgrade().unwrap();
                let mut last_child_borrow = last_child_strong.borrow_mut();
                debug_assert!(last_child_borrow.next_sibling.is_none());
                new_child_borrow.previous_sibling = Some(last_child_weak);
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
}

pub struct DataRef<'a, T: 'a>(cell::Ref<'a, Node<T>>);
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
    // Detach a node from its parent and siblings. Children are not affected.
    pub fn detach(&mut self) {
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
