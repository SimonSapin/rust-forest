#![feature(alloc)]

use std::cell::{self, RefCell};
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
