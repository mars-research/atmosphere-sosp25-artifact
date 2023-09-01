use vstd::prelude::*;

verus! {

use crate::page::{PageArena, PagePPtr, PageElementPtr, PageMetadataPtr};
use crate::stubs::PageAllocator;

type Arena<T> = PageArena<Node<T>, PageNode>;
type NodePtr<T> = PageElementPtr<Node<T>>;
type PageNodePtr = PageMetadataPtr<PageNode>;

/// A linked list holding sized values.
pub struct LinkedList<T: Default> {
    head: Option<NodePtr<T>>,
    free_head: Option<NodePtr<T>>,
    pages_head: Option<PageNodePtr>,

    perms: Ghost<Map<PagePPtr, Tracked<Arena<T>>>>,
}

/// A reference to a node in a linked list.
pub struct NodeRef<T>(NodePtr<T>);

/// A node in the value/free list.
struct Node<T> {
    value: T,
    prev: Option<NodePtr<T>>,
    next: Option<NodePtr<T>>,
}

/// A node in the page list.
///
/// This is stored as the per-page metadata in PageArena.
struct PageNode {
    next: Option<PageNodePtr>,
}

impl<T: Default> LinkedList<T> {
    pub fn new() -> (ret: Self)
        ensures
            // ...
    {
        let r = Self {
            head: None,
            free_head: None,
            pages_head: None,

            perms: Ghost(Map::empty()),
        };

        r.init_view();

        r
    }

    /// Specs

    // Maybe construct a Seq from PageElementPtrs and PageArenas?
    pub spec fn view(self) -> Seq<T>;

    // TODO

    #[verifier(external_body)] // TODO
    pub fn push(&mut self, value: T, allocator: &mut PageAllocator) -> (result: NodeRef<T>)
        requires
        ensures
            self@.len() == old(self)@.len() + 1,
    {
        todo!()
    }

    #[verifier(external_body)] // TODO
    pub fn pop(&mut self) -> Option<NodeRef<T>> {
        todo!()
    }

    #[verifier(external_body)] // TODO
    pub fn remove(&mut self, node: NodeRef<T>) -> Option<NodeRef<T>> {
        todo!()
    }

    /// Destroys the link list, returning all allocated pages back to the allocator.
    #[verifier(external_body)] // TODO
    pub fn dispose(self, allocator: &mut PageAllocator) {
        todo!()
    }

    /// Trusted methods

    #[verifier(external_body)]
    fn init_view(&self)
        requires
            self.head.is_None(),
        ensures
            self@ == Seq::<T>::empty(),
    {
    }
}

}
