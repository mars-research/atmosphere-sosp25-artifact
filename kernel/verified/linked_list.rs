use vstd::prelude::*;

verus! {

use crate::page::{PagePtr, PagePPtr};
use crate::page_arena::{PageArena, PageElementPtr, PageMetadataPtr};

type Arena<T> = PageArena<Node<T>, PageNode>;
type NodePtr<T> = PageElementPtr<Node<T>>;
type PageNodePtr = PageMetadataPtr<PageNode>;


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

/// A doubly linked list holding sized values.
pub struct LinkedList<T: Default> {
    ptrs: Ghost<Seq<NodePtr<T>>>,
    head: Option<NodePtr<T>>,
    tail: Option<NodePtr<T>>,

    free_ptrs: Ghost<Seq<NodePtr<T>>>,
    free_head: Option<NodePtr<T>>,
    free_tail: Option<NodePtr<T>>,

    page_ptrs: Ghost<Seq<PageNodePtr>>,
    page_head: Option<PageNodePtr>,

    perms: Ghost<Map<PagePPtr, Tracked<Arena<T>>>>,
}

impl<T: Default> LinkedList<T> {

    //start of tmp
    pub closed spec fn view(&self) -> Seq<T>
        recommends self.wf()
    {
        Seq::new(self.ptrs@.len(), |i: int| {
            let ptr = self.ptrs@[i];
            let arena: &Arena<T> = &self.perms@[ptr.page_pptr()]@;
            arena.value_at(ptr.index()).value
        })
    }

    pub closed spec fn unique(&self) -> bool
    {
        forall|i:int, j:int| i != j && 0<=i<self@.len() && 0<=j<self@.len() ==> self@[i] != self@[j]
    }

    pub closed spec fn len(&self) -> nat
    {
        self.ptrs@.len()
    }

    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        Set::empty()
    }

    pub closed spec fn node_ref_valid(&self, nr: &NodeRef<T>) -> bool
    {
        arbitrary()
    }

    pub closed spec fn node_ref_resolve(&self, nr: &NodeRef<T>) -> &T
    {
        arbitrary()
    }

    pub closed spec fn capacity(&self) -> nat {
        self.free_ptrs@.len()
    }

    //end of tmp
    //@Lukas: just change to whatever you want

    // *********************
    // API *****************
    // *********************

    pub fn new() -> (ret: Self)
        ensures ret.wf()
    {
        Self {
            ptrs: Ghost(Seq::empty()),
            head: None,
            tail: None,

            free_ptrs: Ghost(Seq::empty()),
            free_head: None,
            free_tail: None,

            page_ptrs: Ghost(Seq::empty()),
            page_head: None,

            perms: Ghost(Map::empty()),
        }
    }

    pub fn push_back(&mut self, v: T) 
        requires
            old(self).wf(),
            old(self).capacity() > 0
        ensures
            self.wf(),
            // self@ == old(self)@.push(v)
    {

    }

    fn push_back_empty(&mut self, v: T) 
    requires
        old(self).wf(),
        old(self).capacity() > 0,
        old(self).len() == 0,
    ensures
        self.wf(),
        // self@ == old(self)@.push(v)
    {
        // From capacity we 
        
    }

    fn pop_free_ptr(&mut self)
        requires
            old(self).wf(),
            old(self).capacity() == 1,
            old(self).len() == 0,
        ensures
            self.wf(),
            self@ == old(self)@,
            self.capacity() == 0,
    {
        assert(self.free_head.is_some() && self.free_tail.is_some());

        // Update ghost state
        
        proof {
            self.free_ptrs@ = Seq::empty();
        }

        // let result = self.free_tail.clone().unwrap();

        self.free_tail = None;
        self.free_head = None;
        
        // return result;
    }

    // ********************
    // Spec helpers *******
    // ********************

    spec fn prev_of(&self, i: nat) -> Option<NodePtr<T>> {
        if i == 0 {
            None::<NodePtr<T>>
        } else {
            Some(self.ptrs@[i - 1])
        }
    }

    spec fn next_of(&self, i: nat) -> Option<NodePtr<T>> {
        if i + 1 == self.ptrs@.len() {
            None::<NodePtr<T>>
        } else {
            Some(self.ptrs@[i + 1int])
        }
    }

    spec fn free_prev_of(&self, i: nat) -> Option<NodePtr<T>> {
        if i == 0 {
            None::<NodePtr<T>>
        } else {
            Some(self.free_ptrs@[i - 1int])
        }
    }

    spec fn free_next_of(&self, i: nat) -> Option<NodePtr<T>> {
        if i + 1 == self.free_ptrs@.len() {
            None::<NodePtr<T>>
        } else {
            Some(self.free_ptrs@[i + 1int])
        }
    }

    spec fn page_next_of(&self, i: nat) -> Option<PageNodePtr> {
        if i + 1 == self.page_ptrs@.len() {
            None::<PageNodePtr>
        } else {
            Some(self.page_ptrs@[i + 1int])
        }
    }

    // ********************
    // Well Formed Spec ***
    // ********************

    pub closed spec fn wf(&self) -> bool {
        self.wf_perm_map() && self.wf_ptrs() && self.wf_free_ptrs() && self.wf_page_ptrs()
    }

    // Ensures the wf perm map is valid at all times
    spec fn wf_perm_map(&self) -> bool {
        &&& forall|i: PagePPtr| self.perms@.dom().contains(i) ==> #[trigger] self.wf_perm(i)
    }

    spec fn wf_perm(&self, ptr: PagePPtr) -> bool {
        let arena: &Arena<T> = &self.perms@[ptr]@;
        // Key matches arena pointed to
        &&& ptr.id() == arena.page_base()
    }

    // Ensures each ptr is valid
    spec fn wf_ptrs(&self) -> bool {
        self.wf_head() && self.wf_tail() && forall|i: nat| 0 <= i < self.ptrs@.len() ==> #[trigger] self.wf_ptr(i)
    }

    spec fn wf_ptr(&self, i: nat) -> bool {
        let ptr: &NodePtr<T> = &self.ptrs@[i as int];
        let arena: &Arena<T> = &self.perms@[ptr.page_pptr()]@;
        let node = arena.value_at(ptr.index());
        node.prev == self.prev_of(i) && node.next == self.next_of(i)  
    }

    spec fn wf_head(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.head == None::<NodePtr<T>>
        } else {
            self.head == Some(self.ptrs@[0])
        }
    }

    spec fn wf_tail(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.tail == None::<NodePtr<T>>
        } else {
            self.tail == Some(self.ptrs@[self.ptrs@.len() - 1])
        }
    }

    // Ensures each free ptr is valid
    spec fn wf_free_ptrs(&self) -> bool {
        self.wf_free_head() && self.wf_free_tail() && forall|i: nat| 0 <= i < self.free_ptrs@.len() ==> #[trigger] self.wf_free_ptr(i)
    }

    spec fn wf_free_ptr(&self, i: nat) -> bool {
        let ptr: &NodePtr<T> = &self.free_ptrs@[i as int];
        let arena: &Arena<T> = &self.perms@[ptr.page_pptr()]@;
        let node = arena.value_at(ptr.index());
        node.prev == self.prev_of(i) && node.next == self.next_of(i)  
    }

    spec fn wf_free_head(&self) -> bool {
        if self.ptrs@.len() == 0 {
            self.head == None::<NodePtr<T>>
        } else {
            self.head == Some(self.free_ptrs@[0])
        }
    }

    spec fn wf_free_tail(&self) -> bool {
        if self.free_ptrs@.len() == 0 {
            self.tail == None::<NodePtr<T>>
        } else {
            self.tail == Some(self.free_ptrs@[self.free_ptrs@.len() - 1])
        }
    }

    spec fn wf_page_ptrs(&self) -> bool {
        self.wf_page_head() && forall |i: nat| 0 <= i < self.page_ptrs@.len() ==> #[trigger] self.wf_page_ptr(i)
    }

    spec fn wf_page_ptr(&self, i: nat) -> bool {
        let ptr: &PageNodePtr = &self.page_ptrs@[i as int];
        let arena: &Arena<T> = &self.perms@[ptr.page_pptr()]@;
        arena.metadata().next == self.page_next_of(i)     
    }

    spec fn wf_page_head(&self) -> bool {
        if self.page_ptrs@.len() == 0 {
            self.page_head == None::<PageNodePtr>
        } else {
            self.page_head == Some(self.page_ptrs@[0])
        }
    }
}

}

// verus! {

// use crate::page::{PageArena, PagePPtr, PageElementPtr, PageMetadataPtr};
// // use crate::stubs::PageAllocator;

// type Arena<T> = PageArena<Node<T>, PageNode>;
// type NodePtr<T> = PageElementPtr<Node<T>>;
// type PageNodePtr = PageMetadataPtr<PageNode>;

// /// A doubly linked list holding sized values.
// pub struct LinkedList<T: Default> {
//     ptrs: Ghost<Seq<NodePtr<T>>>,
//     next: Option<NodePtr<T>>,
//     prev: Option<NodePtr<T>>,

//     free_ptrs: Ghost<Seq<NodePtr<T>>>,
//     free_next: Option<NodePtr<T>>,
//     free_prev: Option<NodePtr<T>>,

//     page_ptrs: Ghost<Seq<PageNodePtr>>,
//     page_next: Option<PageNodePtr>,

//     perms: Ghost<Map<PagePPtr, Tracked<Arena<T>>>>,
// }

// /// A reference to a node in a linked list.
// pub struct NodeRef<T>(NodePtr<T>);

// /// A node in the value/free list.
// struct Node<T> {
//     value: T,
//     prev: Option<NodePtr<T>>,
//     next: Option<NodePtr<T>>,
// }

// /// A node in the page list.
// ///
// /// This is stored as the per-page metadata in PageArena.
// struct PageNode {
//     next: Option<PageNodePtr>,
// }

// impl<T: Default> LinkedList<T> {

//     // pub fn new() -> (ret: Self)
//     //     ensures ret.wf()
//     // {
//     //     Self {
//     //         ptrs: Ghost(Seq::empty()),
//     //         next: None,
//     //         prev: None,

//     //         free_ptrs: Ghost(Seq::empty()),
//     //         free_next: None,
//     //         free_prev: None,

//     //         page_ptrs: Ghost(Seq::empty()),
//     //         page_next: None,

//     //         perms: Ghost(Map::empty()),
//     //     }
//     // }

//     // // Specs

//     // spec fn wf(&self) -> bool {
//     //     self.wf_ptrs() && self.wf_free_ptrs() && self.wf_page_ptrs()
//     // }

//     // spec fn wf_ptrs(&self) -> bool {
//     //     self.wf_head() && self.wf_tail()
//     // }

//     // spec fn wf_head(&self) -> bool {
//     //     if self.ptrs@.len() == 0 {
//     //         self.head == None
//     //     } else {
//     //         self.head == Some(self.ptrs@[0])
//     //     }
//     // }

//     // spec fn wf_tail(&self) -> bool {
//     //     if self.ptrs@.len() == 0 {
//     //         self.head == None
//     //     } else {
//     //         self.head == Some(self.ptrs@[self.ptrs@.len() - 1])
//     //     }
//     // }

//     // spec fn wf_free_ptrs(&self) -> bool {
//     //     true
//     // }

//     // spec fn wf_page_ptrs(&self) -> bool {
//     //     true
//     // }

//     // Maybe construct a Seq from PageElementPtrs and PageArenas?
//     // pub spec fn view(self) -> Seq<T>;

//     // TODO

//     // #[verifier(external_body)] // TODO
//     // pub fn push(&mut self, value: T, allocator: &mut PageAllocator) -> (result: NodeRef<T>)
//     //     requires
//     //     ensures
//     //         self@.len() == old(self)@.len() + 1,
//     // {
//     //     todo!()
//     // }

//     // #[verifier(external_body)] // TODO
//     // pub fn pop(&mut self) -> Option<NodeRef<T>> {
//     //     todo!()
//     // }

//     // #[verifier(external_body)] // TODO
//     // pub fn remove(&mut self, node: NodeRef<T>) -> Option<NodeRef<T>> {
//     //     todo!()
//     // }

//     // /// Destroys the link list, returning all allocated pages back to the allocator.
//     // #[verifier(external_body)] // TODO
//     // pub fn dispose(self, allocator: &mut PageAllocator) {
//     //     todo!()
//     // }

//     /// Trusted methods

//     // #[verifier(external_body)]
//     // fn init_view(&self)
//     //     requires
//     //         self.head.is_None(),
//     //     ensures
//     //         self@ == Seq::<T>::empty(),
//     // {
//     // }
// }

// }
