use vstd::prelude::*;
verus! {



use crate::define::*;
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

    page_ptrs: Ghost<Seq<PageNodePtr>>,
    page_head: Option<PageNodePtr>,

    perms: Tracked<Map<int, Arena<T>>>,
}

impl<T: Default> LinkedList<T> {

    //start of tmp
    pub closed spec fn view(&self) -> Seq<T>
        recommends self.wf()
    {
        Seq::new(self.ptrs@.len(), |i: int| {
            let ptr = self.ptrs@[i];
            let arena: &Arena<T> = &self.perms@[ptr.page_pptr().id()];
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

            page_ptrs: Ghost(Seq::empty()),
            page_head: None,

            perms: Tracked(Map::tracked_empty()),
        }
    }

    fn push_back(&mut self, v: T)
        requires
            old(self).wf(),
            old(self).free_ptrs@.len() > 0,
        ensures
            // self.wf(),
            self.free_ptrs@.len() == old(self).free_ptrs@.len() - 1,
            self.ptrs@.len() == old(self).ptrs@.len() + 1,
            v == self.perms@[self.ptrs@.last().page_base()].value_at(self.ptrs@.last().index()).value
    {
        assert(self.free_head == Some(self.free_ptrs@[0]));
        assert(Self::wf_free_ptr(self.free_ptrs@, 0, self.perms@));
        assert(self.perms@.dom().contains(self.free_ptrs@[0].page_base()));

        let ptr = self.free_head.as_ref().unwrap().clone();

        {
            let ptr_ref: &NodePtr<T> = self.free_head.as_ref().unwrap();

            assert(ptr.same_ptr(ptr_ref));

            assert(ptr_ref.same_ptr(&self.free_ptrs@[0]));
            assert(ptr_ref.page_base() == self.free_ptrs@[0].page_base());

            assert(self.perms@.dom().contains(self.free_ptrs@[0].page_base()));
            assert(self.perms@.dom().contains(ptr_ref.page_base()));
        }

        assert(self.perms@.dom().contains(ptr.page_base()));

        // Assert that the current perms map is wf
        assert(Self::wf_perms(self.perms@));
        // So ptr.page_base() is wf
        assert(Self::wf_perm(ptr.page_base(), self.perms@[ptr.page_base()]));

        // Use lemma to show that after removing the permission, the map is still well formed
        proof {
            Self::lemma_remove_wf_perms(self.perms@, ptr.page_base());
        }

        // Get permission
        let tracked mut perm: Arena<T> = (self.perms.borrow_mut()).tracked_remove(ptr.page_base());

        assert(Self::wf_perms(self.perms@));
        assert(perm.wf());
        assert(perm.page_base() == ptr.page_base());
        assert(perm.has_element(&ptr));

        // Update free ptrs linked list and model sequence
        let node: &Node<T> = ptr.borrow::<PageNode>(Tracked(&perm));

        // assert(Self::wf_free_ptrs(self.free_head, ));

        match &node.next {
            Some(p) => self.free_head = Some(p.clone()),
            None => self.free_head = None,
        }

        proof {
            self.free_ptrs@ = self.free_ptrs@.subrange(1 as int, self.free_ptrs@.len() as int);
        }

        // assert(self.wf_free_ptrs());

        // Update contents of this ptr
        let tail = match &self.tail {
            Some(p) => Some(p.clone()),
            None => None,
        };

        ptr.put::<PageNode>(Tracked(&mut perm), Node { value: v, prev: tail, next: None });

        assert(Self::wf_perm(ptr.page_base(), perm));

        proof {
            Self::lemma_insert_wf_perms(self.perms@, ptr.page_base(), perm);
            (self.perms.borrow_mut()).tracked_insert(ptr.page_base(), perm);
        }

        assert(Self::wf_perms(self.perms@));

        // Update ptrs linked list and model sequence
        if self.tail.is_none() {
            self.head = Some(ptr.clone());
        }
        self.tail = Some(ptr.clone());

        let cloned_ptr = ptr.clone();

        proof {
            self.ptrs@ = self.ptrs@.push(cloned_ptr);
        }
    }

    // ********************
    // Spec helpers *******
    // ********************

    spec fn page_next_of(ptrs: Seq<PageNodePtr>, i: nat) -> Option<PageNodePtr> {
        if i + 1 == ptrs.len() {
            None::<PageNodePtr>
        } else {
            Some(ptrs[i + 1int])
        }
    }

    spec fn node_next_of(ptrs: Seq<NodePtr<T>>, i: nat) -> Option<NodePtr<T>> {
        if i + 1 == ptrs.len() {
            None::<NodePtr<T>>
        } else {
            Some(ptrs[i + 1int])
        }
    }

    spec fn node_prev_of(ptrs: Seq<NodePtr<T>>, i: nat) -> Option<NodePtr<T>> {
        if i == 0 {
            None::<NodePtr<T>>
        } else {
            Some(ptrs[i - 1])
        }
    }

    // ********************
    // Lemmas *************
    // ********************

    proof fn lemma_remove_wf_perms(perms: Map<int, Arena<T>>, key: int)
        requires
            Self::wf_perms(perms)
        ensures
            Self::wf_perms(perms.remove(key))
    {
    }

    proof fn lemma_insert_wf_perms(perms: Map<int, Arena<T>>, key: int, perm: Arena<T>)
        requires
            Self::wf_perms(perms),
            Self::wf_perm(key, perm),
        ensures
            Self::wf_perms(perms.insert(key, perm))
    {
    }

    // *********************
    // Well Formed Helpers *
    // *********************

    // *************************
    // Permission Map

    // Ensures the perm map is valid at all times
    spec fn wf_perms(perms: Map<int, Arena<T>>) -> bool {
        &&& forall|i: int| perms.dom().contains(i) ==> #[trigger] Self::wf_perm(i, perms[i])
    }

    // Checks that for a given pointer, there is a permission corresponding to that page, and that the permission is well formed
    spec fn wf_perm(ptr: int, perm: Arena<T>) -> bool {
        // Key matches arena pointed to
        &&& ptr == perm.page_base()
        &&& perm.wf()
    }

    // *************************
    // Free Ptrs

    spec fn wf_free_ptrs(head: Option<NodePtr<T>>, ptrs: Seq<NodePtr<T>>, perms: Map<int, Arena<T>>) -> bool {
        &&& Self::wf_free_head(head, ptrs)
        &&& forall|i: nat| 0 <= i < ptrs.len() ==> #[trigger] Self::wf_free_ptr(ptrs, i, perms)
    }

    spec fn wf_free_head(head: Option<NodePtr<T>>, ptrs: Seq<NodePtr<T>>) -> bool {
        if ptrs.len() == 0 {
            head == None::<NodePtr<T>>
        } else {
            head == Some(ptrs[0])
        }
    }

    spec fn wf_free_ptr(ptrs: Seq<NodePtr<T>>, i: nat, perms: Map<int, Arena<T>>) -> bool {
        let ptr: NodePtr<T> = ptrs[i as int];
        let base = ptr.page_base();

        perms.dom().contains(base)
        && perms[base].has_element(&ptr)
        && (perms[base].value_at(ptr.index()).next == Self::node_next_of(ptrs, i))
    }


    // ********************
    // Well Formed Spec ***
    // ********************

    pub closed spec fn wf(&self) -> bool {
        &&& Self::wf_perms(self.perms@)
        &&& Self::wf_free_ptrs(self.free_head, self.free_ptrs@, self.perms@)
    }





    // // Ensures each ptr is valid
    // spec fn wf_ptrs(&self) -> bool {
    //     self.wf_head() && self.wf_tail() && forall|i: nat| 0 <= i < self.ptrs@.len() ==> #[trigger] self.wf_ptr(i)
    // }

    // spec fn wf_ptr(&self, i: nat) -> bool {
    //     let ptr: &NodePtr<T> = &self.ptrs@[i as int];
    //     let arena: &Arena<T> = &self.perms@[ptr.page_base()];
    //     let node = arena.value_at(ptr.index());
    //     node.prev == self.prev_of(i) && node.next == self.next_of(i)
    // }

    // spec fn wf_head(&self) -> bool {
    //     if self.ptrs@.len() == 0 {
    //         self.head == None::<NodePtr<T>>
    //     } else {
    //         self.head == Some(self.ptrs@[0])
    //     }
    // }

    // spec fn wf_tail(&self) -> bool {
    //     if self.ptrs@.len() == 0 {
    //         self.tail == None::<NodePtr<T>>
    //     } else {
    //         self.tail == Some(self.ptrs@[self.ptrs@.len() - 1])
    //     }
    // }

    // spec fn wf_page_ptrs(&self) -> bool {
    //     self.wf_page_head() && forall |i: nat| 0 <= i < self.page_ptrs@.len() ==> #[trigger] self.wf_page_ptr(i)
    // }

    // spec fn wf_page_ptr(&self, i: nat) -> bool {
    //     let ptr: &PageNodePtr = &self.page_ptrs@[i as int];
    //     let arena: &Arena<T> = &self.perms@[ptr.page_base()];
    //     arena.metadata().next == self.page_next_of(i)
    // }

    // spec fn wf_page_head(&self) -> bool {
    //     if self.page_ptrs@.len() == 0 {
    //         self.page_head == None::<PageNodePtr>
    //     } else {
    //         self.page_head == Some(self.page_ptrs@[0])
    //     }
    // }
}

}
