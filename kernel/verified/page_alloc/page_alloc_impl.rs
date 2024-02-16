use vstd::prelude::*;
verus!{
// use vstd::ptr::*;
// use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;

use crate::define::*;

use crate::page_alloc::*;



impl PageAllocator {

    pub fn get_num_free_pages(&self) -> (ret: usize)
        requires
            self.wf(),
        ensures 
            ret == self.free_pages.len(),
    {
        self.free_pages.len()
    }

    pub fn alloc_kernel_mem(&mut self) -> (ret : (PagePtr,Tracked<PagePerm>))
        requires 
            old(self).wf(),
            old(self).free_pages.len() > 0,
        ensures
            self.wf(),
            old(self).get_free_pages_as_set().contains(ret.0),
            self.get_free_pages_as_set().contains(ret.0) == false,
            self.get_free_pages_as_set() =~= self.get_free_pages_as_set().remove(ret.0),
            self.get_allocated_pages() =~= old(self).get_allocated_pages().insert(ret.0),
            self.get_page_table_pages() =~= old(self).get_page_table_pages(),
            self.get_mapped_pages() =~= old(self).get_mapped_pages(),
            self.get_allocated_pages().contains(ret.0),
            self.get_available_pages() =~= old(self).get_available_pages(),
            ret.1@@.pptr == ret.0,
            ret.1@@.value.is_Some(),
            self.free_pages.len() as int =~= old(self).free_pages.len() as int - 1,
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.get_page_mappings(page_ptr) =~= old(self).get_page_mappings(page_ptr),
    {
        proof{
            self.page_array_wf_derive();
        }
        let ptr = self.free_pages.pop_unique();
        assert(old(self).free_pages@.contains(ptr));
        assert(self.page_array@[page_ptr2page_index(ptr) as int].is_io_page == false);
        assert(old(self).get_free_pages_as_set().contains(ptr));
        assert(self.free_pages@.contains(ptr) == false);

        assert(old(self).get_allocated_pages() * old(self).get_free_pages_as_set() =~= Set::empty());
        assert(old(self).get_allocated_pages().contains(ptr) == false);
        assert(self.allocated_pages@.contains(ptr) == false);
        self.page_array.set_page_state(page_ptr2page_index(ptr),ALLOCATED);
        proof{
            self.allocated_pages@ = self.allocated_pages@.insert(ptr);
        }

        assert(self.free_pages.wf());
        assert(self.free_pages_wf());

        assert(self.get_free_pages_as_set() =~= old(self).get_free_pages_as_set().remove(ptr));

        assert((self.get_allocated_pages() + self.get_free_pages_as_set()) =~= (old(self).get_allocated_pages() + old(self).get_free_pages_as_set()));
        assert((self.get_allocated_pages() + self.get_mapped_pages() + self.get_free_pages_as_set()) + self.get_page_table_pages() =~= self.get_available_pages());
        assert(self.mem_wf());
        assert(self.allocated_pages_wf());
        assert(self.mapped_pages_wf());

        assert(self.page_perms@.dom().contains(ptr));
        let tracked mut page_perm: PagePerm =
            (self.page_perms.borrow_mut()).tracked_remove(ptr);
        assert(page_perm@.value.is_Some());
        return (ptr,Tracked(page_perm));
    }

    pub fn free_kernel_mem(&mut self, ptr : PagePtr, perm: Tracked<PagePerm>)
        requires 
            old(self).wf(),
            old(self).get_allocated_pages().contains(ptr),
            old(self).free_pages.len() < NUM_PAGES,
            perm@@.pptr == ptr,
            perm@@.value.is_Some(),
        ensures
            self.wf(),
    {
        assert(page_ptr_valid(ptr));
        proof{self.allocated_pages@ = self.allocated_pages@.remove(ptr);}
        assert(self.get_free_pages_as_set().contains(ptr) == false);
        assert(self.free_pages@.contains(ptr) == false);
        self.free_pages.push_unique(ptr);
        assert(self.page_array@[page_ptr2page_index(ptr) as int].rf_count == 0);
        self.page_array.set_page_state(page_ptr2page_index(ptr),FREE);
        proof{
            assert(self.page_perms@.dom().contains(ptr) == false);
            (self.page_perms.borrow_mut())
                .tracked_insert(ptr, perm.get());
        }
        assert(self.wf());
    }

    pub fn alloc_page_and_map(&mut self, target: (Pcid,VAddr), page_type: PageType) -> (ret : PagePtr)
        requires
            old(self).wf(),
            old(self).free_pages.len() > 0,
        ensures
            self.wf(),
    {
        let ret = self.free_pages.pop_unique();
        self.page_array.set_page_state(page_ptr2page_index(ret),MAPPED);
        self.page_array.set_page_rf_count(page_ptr2page_index(ret),1);
        assert(self.page_array@[page_ptr2page_index(ret) as int].mappings@.dom().len() == 0);
        assert(self.page_array@[page_ptr2page_index(ret) as int].mappings@.dom().finite());
        assert(self.page_array@[page_ptr2page_index(ret) as int].mappings@.dom() =~= Set::empty());
        let new_mappings = Ghost(self.page_array@[spec_page_ptr2page_index(ret) as int].mappings@.insert(target, page_type));
        self.page_array.set_page_mappings(page_ptr2page_index(ret),new_mappings);

        assert(self.mapped_pages@.contains(ret) == false);
        proof{
            self.mapped_pages@ = self.mapped_pages@.insert(ret);
        }
        assert(self.wf());
        return ret;
    }

    //Map a page to a process's pagetable whether or not it's an IO page
    pub fn map_user_page(&mut self, page_ptr : PagePtr, target: (Pcid,VAddr), page_type: PageType)
        requires
            page_ptr_valid(page_ptr),
            old(self).wf(),
            old(self).get_mapped_pages().contains(page_ptr),
            old(self).get_page_mappings(page_ptr).contains(target) == false,
            old(self).page_array@[page_ptr2page_index(page_ptr) as int].rf_count < usize::MAX,
        ensures
            self.wf(),
            self.free_pages =~= old(self).free_pages,
            self.page_table_pages =~= old(self).page_table_pages,
            self.allocated_pages =~= old(self).allocated_pages,
            self.mapped_pages =~= old(self).mapped_pages,
            self.available_pages =~= old(self).available_pages,
            forall|i:int| #![auto] 0<=i<NUM_PAGES && i != page_ptr2page_index(page_ptr) ==> self.page_array@[i] =~= old(self).page_array@[i],
            self.page_array@[page_ptr2page_index(page_ptr) as int].mappings@ =~= old(self).page_array@[page_ptr2page_index(page_ptr) as int].mappings@.insert(target, page_type),
            self.page_array@[page_ptr2page_index(page_ptr) as int].mappings@.dom() =~= old(self).page_array@[page_ptr2page_index(page_ptr) as int].mappings@.dom().insert(target),
            forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].io_mappings@ =~= old(self).page_array@[i].io_mappings@,
            forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].io_mappings@.dom() =~= old(self).page_array@[i].io_mappings@.dom(),
    {
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count != 0);
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count > 0);
        let old_rf_count = self.page_array.get(page_ptr2page_index(page_ptr)).rf_count;
        let new_rf_count = old_rf_count + 1;
        self.page_array.set_page_rf_count(page_ptr2page_index(page_ptr), new_rf_count);
        let new_mappings = Ghost(self.page_array@[spec_page_ptr2page_index(page_ptr) as int].mappings@.insert(target, page_type));
        self.page_array.set_page_mappings(page_ptr2page_index(page_ptr),new_mappings);

        assert(self.mem_wf());
        assert(self.page_array_wf());
        assert(self.free_pages_wf());
        assert(self.page_table_pages_wf());
        assert(self.allocated_pages_wf());
        assert(self.mapped_pages_wf());
        assert(self.rf_wf());
        assert(self.page_perms_wf());
        assert(self.available_pages_wf());
        assert(self.io_pages_wf());

        assert(self.wf());
    }

    //Unmap a page from a process's pagetable whether or not it's an IO page
    pub fn unmap_user_page(&mut self, page_ptr : PagePtr, target: (Pcid,VAddr))
        requires
            page_ptr_valid(page_ptr),
            old(self).wf(),
            old(self).get_mapped_pages().contains(page_ptr),
            old(self).get_page_mappings(page_ptr).contains(target) == true,
        ensures
            self.wf(),
            // self.free_pages =~= old(self).free_pages,
            self.page_table_pages =~= old(self).page_table_pages,
            self.allocated_pages =~= old(self).allocated_pages,
            // self.mapped_pages =~= old(self).mapped_pages,
            // self.available_pages =~= old(self).available_pages,
            forall|i:int| #![auto] 0<=i<NUM_PAGES && i != page_ptr2page_index(page_ptr) ==> self.page_array@[i] =~= old(self).page_array@[i],
            self.page_array@[page_ptr2page_index(page_ptr) as int].mappings@ =~= old(self).page_array@[page_ptr2page_index(page_ptr) as int].mappings@.remove(target),
            self.page_array@[page_ptr2page_index(page_ptr) as int].mappings@.dom() =~= old(self).page_array@[page_ptr2page_index(page_ptr) as int].mappings@.dom().remove(target),
            forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].io_mappings@ =~= old(self).page_array@[i].io_mappings@,
            forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].io_mappings@.dom() =~= old(self).page_array@[i].io_mappings@.dom(),

    {
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count > 0);
        let old_rf_count = self.page_array.get(page_ptr2page_index(page_ptr)).rf_count;
        let new_rf_count = old_rf_count - 1;
        self.page_array.set_page_rf_count(page_ptr2page_index(page_ptr), new_rf_count);
        let new_mappings = Ghost(self.page_array@[spec_page_ptr2page_index(page_ptr) as int].mappings@.remove(target));
        self.page_array.set_page_mappings(page_ptr2page_index(page_ptr),new_mappings);
        if new_rf_count == 0{
            if self.page_array.get(page_ptr2page_index(page_ptr)).is_io_page == true {
                proof{self.available_pages@ = self.available_pages@.remove(page_ptr);}
                self.page_array.set_page_state(page_ptr2page_index(page_ptr), UNAVAILABLE);
                proof{self.mapped_pages@ = self.mapped_pages@.remove(page_ptr);}
                proof{(self.page_perms.borrow_mut()).tracked_remove(page_ptr);}
                assert(self.mem_wf());
                assert(self.page_array_wf());
                assert(self.free_pages_wf());
                assert(self.page_table_pages_wf());
                assert(self.allocated_pages_wf());
                assert(self.mapped_pages_wf());
                assert(self.rf_wf());
                assert(self.page_perms_wf());
                assert(self.available_pages_wf());
                assert(self.io_pages_wf());
                assert(self.wf());
            }
            else{
                assert(self.page_array@[spec_page_ptr2page_index(page_ptr) as int].mappings@.dom() =~= Set::empty());
                assert(self.free_pages@.contains(page_ptr) == false);
                proof{
                    Seq::new(NUM_PAGES as nat, |i: int| page_index2page_ptr(i as usize)).lemma_cardinality_of_set();
                }
                assert(self.get_available_pages().len() <= NUM_PAGES);
                assert(self.get_free_pages_as_set().contains(page_ptr) == false);
                assert(self.get_available_pages().contains(page_ptr) == true);
                assert(self.get_free_pages_as_set().subset_of(self.get_available_pages()));
                proof{vstd::set_lib::lemma_len_subset(self.get_free_pages_as_set(),self.get_available_pages().remove(page_ptr) )};
                assert(self.get_free_pages_as_set().len() < NUM_PAGES);
                assert(self.free_pages@.no_duplicates());
                proof{
                    self.free_pages@.unique_seq_to_set();
                }
                assert(self.free_pages@.len() < NUM_PAGES);
                self.free_pages.push_unique(page_ptr);
                self.page_array.set_page_state(page_ptr2page_index(page_ptr), FREE);
                proof{self.mapped_pages@ = self.mapped_pages@.remove(page_ptr);}
                // assert(self.mem_wf());
                // assert(self.page_array_wf());
                // assert(self.free_pages_wf());
                // assert(self.page_table_pages_wf());
                // assert(self.allocated_pages_wf());
                // assert(self.mapped_pages_wf());
                // assert(self.rf_wf());
                // assert(self.page_perms_wf());
                // assert(self.available_pages_wf());
                // assert(self.io_pages_wf());
                assert(self.wf());
            }
        }else{
            // assert(self.mem_wf());
            // assert(self.page_array_wf());
            // assert(self.free_pages_wf());
            // assert(self.page_table_pages_wf());
            // assert(self.allocated_pages_wf());
            // assert(self.mapped_pages_wf());
            // assert(self.rf_wf());
            // assert(self.page_perms_wf());
            // assert(self.available_pages_wf());
            // assert(self.io_pages_wf());
            assert(self.wf());
        }
    }

        pub fn alloc_pagetable_mem(&mut self) -> (ret : (PagePtr,Tracked<PagePerm>))
        requires 
            old(self).wf(),
            old(self).free_pages.len() > 0,
        ensures
            self.wf(),
            old(self).get_free_pages_as_set().contains(ret.0),
            self.get_free_pages_as_set().contains(ret.0) == false,
            self.get_free_pages_as_set() =~= old(self).get_free_pages_as_set().remove(ret.0),
            self.get_allocated_pages() =~= old(self).get_allocated_pages(),
            self.get_page_table_pages() =~= old(self).get_page_table_pages().insert(ret.0),
            self.get_mapped_pages() =~= old(self).get_mapped_pages(),
            self.get_page_table_pages().contains(ret.0),
            self.get_available_pages() =~= old(self).get_available_pages(),
            ret.1@@.pptr == ret.0,
            ret.1@@.value.is_Some(),
            self.free_pages.len() as int =~= old(self).free_pages.len() as int - 1,
            forall|page_ptr:PagePtr| #![auto] self.available_pages@.contains(page_ptr) ==> self.get_page_mappings(page_ptr) =~= old(self).get_page_mappings(page_ptr),
    {
        proof{
            self.page_array_wf_derive();
        }
        let ptr = self.free_pages.pop_unique();
        assert(old(self).free_pages@.contains(ptr));
        assert(self.page_array@[page_ptr2page_index(ptr) as int].is_io_page == false);
        assert(old(self).get_free_pages_as_set().contains(ptr));
        assert(self.free_pages@.contains(ptr) == false);

        assert(old(self).get_page_table_pages() * old(self).get_free_pages_as_set() =~= Set::empty());
        assert(old(self).get_page_table_pages().contains(ptr) == false);
        assert(self.page_table_pages@.contains(ptr) == false);
        self.page_array.set_page_state(page_ptr2page_index(ptr),PAGETABLE);
        proof{
            self.page_table_pages@ = self.page_table_pages@.insert(ptr);
        }

        assert(self.free_pages.wf());
        assert(self.free_pages_wf());

        assert(self.get_free_pages_as_set() =~= old(self).get_free_pages_as_set().remove(ptr));

        assert((self.get_page_table_pages() + self.get_free_pages_as_set()) =~= (old(self).get_page_table_pages() + old(self).get_free_pages_as_set()));
        assert((self.get_allocated_pages() + self.get_mapped_pages() + self.get_free_pages_as_set()) + self.get_page_table_pages() =~= self.get_available_pages());
        assert(self.mem_wf());
        assert(self.page_table_pages_wf());
        assert(self.mapped_pages_wf());

        assert(self.page_perms@.dom().contains(ptr));
        let tracked mut page_perm: PagePerm =
            (self.page_perms.borrow_mut()).tracked_remove(ptr);
        assert(page_perm@.value.is_Some());
        return (ptr,Tracked(page_perm));
    }

    pub fn free_pagetable_mem(&mut self, ptr : PagePtr, perm: Tracked<PagePerm>)
        requires 
            old(self).wf(),
            old(self).get_page_table_pages().contains(ptr),
            old(self).free_pages.len() < NUM_PAGES,
            perm@@.pptr == ptr,
            perm@@.value.is_Some(),
        ensures
            self.wf(),
    {
        assert(page_ptr_valid(ptr));
        proof{self.page_table_pages@ = self.page_table_pages@.remove(ptr);}
        assert(self.get_free_pages_as_set().contains(ptr) == false);
        assert(self.free_pages@.contains(ptr) == false);
        self.free_pages.push_unique(ptr);
        assert(self.page_array@[page_ptr2page_index(ptr) as int].rf_count == 0);
        self.page_array.set_page_state(page_ptr2page_index(ptr),FREE);
        proof{
            assert(self.page_perms@.dom().contains(ptr) == false);
            (self.page_perms.borrow_mut())
                .tracked_insert(ptr, perm.get());
        }
        assert(self.wf());
    }
    // #[verifier(external_body)]
    pub fn init(&mut self, boot_page_ptrs: &ArrayVec<(PageState,VAddr),NUM_PAGES>, mut boot_page_perms: Tracked<Map<PagePtr,PagePerm>>)
    requires
        old(self).page_array.wf(),
        old(self).free_pages.wf(),
        old(self).free_pages.len() == 0,
        old(self).page_table_pages@ =~= Set::empty(),
        old(self).allocated_pages@ =~= Set::empty(),
        old(self).mapped_pages@ =~= Set::empty(),
        old(self).available_pages@ =~= Set::empty(),
        old(self).page_perms@.dom() =~= Set::empty(),
        boot_page_ptrs.wf(),
        boot_page_ptrs.len() == NUM_PAGES,
        (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 <= IO),
        (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> boot_page_ptrs@[i as int].0 != ALLOCATED),
        (forall|i:usize| #![auto] 0<=i<NUM_PAGES && (boot_page_ptrs@[i as int].0 == FREE || boot_page_ptrs@[i as int].0 == MAPPED || boot_page_ptrs@[i as int].0 == IO)==> 
            (boot_page_perms@.dom().contains(page_index2page_ptr(i))
             && 
             boot_page_perms@[page_index2page_ptr(i)]@.pptr == page_index2page_ptr(i)
             &&
             boot_page_perms@[page_index2page_ptr(i)]@.value.is_Some()
            )
        ),
        NUM_PAGES * 4096 <= usize::MAX,
    ensures
        self.wf(),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == FREE ==> self.free_pages@.contains(page_index2page_ptr(i)), 
        self.allocated_pages@ =~= Set::empty(), 
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == MAPPED ==> self.get_page_mappings(page_index2page_ptr(i)) =~= Set::<(Pcid,VAddr)>::empty().insert((0,boot_page_ptrs@[i as int].1)),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == MAPPED ==> self.get_page_mappings(page_index2page_ptr(i)).contains((0,boot_page_ptrs@[i as int].1)),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == MAPPED ==> self.get_mapped_pages().contains(page_index2page_ptr(i)),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == IO ==> self.get_page_mappings(page_index2page_ptr(i)) =~= Set::<(Pcid,VAddr)>::empty().insert((0,boot_page_ptrs@[i as int].1)),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == IO ==> self.get_page_mappings(page_index2page_ptr(i)).contains((0,boot_page_ptrs@[i as int].1)),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == IO ==> self.get_mapped_pages().contains(page_index2page_ptr(i)),
        forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == PAGETABLE ==> self.get_page_table_pages().contains(page_index2page_ptr(i)),
        forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr),
        forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) <==> (
            page_ptr_valid(page_ptr)
            &&
            0<=page_ptr2page_index(page_ptr as usize)<NUM_PAGES
            &&
            boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
        ),
{
    proof{self.free_pages@.unique_seq_to_set();}
    self.mapped_pages = Ghost(Set::empty());
    let mut i = 0;
        while i != NUM_PAGES
            invariant
                0<= i <= NUM_PAGES,
                NUM_PAGES * 4096 <= usize::MAX,
                forall|j:usize| #![auto] 0<=j<NUM_PAGES ==> boot_page_ptrs@[j as int].0 <= IO,
                forall|j:usize| #![auto] 0<=j<NUM_PAGES ==> boot_page_ptrs@[j as int].0 != ALLOCATED,
                forall|j:usize| #![auto] 0<=j<i ==> boot_page_ptrs@[j as int].0 <= IO,
                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].state != ALLOCATED, 
                forall|j:usize| #![auto]  i<=j<NUM_PAGES && (boot_page_ptrs@[j as int].0 == FREE || boot_page_ptrs@[j as int].0 == MAPPED || boot_page_ptrs@[j as int].0 == IO) ==> 
                    (boot_page_perms@.dom().contains(page_index2page_ptr(j))
                    && 
                    boot_page_perms@[page_index2page_ptr(j)]@.pptr == page_index2page_ptr(j)
                    &&
                    boot_page_perms@[page_index2page_ptr(j)]@.value.is_Some()
                    ),
                boot_page_ptrs.wf(),
                boot_page_ptrs.len() == NUM_PAGES,
                self.free_pages.wf(),
                self.page_array.wf(),
                self.free_pages.unique(),
                self.free_pages.len() <= i,
                self.allocated_pages@ =~= Set::empty(), 
                self.mapped_pages@.finite(),
                self.page_table_pages@.finite(),
                self.available_pages@.finite(),
                // self.available_pages@.len() <= NUM_PAGES,
                self.available_pages@.len() <= i, 
                self.mapped_pages@.disjoint(self.get_free_pages_as_set()),
                self.mapped_pages@.disjoint(self.page_table_pages@),
                self.page_table_pages@.disjoint(self.get_free_pages_as_set()),
                self.available_pages@ =~= self.get_free_pages_as_set() + self.mapped_pages@ + self.page_table_pages@,

                forall|j:usize| #![auto] i<=j<NUM_PAGES ==> self.free_pages@.contains(page_index2page_ptr(j)) == false,
                forall|j:usize| #![auto] i<=j<NUM_PAGES ==> self.allocated_pages@.contains(page_index2page_ptr(j)) == false,
                forall|j:usize| #![auto] i<=j<NUM_PAGES ==> self.page_table_pages@.contains(page_index2page_ptr(j)) == false,
                forall|j:usize| #![auto] i<=j<NUM_PAGES ==> self.mapped_pages@.contains(page_index2page_ptr(j)) == false,
                forall|j:usize| #![auto] 0<=j<self.free_pages.len() ==> self.free_pages@[j as int] < page_index2page_ptr(i),

                forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr),
                forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr),
                forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == FREE),
                forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == MAPPED),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == PAGETABLE),

                forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].is_io_page == false),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].is_io_page == false),

                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == UNAVAILABLE ==> self.page_array@[j as int].state == UNAVAILABLE, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == FREE ==> self.page_array@[j as int].state == FREE, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == ALLOCATED ==> self.page_array@[j as int].state == ALLOCATED, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == PAGETABLE ==> self.page_array@[j as int].state == PAGETABLE, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == MAPPED ==> self.page_array@[j as int].state == MAPPED, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == IO ==> self.page_array@[j as int].state == MAPPED, 

                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == UNAVAILABLE ==> self.page_array@[j as int].is_io_page == false, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == FREE ==> self.page_array@[j as int].is_io_page == false,
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == ALLOCATED ==> self.page_array@[j as int].is_io_page == false, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == PAGETABLE ==> self.page_array@[j as int].is_io_page == false,  
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == MAPPED ==> self.page_array@[j as int].is_io_page == false, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == IO ==> self.page_array@[j as int].is_io_page == true, 

                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == UNAVAILABLE ==> self.page_array@[j as int].rf_count == 0, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == FREE ==> self.page_array@[j as int].rf_count == 0, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == ALLOCATED ==> self.page_array@[j as int].rf_count == 0, 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == PAGETABLE ==> self.page_array@[j as int].rf_count == 0, 

                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == UNAVAILABLE ==> self.page_array@[j as int].mappings@ =~= Map::empty(), 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == FREE ==> self.page_array@[j as int].mappings@ =~= Map::empty(), 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == ALLOCATED ==> self.page_array@[j as int].mappings@ =~= Map::empty(), 
                forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int].0 == PAGETABLE ==> self.page_array@[j as int].mappings@ =~= Map::empty(), 


                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == FREE ==> self.free_pages@.contains(self.page_array@[j as int].start),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == FREE ==> self.free_pages@.contains(page_index2page_ptr(j)), 
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == ALLOCATED ==> self.allocated_pages@.contains(self.page_array@[j as int].start),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == ALLOCATED ==> self.allocated_pages@.contains(page_index2page_ptr(j)), 
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == PAGETABLE ==> self.page_table_pages@.contains(self.page_array@[j as int].start),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == PAGETABLE ==> self.page_table_pages@.contains(page_index2page_ptr(j)), 
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == MAPPED ==> self.mapped_pages@.contains(self.page_array@[j as int].start),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == MAPPED ==> self.mapped_pages@.contains(page_index2page_ptr(j)), 
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == MAPPED ==> self.get_page_mappings(page_index2page_ptr(j)) =~= Set::<(Pcid,VAddr)>::empty().insert((0,boot_page_ptrs@[j as int].1)),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == MAPPED && self.page_array@[j as int].is_io_page == true ==> self.get_page_io_mappings(page_index2page_ptr(j)) =~= Set::<(Pcid,VAddr)>::empty(),

                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].is_io_page == true ==>  (self.page_array@[j as int].state == MAPPED),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].is_io_page == false ==>  (self.page_array@[j as int].io_mappings@.dom().len() == 0),
                forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].is_io_page == false ==>  (self.page_array@[j as int].mappings@.dom().len() == self.page_array@[j as int].rf_count),

                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].start == j * PAGE_SZ,
                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].state <= MAPPED,
                forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> page_ptr_valid(self.free_pages@[i]),
                self.page_perms@.dom() =~= self.get_free_pages_as_set() + self.get_mapped_pages(),

                self.page_perms_wf(),
                forall|page_ptr:PagePtr| #![auto] self.page_perms@.dom().contains(page_ptr) ==> self.page_perms@[page_ptr]@.pptr == page_ptr,
                forall|page_ptr:PagePtr| #![auto] self.page_perms@.dom().contains(page_ptr) ==> self.page_perms@[page_ptr]@.value.is_Some(),

                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].start == j * PAGE_SZ,
                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].state <= MAPPED,

                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].mappings@.dom().finite(),
                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].io_mappings@.dom().finite(),
                forall|j:usize| #![auto] 0<=j<i ==> (self.page_array@[j as int].rf_count != 0 <==> self.page_array@[j as int].state == MAPPED),
                forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].rf_count == (self.page_array@[j as int].mappings@.dom().len() + self.page_array@[j as int].io_mappings@.dom().len()),

                forall|j:usize| #![auto] 0<=j<i ==> (self.page_array@[j as int].state != UNAVAILABLE ==> self.available_pages@.contains(page_index2page_ptr(j))),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> (
                    page_ptr_valid(page_ptr)
                    &&
                    0<=page_ptr2page_index(page_ptr as usize)<NUM_PAGES
                    &&
                    boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
                ),
                forall|j:usize| #![auto] self.page_table_pages@.contains(page_index2page_ptr(j)) <== (
                    0<=j<i
                    &&
                    boot_page_ptrs@[j as int].0 == PAGETABLE
                ),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) <== (
                    page_ptr_valid(page_ptr)
                    &&
                    0<=page_ptr2page_index(page_ptr as usize)<i
                    &&
                    boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
                ),
                
            ensures
                i == NUM_PAGES,
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == FREE ==> self.free_pages@.contains(page_index2page_ptr(i)), 
                self.allocated_pages@ =~= Set::empty(), 
                self.mem_wf(),
                self.page_array_wf(),
                self.free_pages_wf(),
                self.page_table_pages_wf(),
                self.allocated_pages_wf(),
                self.mapped_pages_wf(),
                self.rf_wf(),
                self.page_perms_wf(),
                self.available_pages_wf(),
                self.io_pages_wf(),
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == MAPPED ==> self.get_page_mappings(page_index2page_ptr(i)) =~= Set::<(Pcid,VAddr)>::empty().insert((0,boot_page_ptrs@[i as int].1)),
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == MAPPED ==> self.get_mapped_pages().contains(page_index2page_ptr(i)),
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == IO ==> self.get_page_mappings(page_index2page_ptr(i)) =~= Set::<(Pcid,VAddr)>::empty().insert((0,boot_page_ptrs@[i as int].1)),
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == IO ==> self.get_page_io_mappings(page_index2page_ptr(i)) =~= Set::<(Pcid,VAddr)>::empty(),
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == IO ==> self.get_mapped_pages().contains(page_index2page_ptr(i)),
                forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int].0 == PAGETABLE ==> self.get_page_table_pages().contains(page_index2page_ptr(i)),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == PAGETABLE),
                forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) <==> (
                    page_ptr_valid(page_ptr)
                    &&
                    0<=page_ptr2page_index(page_ptr as usize)<i
                    &&
                    boot_page_ptrs@[page_ptr2page_index(page_ptr as usize) as int].0 == PAGETABLE
                ),
        {
        proof{
            page_ptr_lemma();
        }
        let pair =  *boot_page_ptrs.index(i);
        if pair.0 == UNAVAILABLE {
            self.page_array.set_page_start(i, page_index2page_ptr(i));
            self.page_array.set_page_rf_count(i, 0);
            self.page_array.set_page_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_io_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_state(i, UNAVAILABLE);
            self.page_array.set_get_page_is_io_page(i, false);
            assert(forall|j:usize| #![auto] 0<=j<i+1 ==> self.page_array@[j as int].rf_count == self.page_array@[j as int].mappings@.dom().len() + self.page_array@[j as int].io_mappings@.dom().len());
        }
        else if pair.0 == FREE {
            // assert(self.get_free_pages_as_set().len() + self.mapped_pages@.len() <= i);
            // let free_pages: Ghost<Set<PagePtr>> = Ghost(self.get_free_pages_as_set());
            self.page_array.set_page_start(i, page_index2page_ptr(i));
            self.page_array.set_page_rf_count(i, 0);
            self.page_array.set_page_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_io_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_state(i, FREE);
            self.page_array.set_get_page_is_io_page(i, false);
            self.free_pages.push_unique(page_index2page_ptr(i));
            let tracked mut page_perm: PagePerm =
                (boot_page_perms.borrow_mut()).tracked_remove(page_index2page_ptr(i));
            proof{
                (self.page_perms.borrow_mut())
                    .tracked_insert(page_index2page_ptr(i), page_perm);
            }
            proof{
                self.available_pages@ = self.available_pages@.insert(page_index2page_ptr(i));
            }
            // assert(free_pages@.insert(page_index2page_ptr(i)) =~= self.get_free_pages_as_set());
            // assert(self.get_free_pages_as_set().len() + self.mapped_pages@.len() <= i + 1);
            assert(forall|j:usize| #![auto] 0<=j<i+1 ==> self.page_array@[j as int].rf_count == self.page_array@[j as int].mappings@.dom().len() + self.page_array@[j as int].io_mappings@.dom().len());
        }else if pair.0 == MAPPED{
            // assert(self.get_free_pages_as_set().len() + self.mapped_pages@.len() <= i);
            let mapped_pages:Ghost<Set<PagePtr>> = Ghost(self.mapped_pages@);
            // assert(forall|j:usize| #![auto] 0<=j<i ==> 
            //     (
            //     self.page_array[j as int].start == page_index2page_ptr(j)
            //     &&
            //     self.page_array[j as int].rf_count == self.page_array[j as int].mappings@.dom().len()
            //     &&
            //     self.page_array[j as int].mappings@.dom().finite()
            //     ));
            self.page_array.set_page_start(i, page_index2page_ptr(i));
            self.page_array.set_page_rf_count(i, 1);
            self.page_array.set_page_mappings(i, Ghost(Map::<(Pcid,VAddr),PageType>::empty().insert((0,pair.1),0)));
            self.page_array.set_page_io_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_state(i, MAPPED);
            self.page_array.set_get_page_is_io_page(i, false);

            self.mapped_pages = Ghost(self.mapped_pages@.insert(page_index2page_ptr(i)));
            let tracked mut page_perm: PagePerm =
                (boot_page_perms.borrow_mut()).tracked_remove(page_index2page_ptr(i));
            proof{
                (self.page_perms.borrow_mut())
                    .tracked_insert(page_index2page_ptr(i), page_perm);
            }
            proof{
                self.available_pages@ = self.available_pages@.insert(page_index2page_ptr(i));
            }
            // assert(forall|j:usize| #![auto] 0<=j<i+1 ==> 
            //     (
            //     self.page_array[j as int].start == page_index2page_ptr(j)
            //     &&
            //     self.page_array[j as int].rf_count == self.page_array[j as int].mappings@.dom().len()
            //     &&
            //     self.page_array[j as int].mappings@.dom().finite()
            //     ));
            assert(mapped_pages@.insert(page_index2page_ptr(i)) =~= self.mapped_pages@);
            // assert(mapped_pages@.len() + 1 >= self.mapped_pages@.len());
            // assert(self.get_free_pages_as_set().len() + self.mapped_pages@.len() <= i + 1);
            assert(forall|j:usize| #![auto] 0<=j<i+1 ==> self.page_array@[j as int].rf_count == self.page_array@[j as int].mappings@.dom().len() + self.page_array@[j as int].io_mappings@.dom().len());
        }else if pair.0 == IO{
            // assert(self.get_free_pages_as_set().len() + self.mapped_pages@.len() <= i);
            let mapped_pages:Ghost<Set<PagePtr>> = Ghost(self.mapped_pages@);
            // assert(forall|j:usize| #![auto] 0<=j<i ==> 
            //     (
            //     self.page_array[j as int].start == page_index2page_ptr(j)
            //     &&
            //     self.page_array[j as int].rf_count == self.page_array[j as int].mappings@.dom().len()
            //     &&
            //     self.page_array[j as int].mappings@.dom().finite()
            //     ));
            self.page_array.set_page_start(i, page_index2page_ptr(i));
            self.page_array.set_page_rf_count(i, 1);
            self.page_array.set_page_mappings(i, Ghost(Map::<(Pcid,VAddr),PageType>::empty().insert((0,pair.1),0)));
            self.page_array.set_page_io_mappings(i, Ghost(Map::<(Pcid,VAddr),PageType>::empty()));
            self.page_array.set_page_state(i, MAPPED);
            self.page_array.set_get_page_is_io_page(i, true);

            self.mapped_pages = Ghost(self.mapped_pages@.insert(page_index2page_ptr(i)));
            let tracked mut page_perm: PagePerm =
                (boot_page_perms.borrow_mut()).tracked_remove(page_index2page_ptr(i));
            proof{
                (self.page_perms.borrow_mut())
                    .tracked_insert(page_index2page_ptr(i), page_perm);
            }
            proof{
                self.available_pages@ = self.available_pages@.insert(page_index2page_ptr(i));
            }
            // assert(forall|j:usize| #![auto] 0<=j<i+1 ==> 
            //     (
            //     self.page_array[j as int].start == page_index2page_ptr(j)
            //     &&
            //     self.page_array[j as int].rf_count == self.page_array[j as int].mappings@.dom().len()
            //     &&
            //     self.page_array[j as int].mappings@.dom().finite()
            //     ));
            assert(mapped_pages@.insert(page_index2page_ptr(i)) =~= self.mapped_pages@);
            // assert(mapped_pages@.len() + 1 >= self.mapped_pages@.len());
            // assert(self.get_free_pages_as_set().len() + self.mapped_pages@.len() <= i + 1);
            assert(forall|j:usize| #![auto] 0<=j<i+1 ==> self.page_array@[j as int].rf_count == self.page_array@[j as int].mappings@.dom().len() + self.page_array@[j as int].io_mappings@.dom().len());
        }else {
            assert(pair.0 == PAGETABLE); 
            let page_table_pages:Ghost<Set<PagePtr>> = Ghost(self.page_table_pages@);
            self.page_array.set_page_start(i, page_index2page_ptr(i));
            self.page_array.set_page_rf_count(i, 0);
            self.page_array.set_page_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_io_mappings(i, Ghost(Map::empty()));
            self.page_array.set_page_state(i, PAGETABLE);
            self.page_array.set_get_page_is_io_page(i, false);

            self.page_table_pages = Ghost(self.page_table_pages@.insert(page_index2page_ptr(i)));
            proof{
                self.available_pages@ = self.available_pages@.insert(page_index2page_ptr(i));
            }
            assert(page_table_pages@.insert(page_index2page_ptr(i)) =~= self.page_table_pages@);
            assert(forall|j:usize| #![auto] 0<=j<i+1 ==> self.page_array@[j as int].rf_count == self.page_array@[j as int].mappings@.dom().len() + self.page_array@[j as int].io_mappings@.dom().len());
        }

        

        i = i + 1;
    }
    
}

}
}