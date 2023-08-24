use super::*;

pub const NUM_PAGES: usize = 4096;
pub const MAX_NUM_OWNERSHIP: usize = 4096;
pub type ProcID = usize;
pub type PagePtr = usize;

verus! {
    #[verifier(external_body)]
    proof fn lemma_same_raw_ptr(ptr1 :int, ptr2 :int)
        ensures
            ptr1 == ptr2,
    {
        unimplemented!();
    }

    pub struct Page{
        pub start: usize,
        pub end: usize,
        pub rf_counter: usize,
        pub is_free: bool,
    }
    pub struct PageManager{
        pub free_page_ptrs: MarsStaticLinkedList<NUM_PAGES>,
        pub page_perms: Tracked<Map<int, PermissionOpt<Page>>>,
    }
    impl PageManager {
        pub open spec fn wf_page_perms(&self) -> bool{
            forall|i: PagePtr| #![auto] self.page_perms@.dom().contains(i as int) ==> 
            (
                (self.page_perms@[i as int].view().pptr == i)
                &&
                (self.page_perms@[i as int].view().value.is_Some())
                &&
                (i != 0)
                &&
                (self.page_perms@[i as int].view().value.get_Some_0().rf_counter <= MAX_NUM_OWNERSHIP)

            )
        }
        pub open spec fn wf_free_page_ptrs(&self) -> bool{
            self.free_page_ptrs.wf()
            &&
            (
                self.free_page_ptrs.is_unique()
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_page_ptrs@.len()                     
                    ==> (
                            self.page_perms@.dom().contains(self.free_page_ptrs@[i] as int)
                        )
            )      
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_page_ptrs@.len()                     
                    ==> (
                        self.page_perms@[self.free_page_ptrs@[i] as int].view().value.get_Some_0().rf_counter == 0
                        )
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < self.free_page_ptrs@.len()                     
                    ==> (
                        self.page_perms@[self.free_page_ptrs@[i] as int].view().value.get_Some_0().is_free == true
                        )
            )
        }
        pub open spec fn wf(&self) -> bool{
            self.wf_page_perms()
            &&
            self.wf_free_page_ptrs()
        }

        pub fn alloc_page(&mut self) -> (page_ptr: PagePtr)
            requires
                old(self).wf(),
                old(self).free_page_ptrs.pointer_list_len > 0,
            ensures
                self.wf(),
                self.free_page_ptrs.pointer_list_len == old(self).free_page_ptrs.pointer_list_len - 1,
                self.page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == 0
        {
            let page_ptr = self.free_page_ptrs.pop();

            let page_pptr = PPtr::<Page>::from_usize(page_ptr as usize);
            assert(self.page_perms@[page_ptr as int].view().pptr == page_ptr as int);
            let page_perm: Tracked<PermissionOpt<Page>> = tracked(
                (tracked self.page_perms.borrow_mut()).tracked_remove(page_ptr as int));
            assert(page_perm@@.pptr == page_ptr as int);
            assert(page_ptr as int == page_pptr.id());
            let mut page = page_pptr.into_inner(page_perm);
            page.is_free = false;


            // self.free_page_count = self.free_page_count + 1;
            let (new_page_pptr, new_page_perm) = PPtr::new(page);
            proof {
                lemma_same_raw_ptr(new_page_pptr.id(), page_ptr as int);
                (tracked self.page_perms.borrow_mut())
                    .tracked_insert(page_ptr as int, (tracked new_page_perm).get());
            } 
            return page_ptr
        }

        pub fn free_page(&mut self, page_ptr: PagePtr)
            requires
                old(self).wf(),
                old(self).free_page_ptrs.pointer_list_len < NUM_PAGES,
                old(self).page_perms@.dom().contains(page_ptr as int),
                old(self).page_perms@[page_ptr as int].view().value.get_Some_0().is_free == false,
                old(self).page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == 0,
            ensures
                self.wf(),
                self.free_page_ptrs.pointer_list_len == old(self).free_page_ptrs.pointer_list_len + 1,
                self.page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == 0,
                self.page_perms@[page_ptr as int].view().value.get_Some_0().is_free == true,
        {
            assert(self.free_page_ptrs@.contains(page_ptr) == false);
            let page_pptr = PPtr::<Page>::from_usize(page_ptr as usize);
            assert(self.page_perms@[page_ptr as int].view().pptr == page_ptr as int);
            let page_perm: Tracked<PermissionOpt<Page>> = tracked(
                (tracked self.page_perms.borrow_mut()).tracked_remove(page_ptr as int));
            assert(page_perm@@.pptr == page_ptr as int);
            assert(page_ptr as int == page_pptr.id());
            let mut page = page_pptr.into_inner(page_perm);
            page.is_free = true;

            let (new_page_pptr, new_page_perm) = PPtr::new(page);
            proof {
                lemma_same_raw_ptr(new_page_pptr.id(), page_ptr as int);
                (tracked self.page_perms.borrow_mut())
                    .tracked_insert(page_ptr as int, (tracked new_page_perm).get());
            } 
            self.free_page_ptrs.push(page_ptr);
        }

        #[verifier(external_body)]
        fn check_page_counter_not_zero(&self, page_ptr:PagePtr)
            ensures 
                self.page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter != 0,
        {
            unimplemented!();
        }

        pub fn unmap_page(&mut self, page_ptr: PagePtr)
            requires
                old(self).wf(),
                old(self).page_perms@.dom().contains(page_ptr as int),
            ensures
                self.wf(),
                self.page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == old(self).page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter - 1,
        {
            self.check_page_counter_not_zero(page_ptr);
            assert(self.free_page_ptrs@.contains(page_ptr) == false);
            let page_pptr = PPtr::<Page>::from_usize(page_ptr as usize);
            assert(self.page_perms@[page_ptr as int].view().pptr == page_ptr as int);
            let page_perm: Tracked<PermissionOpt<Page>> = tracked(
                (tracked self.page_perms.borrow_mut()).tracked_remove(page_ptr as int));
            assert(page_perm@@.pptr == page_ptr as int);
            assert(page_ptr as int == page_pptr.id());
            let mut page = page_pptr.into_inner(page_perm);
            page.rf_counter = page.rf_counter - 1;

            let (new_page_pptr, new_page_perm) = PPtr::new(page);
            proof {
                lemma_same_raw_ptr(new_page_pptr.id(), page_ptr as int);
                (tracked self.page_perms.borrow_mut())
                    .tracked_insert(page_ptr as int, (tracked new_page_perm).get());
            }
        }

        pub fn map_page(&mut self, page_ptr: PagePtr) -> (success: bool)
            requires
                old(self).wf(),
                old(self).page_perms@.dom().contains(page_ptr as int),
                old(self).page_perms@[page_ptr as int].view().value.get_Some_0().is_free == false,
            ensures
                self.wf(),
                old(self).page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter < MAX_NUM_OWNERSHIP 
                    ==> (
                        self.page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == old(self).page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter + 1
                        &&
                        success == true
                    ),
                old(self).page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == MAX_NUM_OWNERSHIP 
                    ==> (
                        self.page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter == old(self).page_perms@[page_ptr as int].view().value.get_Some_0().rf_counter
                        &&
                        success == false
                    )
        {
            let page_pptr = PPtr::<Page>::from_usize(page_ptr as usize);
            assert(self.page_perms@[page_ptr as int].view().pptr == page_ptr as int);
            let page_perm: Tracked<PermissionOpt<Page>> = tracked(
                (tracked self.page_perms.borrow_mut()).tracked_remove(page_ptr as int));
            assert(page_perm@@.pptr == page_ptr as int);
            assert(page_ptr as int == page_pptr.id());
            let mut page = page_pptr.into_inner(page_perm);
            
            let mut success = false;
            if page.rf_counter < MAX_NUM_OWNERSHIP{
                page.rf_counter = page.rf_counter + 1;
                success = true;
            }

            let (new_page_pptr, new_page_perm) = PPtr::new(page);
            proof {
                lemma_same_raw_ptr(new_page_pptr.id(), page_ptr as int);
                (tracked self.page_perms.borrow_mut())
                    .tracked_insert(page_ptr as int, (tracked new_page_perm).get());
            }
            return success;
        }
    }  

}