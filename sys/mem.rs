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

    pub struct PageMem{
        //4K chunk
    }
    pub struct Page{
        pub start: usize,
        //pub end: usize,
        pub rf_counter: usize,
        pub is_free: bool,
    }

    impl<const N: usize> MarsArray<Page, N> {
        #[verifier(external_body)]
        pub fn set_is_free(&mut self, i: usize, new: bool) 
            requires 
                0 <= i < N,
                old(self).wf(),
            ensures
                forall|index:int| 0<= index < N && index != i ==> self.seq@[index] == old(self).seq@[index],
                self.seq@[i as int].start == old(self).seq@[i as int].start,
                self.seq@[i as int].rf_counter == old(self).seq@[i as int].rf_counter,
                self.seq@[i as int].is_free == new,
                self.wf(),
        {
            self.ar[i].is_free = new;
        }
    }

    pub struct PageManager{
        pub page_array: MarsArray<Page, NUM_PAGES>, // all the metadata is here
        
        pub mapping: Ghost<Seq<Set<ProcID>>>, //ProcID for now
        pub page_perms_mapped: Tracked<Map<int, PointsTo<PageMem>>>,


        pub free_pages: MarsStaticLinkedList<NUM_PAGES>,

        pub page_pptrs:  MarsArray<PageMemPPtr, NUM_PAGES>,
        pub page_perms_free: Tracked<Map<int, PointsTo<PageMem>>>,
    }
    impl PageManager {  
        pub open spec fn wf_free_pages(&self) -> bool{
            self.free_pages.wf()
            &&
            self.free_pages.is_unique()
            &&
            (
                forall|i: usize| #![auto] self.free_pages@.contains(i) ==> 0 <= i < NUM_PAGES
            )
            &&
            (
                forall|i: usize| #![auto] self.free_pages@.contains(i) ==> self.page_array@[i as int].is_free == true
            )
            &&
            (
                forall|i: usize| #![auto] self.free_pages@.contains(i) == false && 0 <= i < NUM_PAGES ==> self.page_array@[i as int].is_free == false
            )
        }
        pub open spec fn wf_page_mem(&self) -> bool{
            self.page_pptrs.wf()
            &&
            (
                forall|i: int| #![auto] self.page_perms_free@.dom().contains(i) ==>  self.page_perms_free@[i].view().value.is_Some()
            )
        }

        pub open spec fn wf_page_array(&self) -> bool{
            self.page_array.wf()
            &&
            (
                forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==> self.page_pptrs@[i] == self.page_array@[i].start
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == false ==> self.page_pptrs@[i] == 0
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==>  self.page_array@[i].rf_counter == 0
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == false ==> self.page_perms_free@.dom().contains(self.page_array@[i].start as int) == false
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==> self.page_perms_free@.dom().contains(self.page_array@[i].start as int) == true
            )
            &&
            (
                forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==> self.page_perms_free@[self.page_array@[i].start as int].view().pptr == self.page_array@[i].start
            )
            &&
            (
                forall|i: int, j: int| #![auto] 0 <= i < NUM_PAGES && 0 <= j < NUM_PAGES && i != j ==> self.page_array@[i].start != self.page_array@[j].start
            )
            
        }

        pub open spec fn wf(&self) -> bool{
            self.wf_page_array()
            &&
            self.wf_page_mem()
            &&
            self.wf_free_pages()
        }
        pub fn alloc_page(&mut self) -> (ptr : (PPtr::<PageMem>, Tracked<PointsTo<PageMem>>)) 
            requires old(self).wf(),
                     old(self).free_pages.value_list_len > 0,
            ensures
                    self.wf(),
                    self.free_pages.value_list_len == old(self).free_pages.value_list_len - 1,
                    ptr.0.id() == ptr.1@.view().pptr,
                    ptr.1@.view().value.is_Some(),
        {
            let free_page_index = self.free_pages.pop();
            assert(old(self).free_pages@.contains(free_page_index));
            assert(0<= free_page_index < NUM_PAGES);
            let free_page_start = self.page_array.get(free_page_index).start;
            let free_page_pptr = self.page_pptrs.get(free_page_index);

            assert(self.page_array@[free_page_index as int].is_free == true);
            assert(self.page_pptrs@[free_page_index as int] == self.page_array@[free_page_index as int].start);
            assert(free_page_start == free_page_pptr);

            self.page_array.set_is_free(free_page_index, false);
            assert(self.page_perms_free@.dom().contains(free_page_start as int));
            let tracked mut free_page_perm: PointsTo<PageMem> = 
                (self.page_perms_free.borrow_mut()).tracked_remove(free_page_start as int);
            self.page_pptrs.set(free_page_index, 0);
            let free_page_pptr = PPtr::<PageMem>::from_usize(free_page_start);
            assert(free_page_pptr.id() == free_page_perm.view().pptr);
            
            assert(self.wf_page_mem());
            
            assert(self.wf_free_pages());

            assert(self.page_array.wf());
            assert(forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==> self.page_pptrs@[i] == self.page_array@[i].start);
            assert(forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == false ==> self.page_pptrs@[i] == 0);
            assert(forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==>  self.page_array@[i].rf_counter == 0);
            assert(forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == false ==> self.page_perms_free@.dom().contains(self.page_array@[i].start as int) == false);
            assert(forall|i: int| #![auto] 0 <= i < NUM_PAGES && self.page_array@[i].is_free == true ==> self.page_perms_free@.dom().contains(self.page_array@[i].start as int) == true);
            assert(self.wf_page_array());
            assert(free_page_perm.view().value.is_Some());
            return (free_page_pptr, Tracked(free_page_perm));
        }
    }
}