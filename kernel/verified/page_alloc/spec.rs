use vstd::prelude::*;
// use vstd::ptr::*;

use crate::define::*;
use crate::page_alloc::*;

use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;

verus! {

pub struct Page{
    pub start: PagePtr,
    pub state: PageState,
    pub is_io_page: bool,
    pub rf_count: usize,

    pub mappings: Ghost<Map<(Pcid,VAddr),PageType>>,
    pub io_mappings: Ghost<Map<(Pcid,VAddr),PageType>>,
}

pub struct PageAllocator{
    pub page_array: MarsArray<Page,NUM_PAGES>,
    pub free_pages: ArrayVec<PagePtr,NUM_PAGES>,

    pub page_table_pages: Ghost<Set<PagePtr>>,
    pub allocated_pages: Ghost<Set<PagePtr>>,
    pub mapped_pages: Ghost<Set<PagePtr>>,

    pub available_pages: Ghost<Set<PagePtr>>,

    pub page_perms: Tracked<Map<PagePtr,PagePerm>>,


    // //fields for virtual addresses
    // pub free_pcids: ArrayVec<Pcid,PCID_MAX>,
    // pub page_tables: MarsArray<AddressSpace,PCID_MAX>,
}

pub open spec fn spec_page_ptr2page_index(ptr: usize) -> usize
    recommends
        page_ptr_valid(ptr),
{
    (ptr/4096usize) as usize
}


pub open spec fn spec_page_index2page_ptr(i:usize) -> usize
    recommends
        page_index_valid(i),
{
    (i * 4096) as usize
}

#[verifier(when_used_as_spec(spec_page_ptr2page_index))]
pub fn page_ptr2page_index(ptr: usize) -> (ret: usize)
    requires
        ptr % 4096 == 0,
    ensures
        ret == spec_page_ptr2page_index(ptr)
{
    return ptr/4096usize;
}

#[verifier(when_used_as_spec(spec_page_index2page_ptr))]
pub fn page_index2page_ptr(i: usize) -> (ret:usize)
    requires
        0<=i<NUM_PAGES,
    ensures
        ret == spec_page_index2page_ptr(i),
{
    proof{
        lemma_usize_u64(MAX_USIZE);
    }
    (i * 4096usize) 
}

#[verifier(inline)]
pub open spec fn page_ptr_valid(ptr: usize) -> bool
{
    ((ptr % 4096) == 0)
    &&
    ((ptr/4096) < NUM_PAGES)
}

pub open spec fn page_index_valid(index: usize) -> bool
{
    0<=index<NUM_PAGES
}


impl PageAllocator {

    ///Spec helper for kernel memory management.
    ///In Atmo, each physical page has three possible states: Free, Allocated, Mapped.
    ///The state of each page can be inferred by:
    ///If a physical page is mapped by any pagetable or in the global page array is marked as Mapped, it is in Mapped state
    ///If a physical page's page permission is held by any kernel component or in the global page array is marked as Allocated, it is in Allocated state
    ///If a physical page in the global page array is marked as Free, it is in Free state
    #[verifier(inline)]
    pub open spec fn page_table_pages(&self) -> Set<PagePtr>
    {
        self.page_table_pages@
    }

    #[verifier(inline)]
    pub open spec fn allocated_pages(&self) -> Set<PagePtr>
    {
        self.allocated_pages@
    }
    
    #[verifier(inline)]
    pub open spec fn mapped_pages(&self) -> Set<PagePtr>
    {
        self.mapped_pages@
    }
    
    #[verifier(inline)]
    pub open spec fn free_pages_as_set(&self) -> Set<PagePtr>
    {
        self.free_pages@.to_set()
    }

    #[verifier(inline)]
    pub open spec fn available_pages(&self) -> Set<PagePtr>
    {
        
        self.available_pages@
    }


    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
        ensures
            ret.page_array.wf(),
            ret.free_pages.wf(),
            ret.free_pages.len() == 0,
    {
        let ret = Self {
            page_array: MarsArray::<Page,NUM_PAGES>::new(),
            free_pages: ArrayVec::<PagePtr,NUM_PAGES>::new(),

            page_table_pages: arbitrary(),
            allocated_pages: arbitrary(),
            mapped_pages: arbitrary(),

            available_pages: arbitrary(),
            page_perms: arbitrary(),

            // free_pcids: ArrayVec::<Pcid,PCID_MAX>::new(),
            // page_tables: MarsArray::<AddressSpace,PCID_MAX>::new(),
        };

        ret
    }


    pub proof fn page_array_wf_derive(&self)
    requires 
        self.page_array_wf(),
    ensures 
        forall|i:int| #![auto] 0<=i<NUM_PAGES ==> page_ptr_valid(self.page_array@[i].start),
        forall|i:int,j:int| #![auto] 0<=i<NUM_PAGES && 0<=j<NUM_PAGES && i != j==> self.page_array@[i].start != self.page_array@[j].start,
    {
        assert(forall|i:int| #![auto] 0<=i<NUM_PAGES ==> page_ptr_valid(self.page_array@[i].start));
        assert(forall|i:int,j:int| #![auto] 0<=i<NUM_PAGES && 0<=j<NUM_PAGES && i != j==> self.page_array@[i].start != self.page_array@[j].start);
    }

    pub open spec fn page_array_wf(&self) -> bool{
        (self.page_array.wf())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].start == i * PAGE_SZ)
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].state <= MAPPED)
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count != 0 <==> self.page_array@[i].state == MAPPED))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].mappings@.dom().finite())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].io_mappings@.dom().finite())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].rf_count == self.page_array@[i].mappings@.dom().len() + self.page_array@[i].io_mappings@.dom().len())
    }

    pub open spec fn page_perms_wf(&self) -> bool{
        (self.page_perms@.dom() =~= self.free_pages_as_set() + self.mapped_pages())
        &&
        (forall|page_ptr:PagePtr| #![auto] self.page_perms@.dom().contains(page_ptr) ==> self.page_perms@[page_ptr]@.pptr == page_ptr)
        &&
        (forall|page_ptr:PagePtr| #![auto] self.page_perms@.dom().contains(page_ptr) ==> self.page_perms@[page_ptr]@.value.is_Some())
    }

    pub open spec fn free_pages_wf(&self) -> bool{
        (self.free_pages.wf())
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> page_ptr_valid(self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> (self.page_array@[(self.free_pages@[i] as usize/PAGE_SZ) as int].start =~= self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == FREE ==> self.free_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == FREE))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].is_io_page == false))
        &&
        (forall|i:int,j:int| #![auto] 0<=i<self.free_pages.len() && 0<=j<self.free_pages.len() && i != j ==> self.free_pages@[i] != self.free_pages@[j])
    }

    pub open spec fn allocated_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == ALLOCATED ==> self.allocated_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == ALLOCATED))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].is_io_page == false))

    }

    pub open spec fn page_table_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == PAGETABLE ==> self.page_table_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == PAGETABLE))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.page_table_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].is_io_page == false))

    }

    pub open spec fn mapped_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == MAPPED ==> self.mapped_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == MAPPED))
    }

    pub open spec fn io_pages_wf(&self) -> bool{
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].is_io_page == true ==> (self.page_array@[i].state == MAPPED || self.page_array@[i].state == UNAVAILABLE)))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].is_io_page == false ==> (self.page_array@[i].io_mappings@.dom().len() == 0)))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].is_io_page == false ==> (self.page_array@[i].mappings@.dom().len() == self.page_array@[i].rf_count)))
    }

    pub open spec fn available_pages_wf(&self) -> bool{
        &&&
        self.available_pages@.finite()
        &&&
        self.available_pages@.len() <= NUM_PAGES
        &&&
        (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i as int].state != UNAVAILABLE ==> self.available_pages@.contains(page_index2page_ptr(i))))
    }

    pub open spec fn mem_wf(&self) -> bool
    {
        //The first three ensure no memory corruption bug in our kernel or in userspace, these three are needed.
        &&&
        (self.allocated_pages().disjoint(self.mapped_pages()))
        &&&
        (self.allocated_pages().disjoint(self.free_pages_as_set()))
        &&&
        (self.allocated_pages().disjoint(self.page_table_pages()))
        &&&
        (self.free_pages_as_set().disjoint(self.mapped_pages()))
        &&&
        (self.free_pages_as_set().disjoint(self.page_table_pages()))
        &&&
        (self.mapped_pages().disjoint(self.page_table_pages()))
        //Not sure if we can prove this, but this ensures exact 1 ownership of all pages, 
        //hence No memory leak. 
        &&&
        ((self.allocated_pages() + self.mapped_pages() + self.free_pages_as_set() + self.page_table_pages()) =~= self.available_pages()) 
    }

    pub open spec fn rf_wf(&self) -> bool{
        forall|page_ptr:PagePtr| #![auto] self.mapped_pages().contains(page_ptr) ==>
            (
                self.page_rf_counter(page_ptr) == self.get_page_mappings(page_ptr).len() + self.get_page_io_mappings(page_ptr).len()
            )
    }

    pub open spec fn page_alloc_wf(&self) -> bool
    {
        self.mem_wf()
        &&
        self.page_array_wf()
        &&
        self.free_pages_wf()
        &&
        self.page_table_pages_wf()
        &&
        self.allocated_pages_wf()
        &&
        self.mapped_pages_wf()
        &&
        self.rf_wf()
        &&
        self.page_perms_wf()
        &&
        self.available_pages_wf()
        &&
        self.io_pages_wf()
           
    }

    // pub open spec fn address_space_wf(&self) -> bool{
    //     &&&
    //     self.free_pcids.wf()
    //     &&&
    //     self.free_pcids@.no_duplicates()
    //     &&&
    //     (
    //         forall|i:int| #![auto] 0<=i<PCID_MAX ==> self.free_pcids@[i]<PCID_MAX
    //     )
    //     &&&
    //     self.page_tables.wf()
    //     &&&
    //     (
    //         forall|i:int| #![auto] 0<=i<self.free_pcids.len() ==> self.page_tables[self.free_pcids@[i] as int].0.tmp_get_mem_mappings() =~= Map::empty()
    //     )
    //     &&&
    //     (
    //         forall|i:int,va:VAddr| #![auto] 0<=i<PCID_MAX && self.page_tables[i].0.tmp_get_mem_mappings().dom().contains(va) ==> page_ptr_valid(self.page_tables[i].0.tmp_get_mem_mappings()[va] as usize)
    //     )
    //     &&&
    //     (
    //         forall|i:int,page_ptr:PagePtr| #![auto] 0<=i<PCID_MAX && self.page_tables[i].0.tmp_page_table_page_closure().contains(page_ptr) ==> self.page_table_pages@.contains(page_ptr)
    //     )
    //     &&&
    //     (
    //         forall|i:int,j:int| #![auto] 0<=i<PCID_MAX && 0<=j<PCID_MAX && i != j ==> self.page_tables[i].0.tmp_page_table_page_closure().disjoint(self.page_tables[j].0.tmp_page_table_page_closure())
    //     )
    // }

    pub open spec fn wf(&self) -> bool
    {
        self.page_alloc_wf()
    }

    pub open spec fn get_page_mappings(&self, page_ptr: PagePtr) -> Set<(Pcid,VAddr)>
        recommends
            self.available_pages().contains(page_ptr),
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].mappings@.dom()
    }

    pub open spec fn get_page_io_mappings(&self, page_ptr: PagePtr) -> Set<(Pcid,VAddr)>
        recommends
            self.available_pages().contains(page_ptr),
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].io_mappings@.dom()
    }

    pub open spec fn page_rf_counter(&self, page_ptr: PagePtr) -> usize
        recommends
            page_ptr_valid(page_ptr),
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count
    }

    pub open spec fn page_is_io_page(&self, page_ptr: PagePtr) -> bool
        recommends
            page_ptr_valid(page_ptr),
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].is_io_page
    }

    // pub open spec fn free_pcids(&self) -> Set<Pcid>
    // {
    //     self.free_pcids@.to_set()
    // }

    // pub open spec fn all_pcids(&self) -> Set<Pcid>
    // {
    //     Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
    // }

    // pub open spec fn get_address_space(&self,pcid:Pcid) ->  Map<VAddr,PAddr>
    //     recommends 
    //         0<=pcid<PCID_MAX,
    // {
    //     self.page_tables@[pcid as int].0.tmp_get_mem_mappings()
    // }

}

}