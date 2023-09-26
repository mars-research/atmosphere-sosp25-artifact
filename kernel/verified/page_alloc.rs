use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{PagePtr,VAddr,Pcid};
use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;
verus! {

pub const NUM_PAGES_ALL:usize = 8*1024*1024; //32GB
pub const KERNEL_END_PAGE_NO:usize = 1*1024*1024; //4GB
pub const NUM_PAGES:usize = NUM_PAGES_ALL - KERNEL_END_PAGE_NO; //32GB
pub const PAGE_SIZE:usize = 4096;

pub open spec fn page_ptr2page_index(ptr: usize) -> usize
    recommends
        ptr % 4096 == 0,
        ptr/4096 >= KERNEL_END_PAGE_NO,
{
    (ptr/4096usize - KERNEL_END_PAGE_NO) as usize
}

pub open spec fn page_index2page_ptr(i: usize) -> usize
    recommends
        0<=i<NUM_PAGES,
{
    ((i + KERNEL_END_PAGE_NO) * 4096) as usize
}

pub struct Page{
    pub start: PagePtr,
    pub is_free: bool,
    pub rf_count: usize,

    pub mappings: Set<(Pcid,VAddr)>
}

pub struct PageAllocator{
    pub page_array: MarsArray<Page,NUM_PAGES>,
    pub free_pages: ArrayVec<PagePtr,NUM_PAGES>,

    pub allocated_pages: Ghost<Set<PagePtr>>,
    pub mapped_pages: Ghost<Set<PagePtr>>,
}

impl PageAllocator {

    ///Spec helper for kernel memory management.
    ///In Atmo, each physical page has three possible states: Free, Allocated, Mapped.
    ///The state of each page can be inferred by:
    ///If a physical page is mapped by any pagetable or in the global page array is marked as Mapped, it is in Mapped state
    ///If a physical page's page permission is held by any kernel component or in the global page array is marked as Allocated, it is in Allocated state
    ///If a physical page in the global page array is marked as Free, it is in Free state
    pub closed spec fn allocated_pages(&self) -> Set<PagePtr>
    {
        self.allocated_pages@
    }

    pub closed spec fn mapped_pages(&self) -> Set<PagePtr>
    {
        self.mapped_pages@
    }
    
    pub closed spec fn free_pages_as_set(&self) -> Set<PagePtr>
    {
        self.free_pages@.to_set()
    }

    pub closed spec fn all_pages(&self) -> Set<PagePtr>
    {
        
        self.page_array@.fold_left(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: Page| -> Set::<PagePtr> {
            acc.insert(e.start)
        })
    }

    

    pub closed spec fn page_array_wf(&self) -> bool{
        (self.page_array.wf())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].start == (KERNEL_END_PAGE_NO + i) * PAGE_SIZE)
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].rf_count == self.page_array@[i].mappings.len())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].is_free ==> self.page_array@[i].rf_count == 0))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count != 0 ==> self.page_array@[i].is_free == false))
    }

    pub closed spec fn free_pages_wf(&self) -> bool{
        (self.free_pages.wf())
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> self.all_pages().contains(self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> (self.page_array@[self.free_pages@[i] as usize/PAGE_SIZE-KERNEL_END_PAGE_NO].start =~= self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].is_free ==> self.free_pages@.contains(self.page_array@[i].start)))
    }

    pub closed spec fn allocated_pages_wf(&self) -> bool{
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count == 0 && self.page_array@[i].is_free == false ==> self.allocated_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_pptr:PagePtr| #![auto] self.allocated_pages@.contains(page_pptr) ==> ( self.page_array@[page_ptr2page_index(page_pptr as usize) as int].rf_count == 0 && self.page_array@[page_ptr2page_index(page_pptr as usize) as int].is_free == false))
    }

    pub closed spec fn mapped_pages_wf(&self) -> bool{
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count != 0 ==> self.mapped_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_pptr:PagePtr| #![auto] self.mapped_pages@.contains(page_pptr) ==> ( self.page_array@[page_ptr2page_index(page_pptr as usize) as int].rf_count != 0))
    }

    pub closed spec fn mem_wf(&self) -> bool
    {
        //The first three ensure no memory corruption bug in our kernel or in userspace, these three are needed.
        &&&
        (self.allocated_pages() * self.mapped_pages() =~= Set::empty())
        &&&
        (self.allocated_pages() * self.free_pages_as_set() =~= Set::empty())
        &&&
        (self.free_pages_as_set() * self.mapped_pages() =~= Set::empty())
        //Not sure if we can prove this, but this ensures exact 1 ownership of all pages, 
        //hence No memory leak. 
        &&&
        ((self.allocated_pages() + self.mapped_pages() + self.free_pages_as_set()) =~= self.all_pages()) 
    }

    pub closed spec fn wf(&self) -> bool
    {
        self.mem_wf()
        &&
        self.page_array_wf()
        &&
        self.free_pages_wf()
        &&
        self.allocated_pages_wf()
        &&
        self.mapped_pages_wf()
           
    }

    pub closed spec fn page_mappings(&self, page_pptr: PagePtr) -> Set<(Pcid,VAddr)>
        recommends
            self.mapped_pages().contains(page_pptr),
    {
        arbitrary()
    }

    pub closed spec fn page_rf_counter(&self, page_ptr: PagePtr) -> usize
        recommends
            page_ptr % 4096 == 0,
            page_ptr/4096 >= KERNEL_END_PAGE_NO,
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count
    }

    pub closed spec fn rf_wf(&self) -> bool{
        forall|page_pptr:PagePtr| #![auto] self.mapped_pages().contains(page_pptr) ==>
            (
                self.page_rf_counter(page_pptr) == self.page_mappings(page_pptr).len()
            )
    }

}

}