use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::PagePPtr;
pub struct PageAllocator{
}
verus! {
impl PageAllocator {

    ///Spec helper for kernel memory management.
    ///In Atmo, each physical page has three possible states: Free, Allocated, Mapped.
    ///The state of each page can be inferred by:
    ///If a physical page is mapped by any pagetable or in the global page array is marked as Mapped, it is in Mapped state
    ///If a physical page's page permission is held by any kernel component or in the global page array is marked as Allocated, it is in Allocated state
    ///If a physical page in the global page array is marked as Free, it is in Free state
    pub closed spec fn allocated_pages(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }

    pub closed spec fn mapped_pages(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }
    
    pub closed spec fn free_pages(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }

    pub closed spec fn all_pages(&self) -> Set<PagePPtr>
    {
        Set::empty()
    }

    pub closed spec fn mem_wf(&self) -> bool
    {
        //The first three ensure no memory corruption bug in our kernel or in userspace, these three are needed.
        &&&
        (self.allocated_pages() * self.mapped_pages() =~= Set::empty())
        &&&
        (self.allocated_pages() * self.free_pages() =~= Set::empty())
        &&&
        (self.free_pages() * self.mapped_pages() =~= Set::empty())
        //Not sure if we can prove this, but this ensures exact 1 ownership of all pages, 
        //hence No memory leak. 
        &&&
        ((self.allocated_pages() + self.mapped_pages() + self.free_pages()) =~= self.all_pages()) 
    }

    //pub closed spec fn get_mapping(&self, page_pptr: PagePPtr) -> Set<(usize,)>

}

}