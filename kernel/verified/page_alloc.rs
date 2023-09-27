use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{PagePtr,VAddr,Pcid};
use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;
verus! {

pub const NUM_PAGES_ALL:usize = 4*1024*1024; //16GB
pub const KERNEL_END_PAGE_NO:usize = 1*1024*1024; //4GB
pub const NUM_PAGES:usize = NUM_PAGES_ALL - KERNEL_END_PAGE_NO; //12GB
pub const PAGE_SIZE:usize = 4096;
pub const MAX_USIZE:u64 = 31*1024*1024*1024;

#[verifier(external_body)]
proof fn lemma_usize_u64(x: u64)
    ensures
        x as usize as u64 == x,
{
    unimplemented!();
}

#[verifier(external_body)]
proof fn lemma_usize_int(x: int)
    ensures
        x as usize as int == x,
{
    unimplemented!();
}

pub open spec fn spec_page_ptr2page_index(ptr: usize) -> usize
    recommends
        page_ptr_valid(ptr),
{
    (ptr/4096usize - KERNEL_END_PAGE_NO) as usize
}


pub open spec fn spec_page_index2page_ptr(i:usize) -> usize
    recommends
        page_index_valid(i),
{
    ((i + KERNEL_END_PAGE_NO) * 4096) as usize
}

#[verifier(when_used_as_spec(spec_page_ptr2page_index))]
pub fn page_ptr2page_index(ptr: usize) -> (ret: usize)
    requires
        ptr % 4096 == 0,
        ptr/4096 >= KERNEL_END_PAGE_NO,
    ensures
        ret == spec_page_ptr2page_index(ptr)
{
    return ptr/4096usize - KERNEL_END_PAGE_NO;
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
    ((i + KERNEL_END_PAGE_NO) * 4096usize) 
}

#[verifier(inline)]
pub open spec fn page_ptr_valid(ptr: usize) -> bool
{
    
    ((ptr % 4096) == 0)
    &&
    ((ptr/4096) >= KERNEL_END_PAGE_NO)
    &&
    ((ptr/4096) < NUM_PAGES_ALL)
}

pub open spec fn page_index_valid(index: usize) -> bool
{
    0<=index<NUM_PAGES
}

pub proof fn page_ptr_derive()
    ensures 
        forall|ptr:PagePtr| #![auto] page_ptr_valid(ptr) ==> page_index_valid(page_ptr2page_index(ptr)),
     // forall|index:usize| #![auto] page_index_valid(index) ==> page_ptr_valid(page_index2page_ptr(index)),
{
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> ((index + KERNEL_END_PAGE_NO) * 4096) % 4096 == 0);
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> ((index + KERNEL_END_PAGE_NO) * 4096) == page_index2page_ptr(index));
    // assert(forall|index:usize| #![auto] page_index_valid(index) ==> page_index2page_ptr(index) % 4096 == 0);
}


pub struct Page{
    pub start: PagePtr,
    pub is_free: bool,
    pub rf_count: usize,

    pub mappings: Set<(Pcid,VAddr)>
}

impl<const N: usize> MarsArray<Page, N> {

    #[verifier(external_body)]
    pub fn set_page_is_free(&mut self, index: usize, is_free: bool) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            //self@[index].is_free =~= old(self)@[index].is_free,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].is_free =~= is_free,
            self.wf(),
    {
        self.ar[index].is_free = is_free;
    }
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
        
        Seq::new(NUM_PAGES as nat, |i: int| page_index2page_ptr(i as usize)).to_set()
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

    pub closed spec fn free_pages_wf(&self) -> bool{
        (self.free_pages.wf())
        // &&
        // (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> self.all_pages().contains(self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> page_ptr_valid(self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> (self.page_array@[self.free_pages@[i] as usize/PAGE_SIZE-KERNEL_END_PAGE_NO].start =~= self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].is_free ==> self.free_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|i:int,j:int| #![auto] 0<=i<self.free_pages.len() && 0<=j<self.free_pages.len() && i != j ==> self.free_pages@[i] != self.free_pages@[j])
    }

    pub closed spec fn allocated_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count == 0 && self.page_array@[i].is_free == false ==> self.allocated_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].rf_count == 0 && self.page_array@[page_ptr2page_index(page_ptr as usize) as int].is_free == false))
    }

    pub closed spec fn mapped_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count != 0 ==> self.mapped_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].rf_count != 0))
    }

    pub closed spec fn mem_wf(&self) -> bool
    {
        //The first three ensure no memory corruption bug in our kernel or in userspace, these three are needed.
        &&&
        (self.allocated_pages().disjoint(self.mapped_pages()))
        &&&
        (self.allocated_pages().disjoint(self.free_pages_as_set()))
        &&&
        (self.free_pages_as_set().disjoint(self.mapped_pages()))
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

    pub fn alloc_kernel_mem(&mut self) -> (ret : PagePtr)
        requires 
            old(self).wf(),
            old(self).free_pages.len() > 0,
        ensures
            self.wf(),
    {
        proof{
            self.page_array_wf_derive();
        }
        let ret = self.free_pages.pop_unique();
        assert(old(self).free_pages@.contains(ret));
        assert(old(self).free_pages_as_set().contains(ret));
        assert(self.free_pages@.contains(ret) == false);

        assert(old(self).allocated_pages() * old(self).free_pages_as_set() =~= Set::empty());
        assert(old(self).allocated_pages().contains(ret) == false);
        assert(self.allocated_pages@.contains(ret) == false);
        self.page_array.set_page_is_free(page_ptr2page_index(ret),false);
        proof{
            self.allocated_pages@ = self.allocated_pages@.insert(ret);
        }

        assert(self.free_pages.wf());
        assert(self.free_pages_wf());

        assert(self.free_pages_as_set() =~= old(self).free_pages_as_set().remove(ret));

        assert((self.allocated_pages() + self.free_pages_as_set()) =~= (old(self).allocated_pages() + old(self).free_pages_as_set()));
        assert((self.allocated_pages() + self.mapped_pages() + self.free_pages_as_set()) =~= self.all_pages());
        assert(self.mem_wf());
        assert(self.allocated_pages_wf());
        assert(self.mapped_pages_wf());
        return ret;
    }

}

}