use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{PagePtr,VAddr,Pcid,PagePerm};
use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;
verus! {

pub const NUM_PAGES:usize = 4*1024*1024; //16GB
pub const PAGE_SIZE:usize = 4096;
pub const MAX_USIZE:u64 = 31*1024*1024*1024;

pub type PageType = u8;
pub type PageState = usize;

pub const UNAVAILABLE:PageState = 0;
pub const FREE:PageState = 1;
pub const ALLOCATED:PageState = 2;
pub const MAPPED:PageState = 3;


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
    pub state: PageState,
    pub rf_count: usize,

    pub mappings: Ghost<Map<(Pcid,VAddr),PageType>>,
}

pub struct PageAllocator{
    pub page_array: MarsArray<Page,NUM_PAGES>,
    pub free_pages: ArrayVec<PagePtr,NUM_PAGES>,

    pub allocated_pages: Ghost<Set<PagePtr>>,
    pub mapped_pages: Ghost<Set<PagePtr>>,

    pub available_pages: Ghost<Set<PagePtr>>,

    pub page_perms: Tracked<Map<PagePtr,PagePerm>>,
}


impl<const N: usize> MarsArray<Page, N> {

    #[verifier(external_body)]
    pub fn set_page_start(&mut self, index: usize, start: PagePtr) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            //self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].start =~= start,
            self.wf(),
    {
        self.ar[index].start = start;
    }

    #[verifier(external_body)]
    pub fn set_page_state(&mut self, index: usize, state: PageState) 
        requires 
            0 <= index < N,
            state <= MAPPED,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            //self@[index].state =~= old(self)@[index].state,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].state =~= state,
            self.wf(),
    {
        self.ar[index].state = state;
    }

    #[verifier(external_body)]
    pub fn set_page_rf_count(&mut self, index: usize, rf_count: usize) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            //self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].rf_count =~= rf_count,
            self.wf(),
    {
        self.ar[index].rf_count = rf_count;
    }

    #[verifier(external_body)]
    pub fn set_page_mappings(&mut self, index: usize, mappings: Ghost<Map<(Pcid,VAddr),PageType>>) 
        requires 
            0 <= index < N,
            old(self).wf(),
        ensures
            forall|i:int| #![auto] 0<=i<N && i != index ==> self@[i] =~= old(self)@[i],
            self@[index as int].start =~= old(self)@[index as int].start,
            self@[index as int].state =~= old(self)@[index as int].state,
            self@[index as int].rf_count =~= old(self)@[index as int].rf_count,
            //self@[index as int].mappings =~= old(self)@[index as int].mappings,
            self@[index as int].mappings =~= mappings,
            self.wf(),
    {
        self.ar[index].mappings = mappings;
    }
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

            allocated_pages: arbitrary(),
            mapped_pages: arbitrary(),

            available_pages: arbitrary(),
            page_perms: arbitrary(),
        };

        ret
    }

    pub fn init(&mut self, boot_page_ptrs: &ArrayVec<bool,NUM_PAGES>, mut boot_page_perms: Tracked<Map<PagePtr,PagePerm>>)
        requires
            old(self).page_array.wf(),
            old(self).free_pages.wf(),
            old(self).free_pages.len() == 0,
            old(self).allocated_pages@ =~= Set::empty(),
            old(self).mapped_pages@ =~= Set::empty(),
            old(self).available_pages@ =~= Set::empty(),
            old(self).page_perms@.dom() =~= Set::empty(),
            boot_page_ptrs.wf(),
            boot_page_ptrs.len() == NUM_PAGES,
            (forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int] == true ==> 
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
            forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int] == true ==> self.free_pages@.contains(page_index2page_ptr(i)), 

    {
        proof{self.free_pages@.unique_seq_to_set();}

        let mut i = 0;
            while i != NUM_PAGES
                invariant
                    0<= i <= NUM_PAGES,
                    NUM_PAGES * 4096 <= usize::MAX,
                    forall|j:usize| #![auto] 0<=j<i ==> 
                        (self.page_array[j as int].start == page_index2page_ptr(j)
                        &&
                        self.page_array[j as int].rf_count == 0
                        &&
                        self.page_array[j as int].mappings@.dom().finite()
                        ),
                    self.page_array.wf(),
                    boot_page_ptrs.wf(),
                    boot_page_ptrs.len() == NUM_PAGES,
                    self.free_pages.wf(),
                    self.free_pages.unique(),
                    self.free_pages.len() <= i,
                    self.allocated_pages@ =~= Set::empty(),
                    self.mapped_pages@ =~= Set::empty(),
                    forall|j:usize| #![auto] 0<=j<self.free_pages.len() ==> self.free_pages@[j as int] < page_index2page_ptr(i),
                    forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].rf_count == 0, 
                    forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].mappings@ =~= Map::empty(), 
                    forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].state != MAPPED, 
                    forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].state != ALLOCATED, 
                    forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int] == true ==> self.page_array@[j as int].state == FREE, 
                    forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == FREE),
                    forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == FREE ==> self.free_pages@.contains(self.page_array@[j as int].start),
                    forall|j:usize| #![auto] 0<=j<i && self.page_array@[j as int].state == FREE ==> self.free_pages@.contains(page_index2page_ptr(j)), 
                    forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int] == true ==> self.free_pages@.contains(page_index2page_ptr(j)), 
                    forall|j:usize| #![auto] 0<=j<i && boot_page_ptrs@[j as int] == false ==> self.page_array@[j as int].state == UNAVAILABLE, 
                    (forall|j:usize| #![auto] i<=j<NUM_PAGES && boot_page_ptrs@[j as int] == true ==> 
                        (boot_page_perms@.dom().contains(page_index2page_ptr(j))
                         && 
                         boot_page_perms@[page_index2page_ptr(j)]@.pptr == page_index2page_ptr(j)
                         &&
                         boot_page_perms@[page_index2page_ptr(j)]@.value.is_Some()
                        )
                    ),
                    forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].start == j * PAGE_SIZE,
                    forall|j:usize| #![auto] 0<=j<i ==> self.page_array@[j as int].state <= MAPPED,
                    forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> page_ptr_valid(self.free_pages@[i]),
                    self.page_perms_wf(),
                    self.free_pages_as_set().len() <= i,
                    self.available_pages@ =~= self.free_pages_as_set(),
                ensures
                    i == NUM_PAGES,
                    self.wf(),
                    forall|i:usize| #![auto] 0<=i<NUM_PAGES && boot_page_ptrs@[i as int] == true ==> self.free_pages@.contains(page_index2page_ptr(i)), 
        {
            self.page_array.set_page_start(i, page_index2page_ptr(i));
            self.page_array.set_page_rf_count(i, 0);
            self.page_array.set_page_mappings(i, Ghost(Map::empty()));
            if *boot_page_ptrs.index(i) {
                self.page_array.set_page_state(i, FREE);
                self.free_pages.push_unique(page_index2page_ptr(i));
                let tracked mut page_perm: PagePerm =
                    (boot_page_perms.borrow_mut()).tracked_remove(page_index2page_ptr(i));
                proof{
                    (self.page_perms.borrow_mut())
                        .tracked_insert(page_index2page_ptr(i), page_perm);
                }
            }else{
                self.page_array.set_page_state(i, UNAVAILABLE);
            }
            proof{
                self.available_pages@ = self.free_pages_as_set();
            }
            proof{self.free_pages@.unique_seq_to_set();}
            i = i + 1;
        }
        
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
    // pub fn init(&mut self)
    //     requires 
    //         old(self).page_array.wf(),
    //         old(self).free_pages.wf(),
    //         old(self).free_pages.len() == 0,
    //     ensures
    //         self.wf(),
    //         self.free_pages_as_set() =~= self.all_available_pages(),
    // {
    //     let mut index = 0;
    //     while index != NUM_PAGES
    //         invariant
    //             0<= index <= NUM_PAGES,
    //             self.page_array.wf(),
    //             forall|i:int| #![auto] 0<=i<index ==> self.page_array@[i].start == (KERNEL_END_PAGE_NO + i) * PAGE_SIZE,
    //             forall|i:int| #![auto] 0<=i<index ==> self.page_array@[i].mappings@.dom().finite(),
    //             forall|i:int| #![auto] 0<=i<index ==> self.page_array@[i].rf_count == self.page_array@[i].mappings@.dom().len(),
    //             forall|i:int| #![auto] 0<=i<index ==> (self.page_array@[i].is_free ==> self.page_array@[i].rf_count == 0),
    //             forall|i:int| #![auto] 0<=i<index ==> (self.page_array@[i].rf_count != 0 ==> self.page_array@[i].is_free == false),
    //             self.free_pages.wf(),
    //             self.free_pages.len() == index,
    //             forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> self.free_pages@[i] == (KERNEL_END_PAGE_NO + i) * PAGE_SIZE,
    //             forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> page_ptr_valid(self.free_pages@[i]),
    //             forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> (self.page_array@[self.free_pages@[i] as usize/PAGE_SIZE-KERNEL_END_PAGE_NO].start =~= self.free_pages@[i]),
    //             forall|i:int| #![auto] 0<=i<index ==> (self.page_array@[i].is_free ==> self.free_pages@.contains(self.page_array@[i].start)),
    //             forall|i:int,j:int| #![auto] 0<=i<self.free_pages.len() && 0<=j<self.free_pages.len() && i != j ==> self.free_pages@[i] != self.free_pages@[j],
    //             forall|i:int| #![auto] 0<=i<index ==> self.page_array@[i].rf_count == 0 && self.page_array@[i].is_free == true,
    //             self.free_pages@ =~= Seq::new(index as nat, |i: int| page_index2page_ptr(i as usize)),
    //         ensures
    //             index == NUM_PAGES,
    //             self.page_array_wf(),
    //             self.free_pages_wf(),
    //             forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count == 0 && self.page_array@[i].is_free == true),
    //             forall|i:int| #![auto] 0<=i<NUM_PAGES ==> !(self.page_array@[i].rf_count == 0 && self.page_array@[i].is_free == false),
    //             self.free_pages@ =~= Seq::new(NUM_PAGES as nat, |i: int| page_index2page_ptr(i as usize)),
    //     {
    //         assume((KERNEL_END_PAGE_NO + index) * PAGE_SIZE < usize::MAX);
    //         self.page_array.set_page_start(index, (KERNEL_END_PAGE_NO + index) * PAGE_SIZE);
    //         self.page_array.set_page_is_free(index, true);
    //         self.page_array.set_page_rf_count(index, 0);
    //         self.page_array.set_page_mappings(index, Ghost(Map::empty()));
    //         self.free_pages.push_unique((KERNEL_END_PAGE_NO + index) * PAGE_SIZE);
    //         index = index + 1;
    //     }

    //     self.mapped_pages=Ghost(Set::empty());
    //     self.allocated_pages = Ghost(Set::empty());
    //     assume(self.page_perms_wf()); //TODO: @Xiangdong Actually create the perms, but this is fine for now.
    // }

    pub closed spec fn page_array_wf(&self) -> bool{
        (self.page_array.wf())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].start == i * PAGE_SIZE)
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].state <= MAPPED)
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].rf_count != 0 <==> self.page_array@[i].state == MAPPED))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].mappings@.dom().finite())
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> self.page_array@[i].rf_count == self.page_array@[i].mappings@.dom().len())
    }

    pub closed spec fn page_perms_wf(&self) -> bool{
        (self.page_perms@.dom() =~= self.free_pages_as_set() + self.mapped_pages())
        &&
        (forall|page_ptr:PagePtr| #![auto] self.page_perms@.dom().contains(page_ptr) ==> self.page_perms@[page_ptr]@.pptr == page_ptr)
        &&
        (forall|page_ptr:PagePtr| #![auto] self.page_perms@.dom().contains(page_ptr) ==> self.page_perms@[page_ptr]@.value.is_Some())
    }

    pub closed spec fn free_pages_wf(&self) -> bool{
        (self.free_pages.wf())
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> page_ptr_valid(self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<self.free_pages.len() ==> (self.page_array@[(self.free_pages@[i] as usize/PAGE_SIZE) as int].start =~= self.free_pages@[i]))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == FREE ==> self.free_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.free_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == FREE))
        &&
        (forall|i:int,j:int| #![auto] 0<=i<self.free_pages.len() && 0<=j<self.free_pages.len() && i != j ==> self.free_pages@[i] != self.free_pages@[j])
    }

    pub closed spec fn allocated_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == ALLOCATED ==> self.allocated_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.allocated_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == ALLOCATED))
    }

    pub closed spec fn mapped_pages_wf(&self) -> bool{
        (forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> page_ptr_valid(page_ptr))
        &&
        (forall|i:int| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i].state == MAPPED ==> self.mapped_pages@.contains(self.page_array@[i].start)))
        &&
        (forall|page_ptr:PagePtr| #![auto] self.mapped_pages@.contains(page_ptr) ==> (self.page_array@[page_ptr2page_index(page_ptr as usize) as int].state == MAPPED))
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
        ((self.allocated_pages() + self.mapped_pages() + self.free_pages_as_set()) =~= self.available_pages()) 
    }

    pub closed spec fn available_pages_wf(&self) -> bool{
        &&&
        self.available_pages@.finite()
        &&&
        self.available_pages@.len() <= NUM_PAGES
        &&&
        (forall|i:usize| #![auto] 0<=i<NUM_PAGES ==> (self.page_array@[i as int].state != UNAVAILABLE ==> self.available_pages@.contains(page_index2page_ptr(i))))
    }

    pub closed spec fn rf_wf(&self) -> bool{
        forall|page_ptr:PagePtr| #![auto] self.mapped_pages().contains(page_ptr) ==>
            (
                self.page_rf_counter(page_ptr) == self.page_mappings(page_ptr).len()
            )
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
        &&
        self.rf_wf()
        &&
        self.page_perms_wf()
        &&
        self.available_pages_wf()
           
    }

    pub closed spec fn page_mappings(&self, page_ptr: PagePtr) -> Set<(Pcid,VAddr)>
        recommends
            self.mapped_pages().contains(page_ptr),
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].mappings@.dom()
    }

    pub closed spec fn page_rf_counter(&self, page_ptr: PagePtr) -> usize
        recommends
            page_ptr_valid(page_ptr),
    {
        self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count
    }

    pub fn alloc_kernel_mem(&mut self) -> (ret : (PagePtr,Tracked<PagePerm>))
        requires 
            old(self).wf(),
            old(self).free_pages.len() > 0,
        ensures
            self.wf(),
            old(self).free_pages_as_set().contains(ret.0),
            self.allocated_pages().contains(ret.0),
            self.available_pages() =~= old(self).available_pages(),
            ret.1@@.pptr == ret.0,
            ret.1@@.value.is_Some(),
    {
        proof{
            self.page_array_wf_derive();
        }
        let ptr = self.free_pages.pop_unique();
        assert(old(self).free_pages@.contains(ptr));
        assert(old(self).free_pages_as_set().contains(ptr));
        assert(self.free_pages@.contains(ptr) == false);

        assert(old(self).allocated_pages() * old(self).free_pages_as_set() =~= Set::empty());
        assert(old(self).allocated_pages().contains(ptr) == false);
        assert(self.allocated_pages@.contains(ptr) == false);
        self.page_array.set_page_state(page_ptr2page_index(ptr),ALLOCATED);
        proof{
            self.allocated_pages@ = self.allocated_pages@.insert(ptr);
        }

        assert(self.free_pages.wf());
        assert(self.free_pages_wf());

        assert(self.free_pages_as_set() =~= old(self).free_pages_as_set().remove(ptr));

        assert((self.allocated_pages() + self.free_pages_as_set()) =~= (old(self).allocated_pages() + old(self).free_pages_as_set()));
        assert((self.allocated_pages() + self.mapped_pages() + self.free_pages_as_set()) =~= self.available_pages());
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
            old(self).allocated_pages().contains(ptr),
            old(self).free_pages.len() < NUM_PAGES,
            perm@@.pptr == ptr,
            perm@@.value.is_Some(),
        ensures
            self.wf(),
    {
        assert(page_ptr_valid(ptr));
        proof{self.allocated_pages@ = self.allocated_pages@.remove(ptr);}
        assert(self.free_pages_as_set().contains(ptr) == false);
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

    pub fn map_user_page(&mut self, page_ptr : PagePtr, target: (Pcid,VAddr), page_type: PageType)
        requires
            page_ptr_valid(page_ptr),
            old(self).wf(),
            old(self).mapped_pages().contains(page_ptr),
            old(self).page_mappings(page_ptr).contains(target) == false,
            old(self).page_array@[page_ptr2page_index(page_ptr) as int].rf_count < usize::MAX,
        ensures
            self.wf(),
    {
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count != 0);
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count > 0);
        let old_rf_count = self.page_array.get(page_ptr2page_index(page_ptr)).rf_count;
        let new_rf_count = old_rf_count + 1;
        self.page_array.set_page_rf_count(page_ptr2page_index(page_ptr), new_rf_count);
        let new_mappings = Ghost(self.page_array@[spec_page_ptr2page_index(page_ptr) as int].mappings@.insert(target, page_type));
        self.page_array.set_page_mappings(page_ptr2page_index(page_ptr),new_mappings);

        assert(self.wf());
    }

    pub fn unmap_user_page(&mut self, page_ptr : PagePtr, target: (Pcid,VAddr))
        requires
            page_ptr_valid(page_ptr),
            old(self).wf(),
            old(self).mapped_pages().contains(page_ptr),
            old(self).page_mappings(page_ptr).contains(target) == true,
    {
        assert(self.page_array@[page_ptr2page_index(page_ptr) as int].rf_count > 0);
        let old_rf_count = self.page_array.get(page_ptr2page_index(page_ptr)).rf_count;
        let new_rf_count = old_rf_count - 1;
        self.page_array.set_page_rf_count(page_ptr2page_index(page_ptr), new_rf_count);
        let new_mappings = Ghost(self.page_array@[spec_page_ptr2page_index(page_ptr) as int].mappings@.remove(target));
        self.page_array.set_page_mappings(page_ptr2page_index(page_ptr),new_mappings);
        if new_rf_count == 0{
            assert(self.page_array@[spec_page_ptr2page_index(page_ptr) as int].mappings@.dom() =~= Set::empty());
            assert(self.free_pages@.contains(page_ptr) == false);
            proof{
                Seq::new(NUM_PAGES as nat, |i: int| page_index2page_ptr(i as usize)).lemma_cardinality_of_set();
            }
            assert(self.available_pages().len() <= NUM_PAGES);
            assert(self.free_pages_as_set().contains(page_ptr) == false);
            assert(self.available_pages().contains(page_ptr) == true);
            assert(self.free_pages_as_set().subset_of(self.available_pages()));
            proof{vstd::set_lib::lemma_len_subset(self.free_pages_as_set(),self.available_pages().remove(page_ptr) )};
            assert(self.free_pages_as_set().len() < NUM_PAGES);
            assert(self.free_pages@.no_duplicates());
            proof{
                self.free_pages@.unique_seq_to_set();
            }
            assert(self.free_pages@.len() < NUM_PAGES);
            self.free_pages.push_unique(page_ptr);
            self.page_array.set_page_state(page_ptr2page_index(page_ptr), FREE);
            proof{self.mapped_pages@ = self.mapped_pages@.remove(page_ptr);}
            assert(self.wf());
        }else{
            assert(self.wf());
        }
    }
}

}