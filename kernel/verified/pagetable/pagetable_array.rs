use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
use crate::page_alloc::*;

use crate::pagetable::*;
verus!{

impl MarsArray<PageTable,PCID_MAX>{

    #[verifier(external_body)]
    pub fn init(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].tmp_page_table_page_closure() =~= Set::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].tmp_get_mem_mappings() =~= Map::empty(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_adopt(&mut self, pcid:Pcid, addr_spa: &PageTable)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
        ensures
            self.wf(),
            self@[pcid as int].wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
            self@[pcid as int].tmp_get_mem_mappings() =~= addr_spa.tmp_get_mem_mappings(),
            self@[pcid as int].tmp_page_table_page_closure() =~= addr_spa.tmp_page_table_page_closure(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_init(&mut self, pcid:Pcid, kernel_pml4_entry: usize)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        // old(self)@[pcid as int].wf(),
    ensures
        self.wf(),
        self@[pcid as int].wf(),
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].tmp_get_mem_mappings() =~= Map::empty(),
        self@[pcid as int].tmp_page_table_page_closure() =~= Set::empty(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_map(&mut self, pcid:Pcid, va:VAddr, pa:PAddr)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        old(self)@[pcid as int].wf(),
        old(self)@[pcid as int].tmp_get_mem_mappings().dom().contains(va) == false,
    ensures
        self.wf(),
        self@[pcid as int].wf(),
        self@[pcid as int].tmp_get_mem_mappings().dom().contains(va) == true,
        self@[pcid as int].tmp_get_mem_mappings()[va] == pa,
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].tmp_get_mem_mappings() =~= old(self)@[pcid as int].tmp_get_mem_mappings().insert(va,pa),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_unmap(&mut self, pcid:Pcid, va:VAddr) -> (ret: PAddr)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        old(self)@[pcid as int].wf(),
        old(self)@[pcid as int].tmp_get_mem_mappings().dom().contains(va),
    ensures
        self.wf(),
        self@[pcid as int].wf(),
        self@[pcid as int].tmp_get_mem_mappings().dom().contains(va) == false,
        old(self)@[pcid as int].tmp_get_mem_mappings()[va] == ret,
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].tmp_get_mem_mappings() =~= old(self)@[pcid as int].tmp_get_mem_mappings().remove(va),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_create_va_entry(&mut self, pcid:Pcid, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
        ensures
            self.wf(),
            self@[pcid as int].wf(),
            page_alloc.wf(),
            self@[pcid as int].tmp_page_table_page_closure() =~= old(self)@[pcid as int].tmp_page_table_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self@[pcid as int].va_entry_exists(va) == true,
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int]
    {
        arbitrary()
    }

    // new
    #[verifier(external_body)]
    pub fn map_pagetable_page_by_pcid(&mut self, pcid:Pcid, va: VAddr, dst:PAddr) -> (ret: bool)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].wf(),
            spec_va_valid(va),
            old(self)@[pcid as int].get_pagetable_page_closure().contains(dst) == false,
            old(self)@[pcid as int].mapping@[va] == 0,
        ensures 
            self.wf(),
            self@[pcid as int].wf(),
            old(self)@[pcid as int].va_exists(va) == ret ,
            old(self)@[pcid as int].va_exists(va) ==> 
                self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@.insert(va,dst),
            !old(self)@[pcid as int].va_exists(va) ==> 
                self@[pcid as int].mapping@ =~=old(self)@[pcid as int].mapping@,
            self@[pcid as int].get_pagetable_page_closure() =~= old(self)@[pcid as int].get_pagetable_page_closure(),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
    {
        return self.ar[pcid].add_mapping(va, dst);
    }

}
}