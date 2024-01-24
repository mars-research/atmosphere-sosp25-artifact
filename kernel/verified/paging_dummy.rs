use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
use crate::page_alloc::*;

verus!{
pub struct AddressSpace(pub PML4);
pub struct PML4{}

impl PML4{
    pub open spec fn wf(&self) -> bool{
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn tmp_init(&mut self, kernel_pml4_entry: usize)
        ensures
            self.tmp_get_mem_mappings() =~= Map::empty(),
            self.tmp_page_table_page_closure() =~= Set::empty(),
    {

    }

    #[verifier(external_body)]
    pub fn tmp_adopt(&mut self, addr_spa: &AddressSpace)
        ensures
            self.tmp_get_mem_mappings() =~= addr_spa.0.tmp_get_mem_mappings(),
            self.tmp_page_table_page_closure() =~= addr_spa.0.tmp_page_table_page_closure(),
    {

    }

    pub open spec fn tmp_wf(&self)->bool{
        &&&
        (forall|va:VAddr| #![auto] self.tmp_get_mem_mappings().dom().contains(va) ==> page_ptr_valid(self.tmp_get_mem_mappings()[va] as usize))

    }

    pub closed spec fn tmp_page_table_page_closure(&self) -> Set<PagePtr> {
        Set::empty()
    }

    pub closed spec fn tmp_get_mem_mappings(&self) -> Map<VAddr,PAddr> {
        Map::empty()
    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_va_entry_exists))]
    pub fn va_entry_exists(&self, va:VAddr) -> (ret: bool)
        ensures
            ret == self.va_entry_exists(va),
    {
        arbitrary()
    }


    pub closed spec fn spec_va_entry_exists(&self, va:VAddr) -> bool
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn create_va_entry(&mut self, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            old(self).wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
        ensures
            self.wf(),
            self.tmp_get_mem_mappings() =~= old(self).tmp_get_mem_mappings(),
            page_alloc.wf(),
            self.tmp_page_table_page_closure() =~= old(self).tmp_page_table_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self.va_entry_exists(va) == true,
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn resolve(&self, va:VAddr) -> (ret: Option<PAddr>)
        ensures
            ret.is_None() ==> self.tmp_get_mem_mappings().dom().contains(va) == false,
            ret.is_Some() ==> self.tmp_get_mem_mappings().dom().contains(va) && self.tmp_get_mem_mappings()[va] == ret.unwrap(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn map(&mut self, va:VAddr, pa:PAddr)
        requires
            old(self).wf(),
            old(self).tmp_get_mem_mappings().dom().contains(va) == false,
        ensures
            self.wf(),
            self.tmp_get_mem_mappings().dom().contains(va) == true,
            self.tmp_get_mem_mappings()[va] == pa,
            self.tmp_get_mem_mappings() =~= old(self).tmp_get_mem_mappings().insert(va,pa),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn unmap(&mut self, va:VAddr) -> (ret: PAddr)
        requires
            old(self).wf(),
            old(self).tmp_get_mem_mappings().dom().contains(va),
        ensures
            self.wf(),
            self.tmp_get_mem_mappings().dom().contains(va) == false,
            old(self).tmp_get_mem_mappings()[va] == ret,
            self.tmp_get_mem_mappings() =~= old(self).tmp_get_mem_mappings().remove(va),
    {
        arbitrary()
    }
}

impl MarsArray<AddressSpace,PCID_MAX>{

    #[verifier(external_body)]
    pub fn init(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].0.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].0.tmp_page_table_page_closure() =~= Set::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].0.tmp_get_mem_mappings() =~= Map::empty(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_adopt(&mut self, pcid:Pcid, addr_spa: &AddressSpace)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
        ensures
            self.wf(),
            self@[pcid as int].0.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
            self@[pcid as int].0.tmp_get_mem_mappings() =~= addr_spa.0.tmp_get_mem_mappings(),
            self@[pcid as int].0.tmp_page_table_page_closure() =~= addr_spa.0.tmp_page_table_page_closure(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_init(&mut self, pcid:Pcid, kernel_pml4_entry: usize)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        // old(self)@[pcid as int].0.wf(),
    ensures
        self.wf(),
        self@[pcid as int].0.wf(),
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].0.tmp_get_mem_mappings() =~= Map::empty(),
        self@[pcid as int].0.tmp_page_table_page_closure() =~= Set::empty(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_map(&mut self, pcid:Pcid, va:VAddr, pa:PAddr)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        old(self)@[pcid as int].0.wf(),
        old(self)@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va) == false,
    ensures
        self.wf(),
        self@[pcid as int].0.wf(),
        self@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va) == true,
        self@[pcid as int].0.tmp_get_mem_mappings()[va] == pa,
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].0.tmp_get_mem_mappings() =~= old(self)@[pcid as int].0.tmp_get_mem_mappings().insert(va,pa),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_unmap(&mut self, pcid:Pcid, va:VAddr) -> (ret: PAddr)
    requires
        0<=pcid<PCID_MAX,
        old(self).wf(),
        old(self)@[pcid as int].0.wf(),
        old(self)@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va),
    ensures
        self.wf(),
        self@[pcid as int].0.wf(),
        self@[pcid as int].0.tmp_get_mem_mappings().dom().contains(va) == false,
        old(self)@[pcid as int].0.tmp_get_mem_mappings()[va] == ret,
        forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
        self@[pcid as int].0.tmp_get_mem_mappings() =~= old(self)@[pcid as int].0.tmp_get_mem_mappings().remove(va),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn pcid_create_va_entry(&mut self, pcid:Pcid, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].0.wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
        ensures
            self.wf(),
            self@[pcid as int].0.wf(),
            page_alloc.wf(),
            self@[pcid as int].0.tmp_page_table_page_closure() =~= old(self)@[pcid as int].0.tmp_page_table_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self@[pcid as int].0.va_entry_exists(va) == true,
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int]
    {
        arbitrary()
    }
}

}