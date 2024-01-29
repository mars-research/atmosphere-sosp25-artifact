use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::page_alloc::*;

use crate::iommutable::*;

verus!{
impl IOMMUTable{

    #[verifier(external_body)]
    pub fn init(&mut self)
        ensures
            self.iommutable_mappings() =~= Map::empty(),
            self.iommutable_page_closure() =~= Set::empty(),
    {

    }

    #[verifier(external_body)]
    pub fn adopt(&mut self, io_table: &IOMMUTable)
        ensures
            self.iommutable_mappings() =~= io_table.iommutable_mappings(),
            self.iommutable_page_closure() =~= io_table.iommutable_page_closure(),
    {

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
            self.iommutable_mappings() =~= old(self).iommutable_mappings(),
            page_alloc.wf(),
            self.iommutable_page_closure() =~= old(self).iommutable_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self.va_entry_exists(va) == true,
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn resolve(&self, va:VAddr) -> (ret: Option<PAddr>)
        ensures
            ret.is_None() ==> self.iommutable_mappings().dom().contains(va) == false,
            ret.is_Some() ==> self.iommutable_mappings().dom().contains(va) && self.iommutable_mappings()[va] == ret.unwrap(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn map(&mut self, va:VAddr, pa:PAddr)
        requires
            old(self).wf(),
            old(self).iommutable_mappings().dom().contains(va) == false,
        ensures
            self.wf(),
            self.iommutable_mappings().dom().contains(va) == true,
            self.iommutable_mappings()[va] == pa,
            self.iommutable_mappings() =~= old(self).iommutable_mappings().insert(va,pa),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn unmap(&mut self, va:VAddr) -> (ret: PAddr)
        requires
            old(self).wf(),
            old(self).iommutable_mappings().dom().contains(va),
        ensures
            self.wf(),
            self.iommutable_mappings().dom().contains(va) == false,
            old(self).iommutable_mappings()[va] == ret,
            self.iommutable_mappings() =~= old(self).iommutable_mappings().remove(va),
    {
        arbitrary()
    }
}

}