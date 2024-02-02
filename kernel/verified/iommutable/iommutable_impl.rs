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
            self.get_iommutable_mappings() =~= Map::empty(),
            self.get_iommutable_page_closure() =~= Set::empty(),
    {

    }

    #[verifier(external_body)]
    pub fn adopt(&mut self, io_table: &IOMMUTable)
        ensures
            self.get_iommutable_mappings() =~= io_table.get_iommutable_mappings(),
            self.get_iommutable_page_closure() =~= io_table.get_iommutable_page_closure(),
    {

    }

    #[verifier(external_body)]
    #[verifier(when_used_as_spec(spec_va_entry_exists))]
    pub fn va_entry_exists(&self, va:usize) -> (ret: bool)
        ensures
            ret == self.va_entry_exists(va),
    {
        arbitrary()
    }


    pub closed spec fn spec_va_entry_exists(&self, va:usize) -> bool
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn create_va_entry(&mut self, va:usize,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            old(self).wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
        ensures
            self.wf(),
            self.get_iommutable_mappings() =~= old(self).get_iommutable_mappings(),
            page_alloc.wf(),
            self.get_iommutable_page_closure() =~= old(self).get_iommutable_page_closure() + ret@,
            ret@.subset_of(old(page_alloc).free_pages_as_set()),
            page_alloc.free_pages_as_set() =~= old(page_alloc).free_pages_as_set() - ret@,
            self.va_entry_exists(va) == true,
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn resolve(&self, va:usize) -> (ret: Option<usize>)
        ensures
            ret.is_None() ==> self.get_iommutable_mappings().dom().contains(va) == false,
            ret.is_Some() ==> self.get_iommutable_mappings().dom().contains(va) && self.get_iommutable_mappings()[va] == ret.unwrap(),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn map(&mut self, va:usize, pa:usize)
        requires
            old(self).wf(),
            old(self).get_iommutable_mappings().dom().contains(va) == false,
        ensures
            self.wf(),
            self.get_iommutable_mappings().dom().contains(va) == true,
            self.get_iommutable_mappings()[va] == pa,
            self.get_iommutable_mappings() =~= old(self).get_iommutable_mappings().insert(va,pa),
    {
        arbitrary()
    }

    #[verifier(external_body)]
    pub fn unmap(&mut self, va:usize) -> (ret: usize)
        requires
            old(self).wf(),
            old(self).get_iommutable_mappings().dom().contains(va),
        ensures
            self.wf(),
            self.get_iommutable_mappings().dom().contains(va) == false,
            old(self).get_iommutable_mappings()[va] == ret,
            self.get_iommutable_mappings() =~= old(self).get_iommutable_mappings().remove(va),
    {
        arbitrary()
    }
}

}