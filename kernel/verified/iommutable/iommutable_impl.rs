use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::page_alloc::*;
use crate::pagetable::*;

use crate::iommutable::*;


impl IOMMUTable{
    pub fn map(&mut self, va:VAddr, dst:PageEntry) -> (ret: bool)
        requires 
            old(self).dummy.wf(),
            spec_va_valid(va),
            //old(self).dummy.is_va_entry_exist(va),
            old(self).dummy.get_pagetable_page_closure().contains(dst.addr) == false,
            old(self).dummy.mapping@[va].is_None(),
            page_ptr_valid(dst.addr),
            va_perm_bits_valid(dst.perm),
        ensures
            self.dummy.wf(),
            old(self).dummy.is_va_entry_exist(va) == ret ,
            old(self).dummy.is_va_entry_exist(va) ==> 
                self.dummy.mapping@ =~= old(self).dummy.mapping@.insert(va,Some(dst)),
            !old(self).dummy.is_va_entry_exist(va) ==> 
                self.dummy.mapping@ =~= old(self).dummy.mapping@,
    {
        return self.dummy.map(va,dst);
    }

    pub fn unmap(&mut self, va:VAddr) -> (ret: Option<PageEntry>)
        requires 
            old(self).dummy.wf(),
            spec_va_valid(va),
            // old(self).dummy.mapping@[va] != 0,
        ensures
            self.dummy.wf(),
            old(self).dummy.is_va_entry_exist(va) ==> 
                self.dummy.mapping@ =~= old(self).dummy.mapping@.insert(va,None),
            !old(self).dummy.is_va_entry_exist(va) ==> 
                self.dummy.mapping@ =~= old(self).dummy.mapping@,
            old(self).dummy.mapping@[va].is_Some() ==> 
                self.dummy.mapping@ =~= old(self).dummy.mapping@.insert(va,None),
            old(self).dummy.mapping@[va].is_None() ==> 
                self.dummy.mapping@ =~= old(self).dummy.mapping@,
            ret == old(self).dummy.mapping@[va],
    {
        return self.dummy.unmap(va);
    }
    pub fn get_va_entry(&self, va:VAddr) -> (ret:Option<PageEntry>)
        requires
            self.dummy.wf(),
            spec_va_valid(va),
        ensures
            self.dummy.mapping@[va] == ret,
    {
        return self.dummy.get_va_entry(va);
    }

    pub fn create_va_entry(&mut self, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            old(self).dummy.wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 4,
            spec_va_valid(va),
            old(self).dummy.get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
            old(self).dummy.get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.dummy.wf(),
            self.dummy.get_pagetable_page_closure() =~= old(self).dummy.get_pagetable_page_closure() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            self.dummy.get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
            self.dummy.mapping@ =~= old(self).dummy.mapping@,
            self.dummy.get_pagetable_page_closure() =~= old(self).dummy.get_pagetable_page_closure() + ret@,
            // self.dummy.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.dummy.is_va_entry_exist(va),
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            forall|page_ptr:PagePtr| #![auto] page_alloc.available_pages@.contains(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
    {
        return self.dummy.create_va_entry(va,page_alloc);
    }

    pub fn init_to_wf(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>)
        requires
            old(self).dummy.wf_mapping(),
            old(self).get_iommutable_page_closure() =~= Set::empty(),
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> old(self).get_iommutable_mapping()[va].is_None(),
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.get_iommutable_mapping()[va].is_None(),
            self.get_iommutable_page_closure() =~= Set::empty().insert(page_ptr),
    {
        self.dummy.init_to_wf(page_ptr,page_perm,None);
    }
}

}