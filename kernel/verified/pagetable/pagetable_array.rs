use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
use crate::page_alloc::*;

use crate::pagetable::*;


impl MarsArray<PageTable,PCID_MAX>{
    
    // new

    #[verifier(external_body)]
    pub fn init_all_pagetables(&mut self)
        requires
            old(self).wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> old(self)@[i].l4_table@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> old(self)@[i].l3_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> old(self)@[i].l2_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> old(self)@[i].l1_tables@ =~= Map::empty(),
        ensures
            self.wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].wf_mapping(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].get_pagetable_page_closure() =~= Set::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].cr3 == 0,
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].l4_table@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].l3_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].l2_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i].l1_tables@ =~= Map::empty(),
            forall|i:int, va:VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==> self@[i].mapping@.dom().contains(va),
            forall|i:int, va:VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==> self@[i].mapping@[va].is_None(),
        {
            let mut i = 0;
            while i != PCID_MAX{
                self.ar[i].init();
                i = i + 1;
            }
        }

    #[verifier(external_body)]
    pub fn map_pagetable_page_by_pcid(&mut self, pcid:Pcid, va: VAddr, dst:PageEntry) -> (ret: bool)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].wf(),
            spec_va_valid(va),
            old(self)@[pcid as int].get_pagetable_page_closure().contains(dst.addr) == false,
            old(self)@[pcid as int].mapping@[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
        ensures 
            self.wf(),
            self@[pcid as int].wf(),
            old(self)@[pcid as int].is_va_entry_exist(va) == ret ,
            old(self)@[pcid as int].is_va_entry_exist(va) ==> 
                self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@.insert(va,Some(dst)),
            !old(self)@[pcid as int].is_va_entry_exist(va) ==> 
                self@[pcid as int].mapping@ =~=old(self)@[pcid as int].mapping@,
            self@[pcid as int].get_pagetable_page_closure() =~= old(self)@[pcid as int].get_pagetable_page_closure(),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int].get_pagetable_mapping() =~= old(self)@[i as int].get_pagetable_mapping(),
    {
        return self.ar[pcid].map(va, dst);
    }

    #[verifier(external_body)]
    pub fn unmap_pagetable_page_by_pcid(&mut self, pcid:Pcid, va: VAddr) -> (ret: Option<PageEntry>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].wf(),
            spec_va_valid(va),
            // old(self)@[pcid as int].mapping@[va] != 0,
        ensures
            self.wf(),
            self@[pcid as int].wf(),
            old(self)@[pcid as int].is_va_entry_exist(va) ==> 
                self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@.insert(va,None),
            !old(self)@[pcid as int].is_va_entry_exist(va) ==> 
                self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@,
            old(self)@[pcid as int].mapping@[va].is_Some() ==> 
                self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@.insert(va,None),
            !old(self)@[pcid as int].mapping@[va].is_None() ==> 
                self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@,
            ret == old(self)@[pcid as int].mapping@[va],
            self@[pcid as int].get_pagetable_page_closure() =~= old(self)@[pcid as int].get_pagetable_page_closure(),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int].get_pagetable_mapping() =~= old(self)@[i as int].get_pagetable_mapping(),

    {
        return self.ar[pcid].unmap(va);
    }

    #[verifier(external_body)]
    pub fn init_into_wf_by_pcid(&mut self, pcid:Pcid, page_ptr: PagePtr, page_perm: Tracked<PagePerm>, kernel_pml4_entry: Option<PageEntry>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].wf_mapping(),
            old(self)@[pcid as int].get_pagetable_page_closure() =~= Set::empty(),
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> old(self)@[pcid as int].get_pagetable_mapping()[va].is_None(),
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self@[pcid as int].wf(),
            self@[pcid as int].mapping@ =~= old(self)@[pcid as int].mapping@,
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self@[pcid as int].get_pagetable_mapping()[va].is_None(),
            self@[pcid as int].get_pagetable_page_closure() =~= Set::empty().insert(page_ptr),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int].get_pagetable_mapping() =~= old(self)@[i as int].get_pagetable_mapping(),
    {
        self.ar[pcid].init_to_wf(page_ptr,page_perm, kernel_pml4_entry);
    }

    #[verifier(external_body)]
    pub fn create_va_entry_by_pcid(&mut self, pcid:Pcid, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self)@[pcid as int].wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(self)@[pcid as int].get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
            old(self)@[pcid as int].get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self@[pcid as int].wf(),
            forall|i:int| #![auto] 0<=i<PCID_MAX && i != pcid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<PCID_MAX ==> self@[i as int].get_pagetable_mapping() =~= old(self)@[i as int].get_pagetable_mapping(),
            self@[pcid as int].get_pagetable_page_closure() =~= old(self)@[pcid as int].get_pagetable_page_closure() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            self@[pcid as int].get_pagetable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
            self@[pcid as int].get_pagetable_page_closure() =~= old(self)@[pcid as int].get_pagetable_page_closure() + ret@,
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self@[pcid as int].is_va_entry_exist(va),
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 3,
    {
        return self.ar[pcid].create_va_entry(va,page_alloc);
    }

}
}