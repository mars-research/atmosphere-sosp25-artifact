use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
use crate::page_alloc::*;

use crate::iommutable::*;

use crate::pagetable::*;


impl MarsArray<IOMMUTable,IOID_MAX>{
    
    // new

    #[verifier(external_body)]
    pub fn init_all_iommutables(&mut self)
        requires
            old(self).wf(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> old(self)@[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> old(self)@[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> old(self)@[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> old(self)@[i].dummy.l1_tables@ =~= Map::empty(),
        ensures
            self.wf(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].dummy.wf_mapping(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].get_iommutable_page_closure() =~= Set::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].dummy.cr3 == 0,
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:int, va:VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==> self@[i].dummy.mapping@.dom().contains(va),
            forall|i:int, va:VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==> self@[i].dummy.mapping@[va].is_None(),
        {
            let mut i = 0;
            while i != IOID_MAX{
                self.ar[i].dummy.init();
                i = i + 1;
            }
        }
    

    #[verifier(external_body)]
    pub fn init_into_wf_by_ioid(&mut self, ioid:Pcid, page_ptr: PagePtr, page_perm: Tracked<PagePerm>)
        requires
            0<=ioid<IOID_MAX,
            old(self).wf(),
            old(self)@[ioid as int].wf_mapping(),
            old(self)@[ioid as int].get_iommutable_page_closure() =~= Set::empty(),
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> old(self)@[ioid as int].get_iommutable_mapping()[va].is_None(),
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self@[ioid as int].wf(),
            self@[ioid as int].dummy.mapping@ =~= old(self)@[ioid as int].dummy.mapping@,
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self@[ioid as int].get_iommutable_mapping()[va].is_None(),
            self@[ioid as int].get_iommutable_page_closure() =~= Set::empty().insert(page_ptr),
            forall|i:int| #![auto] 0<=i<IOID_MAX && i != ioid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<IOID_MAX && i != ioid ==> self@[i as int].get_iommutable_mapping() =~= old(self)@[i as int].get_iommutable_mapping(),
    {
        self.ar[ioid].init_to_wf(page_ptr,page_perm);
    }


    #[verifier(external_body)]
    pub fn map_iommutable_page_by_ioid(&mut self, ioid:IOid, va: VAddr, dst:PageEntry) -> (ret: bool)
        requires
            0<=ioid<IOID_MAX,
            old(self).wf(),
            old(self)@[ioid as int].wf(),
            spec_va_valid(va),
            old(self)@[ioid as int].get_iommutable_page_closure().contains(dst.addr) == false,
            old(self)@[ioid as int].get_iommutable_mapping()[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
        ensures 
            self.wf(),
            self@[ioid as int].wf(),
            old(self)@[ioid as int].dummy.is_va_entry_exist(va) == ret ,
            old(self)@[ioid as int].dummy.is_va_entry_exist(va) ==> 
                self@[ioid as int].get_iommutable_mapping() =~= old(self)@[ioid as int].get_iommutable_mapping().insert(va,Some(dst)),
            !old(self)@[ioid as int].dummy.is_va_entry_exist(va) ==> 
                self@[ioid as int].get_iommutable_mapping() =~=old(self)@[ioid as int].get_iommutable_mapping(),
            self@[ioid as int].get_iommutable_page_closure() =~= old(self)@[ioid as int].get_iommutable_page_closure(),
            forall|i:int| #![auto] 0<=i<IOID_MAX && i != ioid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<IOID_MAX && i != ioid ==> self@[i as int].get_iommutable_mapping() =~= old(self)@[i as int].get_iommutable_mapping(),
    {
        return self.ar[ioid].map(va, dst);
    }

    #[verifier(external_body)]
    pub fn create_va_entry_by_ioid(&mut self, ioid:IOid, va:VAddr,page_alloc :&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=ioid<IOID_MAX,
            old(self).wf(),
            old(self)@[ioid as int].wf(),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(self)@[ioid as int].get_iommutable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
            old(self)@[ioid as int].get_iommutable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self@[ioid as int].wf(),
            forall|i:int| #![auto] 0<=i<IOID_MAX && i != ioid ==> self@[i as int] =~= old(self)@[i as int],
            forall|i:int| #![auto] 0<=i<IOID_MAX ==> self@[i as int].get_iommutable_mapping() =~= old(self)@[i as int].get_iommutable_mapping(),
            self@[ioid as int].get_iommutable_page_closure() =~= old(self)@[ioid as int].get_iommutable_page_closure() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            self@[ioid as int].get_iommutable_page_closure().disjoint(page_alloc.get_free_pages_as_set()),
            self@[ioid as int].get_iommutable_page_closure() =~= old(self)@[ioid as int].get_iommutable_page_closure() + ret@,
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self@[ioid as int].dummy.is_va_entry_exist(va),
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 3,
    {
        return self.ar[ioid].dummy.create_va_entry(va,page_alloc);
    }
}
}