use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
use crate::page_alloc::*;

use crate::pagetable::*;
use crate::iommutable::*;


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
}
}