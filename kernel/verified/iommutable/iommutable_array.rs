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
    }
}