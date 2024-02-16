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
            va_perm_bits_valid(dst.perm),
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

}
}