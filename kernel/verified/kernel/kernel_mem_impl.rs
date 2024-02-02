use vstd::prelude::*;

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use crate::kernel::*;

verus! {

impl Kernel{
    pub fn kernel_map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:usize)
        requires
            old(self).wf(), 
            old(self).kernel_pagetable_mem_wf(),
            0<=pcid<PCID_MAX,
            old(self).mmu_man.free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).mmu_man.get_mmu_page_closure().contains(dst) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] == 0,
            page_ptr_valid(dst),
            old(self).page_alloc.mapped_pages().contains(dst),
            old(self).page_alloc.get_page_mappings(dst).contains((pcid,va)) == false,
            old(self).page_alloc.page_array@[page_ptr2page_index(dst) as int].rf_count < usize::MAX,

            old(self).mmu_man.get_pagetable_by_pcid(pcid).va_exists(va)
    {
        let result = self.mmu_man.map_pagetable_page(pcid,va,dst);
        assert(result == true);
        assert(old(self).page_alloc.available_pages().contains(dst));
        self.page_alloc.map_user_page(dst,(pcid,va),RWX);
        assert(self.page_alloc.page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

        proof{page_ptr_lemma();}

        // assert((
        //     forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==>
        //     (
        //         self.mmu_man.get_pagetable_mapping_by_pcid(_pcid) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(_pcid)
        //     )
        // ));

        // assert(self.page_alloc.available_pages() =~= old(self).page_alloc.available_pages());

        // assert((
        //     forall|_pcid:Pcid,_va:usize| #![auto] 0<=_pcid<PCID_MAX && spec_va_valid(_va) && old(self).mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va] != 0 ==>
        //     (
        //         old(self).page_alloc.available_pages().contains(old(self).mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va])
        //     )
        // ));

        // assert((
        //     forall|_pcid:Pcid,_va:usize| #![auto] 0<=_pcid<PCID_MAX && spec_va_valid(_va) && self.mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va] != 0 && _pcid != pcid ==>
        //     (
        //         self.page_alloc.available_pages().contains(self.mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va])
        //     )
        // ));
        // assert(
        //     forall|_pcid:Pcid, _va:usize| #![auto] 0<=_pcid<PCID_MAX && spec_va_valid(_va) && self.mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va] != 0 && _pcid != pcid ==>
        //     (
        //         self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va]).contains((_pcid,_va))
        //     )
        // );

        // assert(
        //     forall|_pcid:Pcid, _va:usize| #![auto] 0<=_pcid<PCID_MAX && spec_va_valid(_va) && self.mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va] != 0 ==>
        //     (
        //         self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(_pcid)[_va]).contains((_pcid,_va))
        //     )
        // );
        assert(self.kernel_pagetable_mem_wf());
        assert(self.wf());
    }  
}

}