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
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            0<=pcid<PCID_MAX,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).mmu_man.get_mmu_page_closure().contains(dst) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] == 0,
            page_ptr_valid(dst),
            old(self).page_alloc.get_mapped_pages().contains(dst),
            old(self).page_alloc.get_page_mappings(dst).contains((pcid,va)) == false,
            old(self).page_alloc.page_array@[page_ptr2page_index(dst) as int].rf_count < usize::MAX,
            old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va)
    {
        assert(
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] != 0 ==>
            (
                page_ptr_valid(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va])
            )
        );
        let result = self.mmu_man.map_pagetable_page(pcid,va,dst);
        assert(result == true);
        assert(old(self).page_alloc.get_available_pages().contains(dst));
        self.page_alloc.map_user_page(dst,(pcid,va),RWX);
        // assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

        proof{page_ptr_lemma();}
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.wf());
    }  
}

}