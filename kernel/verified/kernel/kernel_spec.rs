use vstd::prelude::*;

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

verus! {
pub struct Kernel{
    pub proc_man : ProcessManager,
    pub page_alloc: PageAllocator,
    pub mmu_man: MMUManager,
    pub cpu_list: MarsArray<Cpu,NUM_CPUS>,
}

impl Kernel{

    pub open spec fn kernel_pagetable_mem_wf(&self) -> bool{
        // all pages used to construct pagetable/iommutables are marked correctly in page allocator 
        &&&
        (self.page_alloc.page_table_pages() =~= self.mmu_man.get_mmu_page_closure())
        // for each (va,pa) pairs in all pagetables, the page allocator correctly records the pair and the counter
        // of each page. Thus, if the counter of a mapped page drops to zero, it is for sure that no process still 
        // obtains a mapping to this page, and it is safe to free this page.
        // &&&
        // (
        //     forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] != 0 ==>
        //     (
        //         self.page_alloc.available_pages().contains(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va])
        //     )
        // )
        &&&
        (
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] != 0 ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]).contains((pcid,va))
            )
        )
    }

    pub proof fn pagetable_mem_wf_derive(&self)
        requires
            self.wf(),
            self.kernel_pagetable_mem_wf(),
        {
            assert(
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] != 0 ==>
                (
                    self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]).len() > 0
                )
            );
            assert(
                forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] != 0 ==>
                (
                    self.page_alloc.get_page(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]).state == MAPPED
                )
            );
        }

    pub open spec fn wf(&self) -> bool{
        &&&
        (
            self.page_alloc.wf()
        )
        &&&
        (
            self.mmu_man.wf()
        )
    }

}

}
