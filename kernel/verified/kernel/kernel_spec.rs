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

    pub open spec fn kernel_mmu_page_alloc_pagetable_wf(&self) -> bool{
        &&&
        (
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] != 0 ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va]).contains((pcid,va))
            )
        )
    }

    pub open spec fn kernel_mmu_page_alloc_iommutable_wf(&self) -> bool{
        &&&
        (
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va] != 0 ==>
            (
                self.page_alloc.get_page_io_mappings(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va]).contains((ioid,va))
            )
        )
    }

    pub open spec fn kernel_proc_mmu_wf(&self) -> bool{
        &&&
        (forall|pcid:Pcid|#![auto] self.proc_man.get_pcid_closure().contains(pcid) ==> 
            (0 <= pcid< PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false))
        &&&
        (self.proc_man.get_ioid_closure() =~= self.mmu_man.get_iommu_ids())
    }

    pub open spec fn kernel_proc_no_thread_in_transit(&self) -> bool{
        &&&
        (forall|thread_ptr:ThreadPtr|#![auto] self.proc_man.get_thread_ptrs().contains(thread_ptr) ==> 
            self.proc_man.get_thread(thread_ptr).state != TRANSIT)
    }
    pub open spec fn kernel_mem_layout_wf(&self) -> bool {
        // all pages used to construct pagetable/iommutables are marked correctly in page allocator 
        &&&
        (self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure())
        &&&
        (self.page_alloc.get_allocated_pages() =~= self.proc_man.get_proc_man_page_closure())
    }

    pub proof fn pagetable_mem_wf_derive(&self)
        requires
            self.wf(),
            self.kernel_mmu_page_alloc_pagetable_wf(),
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
            self.proc_man.wf()
        )
        &&&
        (
            self.mmu_man.wf()
        )
        &&&
        (
            self.page_alloc.wf()
        )
        &&&
        (
            self.kernel_mem_layout_wf()
        )
        &&&
        (
            self.kernel_mmu_page_alloc_pagetable_wf()
        )
        &&&
        (
            self.kernel_mmu_page_alloc_iommutable_wf()
        )
        &&&
        (self.kernel_proc_mmu_wf())
        &&&
        (self.kernel_proc_no_thread_in_transit())
    }

}

}
