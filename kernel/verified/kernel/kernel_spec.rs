use vstd::prelude::*;

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::*;
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use vstd::set_lib::lemma_set_properties;
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
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).contains((pcid,va))
            )
        )
    }

    pub open spec fn kernel_mmu_page_alloc_iommutable_wf(&self) -> bool{
        &&&
        (
            forall|ioid:IOid, va:usize| #![auto] self.mmu_man.get_iommu_ids().contains(ioid) && spec_va_valid(va) && self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_io_mappings(self.mmu_man.get_iommutable_mapping_by_ioid(ioid)[va].get_Some_0().addr).contains((ioid,va))
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

    pub open spec fn kernel_cpu_list_wf(&self) -> bool {
        &&&
        (
            forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS 
                ==> (
                    self.cpu_list[cpu_id as int].wf()
                    )
        )
        &&&
        (
            forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS && self.cpu_list[cpu_id as int].get_is_idle() == false
                ==> (
                    self.proc_man.get_thread_ptrs().contains(self.cpu_list[cpu_id as int].get_current_thread().unwrap())
                    &&
                    self.proc_man.get_thread(self.cpu_list[cpu_id as int].get_current_thread().unwrap()).state == RUNNING
                    )
        )
    }
    pub open spec fn kernel_tlb_wf(&self) -> bool {
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) 
                ==> (
                    self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid) =~= Map::empty()
                )
        )
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid, va:VAddr| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false
                && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None()
                ==> (
                    self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid).dom().contains(va) == false

                )
        )        
        &&&
        (
            forall|cpu_id:CPUID, pcid:Pcid, va:VAddr| #![auto] 0 <= cpu_id < NUM_CPUS && 0<=pcid<PCID_MAX && self.mmu_man.get_free_pcids_as_set().contains(pcid) == false
                && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some()
                ==> (
                    (self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid).dom().contains(va) == false)
                    ||
                    (self.cpu_list[cpu_id as int].get_tlb_for_pcid(pcid)[va] =~= self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0())
                )
        )
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
            self.cpu_list.wf()
        )
        &&&
        (
            self.kernel_cpu_list_wf()
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
        &&&
        (self.kernel_tlb_wf())
    }

    pub proof fn pagetable_mem_wf_derive(&self)
        requires
            self.wf(),
            self.kernel_mmu_page_alloc_pagetable_wf(),
        ensures
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).subset_of(self.page_alloc.get_mapped_pages()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_page_table_pages()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_free_pages_as_set()),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_allocated_pages()),
    {
        lemma_set_properties::<Set<PagePtr>>();  
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page_mappings(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).len() > 0
            )
        );
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_page(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr).state == MAPPED
            )
        );
        assert(
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() ==>
            (
                self.page_alloc.get_mapped_pages().contains(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr)
            )
        );
        assert(
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                exists|va:usize| #![auto] spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some() && spec_va_valid(va) && self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].get_Some_0().addr =~= pa
            )
        );
        assert(
            forall|pcid:Pcid, pa:PAddr| #![auto] 0<=pcid<PCID_MAX && page_ptr_valid(pa) && self.mmu_man.get_pagetable_by_pcid(pcid).get_pagetable_mapped_pages().contains(pa) ==>
            (
                self.page_alloc.get_mapped_pages().contains(pa)
            )
        );
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).subset_of(self.page_alloc.get_mapped_pages()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_page_table_pages()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_free_pages_as_set()));
        assert(forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.mmu_man.get_pagetable_mapped_pages_by_pcid(pcid).disjoint(self.page_alloc.get_allocated_pages()));
    }

}

}
