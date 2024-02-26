use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {

    pub fn syscall_malloc(&mut self, cpu_id:CPUID, pt_regs: PtRegs, va: usize, perm_bits:usize, range: usize) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs),None,None);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,0,0,pt_regs),None,None);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        assert(self.mmu_man.get_free_pcids_as_set().contains(pcid) == false);

        if va_perm_bits_valid(perm_bits) == false{
            return (SyscallReturnStruct::new(VMEM_PERMBITS_INVALID,0,0,pt_regs),None,None);
        }

        if range == 0 || range >= (usize::MAX/4) {
            return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0,pt_regs),None,None);
        }

        if  self.page_alloc.free_pages.len() < 4 * range {
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,0,0,pt_regs),None,None);
        }

        let mut i = 0;
        while i != range 
            invariant
                0<=i<=range,
                self == old(self),
                self.wf(),
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.page_alloc.free_pages.len() >= 4*range,
                spec_va_perm_bits_valid(perm_bits),
                0<=pcid<PCID_MAX,
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(va,j)),
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None(),
            ensures
                self == old(self),
                self.wf(),
                i==range,
                self == old(self),
                self.wf(),
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.page_alloc.free_pages.len() >= 4*range,
                spec_va_perm_bits_valid(perm_bits),
                0<=pcid<PCID_MAX,
                forall|j:usize| #![auto] 0<=j<i ==> spec_va_valid(spec_va_add_range(va,j)),
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None(),
        {
            if va_valid(va_add_range(va,i)) == false {
                return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0,pt_regs),None,None);
            }
            if self.mmu_man.mmu_get_va_entry_by_pcid(pcid,va_add_range(va,i)).is_some(){
                return (SyscallReturnStruct::new(MMAP_VADDR_NOT_FREE,0,0,pt_regs),None,None);
            }
        }

        self.kernel_create_and_map_range_new_pages(pcid,va,perm_bits,range);
        assert(self.wf());
        return (SyscallReturnStruct::new(SUCCESS,0,0,pt_regs),None,None);
    }

    pub fn syscall_map_pagetable_pages_to_iommutable(&mut self, cpu_id:CPUID, pt_regs: PtRegs, va:VAddr, perm_bits:usize, range:usize) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))

        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs),None,None);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,0,0,pt_regs),None,None);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        let ioid_op = self.proc_man.get_ioid_by_thread_ptr(current_thread_ptr);

        assert(self.mmu_man.get_free_pcids_as_set().contains(pcid) == false);

        if va_perm_bits_valid(perm_bits) == false{
            return (SyscallReturnStruct::new(VMEM_PERMBITS_INVALID,0,0,pt_regs),None,None);
        }

        if ioid_op.is_none() {
            return (SyscallReturnStruct::new(PROC_NO_IOMMUTABLE,0,0,pt_regs),None,None);
        }

        let ioid = ioid_op.unwrap();

        if range == 0 || range >= (usize::MAX/3) {
            return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0,pt_regs),None,None);
        }

        if  self.page_alloc.free_pages.len() < 3 * range {
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,0,0,pt_regs),None,None);
        }

        let mut i = 0;
        while i != range 
            invariant
                0<=i<=range,
                self == old(self),
                self.wf(),
                0<=pcid<PCID_MAX,
                0<=ioid<IOID_MAX,
                spec_va_perm_bits_valid(perm_bits),
                self.page_alloc.free_pages.len() >= 3 * range,
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.mmu_man.get_free_ioids_as_set().contains(ioid) == false,
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].get_Some_0().addr) as int].rf_count < usize::MAX - range,
                forall|j:usize| #![auto] 0<=j<i ==> old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid)[spec_va_add_range(va,j)].is_None(),
            ensures
                i==range,
                self == old(self),
                self.wf(),
                0<=pcid<PCID_MAX,
                0<=ioid<IOID_MAX,
                spec_va_perm_bits_valid(perm_bits),
                self.page_alloc.free_pages.len() >= 3 * range,
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                self.mmu_man.get_free_ioids_as_set().contains(ioid) == false,
                forall|j:usize| #![auto] 0<=j<i  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
                forall|j:usize| #![auto] 0<=j<i ==>  self.page_alloc.page_array@[
                    page_ptr2page_index(self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].get_Some_0().addr) as int].rf_count < usize::MAX - range,
                forall|j:usize| #![auto] 0<=j<i ==> old(self).mmu_man.get_iommutable_mapping_by_ioid(ioid)[spec_va_add_range(va,j)].is_None(),
        {
            if va_valid(va_add_range(va,i)) == false {
                return (SyscallReturnStruct::new(MMAP_VADDR_INVALID,0,0,pt_regs),None,None);
            }

            if self.mmu_man.mmu_get_va_entry_by_ioid(ioid,va_add_range(va,i)).is_some() 
            {
                return (SyscallReturnStruct::new(MMAP_VADDR_NOT_FREE,0,0,pt_regs),None,None);
            }

            let page_entry = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,va_add_range(va,i));
            
            if page_entry.is_none(){
                return (SyscallReturnStruct::new(MMAP_VADDR_NOT_FREE,0,0,pt_regs),None,None);
            }

            if self.page_alloc.get_page_rf_counter_by_page_ptr(page_entry.unwrap().addr) >= usize::MAX - range {
                return (SyscallReturnStruct::new(PAGE_RF_COUNTER_OVERFLOW,0,0,pt_regs),None,None);
            }
        }

        self.kernel_map_pagetable_range_page_to_iommutable(pcid,ioid,va,perm_bits,range);
        assert(self.wf());

        return (SyscallReturnStruct::new(SUCCESS,0,0,pt_regs),None,None);
    }
}
}