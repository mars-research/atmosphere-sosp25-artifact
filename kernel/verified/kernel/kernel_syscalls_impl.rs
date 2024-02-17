use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
// use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;

use crate::kernel::*;


impl Kernel {


    fn kernel_new_proc_checker(&self, cpu_id:CPUID, endpoint_index: EndpointIdx) -> (ret: ErrorCodeType)
        requires
            self.wf(),
        ensures
            ret == SUCCESS ==> (
                (0<=cpu_id<NUM_CPUS)
                &&
                (self.cpu_list[cpu_id as int].get_is_idle() == false)
                &&
                (0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS)
                &&
                (self.proc_man.get_thread(self.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors[endpoint_index as int] != 0)
                &&
                (self.proc_man.get_endpoint(self.proc_man.get_thread(self.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors[endpoint_index as int]).rf_counter < usize::MAX)
                &&
                (self.page_alloc.free_pages.len() >= 4)
                &&
                (self.proc_man.scheduler.len() < MAX_NUM_THREADS)
                &&
                (self.proc_man.proc_ptrs.len() < MAX_NUM_PROCS)
                &&
                (self.mmu_man.free_pcids.len() != 0)
            )
    {
        if cpu_id >= NUM_CPUS{
            return CPU_ID_INVALID;
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return NO_RUNNING_THREAD;
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return ENDPOINT_INDEX_INVALID;
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SHARED_ENDPOINT_NOT_EXIST;
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            return SHARED_ENDPOINT_REF_COUNT_OVERFLOW;
        }

        if self.page_alloc.free_pages.len() < 4 {
            return SYSTEM_OUT_OF_MEM;
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            return SCHEDULER_NO_SPACE;
        }

        if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
            return PROCESS_LIST_NO_SPEC;
        }
        if self.mmu_man.free_pcids.len() == 0 {
            return NO_FREE_PCID;
        }

        return SUCCESS;
    }

    fn kernel_new_proc_endpoint_passer(&mut self, sender_ptr: ThreadPtr, sender_endpoint_index: EndpointIdx, receiver_ptr: ThreadPtr, receiver_endpoint_index: EndpointIdx)
        requires
            old(self).wf(),
            old(self).proc_man.get_thread_ptrs().contains(sender_ptr),
            old(self).proc_man.get_thread_ptrs().contains(receiver_ptr),
            0<=sender_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            0<=receiver_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int] != 0,
            old(self).proc_man.get_thread(receiver_ptr).endpoint_descriptors@[receiver_endpoint_index as int] == 0,
            forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(self).proc_man.get_thread(receiver_ptr).endpoint_descriptors@[i as int] != old(self).proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int],
            old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).rf_counter != usize::MAX,
        ensures
            self.wf(),    
        {
            self.proc_man.pass_endpoint(sender_ptr,sender_endpoint_index,receiver_ptr,receiver_endpoint_index);
            assert(
                self.proc_man.wf());
            assert(
                self.mmu_man.wf()
            );
            assert(
                self.page_alloc.wf()
            );
            assert(
                self.cpu_list.wf()
            );
            assert(
                self.kernel_cpu_list_wf()
            );
            assert(
                self.kernel_mem_layout_wf()
            );
            assert(
                self.kernel_mmu_page_alloc_pagetable_wf()
            );
            assert(
                self.kernel_mmu_page_alloc_iommutable_wf()
            );
            assert(self.kernel_proc_mmu_wf());
            assert(self.kernel_proc_no_thread_in_transit());
            assert(self.kernel_tlb_wf());
            assert(self.wf());
        }

    pub fn kernel_new_proc(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx, pt_regs_new_proc: PtRegs) -> (ret:(ErrorCodeType, Pcid, usize, PtRegs))
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {   
        if cpu_id >= NUM_CPUS{
            return (CPU_ID_INVALID,0,0,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (NO_RUNNING_THREAD,0,0,pt_regs);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return (ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return (SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs);
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            return (SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,pt_regs);
        }

        if self.page_alloc.free_pages.len() < 4 {
            return (SYSTEM_OUT_OF_MEM,pcid,cr3,pt_regs);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            return (SCHEDULER_NO_SPACE,pcid,cr3,pt_regs);
        }

        if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
            return (PROCESS_LIST_NO_SPEC,pcid,cr3,pt_regs);
        }
        if self.mmu_man.free_pcids.len() == 0 {
            return (NO_FREE_PCID,pcid,cr3,pt_regs);
        }
 
        let (page_ptr1, page_perm1) = self.page_alloc.alloc_pagetable_mem(); 
        let new_pcid = self.mmu_man.new_pagetable(page_ptr1,page_perm1,Some(self.kernel_pml4_entry));
        let (page_ptr2, page_perm2) = self.page_alloc.alloc_kernel_mem(); 
        let (page_ptr3, page_perm3) = self.page_alloc.alloc_kernel_mem(); 
        let new_proc = self.proc_man.new_proc(page_ptr2, page_perm2, new_pcid, None);
        let new_thread = self.proc_man.new_thread(pt_regs_new_proc,page_ptr3, page_perm3,new_proc);

        assert(
            self.proc_man.wf());
        assert(
            self.mmu_man.wf()
        );
        assert(
            self.page_alloc.wf()
        );
        assert(
            self.cpu_list.wf()
        );
        assert(
            self.kernel_cpu_list_wf()
        );
        assert(
            self.kernel_mem_layout_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_pagetable_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_iommutable_wf()
        );
        assert(self.kernel_proc_mmu_wf());
        assert(self.kernel_proc_no_thread_in_transit());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
        
        self.kernel_new_proc_endpoint_passer(current_thread_ptr, endpoint_index, new_thread, 0);
        return (SUCCESS,pcid,cr3,pt_regs);

    }


}

pub fn hello_world() -> (ret:usize){
    return 233;
}
}