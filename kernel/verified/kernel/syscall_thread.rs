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
// use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {

    pub fn syscall_new_thread(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx, pt_regs_new_thread: PtRegs) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
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
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs),None,None);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs),None,None);
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,pt_regs),None,None);
        }

        if self.page_alloc.free_pages.len() < 1 {
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs),None,None);
        }
        if self.mmu_man.free_pcids.len() == 0 {
            return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.get_proc_num_of_threads_by_proc_ptr(current_proc_ptr) >= MAX_NUM_THREADS_PER_PROC {
            return (SyscallReturnStruct::new(PROC_THREAD_LIST_FULL,pcid,cr3,pt_regs),None,None);
        }
 
        let (page_ptr1, page_perm1) = self.page_alloc.alloc_kernel_mem(); 
        let new_thread = self.proc_man.new_thread(pt_regs_new_thread,page_ptr1, page_perm1,current_proc_ptr);

        assert(self.wf());
        self.proc_man.pass_endpoint(current_thread_ptr,endpoint_index,new_thread,0);

        assert(self.wf());
        return (SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs),None,None);
    }

}
}