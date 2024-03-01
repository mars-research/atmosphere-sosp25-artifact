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

    pub fn syscall_new_endpoint(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx) -> (ret:SyscallReturnStruct)
        requires
            old(self).wf(),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();  
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3,pt_regs);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr != 0 {
            return SyscallReturnStruct::new(ENDPOINT_SLOT_TAKEN,pcid,cr3,pt_regs);
        }

        if self.page_alloc.free_pages.len() < 1 {
            return SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,pt_regs);
        }

        let (page_ptr1, page_perm1) = self.page_alloc.alloc_kernel_mem(); 
        self.proc_man.new_endpoint(page_ptr1, page_perm1,current_thread_ptr, endpoint_index);

        assert(self.wf());
        return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
    }



}
}