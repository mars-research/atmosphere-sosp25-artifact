use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::proc::*;
// use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {
    pub fn syscall_reply(&mut self, cpu_id:CPUID, pt_regs: PtRegs, ipc_payload:IPCPayLoad) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,0,0,pt_regs);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        
        let caller_ptr_op = self.proc_man.get_thread_caller(current_thread_ptr);

        if caller_ptr_op.is_none() {
            return SyscallReturnStruct::new(NO_CALLER,pcid,cr3,pt_regs);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS {

            return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs);
        }
        let caller_ptr = caller_ptr_op.unwrap();

        self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr);
        self.cpu_list.set_current_thread(cpu_id, Some(caller_ptr));
        assert(self.wf());

        let error_code_message_copy = self.kernel_ipc_copy_messages(current_thread_ptr, caller_ptr);
        if error_code_message_copy != SUCCESS{
            return SyscallReturnStruct::new(error_code_message_copy,pcid,cr3,pt_regs)
        }
        let error_code_page_copy = self.kernel_ipc_copy_pages(current_thread_ptr, caller_ptr);
        if error_code_page_copy != SUCCESS{
            return SyscallReturnStruct::new(error_code_page_copy,pcid,cr3,pt_regs)
        }    
        assert(self.wf());
        return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
    }
}
}