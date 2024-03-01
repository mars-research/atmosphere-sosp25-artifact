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
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,pt_regs);
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

        let new_pcid = self.proc_man.get_pcid_by_thread_ptr(caller_ptr);
        let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);

        let callee_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(current_thread_ptr);
        let caller_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(caller_ptr);

        if callee_ipc_payload.message.is_some() || caller_ipc_payload.message.is_some()
        {
            //sharing message
            if callee_ipc_payload.message.is_none() || caller_ipc_payload.message.is_none() {
                let new_pt_regs = self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
            }
            else if callee_ipc_payload.page_payload.is_some() || caller_ipc_payload.page_payload.is_some() 
                || callee_ipc_payload.endpoint_payload.is_some() || caller_ipc_payload.endpoint_payload.is_some() 
                || callee_ipc_payload.pci_payload.is_some() || caller_ipc_payload.pci_payload.is_some() 
            {
                let new_pt_regs = self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
            } 
            else{
                let sender_va = caller_ipc_payload.message.unwrap().0;
                let receiver_va = callee_ipc_payload.message.unwrap().0;

                let sender_len = sender_ipc_payload.message.unwrap().1;
                let receiver_len = receiver_ipc_payload.message.unwrap().1;

                if (va_valid(sender_va) == false) || (va_valid(receiver_va) == false) || (sender_len != receiver_len) 
                    || (receiver_len>4096) || (receiver_len<=0)
                {
                    let new_pt_regs = self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                    self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                    return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                }else{
                    let sender_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(pcid,sender_va);
                    let receiver_pa_op = self.mmu_man.mmu_get_va_entry_by_pcid(new_pcid,receiver_va);

                    if sender_pa_op.is_none() || receiver_pa_op.is_none() {
                        let new_pt_regs = self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                        self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                        return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                    }else{
                        let sender_pa = sender_pa_op.unwrap().addr;
                        let receiver_pa = receiver_pa_op.unwrap().addr;
                        
                        if sender_pa == receiver_pa {
                            let new_pt_regs = self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(MESSAGE_INVALID));
                            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                            return SyscallReturnStruct::new(MESSAGE_INVALID,new_pcid,new_cr3,new_pt_regs);
                        }else{
                            self.kernel_pass_message(sender_pa, receiver_pa, receiver_len);

                            let new_pt_regs = self.proc_man.weak_up_caller_and_schedule(caller_ptr, current_thread_ptr, pt_regs, Some(SUCCESS));
                            self.cpu_list.set_current_thread(cpu_id,Some(caller_ptr));
                            return SyscallReturnStruct::new(SUCCESS,new_pcid,new_cr3,new_pt_regs);
                        }
                    }
                }
            }
        }
    }
}
}