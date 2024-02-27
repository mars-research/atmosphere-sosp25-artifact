use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::proc::*;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {
    pub fn syscall_send_wait(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx, ipc_payload:IPCPayLoad) -> (ret: SyscallReturnStruct)
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
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs);
        }

        if self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
            //sender queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == MAX_NUM_THREADS_PER_ENDPOINT{
                return SyscallReturnStruct::new(ENDPOINT_FULL,pcid,cr3,pt_regs);
            }

            // self.kernel_push_current_thread_to_endpoint()
            if self.proc_man.scheduler.len() == 0{
                assert(self.proc_man.get_thread(current_thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0);
                self.proc_man.set_thread_to_transit(current_thread_ptr);
                self.proc_man.push_endpoint(current_thread_ptr, endpoint_index, ipc_payload);
                self.cpu_list.set_current_thread(cpu_id, None);
                assert(self.wf());
                return SyscallReturnStruct::new(NO_NEXT_THREAD,0,0,pt_regs);
            }else{
                self.proc_man.set_thread_to_transit(current_thread_ptr);
                self.proc_man.push_endpoint(current_thread_ptr, endpoint_index, ipc_payload);
                let new_thread_ptr = self.proc_man.pop_scheduler();
                self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
                assert(self.wf());
                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
                return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,pt_regs);
            }
        }
        else{
            //receiver queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == 0{
                //change the endpoint to a sender queue.

                // self.proc_man.proc_man_set_endpoint_queue_state_by_endpoint_ptr(target_endpoint_ptr, SEND);
                // assert(self.wf());
                if self.proc_man.scheduler.len() == 0{
                    assert(self.proc_man.get_thread(current_thread_ptr).endpoint_descriptors@[endpoint_index as int] != 0);
                    self.proc_man.set_thread_to_transit(current_thread_ptr);
                    self.proc_man.push_endpoint_and_set_state(current_thread_ptr, endpoint_index, ipc_payload, SEND);
                    self.cpu_list.set_current_thread(cpu_id, None);
                    assert(self.wf());
                    return SyscallReturnStruct::new(NO_NEXT_THREAD,0,0,pt_regs);
                }else{
                    self.proc_man.set_thread_to_transit(current_thread_ptr);
                    self.proc_man.push_endpoint_and_set_state(current_thread_ptr, endpoint_index, ipc_payload, SEND);
                    let new_thread_ptr = self.proc_man.pop_scheduler();
                    self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
                    assert(self.wf());
                    let new_pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
                    let new_cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
                    return SyscallReturnStruct::new(NO_ERROR_CODE,new_pcid,new_cr3,pt_regs);
                }

            }
                // pop the receiver. 
                if self.proc_man.scheduler.len() == MAX_NUM_THREADS {
                    return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs);
                }
                
                // next line will check call/receive_call and everything and return the current thread. 
                let (receiver_ptr,error_code_pop) = self.kernel_pop_receiver_endpoint(cpu_id,current_thread_ptr,endpoint_index);
                if error_code_pop != SUCCESS {
                    return SyscallReturnStruct::new(error_code_pop,pcid,cr3,pt_regs)
                }


                let error_code_message_copy = self.kernel_ipc_copy_messages(current_thread_ptr, receiver_ptr);
                if error_code_message_copy != SUCCESS{
                    return SyscallReturnStruct::new(error_code_message_copy,pcid,cr3,pt_regs)
                }
                let error_code_page_copy = self.kernel_ipc_copy_pages(current_thread_ptr, receiver_ptr);
                if error_code_page_copy != SUCCESS{
                    return SyscallReturnStruct::new(error_code_page_copy,pcid,cr3,pt_regs)
                }            

                return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
        }
    }
}
}