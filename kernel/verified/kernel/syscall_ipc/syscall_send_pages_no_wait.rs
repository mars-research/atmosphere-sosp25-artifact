use vstd::prelude::*;
verus! {

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
// use crate::page_alloc::*;
use crate::page_alloc::*;

use crate::kernel::*;

// pub closed spec fn syscall_send_pages_no_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool
// {
//     if !old.wf() || !new.wf()
//     {
//         false
//     }
//     else{
//         let valid_thread = (cpu_id < NUM_CPUS && 
//             old.cpu_list@[cpu_id as int].get_is_idle() == false);
//         let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
//             old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;
            

//         if valid_thread && valid_endpoint 
//         {
//             let endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int];
//             let endpoint_state = old.proc_man.get_endpoint(endpoint_ptr).queue_state;
//             let scheduler_len = old.proc_man.scheduler.len();
//             let endpoint_len = old.proc_man.get_endpoint(endpoint_ptr).len();
//             if endpoint_state == SEND {
//                 old == new
//             }else{
//                 if endpoint_len == 0 {
//                     old == new
//                 }else{
//                     let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
//                     let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;
                    
//                     if scheduler_len == MAX_NUM_THREADS{
//                         old == new
//                     }else if receiver_ipc_payload.calling != false ||
//                     receiver_ipc_payload.message.is_some() ||
//                     receiver_ipc_payload.page_payload.is_some() ||
//                     receiver_ipc_payload.endpoint_payload.is_some() ||
//                     receiver_ipc_payload.pci_payload.is_some()
//                     {
                        
//                         new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
//                         &&
//                         new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
//                         &&
//                         new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
//                     }else{
//                         new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
//                         &&
//                         new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
//                         &&
//                         new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
//                     }

//                 }
//             }
//         }else{
//             //if the syscall is not success, nothing will change, goes back to user level
//             old == new
//         }
            
//     }
// }


impl Kernel {
    pub fn syscall_send_pages_no_wait(&mut self, cpu_id:CPUID, pt_regs: &mut Registers, endpoint_index: EndpointIdx, va: VAddr, range: usize) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            // syscall_send_pages_no_wait_spec(*old(self), *self, cpu_id, endpoint_index),
    {
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,0);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,default_pcid,default_cr3,0);
        }

        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);

        let ipc_payload = IPCPayLoad::new_to_none();
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,current_thread_ptr);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,current_thread_ptr);
        }

        if self.proc_man.get_endpoint_state_by_endpoint_ptr(target_endpoint_ptr) == SEND {
            //sender queue
            return SyscallReturnStruct::new(NO_RECEIVER,pcid,cr3,current_thread_ptr);
        }
        else{
            //receiver queue
            if self.proc_man.get_endpoint_len_by_endpoint_ptr(target_endpoint_ptr) == 0{
                //change the endpoint to a sender queue.

                // self.proc_man.proc_man_set_endpoint_queue_state_by_endpoint_ptr(target_endpoint_ptr, SEND);
                // assert(self.wf());
                return SyscallReturnStruct::new(NO_RECEIVER,pcid,cr3,current_thread_ptr);

            }
                // pop the receiver.
                if self.proc_man.scheduler.len() == MAX_NUM_THREADS {
                    return SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,current_thread_ptr);
                }

                let new_thread_ptr = self.proc_man.get_head_of_endpoint_by_endpoint_ptr(target_endpoint_ptr);

                let sender_ipc_payload = ipc_payload;
                let receiver_ipc_payload = self.proc_man.get_ipc_payload_by_thread_ptr(new_thread_ptr);

                let sender_pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
                let receiver_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                assert(0<=sender_pcid<PCID_MAX);
                assert(self.mmu_man.get_free_pcids_as_set().contains(sender_pcid) == false);
                assert(0<=receiver_pcid<PCID_MAX);
                assert(self.mmu_man.get_free_pcids_as_set().contains(receiver_pcid) == false);

                let new_pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                let new_cr3 = self.mmu_man.get_cr3_by_pcid(new_pcid);

                let perm_bits = READ_WRITE_EXECUTE as usize;

                assume(spec_va_perm_bits_valid(perm_bits));

                if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_some() ||
                    receiver_ipc_payload.page_payload.is_none() ||
                    receiver_ipc_payload.endpoint_payload.is_some() ||
                    receiver_ipc_payload.pci_payload.is_some()
                {
                    self.proc_man.pop_endpoint_to_scheduler(current_thread_ptr,endpoint_index,Some(IPC_TYPE_NOT_MATCH));
                    return SyscallReturnStruct::new(IPC_TYPE_NOT_MATCH,pcid,cr3,current_thread_ptr);
                }else if receiver_ipc_payload.page_payload.unwrap().1 != range ||
                            range >= usize::MAX/3 || 
                            self.page_alloc.free_pages.len() < 3 * range
                {              
                    self.proc_man.pop_endpoint_to_scheduler(current_thread_ptr,endpoint_index,Some(PAGE_PAYLOAD_INVALID));
                    return SyscallReturnStruct::new(IPC_TYPE_NOT_MATCH,pcid,cr3,current_thread_ptr);     
                }else if self.kernel_page_sharing_helper(sender_pcid, new_pcid, perm_bits, va, receiver_ipc_payload.page_payload.unwrap().0, range) == true{
                    self.proc_man.pop_endpoint_to_scheduler(current_thread_ptr,endpoint_index,Some(SUCCESS));
                    self.kernel_map_pagetable_range_page_to_pagetable(sender_pcid, new_pcid, va, receiver_ipc_payload.page_payload.unwrap().0, perm_bits,range);
                    return SyscallReturnStruct::new(SUCCESS,pcid,cr3,current_thread_ptr);
                }
                else {
                    // assert(kernel_page_sharing_spec_helper(*old(self),sender_pcid,receiver_pcid, va, receiver_ipc_payload.page_payload.unwrap().0, range) == false);
                    self.proc_man.pop_endpoint_to_scheduler(current_thread_ptr,endpoint_index,Some(PAGE_PAYLOAD_INVALID));
                    return SyscallReturnStruct::new(IPC_TYPE_NOT_MATCH,pcid,cr3,current_thread_ptr);     
                }
 

                
        }
    }
}
}
