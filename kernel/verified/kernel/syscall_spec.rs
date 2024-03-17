use vstd::prelude::*;
verus! {

use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
use crate::page_alloc::*;

use crate::kernel::*;

pub open spec fn syscall_send_pages_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, va: VAddr, range: usize) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;
            

        if valid_thread && valid_endpoint 
        {
            let endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int];
            let endpoint_state = old.proc_man.get_endpoint(endpoint_ptr).queue_state;
            let scheduler_len = old.proc_man.scheduler.len();
            let endpoint_len = old.proc_man.get_endpoint(endpoint_ptr).len();
            if endpoint_state == SEND {
                if endpoint_len == MAX_NUM_THREADS_PER_ENDPOINT{
                    old == new
                }else if scheduler_len == 0{
                    new.cpu_list@[cpu_id as int].get_is_idle() == true
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
            }else{
                if endpoint_len == 0 {
                    if scheduler_len == 0{
                        new.cpu_list@[cpu_id as int].get_is_idle() == true
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                    else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;
                    
                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;

                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                                receiver_ipc_payload.message.is_some() ||
                                receiver_ipc_payload.page_payload.is_None() ||
                                receiver_ipc_payload.endpoint_payload.is_some() ||
                                receiver_ipc_payload.pci_payload.is_some()
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED

                    }else if receiver_ipc_payload.page_payload.unwrap().1 != range ||
                                range >= usize::MAX/3 || 
                                old.page_alloc.free_pages.len() < 3 * range
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }
                    else if kernel_page_sharing_spec_helper(old,sender_pcid,receiver_pcid, va, receiver_ipc_payload.page_payload.unwrap().0, range)
                    {
                        forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[spec_va_add_range(receiver_ipc_payload.page_payload.unwrap().0,j)].is_Some()
                    }else
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED  
                    }


                }
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}


pub open spec fn syscall_send_message_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, message_va: VAddr, length:usize) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;
            

        if valid_thread && valid_endpoint 
        {
            let endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int];
            let endpoint_state = old.proc_man.get_endpoint(endpoint_ptr).queue_state;
            let scheduler_len = old.proc_man.scheduler.len();
            let endpoint_len = old.proc_man.get_endpoint(endpoint_ptr).len();
            if endpoint_state == SEND {
                if endpoint_len == MAX_NUM_THREADS_PER_ENDPOINT{
                    old == new
                }else if scheduler_len == 0{
                    new.cpu_list@[cpu_id as int].get_is_idle() == true
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
            }else{
                if endpoint_len == 0 {
                    if scheduler_len == 0{
                        new.cpu_list@[cpu_id as int].get_is_idle() == true
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                    else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;

                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_None() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_some() ||
                    receiver_ipc_payload.pci_payload.is_some()
                    {
                        
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }else if (spec_va_valid(message_va) == false) || (spec_va_valid(receiver_ipc_payload.message.unwrap().0) == false) || (length != receiver_ipc_payload.message.unwrap().1)
                            || (length>4096) || (length<=0)
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }else{
                        let sender_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(sender_pcid)[message_va];
                        let receiver_pa_op = old.mmu_man.get_pagetable_mapping_by_pcid(receiver_pcid)[receiver_ipc_payload.message.unwrap().0];

                        if sender_pa_op.is_None() || receiver_pa_op.is_None() {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        }else if  sender_pa_op.unwrap().addr == receiver_pa_op.unwrap().addr
                        {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        }else{
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        }

                    }
                }
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub open spec fn syscall_send_endpoint_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx, share_endpoint_index: EndpointIdx) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;
            

        if valid_thread && valid_endpoint 
        {
            let endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int];
            let endpoint_state = old.proc_man.get_endpoint(endpoint_ptr).queue_state;
            let scheduler_len = old.proc_man.scheduler.len();
            let endpoint_len = old.proc_man.get_endpoint(endpoint_ptr).len();
            if endpoint_state == SEND {
                if endpoint_len == MAX_NUM_THREADS_PER_ENDPOINT{
                    old == new
                }else if scheduler_len == 0{
                    new.cpu_list@[cpu_id as int].get_is_idle() == true
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
            }else{
                if endpoint_len == 0 {
                    if scheduler_len == 0{
                        new.cpu_list@[cpu_id as int].get_is_idle() == true
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                    else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;

                    let sender_pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
                    let receiver_pcid = old.proc_man.get_proc(old.proc_man.get_thread(receiver_ptr).parent).pcid;
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_some() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_none() ||
                    receiver_ipc_payload.pci_payload.is_some()
                    {
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }else
                    {
                        let sender_endpoint_index = share_endpoint_index;
                        let receiver_endpoint_index = receiver_ipc_payload.endpoint_payload.unwrap();
                        if sender_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS || receiver_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS {
                            new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            &&
                            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            &&
                            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                        }else{
                            let sender_endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[sender_endpoint_index as int];
                            let receiver_endpoint_ptr =  old.proc_man.get_thread(receiver_ptr).endpoint_descriptors@[receiver_endpoint_index as int];

                            true 
                            // if sender_endpoint_ptr == 0 || receiver_endpoint_ptr != 0
                            //     ||old.proc_man.get_endpoint(sender_endpoint_ptr).rf_counter == usize::MAX
                            //     || (
                            //         forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old.proc_man.get_thread(receiver_ptr).endpoint_descriptors@[i as int] != sender_endpoint_ptr
                            //     ) == false
                            // {
                            //     new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                            //     &&
                            //     new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                            //     &&
                            //     new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                            // }else{
                            //     new.proc_man.get_thread(receiver_ptr).endpoint_descriptors@ =~= old.proc_man.get_thread(receiver_ptr).endpoint_descriptors@.update(
                            //                             receiver_endpoint_index as int, old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[sender_endpoint_index as int])
                            // }
                        }
                    }
                }
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub open spec fn syscall_send_empty_wait_spec(old:Kernel, new:Kernel, cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0;
            

        if valid_thread && valid_endpoint 
        {
            let endpoint_ptr = old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int];
            let endpoint_state = old.proc_man.get_endpoint(endpoint_ptr).queue_state;
            let scheduler_len = old.proc_man.scheduler.len();
            let endpoint_len = old.proc_man.get_endpoint(endpoint_ptr).len();
            if endpoint_state == SEND {
                if endpoint_len == MAX_NUM_THREADS_PER_ENDPOINT{
                    old == new
                }else if scheduler_len == 0{
                    new.cpu_list@[cpu_id as int].get_is_idle() == true
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
                else{
                    new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                    &&
                    new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                    &&
                    new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                }
            }else{
                if endpoint_len == 0 {
                    if scheduler_len == 0{
                        new.cpu_list@[cpu_id as int].get_is_idle() == true
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                    else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(old.proc_man.scheduler@[0])
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == BLOCKED
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_ptr == Some(endpoint_ptr)
                    }
                }else{
                    let receiver_ptr = old.proc_man.get_endpoint(endpoint_ptr).queue@[0];
                    let receiver_ipc_payload = old.proc_man.get_thread(receiver_ptr).ipc_payload;
                    
                    if scheduler_len == MAX_NUM_THREADS{
                        old == new
                    }else if receiver_ipc_payload.calling != false ||
                    receiver_ipc_payload.message.is_some() ||
                    receiver_ipc_payload.page_payload.is_some() ||
                    receiver_ipc_payload.endpoint_payload.is_some() ||
                    receiver_ipc_payload.pci_payload.is_some()
                    {
                        
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }else{
                        new.cpu_list@[cpu_id as int].get_current_thread() == Some(receiver_ptr)
                        &&
                        new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
                        &&
                        new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).state == SCHEDULED
                    }

                }
            }
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub open spec fn syscall_new_proc_with_iommu_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, new_proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = (endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0 &&
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).rf_counter != usize::MAX);
        let proc_list_has_space = old.proc_man.proc_ptrs.len() != MAX_NUM_PROCS;
        let system_has_memory = old.page_alloc.free_pages.len() >= 5;
        let system_has_free_pcid_ioid = old.mmu_man.free_pcids.len() != 0 && old.mmu_man.free_ioids.len() != 0;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && valid_endpoint && proc_list_has_space && system_has_memory && system_has_free_pcid_ioid && system_scheduler_has_space
        {
            (
                //if the syscall is success, a new process and a new thread of the new process will be created
                new_proc.is_Some()
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs().push(new_proc.unwrap())
                &&
                // kernel correctly created a new thread for that process
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs().insert(new_thread.unwrap())
                &&
                // the new thread is scheduled
                new.proc_man.get_thread(new_thread.unwrap()).state == SCHEDULED
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                new.proc_man.get_thread(new_thread.unwrap()).endpoint_descriptors@[0] =~= new.proc_man.get_thread(new.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int]
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> new.mmu_man.get_pagetable_by_pcid(new.proc_man.get_proc(new.proc_man.get_thread(new_thread.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

pub open spec fn syscall_new_proc_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx, new_proc:Option<ProcPtr>, new_thread:Option<ThreadPtr>) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = (endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0 &&
            old.proc_man.get_endpoint(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int]).rf_counter != usize::MAX);
        let proc_list_has_space = old.proc_man.proc_ptrs.len() != MAX_NUM_PROCS;
        let system_has_memory = old.page_alloc.free_pages.len() >= 4;
        let system_has_free_pcid = old.mmu_man.free_pcids.len() != 0;
        let system_scheduler_has_space = old.proc_man.scheduler.len() != MAX_NUM_THREADS;

        if valid_thread && valid_endpoint && proc_list_has_space && system_has_memory && system_has_free_pcid && system_scheduler_has_space
        {
            (
                //if the syscall is success, a new process and a new thread of the new process will be created
                new_proc.is_Some()
                &&
                new_thread.is_Some()
                &&
                //each cpu still runs the same thread, no context switch
                new.cpu_list =~= old.cpu_list
                &&
                // kernel correctly created a new process
                new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs().push(new_proc.unwrap())
                &&
                // kernel correctly created a new thread for that process
                new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs().insert(new_thread.unwrap())
                &&
                // the new thread is scheduled
                new.proc_man.get_thread(new_thread.unwrap()).state == SCHEDULED
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                new.proc_man.get_thread(new_thread.unwrap()).endpoint_descriptors@[0] =~= new.proc_man.get_thread(new.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int]
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> new.mmu_man.get_pagetable_by_pcid(new.proc_man.get_proc(new.proc_man.get_thread(new_thread.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

pub open spec fn syscall_malloc_spec(old:Kernel, new:Kernel, cpu_id:CPUID, va: usize, perm_bits:usize, range: usize) -> bool
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let perm_bits_valid = spec_va_perm_bits_valid(perm_bits);
        let system_has_memory = old.page_alloc.free_pages.len() >= 4 * range;
        let range_valid = range != 0 && range < (usize::MAX/4);
        let pcid = old.proc_man.get_proc(old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).parent).pcid;
        let va_valid =  (forall|j:usize| #![auto] 0<=j<range ==> spec_va_valid(spec_va_add_range(va,j)));
        let va_mapping_valid = (forall|j:usize| #![auto] 0<=j<range ==> old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None());

        if valid_thread && perm_bits_valid && system_has_memory && range_valid && va_valid && va_mapping_valid
        {
            (new.proc_man =~= old.proc_man
            &&
            new.cpu_list =~= old.cpu_list
            &&
            new.mmu_man.free_pcids =~= old.mmu_man.free_pcids
            &&
            new.mmu_man.free_ioids =~= old.mmu_man.free_ioids
            &&
            (forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && new.mmu_man.get_free_pcids_as_set().contains(_pcid) == false && _pcid != pcid ==> 
                new.mmu_man.get_pagetable_mapping_by_pcid(_pcid) =~= old.mmu_man.get_pagetable_mapping_by_pcid(_pcid))
            &&
            (forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX && new.mmu_man.get_free_ioids_as_set().contains(ioid) == false ==> 
                new.mmu_man.get_iommutable_mapping_by_ioid(ioid) =~= old.mmu_man.get_iommutable_mapping_by_ioid(ioid))
            &&
            (forall|j:usize| #![auto] 0<=j<range ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some())
            &&
            (forall|_va:VAddr| #![auto] spec_va_valid(_va) && 
            (
                forall|j:usize| #![auto] 0<=j<range ==> spec_va_add_range(va,j) != _va
            )
            ==> new.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] == old.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va])
            )
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old == new
        }
            
    }
}

pub open spec fn syscall_new_endpoint_spec(old:Kernel,new:Kernel,cpu_id:CPUID, endpoint_index: EndpointIdx) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let valid_endpoint = endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS && 
            old.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] == 0;
        let system_has_memory = old.page_alloc.free_pages.len() >= 1;

        if valid_thread && valid_endpoint && system_has_memory
        {
            new.cpu_list =~= old.cpu_list
            &&
            // kernel correctly created a new process
            new.proc_man.get_proc_ptrs() =~= old.proc_man.get_proc_ptrs()
            &&
            // kernel correctly created a new thread for that process
            new.proc_man.get_thread_ptrs() =~= old.proc_man.get_thread_ptrs()
            &&
            new.proc_man.get_thread(old.cpu_list@[cpu_id as int].get_current_thread().unwrap()).endpoint_descriptors@[endpoint_index as int] != 0
            &&
            new.proc_man.get_endpoint_ptrs().len() == old.proc_man.get_endpoint_ptrs().len() + 1
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

pub open spec fn kernel_timer_int_spec(old:Kernel,new:Kernel,cpu_id:CPUID) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let valid_thread = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle() == false);
        let scheduler_has_thread = old.proc_man.scheduler.len() != 0;

        if valid_thread && scheduler_has_thread 
        {
            forall|i:CPUID|#![auto] 0 <= i < NUM_CPUS && i != cpu_id ==> new.cpu_list@[i as int] =~= old.cpu_list@[i as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread().unwrap() =~= old.proc_man.scheduler@[0]
            &&
            new.proc_man.scheduler@ =~= old.proc_man.scheduler@.subrange(1, old.proc_man.scheduler.len() as int).push(old.cpu_list@[cpu_id as int].get_current_thread().unwrap())
            &&
            new.mmu_man =~= old.mmu_man
            &&
            new.page_alloc =~= old.page_alloc
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
}

pub open spec fn kernel_idle_pop_sched_spec(old:Kernel,new:Kernel,cpu_id:CPUID) -> bool 
{
    if !old.wf() || !new.wf()
    {
        false
    }
    else{
        //checking arguments
        let cpu_idle = (cpu_id < NUM_CPUS && 
            old.cpu_list@[cpu_id as int].get_is_idle());
        let scheduler_has_thread = old.proc_man.scheduler.len() != 0;

        if cpu_idle && scheduler_has_thread 
        {
            forall|i:CPUID|#![auto] 0 <= i < NUM_CPUS && i != cpu_id ==> new.cpu_list@[i as int] =~= old.cpu_list@[i as int]
            &&
            new.cpu_list@[cpu_id as int].get_current_thread().unwrap() =~= old.proc_man.scheduler@[0]
            &&
            new.proc_man.scheduler@ =~= old.proc_man.scheduler@.subrange(1, old.proc_man.scheduler.len() as int)
            &&
            new.mmu_man =~= old.mmu_man
            &&
            new.page_alloc =~= old.page_alloc
        }else{
            //if the syscall is not success, nothing will change, goes back to user level
            old =~= new
        }
    }
    
}

}