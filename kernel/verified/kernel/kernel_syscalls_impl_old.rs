use vstd::prelude::*;

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::pcid_alloc::*;
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use crate::kernel::*;

verus! {
impl Kernel {

    pub fn sys_timer_int(&mut self, cpu_id: CPUID)
        requires
            old(self).kernel_wf(),
            0 <= cpu_id <NUM_CPUS,
            old(self).proc_man.scheduler.len() < MAX_NUM_THREADS,
    {
        assert(0 <= cpu_id <NUM_CPUS);
        let thread_ptr_option = self.cpu_list.get(cpu_id).current_t;
        if thread_ptr_option.is_none(){
            //should panic as unverified code has some fatal bugs
            return;
        }
        let thread_ptr = thread_ptr_option.unwrap();
        assert(self.proc_man.get_thread(thread_ptr).state == RUNNING);
        assert(self.proc_man.get_thread(thread_ptr).state != SCHEDULED);
        self.proc_man.push_scheduler(thread_ptr);

        let new_thread_ptr = self.proc_man.pop_scheduler();
        assert(self.proc_man.scheduler@.contains(new_thread_ptr) == false);

        let cpu = Cpu{
            current_t: Some(new_thread_ptr),
            tlb: self.cpu_list.get(cpu_id).tlb,
            iotlb: self.cpu_list.get(cpu_id).iotlb
        };

        self.cpu_list.set(cpu_id,cpu);
        assert(self.cpu_list.wf());
        assert(self.kernel_cpulist_wf());
        assert(self.proc_man.wf());
        assert(self.kernel_wf());
    }

    /// Send Do Not Wait syscall
    pub fn sys_send_no_wait(&mut self, cpu_id: CPUID, sender_endpoint_index: EndpointIdx)
        requires
            old(self).kernel_wf(),
            0 <= cpu_id <NUM_CPUS,
            // old(self).proc_man.scheduler.len() < MAX_NUM_THREADS,
    {
        assert(0 <= cpu_id <NUM_CPUS);
        let sender_thread_ptr_option = self.cpu_list.get(cpu_id).current_t;
        if sender_thread_ptr_option.is_none(){
            //should panic as unverified code has some fatal bugs
            return;
        }

        if sender_endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS {
            self.proc_man.set_thread_error_code(sender_thread_ptr_option.unwrap(), Some(SENDER_ENDPOINT_OUT_OF_BOUND));
            return;
        } 
        assert(0<=sender_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS);

        let sender_thread_ptr = sender_thread_ptr_option.unwrap();
        assert(self.proc_man.get_thread(sender_thread_ptr).state == RUNNING);
        assert(self.proc_man.get_thread(sender_thread_ptr).state != SCHEDULED);

        let endpoint_ptr = self.proc_man.get_thread_endpoint_descriptor(sender_thread_ptr, sender_endpoint_index);
        if endpoint_ptr == 0 {
            self.proc_man.set_thread_error_code(sender_thread_ptr_option.unwrap(), Some(SENDER_ENDPOINT_NOT_EXIST));
            return;
        }
        assert(endpoint_ptr != 0);
        assert(self.proc_man.get_endpoint_ptrs().contains(endpoint_ptr));

        let endpoint_len = self.proc_man.get_endpoint_len(endpoint_ptr);
        if endpoint_len == 0{
            self.proc_man.set_thread_error_code(sender_thread_ptr_option.unwrap(), Some(NO_RECEIVER));
            return;
        }

        let endpoint_queue_state = self.proc_man.get_endpoint_queue_state(endpoint_ptr);
        if endpoint_queue_state == SEND{
            self.proc_man.set_thread_error_code(sender_thread_ptr_option.unwrap(), Some(NO_RECEIVER));
            return; // due to no wait
        }

        assert(endpoint_len > 0 && endpoint_queue_state == RECEIVE);

        let sender_endpoint_payload = self.proc_man.get_thread_endpoint_payload(sender_thread_ptr);

        let receiver_thread_ptr = self.proc_man.get_endpoint_queue_head(endpoint_ptr);
        let receiver_endpoint_payload = self.proc_man.get_thread_endpoint_payload(receiver_thread_ptr);
        assert(self.proc_man.get_thread(receiver_thread_ptr).state == BLOCKED);
        assert(sender_thread_ptr != receiver_thread_ptr);

        if sender_endpoint_payload.is_none() && receiver_endpoint_payload.is_none(){
            //just context switch and schedule sender
            assert(self.kernel_wf());
            if self.proc_man.scheduler.len() >= MAX_NUM_THREADS{
                self.proc_man.set_thread_error_code(sender_thread_ptr_option.unwrap(), Some(SCHEDULER_NO_SPACE));
                return;
            }

            assert(self.proc_man.scheduler.len() < MAX_NUM_THREADS);
            self.proc_man.set_thread_to_transit(sender_thread_ptr);

            let tmp = self.proc_man.pop_endpoint(sender_thread_ptr,sender_endpoint_index);
            assert(tmp == receiver_thread_ptr);

            self.proc_man.set_thread_error_code(sender_thread_ptr, Some(SUCCESS));
            self.proc_man.push_scheduler(sender_thread_ptr);
            assert(self.proc_man.get_thread(tmp).state == TRANSIT);
            self.proc_man.set_thread_to_running(receiver_thread_ptr);

            let cpu = Cpu{
                current_t: Some(receiver_thread_ptr),
                tlb: self.cpu_list.get(cpu_id).tlb,
                iotlb: self.cpu_list.get(cpu_id).iotlb
            };

            self.proc_man.set_thread_error_code(receiver_thread_ptr, Some(SUCCESS));
            self.cpu_list.set(cpu_id,cpu);
            assert(self.kernel_wf());

            return;
        }

        if sender_endpoint_payload.is_some() && receiver_endpoint_payload.is_some()
        {

            let sender_endpoint_payload_index = sender_endpoint_payload.unwrap();
            let receiver_endpoint_payload_index = receiver_endpoint_payload.unwrap();

            let endpoint_ptr = self.proc_man.get_thread_endpoint_descriptor(sender_thread_ptr, sender_endpoint_payload_index);
            if endpoint_ptr == 0{
                self.proc_man.set_thread_error_code(sender_thread_ptr, Some(SHARED_ENDPOINT_NOT_EXIST));
                return;
            }

            let endpoint_rf = self.proc_man.get_endpoint_rf_counter(endpoint_ptr);
            if endpoint_rf == usize::MAX{
                // endpoint cannot be shared anymore, counter overflow. (not gonna happen)
                self.proc_man.set_thread_error_code(sender_thread_ptr, Some(SHARED_ENDPOINT_REF_COUNT_OVERFLOW));
                return;
            }

            if self.proc_man.scheduler.len() >= MAX_NUM_THREADS{
                self.proc_man.set_thread_error_code(sender_thread_ptr, Some(SCHEDULER_NO_SPACE));
                return;
            }

            
            let receiver_capable_of_receiving = self.proc_man.check_thread_capable_for_new_endpoint(receiver_thread_ptr, receiver_endpoint_payload_index, endpoint_ptr);
            if receiver_capable_of_receiving == false{
                //receiver no longer able to receive, goes to scheduler

                self.proc_man.set_thread_error_code(receiver_thread_ptr, Some(SHARED_ENDPOINT_SLOT_TAKEN));
                let tmp = self.proc_man.pop_endpoint(sender_thread_ptr,sender_endpoint_index);
                assert(tmp == receiver_thread_ptr);
                self.proc_man.push_scheduler(receiver_thread_ptr);

                self.proc_man.set_thread_error_code(sender_thread_ptr, Some(SHARED_ENDPOINT_SLOT_TAKEN));
                assert(self.kernel_wf());
                return;
            }
            
            self.proc_man.pass_endpoint(sender_thread_ptr,sender_endpoint_payload_index,receiver_thread_ptr,receiver_endpoint_payload_index);
            assert(self.proc_man.scheduler.len() < MAX_NUM_THREADS);
            self.proc_man.set_thread_to_transit(sender_thread_ptr);

            let tmp = self.proc_man.pop_endpoint(sender_thread_ptr,sender_endpoint_index);
            assert(tmp == receiver_thread_ptr);

            self.proc_man.set_thread_error_code(sender_thread_ptr, Some(SUCCESS));
            self.proc_man.push_scheduler(sender_thread_ptr);

            assert(self.proc_man.get_thread(tmp).state == TRANSIT);
            self.proc_man.set_thread_to_running(receiver_thread_ptr);
            self.proc_man.set_thread_error_code(receiver_thread_ptr, Some(SUCCESS));

            let cpu = Cpu{
                current_t: Some(receiver_thread_ptr),
                tlb: self.cpu_list.get(cpu_id).tlb,
                iotlb: self.cpu_list.get(cpu_id).iotlb
            };
    
            self.cpu_list.set(cpu_id,cpu);
            assert(self.kernel_wf());

            return;
        }
    }
}

}