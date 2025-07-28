use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;

// use crate::va_range::VaRange4K;
// use crate::trap::Registers;
// use crate::pagetable::pagemap_util_t::*;
use crate::process_manager::thread::IPCPayLoad;
use crate::trap::Registers;

impl Kernel {
    pub fn syscall_send_empty_try_schedule(
        &mut self,
        cpu_id: CpuId,
        sender_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
        pt_regs: &mut Registers
    ) -> (ret: SyscallReturnStruct)
        requires
            0 <= cpu_id < NUM_CPUS,
            old(self).wf(),
            old(self).get_cpu(cpu_id).current_thread.is_some(),
            old(self).get_cpu(cpu_id).owning_container == old(self).get_thread(sender_thread_ptr).owning_container,
            old(self).get_cpu(cpu_id).current_thread.unwrap() == sender_thread_ptr,
            old(self).get_cpu(cpu_id).active,
            old(self).thread_dom().contains(sender_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(sender_thread_ptr).state == ThreadState::RUNNING,
        ensures
            self.wf(),
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;
        let blocking_endpoint_ptr_op = self.proc_man.get_thread(
            sender_thread_ptr,
        ).endpoint_descriptors.get(blocking_endpoint_index);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        assert(self.receiver_exist(sender_thread_ptr, blocking_endpoint_index));

        let receiver_thread_ptr = self.proc_man.get_endpoint(
            blocking_endpoint_ptr,
        ).queue.get_head();
        let receiver_container_ptr = self.proc_man.get_thread(receiver_thread_ptr).owning_container;

        if sender_container_ptr != receiver_container_ptr{
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        if self.proc_man.get_container(sender_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            // cannot schedule the receiver
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        let blocked_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
        self.proc_man.schedule_running_thread(cpu_id, pt_regs);
        self.proc_man.run_blocked_thread(cpu_id, blocking_endpoint_ptr, pt_regs);

        let blocked_proc_ptr = self.proc_man.get_thread(blocked_thread_ptr).owning_proc;
        let sender_proc_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_proc;
        let blocked_pcid = self.proc_man.get_proc(blocked_proc_ptr).pcid;
        let blocked_cr3 = self.mem_man.get_cr3_by_pcid(blocked_pcid);
        if sender_proc_ptr == blocked_proc_ptr{
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
        }else{
            return SyscallReturnStruct{ error_code: RetValueType::Else, pcid: Some(blocked_pcid), cr3:  Some(blocked_cr3), switch_decision:SwitchDecision::Switch };
        }
    }
}

} // verus!
