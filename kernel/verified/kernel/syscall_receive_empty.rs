use vstd::prelude::*;
verus! {

use crate::define::*;
use crate::kernel::Kernel;
use crate::process_manager::thread::IPCPayLoad;
use crate::trap::Registers;

impl Kernel {
    pub fn syscall_receive_empty_no_block(
        &mut self,
        receiver_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(receiver_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }

        let blocking_endpoint_ptr_op = self.proc_man.get_thread(
            receiver_thread_ptr,
        ).endpoint_descriptors.get(blocking_endpoint_index);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            // return error
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        // Make sure we can access sender from shared endpoint

        assert(self.sender_exist(receiver_thread_ptr, blocking_endpoint_index));

        // checking sender thread payload well formed
        let sender_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;

        // cannot schedule the sender
        if self.proc_man.get_container(sender_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        self.proc_man.schedule_blocked_thread(blocking_endpoint_ptr);
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }

    pub fn syscall_receive_empty_block(
        &mut self,
        receiver_thread_ptr: ThreadPtr,
        blocking_endpoint_index: EndpointIdx,
        pt_regs: &Registers,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(receiver_thread_ptr),
            0 <= blocking_endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(receiver_thread_ptr).state == ThreadState::RUNNING,
        ensures
    {
        proof {
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
        }

        let blocking_endpoint_ptr_op = self.proc_man.get_thread(
            receiver_thread_ptr,
        ).endpoint_descriptors.get(blocking_endpoint_index);

        if blocking_endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let blocking_endpoint_ptr = blocking_endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            < MAX_NUM_THREADS_PER_ENDPOINT {

            self.proc_man.block_running_thread_and_set_trap_frame(
                receiver_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Empty,
                pt_regs,
            );
            assert(self.wf());
            return SyscallReturnStruct::NoNextThreadNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_receive()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len()
            >= MAX_NUM_THREADS_PER_ENDPOINT {
            // return error
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_endpoint(blocking_endpoint_ptr).queue_state.is_send()
            && self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.len() == 0 {
            self.proc_man.block_running_thread_and_change_queue_state_and_set_trap_frame(
                receiver_thread_ptr,
                blocking_endpoint_index,
                IPCPayLoad::Empty,
                EndpointState::RECEIVE,
                pt_regs,
            );
            assert(self.wf());
            return SyscallReturnStruct::NoNextThreadNew(RetValueType::Error);
        }
        // Make sure we can access sender from shared endpoint

        assert(self.sender_exist(receiver_thread_ptr, blocking_endpoint_index));

        // checking sender thread payload well formed
        let sender_thread_ptr = self.proc_man.get_endpoint(blocking_endpoint_ptr).queue.get_head();
        let sender_container_ptr = self.proc_man.get_thread(sender_thread_ptr).owning_container;

        // cannot schedule the sender
        if self.proc_man.get_container(sender_container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        self.proc_man.schedule_blocked_thread(blocking_endpoint_ptr);
        return SyscallReturnStruct::NoSwitchNew(RetValueType::Else);
    }
}

} // verus!
