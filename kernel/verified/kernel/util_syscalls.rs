use vstd::prelude::*;
verus! {
// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;
use crate::trap::*;
use crate::kernel::Kernel;

impl Kernel{

    pub fn get_current_cpu_info(&self, cpu_id:CpuId) -> (ret: (Option<ThreadPtr>,Option<ProcPtr>,ContainerPtr,Option<usize>,Option<Pcid>))
        requires
            self.wf(),
            0 <= cpu_id < NUM_CPUS,
    {
        proof{
            self.proc_man.thread_inv();
            self.proc_man.endpoint_inv();
            self.proc_man.container_inv();
            self.proc_man.cpu_inv();
        }

        let container_ptr = self.proc_man.cpu_list.get(cpu_id).owning_container;
        let thread_ptr_op = self.proc_man.cpu_list.get(cpu_id).current_thread;
        if thread_ptr_op.is_none(){
            return (None,None,container_ptr,None,None);
        }
        assert(self.proc_man.cpu_list@[cpu_id as int].current_thread.is_Some());
        assert(self.proc_man.thread_dom().contains(self.proc_man.cpu_list@[cpu_id as int].current_thread.unwrap()));
    
        let thread_ptr = thread_ptr_op.unwrap();
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let cr3 = self.mem_man.get_cr3_by_pcid(pcid);

        return (Some(thread_ptr),Some(proc_ptr), container_ptr, Some(cr3), Some(pcid));
    }
}

}