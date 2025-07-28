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
use crate::va_range::VaRange4K;


impl Kernel {
    pub fn syscall_resolve_va(&self, thread_ptr: ThreadPtr, va_range: VaRange4K) -> (ret:
        SyscallReturnStruct)
        requires
            self.total_wf(),
            self.thread_dom().contains(thread_ptr),
            va_range.wf(),
            va_range.len == 1,
    {
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;

        proof {
            self.proc_man.thread_inv();
            self.proc_man.process_inv();
        }

        let pa_op = self.mem_man.resolve_pagetable_mapping(pcid, va_range.index(0));

        if pa_op.is_none(){
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessPairUsize { value1:pa_op.unwrap().addr, value2:0 });
    }
}

} // verus!
