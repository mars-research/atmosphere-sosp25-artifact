use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {

    pub fn syscall_new_proc(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx, pt_regs_new_proc: PtRegs) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
        requires
            old(self).wf(),
        ensures
            // kernel is well-formed
            self.wf(),
            //if the syscall is not success, nothing will change, goes back to user level
            ret.0.error_code != SUCCESS ==> (
                self == old(self) 
            ),
            //if the syscall is success, a new process and a new thread of the new process will be created
            ret.0.error_code == SUCCESS ==> (
                0<=cpu_id<NUM_CPUS
                &&
                0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS
                &&
                //each cpu still runs the same thread, no context switch
                self.cpu_list =~= old(self).cpu_list
                &&
                // ret.1 is the new process pointer
                ret.1.is_Some()
                &&
                // kernel correctly created a new process
                self.proc_man.get_proc_ptrs() =~= old(self).proc_man.get_proc_ptrs().push(ret.1.unwrap())
                &&
                // ret.2 is the new thread pointer
                ret.2.is_Some()
                &&
                // kernel correctly created a new thread for that process
                self.proc_man.get_thread_ptrs() =~= old(self).proc_man.get_thread_ptrs().insert(ret.2.unwrap())
                &&
                // helper for the next line
                self.cpu_list[cpu_id as int].current_t.is_Some()
                &&
                // the new thread stores the endpoint from the parent process at 1st slot
                self.proc_man.get_thread(ret.2.unwrap()).endpoint_descriptors@[0] =~= self.proc_man.get_thread(self.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors@[endpoint_index as int] 
                &&
                // the new thread is scheduled 
                self.proc_man.get_thread(ret.2.unwrap()).state == SCHEDULED
                &&
                // the new proccess's pagetable is empty. There are kernel and loader mapped in this new pagetable, but they are transparent to user level
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.mmu_man.get_pagetable_by_pcid(self.proc_man.get_proc(self.proc_man.get_thread(ret.2.unwrap()).parent).pcid).get_pagetable_mapping()[va].is_None()),
    { 
        let (default_pcid, default_cr3) = self.mmu_man.get_reserved_pcid_and_cr3();  
        if cpu_id >= NUM_CPUS{
            assert(self == old(self));
            return (SyscallReturnStruct::new(CPU_ID_INVALID,default_pcid,default_cr3,pt_regs),None,None);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            assert(self == old(self));
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,default_pcid,default_cr3,pt_regs),None,None);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            assert(self == old(self));
            return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs),None,None);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            assert(self == old(self));
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs),None,None);
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            assert(self == old(self));
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,pt_regs),None,None);
        }

        if self.page_alloc.free_pages.len() < 4 {
            assert(self == old(self));
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            assert(self == old(self));
            return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
            assert(self == old(self));
            return (SyscallReturnStruct::new(PROCESS_LIST_NO_SPEC,pcid,cr3,pt_regs),None,None);
        }
        if self.mmu_man.free_pcids.len() == 0 {
            assert(self == old(self));
            return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3,pt_regs),None,None);
        }
 
        let (page_ptr1, page_perm1) = self.page_alloc.alloc_pagetable_mem(); 
        let new_pcid = self.mmu_man.new_pagetable(page_ptr1,page_perm1,Some(self.kernel_pml4_entry));
        let (page_ptr2, page_perm2) = self.page_alloc.alloc_kernel_mem(); 
        let (page_ptr3, page_perm3) = self.page_alloc.alloc_kernel_mem(); 
        let new_proc = self.proc_man.new_proc(page_ptr2, page_perm2, new_pcid, None);
        let new_thread = self.proc_man.new_thread(pt_regs_new_proc,page_ptr3, page_perm3,new_proc);
        assert(self.wf());
        self.proc_man.pass_endpoint(current_thread_ptr,endpoint_index,new_thread,0);
        assert(self.wf());

        return (SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs),Some(new_proc),Some(new_thread));

    }
}
}