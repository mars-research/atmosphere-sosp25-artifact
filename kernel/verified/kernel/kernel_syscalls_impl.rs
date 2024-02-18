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

use crate::kernel::*;


impl Kernel {


    fn kernel_new_proc_checker(&self, cpu_id:CPUID, endpoint_index: EndpointIdx) -> (ret: ErrorCodeType)
        requires
            self.wf(),
        ensures
            ret == SUCCESS ==> (
                (0<=cpu_id<NUM_CPUS)
                &&
                (self.cpu_list[cpu_id as int].get_is_idle() == false)
                &&
                (0<=endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS)
                &&
                (self.proc_man.get_thread(self.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors[endpoint_index as int] != 0)
                &&
                (self.proc_man.get_endpoint(self.proc_man.get_thread(self.cpu_list[cpu_id as int].current_t.unwrap()).endpoint_descriptors[endpoint_index as int]).rf_counter < usize::MAX)
                &&
                (self.page_alloc.free_pages.len() >= 4)
                &&
                (self.proc_man.scheduler.len() < MAX_NUM_THREADS)
                &&
                (self.proc_man.proc_ptrs.len() < MAX_NUM_PROCS)
                &&
                (self.mmu_man.free_pcids.len() != 0)
            )
    {
        if cpu_id >= NUM_CPUS{
            return CPU_ID_INVALID;
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return NO_RUNNING_THREAD;
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return ENDPOINT_INDEX_INVALID;
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return SHARED_ENDPOINT_NOT_EXIST;
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            return SHARED_ENDPOINT_REF_COUNT_OVERFLOW;
        }

        if self.page_alloc.free_pages.len() < 4 {
            return SYSTEM_OUT_OF_MEM;
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            return SCHEDULER_NO_SPACE;
        }

        if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
            return PROCESS_LIST_NO_SPEC;
        }
        if self.mmu_man.free_pcids.len() == 0 {
            return NO_FREE_PCID;
        }

        return SUCCESS;
    }

    fn kernel_new_proc_endpoint_passer(&mut self, sender_ptr: ThreadPtr, sender_endpoint_index: EndpointIdx, receiver_ptr: ThreadPtr, receiver_endpoint_index: EndpointIdx)
        requires
            old(self).wf(),
            old(self).proc_man.get_thread_ptrs().contains(sender_ptr),
            old(self).proc_man.get_thread_ptrs().contains(receiver_ptr),
            0<=sender_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            0<=receiver_endpoint_index<MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int] != 0,
            old(self).proc_man.get_thread(receiver_ptr).endpoint_descriptors@[receiver_endpoint_index as int] == 0,
            forall|i:int| #![auto] 0 <= i < MAX_NUM_ENDPOINT_DESCRIPTORS ==> old(self).proc_man.get_thread(receiver_ptr).endpoint_descriptors@[i as int] != old(self).proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int],
            old(self).proc_man.get_endpoint(old(self).proc_man.get_thread(sender_ptr).endpoint_descriptors@[sender_endpoint_index as int]).rf_counter != usize::MAX,
        ensures
            self.wf(),    
        {
            self.proc_man.pass_endpoint(sender_ptr,sender_endpoint_index,receiver_ptr,receiver_endpoint_index);
            assert(
                self.proc_man.wf());
            assert(
                self.mmu_man.wf()
            );
            assert(
                self.page_alloc.wf()
            );
            assert(
                self.cpu_list.wf()
            );
            assert(
                self.kernel_cpu_list_wf()
            );
            assert(
                self.kernel_mem_layout_wf()
            );
            assert(
                self.kernel_mmu_page_alloc_pagetable_wf()
            );
            assert(
                self.kernel_mmu_page_alloc_iommutable_wf()
            );
            assert(self.kernel_proc_mmu_wf());
            assert(self.kernel_proc_no_thread_in_transit());
            assert(self.kernel_tlb_wf());
            assert(self.wf());
        }

    pub fn kernel_new_proc(&mut self, cpu_id:CPUID, pt_regs: PtRegs, endpoint_index: EndpointIdx, pt_regs_new_proc: PtRegs) -> (ret:(SyscallReturnStruct,Option<ProcPtr>,Option<ThreadPtr>))
        requires
            old(self).wf(),
        ensures
            //kernel is well-formed
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
                forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.mmu_man.get_pagetable_by_pcid(self.proc_man.get_pcid_by_thread_ptr(ret.2.unwrap())).get_pagetable_mapping()[va].is_None() 
            ),
    {   
        if cpu_id >= NUM_CPUS{
            return (SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs),None,None);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return (SyscallReturnStruct::new(NO_RUNNING_THREAD,0,0,pt_regs),None,None);
        }
        assert(self.cpu_list[cpu_id as int].get_is_idle() == false);
        let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
        assert(current_thread_ptr_op.is_Some());
        let current_thread_ptr = current_thread_ptr_op.unwrap();

        let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        
        if endpoint_index >= MAX_NUM_ENDPOINT_DESCRIPTORS{
            return (SyscallReturnStruct::new(ENDPOINT_INDEX_INVALID,pcid,cr3,pt_regs),None,None);
        }

        let target_endpoint_ptr = self.proc_man.get_thread_endpoint_ptr_by_endpoint_idx(current_thread_ptr, endpoint_index);
        if target_endpoint_ptr == 0 {
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_NOT_EXIST,pcid,cr3,pt_regs),None,None);
        }
        assert(self.proc_man.endpoint_perms@.dom().contains(target_endpoint_ptr));

        if self.proc_man.get_endpoint_rf_counter_by_endpoint_ptr(target_endpoint_ptr) == usize::MAX {
            return (SyscallReturnStruct::new(SHARED_ENDPOINT_REF_COUNT_OVERFLOW,pcid,cr3,pt_regs),None,None);
        }

        if self.page_alloc.free_pages.len() < 4 {
            return (SyscallReturnStruct::new(SYSTEM_OUT_OF_MEM,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.scheduler.len() == MAX_NUM_THREADS{
            return (SyscallReturnStruct::new(SCHEDULER_NO_SPACE,pcid,cr3,pt_regs),None,None);
        }

        if self.proc_man.proc_ptrs.len() == MAX_NUM_PROCS {
            return (SyscallReturnStruct::new(PROCESS_LIST_NO_SPEC,pcid,cr3,pt_regs),None,None);
        }
        if self.mmu_man.free_pcids.len() == 0 {
            return (SyscallReturnStruct::new(NO_FREE_PCID,pcid,cr3,pt_regs),None,None);
        }
 
        let (page_ptr1, page_perm1) = self.page_alloc.alloc_pagetable_mem(); 
        let new_pcid = self.mmu_man.new_pagetable(page_ptr1,page_perm1,Some(self.kernel_pml4_entry));
        let (page_ptr2, page_perm2) = self.page_alloc.alloc_kernel_mem(); 
        let (page_ptr3, page_perm3) = self.page_alloc.alloc_kernel_mem(); 
        let new_proc = self.proc_man.new_proc(page_ptr2, page_perm2, new_pcid, None);
        let new_thread = self.proc_man.new_thread(pt_regs_new_proc,page_ptr3, page_perm3,new_proc);

        assert(
            self.proc_man.wf());
        assert(
            self.mmu_man.wf()
        );
        assert(
            self.page_alloc.wf()
        );
        assert(
            self.cpu_list.wf()
        );
        assert(
            self.kernel_cpu_list_wf()
        );
        assert(
            self.kernel_mem_layout_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_pagetable_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_iommutable_wf()
        );
        assert(self.kernel_proc_mmu_wf());
        assert(self.kernel_proc_no_thread_in_transit());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
        
        // self.kernel_new_proc_endpoint_passer(current_thread_ptr, endpoint_index, new_thread, 0);
        self.proc_man.pass_endpoint(current_thread_ptr,endpoint_index,new_thread,0);
        assert(
            self.proc_man.wf());
        assert(
            self.mmu_man.wf()
        );
        assert(
            self.page_alloc.wf()
        );
        assert(
            self.cpu_list.wf()
        );
        assert(
            self.kernel_cpu_list_wf()
        );
        assert(
            self.kernel_mem_layout_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_pagetable_wf()
        );
        assert(
            self.kernel_mmu_page_alloc_iommutable_wf()
        );
        assert(self.kernel_proc_mmu_wf());
        assert(self.kernel_proc_no_thread_in_transit());
        assert(self.kernel_tlb_wf());
        assert(self.wf());

        return (SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs),Some(new_proc),Some(new_thread));

    }


}

pub fn hello_world() -> (ret:usize){
    return 233;
}
}