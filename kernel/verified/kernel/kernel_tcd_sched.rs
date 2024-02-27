use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
// use crate::page_alloc::*;
// use crate::cpu::*;
// use crate::mars_array::MarsArray;
// use crate::pagetable::*;
use crate::cpu::*;
use crate::define::*;
use crate::trap::*;
// use crate::page_alloc::*;

use crate::kernel::*;


impl Kernel {
    pub fn kernel_timer_int(&mut self, cpu_id:CPUID, pt_regs: PtRegs) -> (ret:SyscallReturnStruct) 
        requires
            old(self).wf(),
    {
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() {
            return SyscallReturnStruct::new(CPU_NO_IDLE,0,0,pt_regs);
        }
        if self.proc_man.scheduler.len() == 0 {
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();
            let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);

            let pcid = self.proc_man.get_pcid_by_thread_ptr(current_thread_ptr);
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
            assert(self.wf());
            return SyscallReturnStruct::new(SCHEDULER_EMPTY,pcid,cr3,pt_regs);
        }
        else if self.proc_man.scheduler.len() == MAX_NUM_THREADS {
                let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
                assert(current_thread_ptr_op.is_Some());
                let current_thread_ptr = current_thread_ptr_op.unwrap();
                let current_proc_ptr = self.proc_man.get_parent_proc_ptr_by_thread_ptr(current_thread_ptr);
                let new_thread_ptr = self.proc_man.pop_scheduler();
                self.proc_man.push_scheduler(current_thread_ptr);
                let old_tlb = self.cpu_list.get(cpu_id).tlb;
                let old_iotlb = self.cpu_list.get(cpu_id).iotlb;
                self.cpu_list.set_current_thread(cpu_id,Some(new_thread_ptr));

                let pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
                assert(self.proc_man.get_proc_ptrs().contains(self.proc_man.get_thread(new_thread_ptr).parent));
                assert(self.proc_man.get_pcid_closure().contains(self.proc_man.get_proc(self.proc_man.get_thread(new_thread_ptr).parent).pcid));
                assert(self.proc_man.get_pcid_closure().contains(pcid));
                let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
                assert(self.wf());
                return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
        }
        else{ 
            let current_thread_ptr_op = self.cpu_list.get(cpu_id).get_current_thread();
            assert(current_thread_ptr_op.is_Some());
            let current_thread_ptr = current_thread_ptr_op.unwrap();
            self.proc_man.push_scheduler(current_thread_ptr);
            let new_thread_ptr = self.proc_man.pop_scheduler();
            let old_tlb = self.cpu_list.get(cpu_id).tlb;
            let old_iotlb = self.cpu_list.get(cpu_id).iotlb;
            self.cpu_list.set(cpu_id, Cpu{
                current_t: Some(new_thread_ptr),
                tlb: old_tlb,
                iotlb: old_iotlb,
            });
            let pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
            assert(self.proc_man.get_proc_ptrs().contains(self.proc_man.get_thread(new_thread_ptr).parent));
            assert(self.proc_man.get_pcid_closure().contains(self.proc_man.get_proc(self.proc_man.get_thread(new_thread_ptr).parent).pcid));
            assert(self.proc_man.get_pcid_closure().contains(pcid));
            let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
            assert(self.wf());
            return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
        }
    }
    pub fn kernel_idle_pop_sched(&mut self, cpu_id:CPUID, pt_regs: PtRegs) -> (ret:SyscallReturnStruct)
        requires
            old(self).wf(),
        ensures
            self.wf(),
    {
        if cpu_id >= NUM_CPUS{
            return SyscallReturnStruct::new(CPU_ID_INVALID,0,0,pt_regs);
        }

        if self.cpu_list.get(cpu_id).get_is_idle() == false {
            return SyscallReturnStruct::new(CPU_NO_IDLE,0,0,pt_regs);
        }
        if self.proc_man.scheduler.len() == 0 {
            assert(self.wf());
            return SyscallReturnStruct::new(SCHEDULER_EMPTY,0,0,pt_regs);
        }

        let new_thread_ptr = self.proc_man.pop_scheduler();
        assert(old(self).proc_man.get_thread(new_thread_ptr).state == SCHEDULED);
        // assert(forall|cpu_id:CPUID| #![auto] 0 <= cpu_id < NUM_CPUS && old(self).cpu_list[cpu_id as int].get_is_idle() == false
        // ==> (old(self).cpu_list[cpu_id as int].get_current_thread().unwrap() != new_thread_ptr));
        let old_tlb = self.cpu_list.get(cpu_id).tlb;
        let old_iotlb = self.cpu_list.get(cpu_id).iotlb;
        self.cpu_list.set_current_thread(cpu_id, Some(new_thread_ptr));
        let pcid = self.proc_man.get_pcid_by_thread_ptr(new_thread_ptr);
        assert(self.proc_man.get_proc_ptrs().contains(self.proc_man.get_thread(new_thread_ptr).parent));
        assert(self.proc_man.get_pcid_closure().contains(self.proc_man.get_proc(self.proc_man.get_thread(new_thread_ptr).parent).pcid));
        assert(self.proc_man.get_pcid_closure().contains(pcid));
        let cr3 = self.mmu_man.get_cr3_by_pcid(pcid);
        assert(self.wf());
        return SyscallReturnStruct::new(SUCCESS,pcid,cr3,pt_regs);
    
    }
}

pub fn hello_world() -> (ret:usize){
    return 233;
}
}