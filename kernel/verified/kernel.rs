use vstd::prelude::*;
// use vstd::ptr::PointsTo;

use crate::proc::*;
use crate::page_alloc::PageAllocator;
use crate::page::*;
use crate::pcid_alloc::{PcidAllocator,PCID_MAX};
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;

pub const NUM_CPUS:usize = 32;
pub const SCHEDULED:usize = 1;
pub const BLOCKED:usize = 2;
pub const RUNNING:usize = 3;

pub struct Kernel{
    pub proc_man : ProcessManager,
    pub page_alloc: PageAllocator,
    pub pcid_alloc: PcidAllocator,
    pub cpu_list: MarsArray<Cpu,NUM_CPUS>,
}
verus! {

impl Kernel {



    pub closed spec fn kernel_page_closure(&self) -> Set<PagePPtr>
    {
        self.proc_man.page_closure()
        +
        self.pcid_alloc.page_closure()
        // + 
        // ... add page_closure of other kernel component
    }

    pub closed spec fn system_data_page_closure(&self) -> Set<PagePPtr>
    {
        //system_data_page_closure() equals to data page closures of all the processes
        self.pcid_alloc.data_page_closure()
    }

    pub closed spec fn kernel_mem_wf(&self) -> bool
    {
        &&&
        self.kernel_page_closure() =~= self.page_alloc.allocated_pages()
        &&&
        self.system_data_page_closure() =~= self.page_alloc.mapped_pages()
        &&&
        self.page_alloc.mem_wf()
    }

    pub closed spec fn kernel_pcid_wf(&self) -> bool
    {
        &&&
        self.proc_man.pcid_closure() =~= self.pcid_alloc.allocated_pcids()
        &&&
        self.pcid_alloc.pcid_wf()
    }


    ///TODO: @Xiangdong change variable names when we have the real names ready.
    ///For each Process 'p' and its virtual space 'v', for each '(va,pa)' mapping exists in it's pagetable, 
    ///the ghost set that represents all existing mapping of this 'pa': page_alloc.mappings() -> Set<(vspace,va)> in PA contains such ('v','va') pair 
    ///This help us to reason about the correctness of the rf_counter for each mapped page.
    ///Steps of mapping a physical page (pa) to a new vspace and va,
    ///1. go to the page table of vspace and resolve va. Make sure resolve(vspace,va) is not equals to page_alloc. This ensures that the mapping set of pa does not contain '(vspace,va)' (external body check)
    ///2. map pa into '(vspace,va)', increment rf_counter of pa by 1, and insert '(vspace,va)' into the page_alloc.mappings().
    ///3. we know that page_alloc.mappings() did not contain '(vspace,va)', therefore the length of page_alloc.mappings() is increased by 1 correctly.
    ///It's worth noting that there's no way to actually find all the content of page_alloc.mappings(), without scanning the all the pagetables in the system,
    ///page_alloc.mappings() is just here to help other proofs. 
    ///If page_alloc.rf_count drops to zero, we can infer that no process maps pa anymore without even looking these processes' pagetable
    ///Therefore, page_alloc.mappings() cannot be generated on the fly. (or maybe we can)
    pub closed spec fn kernel_page_mapping_wf(&self) -> bool{
        forall |page_pptr:PagePPtr| #![auto] self.page_alloc.mapped_pages().contains(page_pptr) ==>
            (
                forall|pcid: Pcid| #![auto] 0<=pcid<PCID_MAX && self.pcid_alloc.all_pcids().contains(pcid) ==>
                    (
                        forall|va:VAddr,pa:PAddr| #![auto] self.pcid_alloc.get_va2pa_mapping_for_pcid(pcid).contains_pair(va,pa) && pa == page_pptr.id() ==>
                            (
                                self.page_alloc.page_mappings(page_pptr).contains((pcid,va))
                            )
                    )
            )
        //true
    }

    ///Spec for the tlbs for all the CPUs in the system
    ///If a Pcid is free, meaning that no process is using it, tlb contains no entry for this Pcid (this requires a flushing when freeing a Pcid)
    ///If a Pcid is allocated, meaning exactly one process is using it, the tlb entries agree to the Pcid's pagetable entries
    ///TODO: @Xiangdong, When we have a better representation of the mapping, change agrees() to less_than() to represent that as long as 
    ///the tlb entries have no permission or less permission than the current pagetable, we are good to go. 
    pub closed spec fn kernel_tlb_wf(&self) -> bool{
        &&&
        (
            forall|i:int,pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=pcid<PCID_MAX && self.pcid_alloc.free_pcids().contains(pcid) ==> (
                    self.cpu_list@[i].get_tlb_for_pcid(pcid) =~= Map::empty()
            )
        )
        &&&
        (
            forall|i:int,pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=pcid<PCID_MAX && self.pcid_alloc.allocated_pcids().contains(pcid) ==> (
                    self.cpu_list@[i].get_tlb_for_pcid(pcid).agrees(self.pcid_alloc.get_va2pa_mapping_for_pcid(pcid))
            )
        )
    }

    pub closed spec fn kernel_cpulist_wf(&self) -> bool{
        &&&
        (
            self.cpu_list.wf()
        )
        &&&
        (
            forall|i:CPUID,j:CPUID| #![auto] 0<=i<NUM_CPUS && 0<=j<NUM_CPUS && i != j ==> self.cpu_list@[i as int].current_t != self.cpu_list@[j as int].current_t
        )
        &&&
        (
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self.proc_man.get_thread_ptrs().contains(self.cpu_list@[i as int].current_t)
        )
        &&&
        (
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self.proc_man.get_thread(self.cpu_list@[i as int].current_t).state == 3 //RUNNING
        )
    }

    pub closed spec fn kernel_wf(&self) -> bool
    {
        // &&&
        // self.kernel_mem_wf()
        // &&&
        // self.kernel_tlb_wf()
        &&&
        self.kernel_cpulist_wf()
        &&&
        self.proc_man.wf()
    }


    pub fn sys_timer_int(&mut self, cpu_id: CPUID)
        requires
            old(self).kernel_wf(),
            0 <= cpu_id <NUM_CPUS,
            old(self).proc_man.scheduler.len() < MAX_NUM_THREADS,
    {
        assert(forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self.proc_man.get_thread(self.cpu_list@[i as int].current_t).state == 3);
        assert(0 <= cpu_id <NUM_CPUS);
        let thread_ptr = self.cpu_list.get(cpu_id).current_t;
        assert(self.proc_man.get_thread(thread_ptr).state == RUNNING);
        assert(self.proc_man.get_thread(thread_ptr).state != 1);
        self.proc_man.push_scheduler(thread_ptr);

        let new_thread_ptr = self.proc_man.pop_scheduler();
        assert(self.proc_man.scheduler@.contains(new_thread_ptr) == false);

        let cpu = Cpu{
            current_t: new_thread_ptr,
            tlb: self.cpu_list.get(cpu_id).tlb
        };

        self.cpu_list.set(cpu_id,cpu);
        self.proc_man.set_thread_state(new_thread_ptr,3);
        // assert(self.kernel_tlb_wf());
        assert(self.cpu_list.wf());
        assert(forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self.proc_man.get_thread_ptrs().contains(self.cpu_list@[i as int].current_t));
        assert(forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self.proc_man.get_thread(self.cpu_list@[i as int].current_t).state == 3);
        assert(self.kernel_cpulist_wf());
        assert(self.proc_man.wf());
        assert(self.kernel_wf());
    }
}

}