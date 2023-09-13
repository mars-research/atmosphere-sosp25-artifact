use vstd::prelude::*;
// use vstd::ptr::PointsTo;

use crate::proc::*;
use crate::page_alloc::PageAllocator;
use crate::page::*;

pub struct Kernel{
    pm : ProcessManager,
    pa: PageAllocator,
}
verus! {

impl Kernel {

    pub closed spec fn kernel_page_closure(&self) -> Set<PagePPtr>
    {
        self.pm.page_closure()
        // + 
        // ... add page_closure of other kernel component
    }

    pub closed spec fn system_data_page_closure(&self) -> Set<PagePPtr>
    {
        //system_data_page_closure() equals to data page closures of all the processes
        self.pm.data_page_closure()
    }

    pub closed spec fn kernel_mem_wf(&self) -> bool
    {
        &&&
        self.kernel_page_closure() =~= self.pa.allocated_pages()
        &&&
        self.system_data_page_closure() =~= self.pa.mapped_pages()
        &&&
        self.pa.mem_wf()
    }


    ///TODO: @Xiangdong change variable names when we have the real names ready.
    ///For each Process 'p' and its virtual space 'v', for each '(va,pa)' mapping exists in it's pagetable, 
    ///the ghost set that represents all existing mapping of this 'pa': pa.mappings() -> Set<(vspace,va)> in PA contains such ('v','va') pair 
    ///This help us to reason about the correctness of the rf_counter for each mapped page.
    ///Steps of mapping a physical page (pa) to a new vspace and va,
    ///1. go to the page table of vspace and resolve va. Make sure resolve(vspace,va) is not equals to pa. This ensures that the mapping set of pa does not contain '(vspace,va)' (external body check)
    ///2. map pa into '(vspace,va)', increment rf_counter of pa by 1, and insert '(vspace,va)' into the pa.mappings().
    ///3. we know that pa.mappings() did not contain '(vspace,va)', therefore the length of pa.mappings() is increased by 1 correctly.
    ///It's worth noting that there's no way to actually find all the content of pa.mappings(), without scanning the all the pagetables in the system,
    ///pa.mappings() is just here to help other proofs. 
    ///If pa.rf_count drops to zero, we can infer that no process maps pa anymore without even looking these processes' pagetable
    ///Therefore, pa.mappings() cannot be generated on the fly. (or maybe we can)
    pub closed spec fn kernel_page_mapping_wf(&self) -> bool{
        forall |page_pptr:PagePPtr| #![auto] self.pa.mapped_pages().contains(page_pptr) ==>
            (
                forall|proc: Process| #![auto] self.pm.procs().contains(proc) ==>
                    (
                        forall|va:VAddr,pa:PAddr| #![auto] proc.va2pa_mapping().contains_pair(va,pa) && pa == page_pptr.id() ==>
                            (
                                self.pa.page_mappings(page_pptr).contains((proc.get_cr3(),va))
                            )
                    )
            )
        //true
    }

    pub closed spec fn kernel_wf(&self) -> bool
    {
        &&&
        self.kernel_mem_wf()
    }
}

}