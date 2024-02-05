use vstd::prelude::*;

use crate::array_vec::*;
use crate::proc::*;
use crate::page_alloc::*;
use crate::mmu::*;
use crate::cpu::{Cpu,CPUID};
use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use crate::kernel::*;

verus! {

// pub proof fn va_derive(va:VAddr)
//     requires spec_va_valid(va)
// {
//     assert(va != 0);
// }

impl Kernel{
    pub fn kernel_map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:usize)
        requires
            old(self).wf(), 
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            0<=pcid<PCID_MAX,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).mmu_man.get_mmu_page_closure().contains(dst) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] == 0,
            page_ptr_valid(dst),
            old(self).page_alloc.get_mapped_pages().contains(dst),
            old(self).page_alloc.get_page_mappings(dst).contains((pcid,va)) == false,
            old(self).page_alloc.page_array@[page_ptr2page_index(dst) as int].rf_count < usize::MAX,
            old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
    {
        let result = self.mmu_man.map_pagetable_page(pcid,va,dst);
        assert(result == true);
        assert(old(self).page_alloc.get_available_pages().contains(dst));
        self.page_alloc.map_user_page(dst,(pcid,va),RWX);
        // assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

        proof{page_ptr_lemma();}
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
    }  

    pub fn kernel_unmap_pagetable_page(&mut self, pcid:Pcid, va: usize) -> (ret:PAddr)
        requires
            old(self).wf(), 
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
    {
        let ret = self.mmu_man.unmap_pagetable_page(pcid,va);   
        if ret == 0 {
            assert(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va] == 0);
            assert(self.wf());
        }
        else{
            assert(page_ptr_valid(ret));
            assert(self.page_alloc.get_page_mappings(ret).contains((pcid,va)));
            self.page_alloc.unmap_user_page(ret,(pcid,va));
            self.cpu_list.flush_address(pcid,va);

            assert(
                self.proc_man.wf()
            );
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

        return ret;
    }
}

}