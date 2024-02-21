use vstd::prelude::*;
verus!{

// use crate::array_vec::*;
// use crate::proc::*;
use crate::page_alloc::*;
// use crate::mmu::*;
// use crate::cpu::{Cpu,CPUID};
// use crate::mars_array::MarsArray;
use crate::pagetable::*;
use crate::define::*;

use crate::kernel::*;



// pub proof fn va_derive(va:VAddr)
//     requires spec_va_valid(va)
// {
//     assert(va != 0);
// }

impl Kernel{
    pub fn kernel_map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:PageEntry)
        requires
            old(self).wf(), 
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            0<=pcid<PCID_MAX,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).mmu_man.get_mmu_page_closure().contains(dst.addr) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None(),
            page_ptr_valid(dst.addr),
            spec_va_perm_bits_valid(dst.perm),
            old(self).page_alloc.get_mapped_pages().contains(dst.addr),
            old(self).page_alloc.get_page_mappings(dst.addr).contains((pcid,va)) == false,
            old(self).page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count < usize::MAX,
            old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
        ensures
            self.wf()
    {
        let result = self.mmu_man.map_pagetable_page(pcid,va,dst);
        assert(result == true);
        assert(old(self).page_alloc.get_available_pages().contains(dst.addr));
        self.page_alloc.map_user_page(dst.addr,(pcid,va),RWX);
        // assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

        proof{page_ptr_lemma();}
        assert(self.kernel_mmu_page_alloc_iommutable_wf());
        assert(self.kernel_mmu_page_alloc_pagetable_wf());
        assert(self.kernel_tlb_wf());
        assert(self.wf());
    }

    // pub fn kernel_map_iommutable_page(&mut self, ioid:IOid, va: usize, dst:PageEntry)
    //     requires
    //         old(self).wf(), 
    //         0<=ioid<IOID_MAX,
    //         old(self).mmu_man.get_free_ioids_as_set().contains(ioid) == false,
    //         spec_va_valid(va),
    //         old(self).mmu_man.get_mmu_page_closure().contains(dst.addr) == false,
    //         old(self).mmu_man.get_pagetable_mapping_by_ioid(ioid)[va].is_None(),
    //         page_ptr_valid(dst.addr),
    //         spec_va_perm_bits_valid(dst.perm),
    //         old(self).page_alloc.get_mapped_pages().contains(dst.addr),
    //         old(self).page_alloc.get_page_io_mappings(dst.addr).contains((pcid,va)) == false,
    //         old(self).page_alloc.page_array@[page_ptr2page_index(dst.addr) as int].rf_count < usize::MAX,
    //         old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
    //     ensures
    //         self.wf()
    // {
    //     let result = self.mmu_man.map_pagetable_page(pcid,va,dst);
    //     assert(result == true);
    //     assert(old(self).page_alloc.get_available_pages().contains(dst.addr));
    //     self.page_alloc.map_user_page(dst.addr,(pcid,va),RWX);
    //     // assert(self.page_alloc.get_page_table_pages() =~= self.mmu_man.get_mmu_page_closure());

    //     proof{page_ptr_lemma();}
    //     assert(self.kernel_mmu_page_alloc_iommutable_wf());
    //     assert(self.kernel_mmu_page_alloc_pagetable_wf());
    //     assert(self.kernel_tlb_wf());
    //     assert(self.wf());
    // }

    pub fn kernel_pagetable_create_va_entry(&mut self, pcid:Pcid, va: usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
    {
        
    }

    pub fn kernel_unmap_pagetable_page(&mut self, pcid:Pcid, va: usize) -> (ret:Option<PageEntry>)
        requires
            old(self).wf(), 
            old(self).kernel_mmu_page_alloc_pagetable_wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
    {
        let ret = self.mmu_man.unmap_pagetable_page(pcid,va);   
        if ret.is_none() {
            assert(old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None());
            assert(self.wf());
        }
        else{
            assert(page_ptr_valid(ret.get_Some_0().addr));
            assert(spec_va_perm_bits_valid(ret.get_Some_0().perm));
            assert(self.page_alloc.get_page_mappings(ret.get_Some_0().addr).contains((pcid,va)));
            self.page_alloc.unmap_user_page(ret.unwrap().addr,(pcid,va));
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

    pub fn kernel_map_new_page_by_pcid(&mut self, pcid: Pcid, va: usize, perm_bits:usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 1,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_None(),
            spec_va_perm_bits_valid(perm_bits),
            old(self).mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
        ensures
            self.wf(),
            self.page_alloc.free_pages.len() == old(self).page_alloc.free_pages.len() - 1,
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX && i !=pcid ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|_va:VAddr| #![auto] spec_va_valid(_va) && va != _va ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va] =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[_va],
            self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[va].is_Some(),
    {
        let pa = self.page_alloc.alloc_page_and_map((pcid,va),RWX);
        assert(old(self).page_alloc.get_free_pages_as_set().contains(pa));
        assert(self.mmu_man.get_mmu_page_closure().contains(pa) == false);
        let result = self.mmu_man.map_pagetable_page(pcid, va, PageEntry{addr:pa,perm:perm_bits});
        assert(result == true);
        

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

    pub fn kernel_create_va_entry_by_pcid(&mut self, pcid: Pcid, va: usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 3,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
        ensures
            self.wf(),
            self.mmu_man.free_pcids =~= old(self).mmu_man.free_pcids,
            self.mmu_man.free_ioids =~= old(self).mmu_man.free_ioids,
            // page_alloc.wf(),
            // page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            // page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.page_alloc.get_page_mappings(page_ptr) =~= old(self).page_alloc.get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> self.page_alloc.get_page_io_mappings(page_ptr) =~= old(self).page_alloc.get_page_io_mappings(page_ptr),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.mmu_man.get_pagetable_mapping_by_pcid(i) =~= old(self).mmu_man.get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.mmu_man.get_iommutable_mapping_by_ioid(i) =~= old(self).mmu_man.get_iommutable_mapping_by_ioid(i),
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.mmu_man.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
            self.page_alloc.free_pages.len() >= old(self).page_alloc.free_pages.len() - 3,

    {
        proof{
            self.pagetable_mem_wf_derive();
            self.iommutable_mem_wf_derive();
        }
        self.mmu_man.create_pagetable_va_entry(pcid,va,&mut self.page_alloc);

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

    pub fn kernel_create_and_map_range_new_pages(&mut self, pcid: Pcid, va: usize, perm_bits:usize, range: usize)
        requires
            old(self).wf(),
            0<=pcid<PCID_MAX,
            // spec_va_valid(va),
            old(self).page_alloc.free_pages.len() >= 4*range,
            old(self).mmu_man.get_free_pcids_as_set().contains(pcid) == false,
            spec_va_perm_bits_valid(perm_bits),
            forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va,i)),
            forall|i:usize| #![auto] 0<=i<range ==> old(self).mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,i)].is_None(),
        ensures
            self.wf(),
            forall|j:usize| #![auto] 0<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
    {
        let mut i = 0;
        while i != range
            invariant
                0<=i<=range,
                self.wf(),
                0<=pcid<PCID_MAX,
                // spec_va_valid(va),
                self.page_alloc.free_pages.len() >= 4*(range - i),
                self.mmu_man.get_free_pcids_as_set().contains(pcid) == false,
                spec_va_perm_bits_valid(perm_bits),
                forall|i:usize| #![auto] 0<=i<range ==> spec_va_valid(spec_va_add_range(va,i)),
                forall|j:usize| #![auto] i<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None(),
                forall|j:usize| #![auto] 0<=j<i ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
            ensures
                i == range,
                self.wf(),
                forall|j:usize| #![auto] 0<=j<range ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_Some(),
        {
            // TODO: @Xiangdong prove or make this a lemma
            assume(forall|i:usize, j:usize| #![auto] i != j ==>  spec_va_add_range(va,i) != spec_va_add_range(va,j));
            self.kernel_create_va_entry_by_pcid(pcid,va_add_range(va,i));
            self.kernel_map_new_page_by_pcid(pcid,va_add_range(va,i),perm_bits);
            // assert(forall|j:usize| #![auto] i<=j<range &&  ==> self.mmu_man.get_pagetable_mapping_by_pcid(pcid)[spec_va_add_range(va,j)].is_None());
            i = i + 1;
        }
    }



}

}