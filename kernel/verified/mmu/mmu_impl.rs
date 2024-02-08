use vstd::prelude::*;
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::page_alloc::*;
use crate::define::*;
use crate::iommutable::*;

use crate::mmu::*;
verus! {

impl MMUManager{
    pub fn map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:PageEntry) -> (ret: bool)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).get_mmu_page_closure().contains(dst.addr) == false,
            old(self).get_pagetable_mapping_by_pcid(pcid)[va].is_None(),
            page_ptr_valid(dst.addr),
            va_perm_bits_valid(dst.perm),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.iommu_ids =~= old(self).iommu_ids,
            self.iommu_perms =~= old(self).iommu_perms,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            self.get_pagetable_page_closure_by_pcid(pcid) =~= old(self).get_pagetable_page_closure_by_pcid(pcid),
            old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) == ret,
            old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) ==> 
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid).insert(va,Some(dst)),
            !old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) ==> 
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid),
            forall|_ioid:IOid| #![auto] self.get_iommu_ids().contains(_ioid) ==> self.get_iommutable_by_ioid(_ioid) =~= old(self).get_iommutable_by_ioid(_ioid),
            forall|_ioid:IOid| #![auto] self.get_iommu_ids().contains(_ioid) ==> self.get_iommutable_mapping_by_ioid(_ioid) =~= old(self).get_iommutable_mapping_by_ioid(_ioid),
    {
        let ret = self.page_tables.map_pagetable_page_by_pcid(pcid,va,dst);     
        assert(self.wf());
        return ret;
    }

    pub fn unmap_pagetable_page(&mut self, pcid:Pcid, va: usize) -> (ret: Option<PageEntry>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.iommu_ids =~= old(self).iommu_ids,
            self.iommu_perms =~= old(self).iommu_perms,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            self.get_pagetable_page_closure_by_pcid(pcid) =~= old(self).get_pagetable_page_closure_by_pcid(pcid),
            old(self).get_pagetable_mapping_by_pcid(pcid)[va] == ret,
            ret.is_None() ==> self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid),
            ret.is_Some() ==> self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid).insert(va,None),
    {
        let ret = self.page_tables.unmap_pagetable_page_by_pcid(pcid,va);
        assert(self.wf());
        return ret;
    }

    // pub fn create_pagetable_va_entry(&mut self, pcid:Pcid, va:VAddr, page_alloc:&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
    //     requires
    //         0<=pcid<PCID_MAX,
    //         old(self).wf(),
    //         old(self).get_free_pcids_as_set().contains(pcid) == false,
    //         spec_va_valid(va),
    //         old(page_alloc).wf(),
    //         old(page_alloc).free_pages.len() >= 4,
    //         spec_va_valid(va),
    //         old(self).get_pagetable_page_closure().disjoint(old(page_alloc).get_free_pages_as_set()),
    //         old(self).get_pagetable_mapped_pages().disjoint(old(page_alloc).get_free_pages_as_set()),

}

}
