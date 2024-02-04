use vstd::prelude::*;
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::page_alloc::*;
use crate::define::*;
use crate::iommutable::*;

use crate::mmu::*;
verus! {

impl MMUManager{
    pub fn map_pagetable_page(&mut self, pcid:Pcid, va: usize, dst:usize) -> (ret: bool)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(self).get_mmu_page_closure().contains(dst) == false,
            old(self).get_pagetable_mapping_by_pcid(pcid)[va] == 0,
            page_ptr_valid(dst),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.iommu_ids =~= old(self).iommu_ids,
            self.iommu_perms =~= old(self).iommu_perms,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            // forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_mapping_by_pcid(_pcid) =~= old(self).get_pagetable_mapping_by_pcid(_pcid),
            self.get_pagetable_page_closure_by_pcid(pcid) =~= old(self).get_pagetable_page_closure_by_pcid(pcid),
            old(self).get_pagetable_by_pcid(pcid).va_exists(va) == ret,
            old(self).get_pagetable_by_pcid(pcid).va_exists(va) ==> 
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid).insert(va,dst),
            !old(self).get_pagetable_by_pcid(pcid).va_exists(va) ==> 
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid),
    {
        return self.page_tables.map_pagetable_page_by_pcid(pcid,va,dst);
    }
}

}
