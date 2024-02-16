use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::page_alloc::*;
use crate::define::*;
use crate::iommutable::*;
use vstd::ptr::PointsTo;

use crate::mmu::*;


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

    pub fn adopt_dom0(&mut self, pagetable: PageTable, ioid: IOid, iommutable_perm: PointsTo<IOMMUTable>)
        requires
            old(self).wf(),
            old(self).free_pcids.wf(),
            old(self).free_pcids.unique(),
            old(self).free_pcids.len() == PCID_MAX,
            old(self).free_pcids@ =~= Seq::new(PCID_MAX as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> old(self).get_free_pcids_as_set().contains(pcid),
            old(self).page_tables.wf(),
            old(self).page_table_pages@ =~= Set::empty(),
            old(self).iommu_ids@ =~= Set::empty(),
            old(self).iommu_perms@ =~= Map::empty(),
            old(self).iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  old(self).get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l1_tables@ =~= Map::empty(),

            pagetable.wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                page_ptr_valid(pagetable.get_pagetable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                va_perm_bits_valid(pagetable.get_pagetable_mapping()[va].get_Some_0().perm),
            iommutable_perm@.pptr == ioid,
            iommutable_perm@.value.is_Some(),
            iommutable_perm@.value.get_Some_0().wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && iommutable_perm@.value.get_Some_0().get_iommutable_mapping()[va].is_Some() ==> 
                page_ptr_valid(iommutable_perm@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && iommutable_perm@.value.get_Some_0().get_iommutable_mapping()[va].is_Some() ==> 
                va_perm_bits_valid(iommutable_perm@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().perm),
            pagetable.get_pagetable_page_closure().disjoint(iommutable_perm@.value.get_Some_0().get_iommutable_page_closure()),
        ensures
            self.wf(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
            self.get_pagetable_by_pcid(0) =~= pagetable,
            self.get_iommutable_by_ioid(ioid) =~= iommutable_perm@.value.get_Some_0(),
            self.get_pagetable_mapping_by_pcid(0) =~= pagetable.get_pagetable_mapping(),
            self.get_iommutable_mapping_by_ioid(ioid) =~= iommutable_perm@.value.get_Some_0().get_iommutable_mapping(),
            self.get_mmu_page_closure() =~= pagetable.get_pagetable_page_closure() + iommutable_perm@.value.get_Some_0().get_iommutable_page_closure(),
            forall|i:usize, va: VAddr|#![auto] 1<=i<PCID_MAX && spec_va_valid(va) ==>  self.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            self.get_iommu_ids() =~= Set::empty().insert(ioid),
            self.get_free_pcids_as_set().contains(0) == false,
        {
            let pcid = self.free_pcids.pop_unique();
            assert(pcid == 0);
            proof{
                self.page_table_pages@ = pagetable.get_pagetable_page_closure();
            }
            self.page_tables.set(pcid, pagetable);
            assert(self.pagetables_wf());
            proof{
                self.iommu_table_pages@ = iommutable_perm@.value.get_Some_0().get_iommutable_page_closure();
                self.iommu_ids@ = self.iommu_ids@.insert(ioid);
                (self.iommu_perms.borrow_mut())
                    .tracked_insert(ioid, iommutable_perm);
            }
            assert(self.iommutables_wf());
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
