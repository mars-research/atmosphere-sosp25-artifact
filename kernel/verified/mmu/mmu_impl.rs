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
            spec_va_perm_bits_valid(dst.perm),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            // self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            forall|_pcid:Pcid| #![auto] 0<=_pcid<PCID_MAX && _pcid != pcid ==> self.get_pagetable_by_pcid(_pcid) =~= old(self).get_pagetable_by_pcid(_pcid),
            self.get_pagetable_page_closure_by_pcid(pcid) =~= old(self).get_pagetable_page_closure_by_pcid(pcid),
            old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) == ret,
            old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) ==> 
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid).insert(va,Some(dst)),
            !old(self).get_pagetable_by_pcid(pcid).is_va_entry_exist(va) ==> 
                self.get_pagetable_mapping_by_pcid(pcid) =~= old(self).get_pagetable_mapping_by_pcid(pcid),
            forall|_ioid:IOid| #![auto] 0<=_ioid<IOID_MAX ==> self.get_iommutable_by_ioid(_ioid) =~= old(self).get_iommutable_by_ioid(_ioid),
            forall|_ioid:IOid| #![auto] 0<=_ioid<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(_ioid) =~= old(self).get_iommutable_mapping_by_ioid(_ioid),
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
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
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

    pub fn adopt_dom0(&mut self, pagetable: PageTable)
        requires
            old(self).wf(),
            old(self).free_pcids.wf(),
            old(self).free_pcids.unique(),
            old(self).free_pcids.len() == PCID_MAX,
            old(self).free_pcids@ =~= Seq::new(PCID_MAX as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> old(self).get_free_pcids_as_set().contains(pcid),
            old(self).page_tables.wf(),
            old(self).page_table_pages@ =~= Set::empty(),
            old(self).free_ioids.wf(),
            old(self).free_ioids.unique(),
            old(self).free_ioids.len() == IOID_MAX,
            old(self).free_ioids@ =~= Seq::new(IOID_MAX as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> old(self).get_free_ioids_as_set().contains(ioid),
            old(self).iommu_tables.wf(),
            old(self).iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  old(self).get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  old(self).page_tables[i].l1_tables@ =~= Map::empty(),

            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> old(self).iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  old(self).get_iommutable_mapping_by_ioid(i)[va].is_None(),

            pagetable.wf(),
            forall|va:usize| #![auto] spec_va_valid(va) && pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                page_ptr_valid(pagetable.get_pagetable_mapping()[va].get_Some_0().addr),
            forall|va:usize| #![auto] spec_va_valid(va) && pagetable.get_pagetable_mapping()[va].is_Some() ==> 
                spec_va_perm_bits_valid(pagetable.get_pagetable_mapping()[va].get_Some_0().perm),
        ensures
            self.wf(),
            self.free_ioids.wf(),
            self.free_ioids.unique(),
            self.free_ioids.len() == IOID_MAX,
            self.free_ioids@ =~= Seq::new(IOID_MAX as nat, |i:int| {(IOID_MAX - i - 1) as usize}),
            forall|ioid:IOid| #![auto] 0<=ioid<IOID_MAX ==> self.get_free_ioids_as_set().contains(ioid),
            self.iommu_tables.wf(),
            self.iommu_table_pages@ =~= Set::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 1<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.cr3 == 0,
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<IOID_MAX ==> self.iommu_tables[i].dummy.l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<IOID_MAX && spec_va_valid(va) ==>  self.get_iommutable_mapping_by_ioid(i)[va].is_None(),
            self.get_pagetable_by_pcid(0) =~= pagetable,
            self.get_pagetable_mapping_by_pcid(0) =~= pagetable.get_pagetable_mapping(),
            self.get_mmu_page_closure() =~= pagetable.get_pagetable_page_closure(),
            forall|i:usize, va: VAddr|#![auto] 1<=i<PCID_MAX && spec_va_valid(va) ==>  self.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            self.get_free_pcids_as_set().contains(0) == false,
        {
            let pcid = self.free_pcids.pop_unique();
            assert(pcid == 0);
            proof{
                self.page_table_pages@ = pagetable.get_pagetable_page_closure();
            }
            self.page_tables.set(pcid, pagetable);
            assert(self.pagetables_wf());
            assert(self.iommutables_wf());
        }

    pub fn new_pagetable(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>,kernel_pml4_entry: Option<PageEntry>) -> (ret:Pcid)
        requires
            old(self).wf(),
            old(self).free_pcids.len() > 0,
            old(self).get_mmu_page_closure().contains(page_ptr) == false,
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self.get_free_pcids_as_set() =~= old(self).get_free_pcids_as_set().remove(ret),
            old(self).get_free_pcids_as_set().contains(ret),            
            self.free_ioids =~= old(self).free_ioids,
            self.iommu_tables =~= old(self).iommu_tables,
            self.iommu_table_pages =~= old(self).iommu_table_pages,
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure().insert(page_ptr),
            forall|i:Pcid|#![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> self.get_pagetable_mapping_by_pcid(pcid)[va] =~= old(self).get_pagetable_mapping_by_pcid(pcid)[va],
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> self.get_iommutable_mapping_by_ioid(ioid)[va] =~= old(self).get_iommutable_mapping_by_ioid(ioid)[va],
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.page_tables[ret as int].get_pagetable_mapping()[va].is_None(),
    {
        let ret = self.free_pcids.pop_unique();
        assert(0<=ret<PCID_MAX);
        assert(forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.page_tables[ret as int].get_pagetable_mapping()[va].is_None());
        assert(self.page_tables[ret as int].get_pagetable_page_closure() =~= Set::empty());

        self.page_tables.init_into_wf_by_pcid(ret,page_ptr,page_perm,kernel_pml4_entry);

        proof{
            self.page_table_pages@ = self.page_table_pages@.insert(page_ptr);
        }
        assert(self.wf());
        return ret;
    }

    pub fn new_iommutable(&mut self, page_ptr: PagePtr, page_perm: Tracked<PagePerm>) -> (ret:IOid)
        requires
            old(self).wf(),
            old(self).free_ioids.len() > 0,
            old(self).get_mmu_page_closure().contains(page_ptr) == false,
            page_ptr != 0,
            page_perm@@.pptr == page_ptr,
            page_perm@@.value.is_Some(),
        ensures
            self.wf(),
            self.get_free_ioids_as_set() =~= old(self).get_free_ioids_as_set().remove(ret),
            old(self).get_free_ioids_as_set().contains(ret),            
            self.free_pcids =~= old(self).free_pcids,
            self.page_tables =~= old(self).page_tables,
            self.page_table_pages =~= old(self).page_table_pages,
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure().insert(page_ptr),
            // forall|i:Pcid|#![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|pcid:Pcid, va:usize| #![auto] 0<=pcid<PCID_MAX && spec_va_valid(va) ==> self.get_pagetable_mapping_by_pcid(pcid)[va] =~= old(self).get_pagetable_mapping_by_pcid(pcid)[va],
            forall|ioid:IOid, va:usize| #![auto] 0<=ioid<IOID_MAX && spec_va_valid(va) ==> self.get_iommutable_mapping_by_ioid(ioid)[va] =~= old(self).get_iommutable_mapping_by_ioid(ioid)[va],
            forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.iommu_tables[ret as int].get_iommutable_mapping()[va].is_None(),
    {
        let ret = self.free_ioids.pop_unique();
        assert(0<=ret<IOID_MAX);
        assert(forall|va:VAddr| #![auto] spec_va_valid(va) ==> self.iommu_tables[ret as int].get_iommutable_mapping()[va].is_None());
        assert(self.iommu_tables[ret as int].get_iommutable_page_closure() =~= Set::empty());

        self.iommu_tables.init_into_wf_by_ioid(ret,page_ptr,page_perm);

        proof{
            self.iommu_table_pages@ = self.iommu_table_pages@.insert(page_ptr);
        }
        assert(self.wf());
        return ret;
    }

    pub fn create_pagetable_va_entry(&mut self, pcid:Pcid, va:VAddr, page_alloc:&mut PageAllocator) -> (ret:Ghost<Set<PagePtr>>)
        requires
            0<=pcid<PCID_MAX,
            old(self).wf(),
            old(self).get_free_pcids_as_set().contains(pcid) == false,
            spec_va_valid(va),
            old(page_alloc).wf(),
            old(page_alloc).free_pages.len() >= 3,
            spec_va_valid(va),
            old(page_alloc).get_free_pages_as_set().disjoint(old(self).get_mmu_page_closure()),
            forall|pcid:Pcid|#![auto] 0<=pcid<PCID_MAX ==> old(self).get_pagetable_page_closure_by_pcid(pcid).disjoint(old(page_alloc).get_free_pages_as_set()),
            forall|pcid:Pcid|#![auto] 0<=pcid<PCID_MAX ==> old(self).get_pagetable_mapped_pages_by_pcid(pcid).disjoint(old(page_alloc).get_free_pages_as_set()),
        ensures
            self.wf(),
            self.free_pcids =~= old(self).free_pcids,
            self.free_ioids =~= old(self).free_ioids,
            page_alloc.wf(),
            page_alloc.get_mapped_pages() =~= old(page_alloc).get_mapped_pages(),
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_page_table_pages() =~= old(page_alloc).get_page_table_pages() + ret@,
            page_alloc.get_free_pages_as_set() =~= old(page_alloc).get_free_pages_as_set() - ret@,
            page_alloc.get_allocated_pages() =~= old(page_alloc).get_allocated_pages(),
            ret@.subset_of(old(page_alloc).get_free_pages_as_set()),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_mappings(page_ptr) =~= old(page_alloc).get_page_mappings(page_ptr),
            forall|page_ptr:PagePtr| #![auto] page_ptr_valid(page_ptr) ==> page_alloc.get_page_io_mappings(page_ptr) =~= old(page_alloc).get_page_io_mappings(page_ptr),
            forall|i:Pcid| #![auto] 0<=i<PCID_MAX ==> self.get_pagetable_mapping_by_pcid(i) =~= old(self).get_pagetable_mapping_by_pcid(i),
            forall|i:IOid| #![auto] 0<=i<IOID_MAX ==> self.get_iommutable_mapping_by_ioid(i) =~= old(self).get_iommutable_mapping_by_ioid(i),
            self.get_mmu_page_closure() =~= old(self).get_mmu_page_closure() + ret@,
            // self.resolve_mapping_l2(l4i,l3i,l2i).is_Some(),
            self.get_pagetable_by_pcid(pcid).is_va_entry_exist(va),
            page_alloc.free_pages.len() >= old(page_alloc).free_pages.len() - 3,
    {
        let ret = self.page_tables.create_va_entry_by_pcid(pcid,va,page_alloc);
        proof{
            self.page_table_pages@ = self.page_table_pages@ + ret@;
        }

        assert(
            forall|i:int,| #![auto] 0<=i<PCID_MAX && i != pcid ==> self.page_tables[i].get_pagetable_page_closure().disjoint(ret@)
        );
        assert(
            forall|i:int,| #![auto] 0<=i<PCID_MAX && i != pcid ==> self.page_tables[i].get_pagetable_page_closure().disjoint(old(self).page_tables[pcid as int].get_pagetable_page_closure())
        );

        assert(
            self.pagetables_wf()
        );
        assert(
            self.iommutables_wf()
        );
        assert(
            self.pagetable_iommutable_disjoint()
        );
        ret
    }

    pub fn mmu_get_va_entry_by_pcid(&self, pcid: Pcid, va:VAddr) -> (ret:Option<PageEntry>)
        requires 
            self.wf(),
            0<=pcid<PCID_MAX,
            spec_va_valid(va),
            self.get_free_pcids_as_set().contains(pcid) == false,
        ensures
            ret =~= self.get_pagetable_mapping_by_pcid(pcid)[va],
    {
        assert(self.get_pagetable_by_pcid(pcid).wf());
        self.page_tables.get(pcid).get_va_entry(va)
    }

}

}
