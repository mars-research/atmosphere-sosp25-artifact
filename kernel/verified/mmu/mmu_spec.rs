use vstd::prelude::*;
use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;
use crate::page_alloc::*;
use crate::define::*;
use crate::iommutable::*;

verus! {
pub struct MMUManager{

    pub free_pcids: ArrayVec<Pcid,PCID_MAX>,
    pub page_tables: MarsArray<PageTable,PCID_MAX>,
    pub page_table_pages: Ghost<Set<PagePtr>>,


    pub iommu_ids: Ghost<Set<IOid>>, //actual owners are procs
    pub iommu_perms: Tracked<Map<IOid,PointsTo<IOMMUTable>>>,
    pub iommu_table_pages: Ghost<Set<PagePtr>>,
}

impl MMUManager{
    #[verifier(inline)]
    pub open spec fn get_free_pcids_as_set(&self) -> Set<Pcid>
    {
        self.free_pcids@.to_set()
    }
    #[verifier(inline)]
    pub open spec fn get_mmu_page_closure(&self) -> Set<PagePtr>
    {
        self.iommu_table_pages@ + self.page_table_pages@
    }
    #[verifier(inline)]
    pub open spec fn get_pagetable_by_pcid(&self, pcid: Pcid) -> PageTable
        recommends 0<=pcid<PCID_MAX,
    {
        self.page_tables[pcid as int]
    }
    #[verifier(inline)]
    pub open spec fn get_pagetable_mapping_by_pcid(&self, pcid: Pcid) -> Map<VAddr,Option<PageEntry>>
        recommends 0<=pcid<PCID_MAX,
    {   
        self.page_tables[pcid as int].get_pagetable_mapping()
    }
    #[verifier(inline)]
    pub open spec fn get_pagetable_page_closure_by_pcid(&self, pcid: Pcid) -> Set<PagePtr>
        recommends 0<=pcid<PCID_MAX,
    {   
        self.page_tables[pcid as int].get_pagetable_page_closure()
    }
    #[verifier(inline)]
    pub open spec fn get_pagetable_mapped_pages_by_pcid(&self, pcid: Pcid) -> Set<PagePtr>
        recommends 0<=pcid<PCID_MAX,
    {   
        self.page_tables[pcid as int].get_pagetable_mapped_pages()
    }

    #[verifier(inline)]
    pub open spec fn get_iommu_ids(&self) -> Set<IOid>
    {
        self.iommu_ids@
    }

    #[verifier(inline)]
    pub open spec fn get_iommutable_by_ioid(&self, ioid: IOid) -> IOMMUTable
        recommends self.get_iommu_ids().contains(ioid),
    {
        self.iommu_perms@[ioid].view().value.get_Some_0()
    }

    #[verifier(inline)]
    pub open spec fn get_iommutable_mapping_by_ioid(&self, ioid: IOid) -> Map<usize,Option<PageEntry>>
        recommends self.get_iommu_ids().contains(ioid),
    {   
        self.get_iommutable_by_ioid(ioid).get_iommutable_mapping()
    }
    #[verifier(inline)]
    pub open spec fn get_iommutable_page_closure_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends self.get_iommu_ids().contains(ioid),
    {   
        self.get_iommutable_by_ioid(ioid).get_iommutable_page_closure()
    }

    #[verifier(inline)]
    pub open spec fn get_iommutable_mapped_pages_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends self.get_iommu_ids().contains(ioid),
    {   
        self.get_iommutable_by_ioid(ioid).get_iommutable_mapped_pages()
    }

    #[verifier(inline)]
    pub open spec fn pagetables_wf(&self) -> bool{
        &&&
        self.free_pcids.wf()
        &&&
        self.free_pcids@.no_duplicates()
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_pcids.len()  ==> self.free_pcids@[i]<PCID_MAX
        )
        &&&
        self.page_tables.wf()
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_pcids.len() ==> 
                self.page_tables[self.free_pcids@[i] as int].get_pagetable_mapping() =~= Map::empty()
        )
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_pcids.len() ==> 
                self.page_tables[self.free_pcids@[i] as int].get_pagetable_page_closure() =~= Set::empty()
        )
        &&&
        (
            forall|i:int,va:usize| #![auto] 0<=i<PCID_MAX && spec_va_valid(va) && self.page_tables[i].get_pagetable_mapping()[va].is_Some() ==> 
                page_ptr_valid(self.page_tables[i].get_pagetable_mapping()[va].get_Some_0().addr)
        )           
        &&&
        (
            forall|i:int,va:usize| #![auto] 0<=i<PCID_MAX && spec_va_valid(va) && self.page_tables[i].get_pagetable_mapping()[va].is_Some() ==> 
                va_perm_bits_valid(self.page_tables[i].get_pagetable_mapping()[va].get_Some_0().perm)
        )     
        &&&
        (
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> 
                self.page_tables[pcid as int].wf_mapping()
        )
        &&&
        (
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX && self.get_free_pcids_as_set().contains(pcid) == false ==> 
                self.page_tables[pcid as int].wf()
        )
        &&&
        (
            forall|i:int,page_ptr:PagePtr| #![auto] 0<=i<PCID_MAX && self.page_tables[i].get_pagetable_page_closure().contains(page_ptr) ==> self.page_table_pages@.contains(page_ptr)
        )
        &&&
        (
            forall|i:int,j:int| #![auto] 0<=i<PCID_MAX && 0<=j<PCID_MAX && i != j ==> self.page_tables[i].get_pagetable_page_closure().disjoint(self.page_tables[j].get_pagetable_page_closure())
        )
    }

    #[verifier(inline)]
    pub open spec fn iommutables_wf(&self) -> bool{
        &&&
        (self.iommu_ids@ =~= self.iommu_perms@.dom())
        &&&
        (
            forall|ioid: IOid| #![auto] self.iommu_ids@.contains(ioid) ==> self.iommu_perms@[ioid]@.pptr == ioid
        )
        &&&
        (
            forall|ioid: IOid| #![auto] self.iommu_ids@.contains(ioid) ==> self.iommu_perms@[ioid]@.value.is_Some()
        )
        &&&
        (
            forall|ioid: IOid| #![auto] self.iommu_ids@.contains(ioid) ==> self.iommu_perms@[ioid]@.value.get_Some_0().wf()
        )
        &&&
        (
            forall|ioid: IOid| #![auto] self.iommu_ids@.contains(ioid) ==> self.iommu_perms@[ioid]@.value.get_Some_0().wf_mapping()
        )
        &&&
        (
            forall|ioid: IOid,va:usize| #![auto] self.iommu_ids@.contains(ioid) && spec_va_valid(va) && self.iommu_perms@[ioid]@.value.get_Some_0().get_iommutable_mapping()[va].is_Some()==> 
                page_ptr_valid(self.iommu_perms@[ioid]@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().addr)
        )
        &&&
        (
            forall|ioid: IOid,va:usize| #![auto] self.iommu_ids@.contains(ioid) && spec_va_valid(va) && self.iommu_perms@[ioid]@.value.get_Some_0().get_iommutable_mapping()[va].is_Some()==> 
                va_perm_bits_valid(self.iommu_perms@[ioid]@.value.get_Some_0().get_iommutable_mapping()[va].get_Some_0().perm)
        )
        &&&
        (
            forall|ioid: IOid,page_ptr:PagePtr| #![auto] self.iommu_ids@.contains(ioid) && self.iommu_perms@[ioid]@.value.get_Some_0().get_iommutable_page_closure().contains(page_ptr) ==> self.iommu_table_pages@.contains(page_ptr)
        )        
        &&&
        (
            forall|ioid_i: IOid,ioid_j: IOid,| #![auto] self.iommu_ids@.contains(ioid_i) && self.iommu_ids@.contains(ioid_j) && ioid_i != ioid_j ==> 
                self.iommu_perms@[ioid_i]@.value.get_Some_0().get_iommutable_page_closure().disjoint(self.iommu_perms@[ioid_j]@.value.get_Some_0().get_iommutable_page_closure())
        )
    }

    #[verifier(inline)]
    pub open spec fn pagetable_iommutable_disjoint(&self) -> bool
    {
        self.page_table_pages@.disjoint(self.iommu_table_pages@)
    }

    #[verifier(inline)]
    pub open spec fn wf(&self) -> bool
    {
        &&&
        (
            self.pagetables_wf()
        )
        &&&
        (
            self.iommutables_wf()
        )
        &&&
        (
            self.pagetable_iommutable_disjoint()
        )
    }
}
}