use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;

use crate::pagetable::*;
use crate::mars_array::MarsArray;
use crate::array_vec::ArrayVec;
use crate::page_alloc::*;
use crate::define::*;
use crate::iommutable::*;


pub struct MMUManager{

    pub free_pcids: ArrayVec<Pcid,PCID_MAX>,
    pub page_tables: MarsArray<PageTable,PCID_MAX>,
    pub page_table_pages: Ghost<Set<PagePtr>>,


    pub free_ioids: ArrayVec<IOid,IOID_MAX>, //actual owners are procs
    pub iommu_tables:  MarsArray<IOMMUTable,IOID_MAX>,
    pub iommu_table_pages: Ghost<Set<PagePtr>>,
}

impl MMUManager{
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
            forall|i:int,va:VAddr| #![auto] 0<=i<self.free_pcids.len() && spec_va_valid(va) ==> 
                self.page_tables[self.free_pcids@[i] as int].get_pagetable_mapping()[va].is_None()
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
                spec_va_perm_bits_valid(self.page_tables[i].get_pagetable_mapping()[va].get_Some_0().perm)
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
        self.free_ioids.wf()
        &&&
        self.free_ioids@.no_duplicates()
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_ioids.len()  ==> self.free_ioids@[i]<IOID_MAX
        )
        &&&
        self.iommu_tables.wf()
        &&&
        (
            forall|i:int,va:VAddr| #![auto] 0<=i<self.free_ioids.len() && spec_va_valid(va) ==> 
                self.iommu_tables[self.free_ioids@[i] as int].get_iommutable_mapping()[va].is_None()
        )
        &&&
        (
            forall|i:int| #![auto] 0<=i<self.free_ioids.len() ==> 
                self.iommu_tables[self.free_ioids@[i] as int].get_iommutable_page_closure() =~= Set::empty()
        )
        &&&
        (
            forall|i:int,va:usize| #![auto] 0<=i<IOID_MAX && spec_va_valid(va) && self.iommu_tables[i].get_iommutable_mapping()[va].is_Some() ==> 
                page_ptr_valid(self.iommu_tables[i].get_iommutable_mapping()[va].get_Some_0().addr)
        )           
        &&&
        (
            forall|i:int,va:usize| #![auto] 0<=i<IOID_MAX && spec_va_valid(va) && self.iommu_tables[i].get_iommutable_mapping()[va].is_Some() ==> 
                spec_va_perm_bits_valid(self.iommu_tables[i].get_iommutable_mapping()[va].get_Some_0().perm)
        )     
        &&&
        (
            forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX ==> 
                self.iommu_tables[ioid as int].wf_mapping()
        )
        &&&
        (
            forall|ioid:Pcid| #![auto] 0<=ioid<IOID_MAX && self.get_free_ioids_as_set().contains(ioid) == false ==> 
                self.iommu_tables[ioid as int].wf()
        )
        &&&
        (
            forall|i:int,page_ptr:PagePtr| #![auto] 0<=i<IOID_MAX && self.iommu_tables[i].get_iommutable_page_closure().contains(page_ptr) ==> self.iommu_table_pages@.contains(page_ptr)
        )
        &&&
        (
            forall|i:int,j:int| #![auto] 0<=i<IOID_MAX && 0<=j<IOID_MAX && i != j ==> self.iommu_tables[i].get_iommutable_page_closure().disjoint(self.iommu_tables[j].get_iommutable_page_closure())
        )
    }

    #[verifier(inline)]
    pub open spec fn pagetable_iommutable_disjoint(&self) -> bool
    {
        self.page_table_pages@.disjoint(self.iommu_table_pages@)
    }

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
    pub open spec fn get_free_ioids_as_set(&self) -> Set<IOid>
    {
        self.free_ioids@.to_set()
    }
    #[verifier(inline)]
    pub open spec fn get_iommutable_by_ioid(&self, ioid: IOid) -> IOMMUTable
        recommends 0<=ioid<IOID_MAX,
    {
        self.iommu_tables[ioid as int]
    }
    #[verifier(inline)]
    pub open spec fn get_iommutable_mapping_by_ioid(&self, ioid: IOid) -> Map<VAddr,Option<PageEntry>>
        recommends 0<=ioid<IOID_MAX,
    {   
        self.iommu_tables[ioid as int].get_iommutable_mapping()
    }
    #[verifier(inline)]
    pub open spec fn get_iommutable_page_closure_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends 0<=ioid<IOID_MAX,
    {   
        self.iommu_tables[ioid as int].get_iommutable_page_closure()
    }
    #[verifier(inline)]
    pub open spec fn get_iommutable_mapped_pages_by_ioid(&self, ioid: IOid) -> Set<PagePtr>
        recommends 0<=ioid<IOID_MAX,
    {   
        self.iommu_tables[ioid as int].get_iommutable_mapped_pages()
    }


    pub fn get_cr3_by_pcid(&self, pcid:Pcid) -> (ret:usize)
    requires
        self.wf(),
        0<=pcid<PCID_MAX,
        self.get_free_pcids_as_set().contains(pcid) == false,
    {
        return self.page_tables.get(pcid).cr3;
    }

    pub fn get_cr3_by_ioid(&self, ioid:IOid) -> (ret:usize)
    requires
        self.wf(),
        0<=ioid<IOID_MAX,
        self.get_free_ioids_as_set().contains(ioid) == false,
    {
        return self.iommu_tables.get(ioid).dummy.cr3;
    }

    pub fn get_reserved_pcid_and_cr3(&self) -> (ret:(Pcid, usize))
        requires
            self.wf(),
        ensures
            self.get_pagetable_by_pcid(ret.0).cr3 == ret.1,
    {
        return (0,self.page_tables.get(0).cr3);
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
        &&&
        (
            self.get_pagetable_by_pcid(0).wf()
        )
    }
}
}