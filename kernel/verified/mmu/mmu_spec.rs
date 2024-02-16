use vstd::prelude::*;
verus!{
use vstd::ptr::PointsTo;

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


    pub iommu_ids: Ghost<Set<IOid>>, //actual owners are procs
    pub iommu_perms: Tracked<Map<IOid,PointsTo<IOMMUTable>>>,
    pub iommu_table_pages: Ghost<Set<PagePtr>>,
}

impl MMUManager{

    #[verifier(external_body)]
    pub fn new() -> (ret: MMUManager)
        ensures
            ret.free_pcids.wf(),
            ret.free_pcids@ =~= Seq::empty(),
            ret.page_tables.wf(),
            ret.page_table_pages@ =~= Set::empty(),
            ret.iommu_ids@ =~= Set::empty(),
            ret.iommu_perms@ =~= Map::empty(),
            ret.iommu_table_pages@ =~= Set::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==> ret.page_tables[i].l1_tables@ =~= Map::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  ret.get_pagetable_mapping_by_pcid(i)[va].is_None(),

    {
        let ret = Self{
            free_pcids: ArrayVec::<Pcid,PCID_MAX>::new(),
            page_tables: MarsArray::<PageTable,PCID_MAX>::new(),
            page_table_pages:  Ghost(Set::empty()),
            iommu_ids:  Ghost(Set::empty()),
            iommu_perms: Tracked(Map::tracked_empty()),
            iommu_table_pages: Ghost(Set::empty()),
        };
        ret
    }

    pub fn mmu_man_init(&mut self)
        requires 
            old(self).free_pcids.wf(),
            old(self).free_pcids.len() == 0,
            old(self).free_pcids@ =~= Seq::empty(),
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
        ensures
            self.wf(),
            self.free_pcids.wf(),
            self.free_pcids.unique(),
            self.free_pcids.len() == PCID_MAX,
            self.free_pcids@ =~= Seq::new(PCID_MAX as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
            forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.get_free_pcids_as_set().contains(pcid),
            self.page_tables.wf(),
            self.page_table_pages@ =~= Set::empty(),
            self.iommu_ids@ =~= Set::empty(),
            self.iommu_perms@ =~= Map::empty(),
            self.iommu_table_pages@ =~= Set::empty(),
            forall|i:usize, va: VAddr|#![auto] 0<=i<PCID_MAX && spec_va_valid(va) ==>  self.get_pagetable_mapping_by_pcid(i)[va].is_None(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].cr3 == 0,
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
            forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
    {
        let mut i = 0;

        while i!= PCID_MAX
            invariant
                0<=i<=PCID_MAX,
                self.free_pcids.wf(),
                self.free_pcids.unique(),
                self.free_pcids.len() == i,
                self.free_pcids@ =~= Seq::new(i as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
                forall|pcid:Pcid| #![auto] PCID_MAX>pcid>=(PCID_MAX - i) ==> self.get_free_pcids_as_set().contains(pcid),
                self.page_tables.wf(),
                self.page_table_pages@ =~= Set::empty(),
                self.iommu_ids@ =~= Set::empty(),
                self.iommu_perms@ =~= Map::empty(),
                self.iommu_table_pages@ =~= Set::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
            ensures
                i==PCID_MAX,
                self.free_pcids.wf(),
                self.free_pcids.unique(),
                self.free_pcids.len() == i,
                self.free_pcids@ =~= Seq::new(i as nat, |i:int| {(PCID_MAX - i - 1) as usize}),
                forall|pcid:Pcid| #![auto] 0<=pcid<PCID_MAX ==> self.get_free_pcids_as_set().contains(pcid),
                self.page_tables.wf(),
                self.page_table_pages@ =~= Set::empty(),
                self.iommu_ids@ =~= Set::empty(),
                self.iommu_perms@ =~= Map::empty(),
                self.iommu_table_pages@ =~= Set::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l4_table@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l3_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l2_tables@ =~= Map::empty(),
                forall|i:int|#![auto] 0<=i<PCID_MAX ==>  self.page_tables[i].l1_tables@ =~= Map::empty(),
        {
            self.free_pcids.push_unique(PCID_MAX - i - 1);
            i = i+1;
        }

        self.page_tables.init_all_pagetables();

        assert(self.pagetables_wf());
        assert(self.iommutables_wf());
        assert(self.pagetable_iommutable_disjoint());
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