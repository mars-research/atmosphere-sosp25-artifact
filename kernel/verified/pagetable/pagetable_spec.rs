use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;
use crate::mars_array::*;
use crate::page_alloc::*;
use vstd::ptr::PointsTo;

use crate::pagetable::*;

verus!{

pub struct LookUpTable{
    pub table : MarsArray<PAddr,512>,
}
pub struct PageTable{
    pub cr3: PAddr,
    
    pub l4_table: Tracked<Map<PAddr,PointsTo<LookUpTable>>>,
    pub l3_tables: Tracked<Map<PAddr,PointsTo<LookUpTable>>>,
    pub l2_tables: Tracked<Map<PAddr,PointsTo<LookUpTable>>>,
    pub l1_tables: Tracked<Map<PAddr,PointsTo<LookUpTable>>>,

    pub mapping: Ghost<Map<VAddr,PAddr>>,
}
    

impl PageTable{
    #[verifier(inline)]
    pub open spec fn get_pagetable_page_closure(&self) -> Set<PagePtr>{
        (self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom()).insert(self.cr3)
    }

    #[verifier(inline)]
    pub open spec fn get_pagetable_mapping(&self) -> Map<PAddr,VAddr> {
        self.mapping@
    }
    
    // #[verifier(inline)]
    // pub open spec fn get_pagetable_get_mapped_pages(&self) -> Set<PagePtr>{
    //     Set::<PagePtr>::new(|pa: PagePtr| self.is_pa_mapped(pa))
    // }
    
    // #[verifier(inline)]
    // pub open spec fn is_pa_mapped(&self, pa:PAddr) -> bool
    // {
    //     (pa != 0)
    //     &&
    //     (exists|l1_ptr: PAddr, l1index: L1Index| #![auto] self.l1_tables@.dom().contains(l1_ptr) && 0 <= l1index < 512 && self.l1_tables@[l1_ptr]@.value.get_Some_0().table@[l1index as int] == pa)
    // }

    pub open spec fn wf_l4(&self) -> bool{
        self.cr3 != 0
        &&
        self.l4_table@.dom() =~=  Set::<PAddr>::empty().insert(self.cr3)
        &&
        self.cr3 == self.l4_table@[self.cr3]@.pptr
        &&
        self.l4_table@[self.cr3]@.value.is_Some()
        &&
        self.l4_table@[self.cr3]@.value.get_Some_0().table.wf()
        //L4 table only maps to L3
        &&
        (forall|i: L4Index, j: L4Index| #![auto] i != j && KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 && KERNEL_MEM_END_L4INDEX <= j < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[j as int] != 0 ==> 
            self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != self.l4_table@[self.cr3]@.value.get_Some_0().table@[j as int])
        &&
        (forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 ==> self.l2_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int]) == false)
        &&
        (forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 ==> self.l1_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int]) == false)
        &&
        (forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0  ==> self.cr3 != self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int])
        //hack @Xiangdong We are just to trying to make sure that the kernel PML4Entry is never changed
        &&
        (forall|i: L4Index| #![auto] 0 <= i < KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] == KERNEL_PML4_SIG)
    }

    pub open spec fn wf_l3(&self) -> bool{
        //all l4 mappings exist in l3
        (
            forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 ==> 
                self.l3_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int])
        )
        &&
        (
            self.l3_tables@.dom().contains(0) == false
        )       
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.value.get_Some_0().table.wf()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(i)
        )

        //L3 table only maps to L2
        //L3 tables are disjoint
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i)
                ==> 
                (
                    forall|l3i: L3Index, l3j: L3Index| #![auto] l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != 0 && self.l3_tables@[i]@.value.get_Some_0().table@[l3j as int] != 0 ==>
                        self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != self.l3_tables@[i]@.value.get_Some_0().table@[l3j as int]
                )
        )
        &&
        (
            forall|i: PAddr,j: PAddr| #![auto] i != j && self.l3_tables@.dom().contains(i) && self.l3_tables@.dom().contains(j)
                ==> 
                (
                    forall|l3i: L3Index, l3j: L3Index| #![auto] 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != 0 && self.l3_tables@[j]@.value.get_Some_0().table@[l3j as int] != 0 ==>
                        self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != self.l3_tables@[j]@.value.get_Some_0().table@[l3j as int]
                )
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: L3Index| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[j as int] != 0 ==>
                    self.l3_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (   forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: L3Index| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[j as int] != 0 ==>
                    self.l1_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: L3Index| #![auto] 0 <= j < 512 ==>
                    self.cr3 != self.l3_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }
    
    pub open spec fn wf_l2(&self) -> bool{
      //all l3 mappings exist in l2
        (
            forall|i: PAddr| #![auto] self.l3_tables@.dom().contains(i) ==> (
                forall|j: L3Index| #![auto] 0<= j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[j as int] != 0 ==>
                     self.l2_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int])
            )
        )
        &&
        (
            self.l2_tables@.dom().contains(0) == false
        )  
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.value.get_Some_0().table.wf()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> 
                (
                    exists|j:PAddr| #![auto] self.l3_tables@.dom().contains(j) && self.l3_tables@[j]@.value.get_Some_0().table@.contains(i)
                )
        )


                
        //L2 table only maps to L1
        //L2 tables are disjoint
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==>
            (
                forall|l2i: L2Index, l2j: L2Index| #![auto] l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != 0 && self.l2_tables@[i]@.value.get_Some_0().table@[l2j as int] != 0 ==>
                    self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != self.l2_tables@[i]@.value.get_Some_0().table@[l2j as int]
            )
        )
        &&
        (
            forall|i: PAddr,j: PAddr| #![auto] i != j && self.l2_tables@.dom().contains(i) && self.l2_tables@.dom().contains(j) ==>
            (
                forall|l2i: L2Index, l2j: L2Index| #![auto] 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != 0 && self.l2_tables@[j]@.value.get_Some_0().table@[l2j as int] != 0 ==>
                    self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != self.l2_tables@[j]@.value.get_Some_0().table@[l2j as int]
            )
        )
        &&
        (forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: L2Index| #![auto]  0 <= j < 512 ==>
                self.l2_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: L2Index| #![auto] 0 <= j < 512 ==>
                    self.l3_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: L2Index| #![auto] 0 <= j < 512 ==>
                    self.cr3 != self.l2_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }

    pub open spec fn wf_l1(&self) -> bool{
        //all l2 mappings exist in l1
        (
            forall|i: PAddr| #![auto] self.l2_tables@.dom().contains(i) ==> 
                (forall|j: PAddr| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                     self.l1_tables@.dom().contains(j)
                )
        )
        &&
        (
            self.l1_tables@.dom().contains(0) == false
        )   
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.value.get_Some_0().table.wf()
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> 
                (
                    exists|j:PAddr| #![auto] self.l2_tables@.dom().contains(j) && self.l2_tables@[j]@.value.get_Some_0().table@.contains(i)
                )
        )
    }

    pub open spec fn no_self_mapping(&self) -> bool
    {   
        //L1 table only maps to outside of this pagetable
        //L1 tables do not have to be disjoint
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> 
                forall|j: L1Index| #![auto] 0 <= j < 512 ==>
                    self.l3_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> 
                forall|j: L1Index| #![auto] 0 <= j < 512 ==>
                    self.l2_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> 
                forall|j: L1Index|  #![auto] 0 <= j < 512 ==>
                    self.l1_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false 
        )
        && 
        (forall|i: PAddr| #![auto] self.l1_tables@.dom().contains(i) ==> 
            forall|j: L1Index|  #![auto] 0 <= j < 512 ==>
                self.cr3 != self.l1_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }

    #[verifier(inline)]
    pub open spec fn resolve_mapping_l4(&self, l4i: L4Index) -> PAddr
        recommends
            KERNEL_MEM_END_L4INDEX <= l4i < 512, 
    {
        self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int]
    }

    pub open spec fn resolve_mapping_l3(&self, l4i: L4Index, l3i: L3Index) -> PAddr
    recommends
        KERNEL_MEM_END_L4INDEX<= l4i < 512,
        0<= l3i < 512,
    {
        if self.resolve_mapping_l4(l4i) == 0 {
            0
        }else{
            self.l3_tables@[self.resolve_mapping_l4(l4i)]@.value.get_Some_0().table@[l3i as int]
        }
    }

    pub open spec fn resolve_mapping_l2(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> PAddr
    recommends
        KERNEL_MEM_END_L4INDEX<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
    {
        if self.resolve_mapping_l3(l4i,l3i) == 0 {
            0
        }else{
            self.l2_tables@[self.resolve_mapping_l3(l4i,l3i)]@.value.get_Some_0().table@[l2i as int]
        }
    }

    pub open spec fn resolve_mapping_l1(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L1Index) -> PAddr
    recommends
        KERNEL_MEM_END_L4INDEX<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
        0<= l1i < 512,
    {
        if self.resolve_mapping_l2(l4i,l3i,l2i) == 0 {
            0
        }else{
            self.l1_tables@[self.resolve_mapping_l2(l4i,l3i,l2i)]@.value.get_Some_0().table@[l1i as int]
        }
    
    }

    pub proof fn wf_to_wf_mapping(&self)
        requires self.wf_l4(),
                 self.wf_l3(),
                 self.wf_l2(),
        ensures 
            self.wf_l4_mapping(),
            self.wf_l3_mapping(),
            self.wf_l2_mapping()
    {
        assert(self.wf_l4_mapping());
        assert(self.wf_l3_mapping());
        assert(self.wf_l2_mapping());
    }

    
    pub open spec fn wf_l4_mapping(&self) -> bool{
        forall|l4i: L4Index, l4j: L4Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512) && (KERNEL_MEM_END_L4INDEX<= l4j < 512) && !(l4i == l4j) ==> 
        (self.resolve_mapping_l4(l4i) == 0 || self.resolve_mapping_l4(l4j) == 0 || self.resolve_mapping_l4(l4i) != self.resolve_mapping_l4(l4j))
    }

    pub open spec fn wf_l3_mapping(&self) -> bool{
        forall|l4i: L4Index, l3i: L3Index, l4j: L4Index,l3j: L3Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512 && 0<= l3i < 512) 
            && (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512) 
            && !(l4i == l4j && l3i == l3j) ==> 
                (self.resolve_mapping_l3(l4i,l3i) == 0 || self.resolve_mapping_l3(l4j,l3j) == 0 || self.resolve_mapping_l3(l4i,l3i) != self.resolve_mapping_l3(l4j,l3j))
    }


    pub open spec fn wf_l2_mapping(&self) -> bool{
        forall|l4i: L4Index,l3i: L3Index,l2i: L2Index,l4j: L4Index,l3j: L3Index,l2j: L2Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512) 
        && (KERNEL_MEM_END_L4INDEX<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512) 
        && !(l4i == l4j && l3i == l3j && l2i == l2j ) ==> 
        self.resolve_mapping_l2(l4i,l3i,l2i) == 0 || self.resolve_mapping_l2(l4j,l3j,l2j) == 0 || self.resolve_mapping_l2(l4i,l3i,l2i) != self.resolve_mapping_l2(l4j,l3j,l2j)
            

    }

    pub open spec fn wf_mapping(&self) -> bool{
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) ==> self.mapping@.dom().contains(va) 
        )
        // &&
        // (forall|va: usize| #![auto] spec_va_valid(va) ==> self.mapping@[va] == self.resolve_mapping_l1(spec_v2l4index(va),spec_v2l3index(va),spec_v2l2index(va),spec_v2l1index(va)))
        &&
        (forall|l4i: L4Index,l3i: L3Index,l2i: L2Index, l1i: L1Index| #![auto] (KERNEL_MEM_END_L4INDEX<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512 && 0<= l1i < 512) 
        ==> self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))] == self.resolve_mapping_l1(l4i,l3i,l2i,l1i))
        
    }
    pub open spec fn wf(&self) -> bool
    {
        self.wf_l4()
        &&
        self.wf_l3()
        &&
        self.wf_l2()
        &&
        self.wf_l1()
        &&
        self.no_self_mapping()
        &&
        self.wf_mapping()
        &&
        self.l4_kernel_entries_reserved()
    }

    pub open spec fn l4_kernel_entries_reserved(&self) -> bool
        recommends self.wf_l4(),
    {
        forall|l4i: L4Index| #![auto] 0<=l4i<KERNEL_MEM_END_L4INDEX ==> self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int] == 0
    }


    pub open spec fn l4_entry_exists(&self, l4i: L4Index) -> bool
        recommends self.wf(),
    {
        self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int] != 0
    }

    pub open spec fn l3_entry_exists(&self, l4i: L4Index, l3i :L3Index) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.l3_tables@[
            self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int]
        ]@.value.get_Some_0().table@[l3i as int] != 0
    }

    pub open spec fn l2_entry_exists(&self, l4i: L4Index, l3i: L3Index, l2i: L2Index) -> bool
    recommends self.wf(),
                self.l4_entry_exists(l4i),
                self.l3_entry_exists(l4i,l3i)
    {
        self.l2_tables@[
            self.l3_tables@[
                self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int]
                    ]@.value.get_Some_0().table@[l3i as int]
                ]@.value.get_Some_0().table@[l2i as int] != 0
    }

    pub open spec fn is_va_entry_exist(&self, va:VAddr) -> bool
        recommends spec_va_valid(va),    
    {
        let (l4i,l3i,l2i,_) = spec_va2index(va);

        self.l4_entry_exists(l4i)
        &&
        self.l3_entry_exists(l4i,l3i)
        &&
        self.l2_entry_exists(l4i,l3i,l2i)
    }

    pub proof fn l4_empty_derive(&self)
        requires 
            self.wf(),
            forall|i: L4Index| #![auto] KERNEL_MEM_END_L4INDEX <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] == 0
    {
        assert(self.l3_tables@.dom() =~= Set::empty());
        assert(self.l2_tables@.dom() =~= Set::empty());
        assert(self.l1_tables@.dom() =~= Set::empty());
    }   


}

}