use super::*;

verus! {


pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;

pub const VA_MASK:u64 = 0x0000_ffff_ffff_f000;

#[verifier(external_body)]
pub fn LookUpTable_set(pptr:&PPtr<LookUpTable>, Tracked(perm): Tracked<&mut PointsTo<LookUpTable>>, i: usize, value:usize) 
    requires 
        pptr.id() == old(perm)@.pptr,
        old(perm)@.value.is_Some(),
        old(perm)@.value.get_Some_0().table.wf(),
        0<=i<512,
    ensures
        pptr.id() == perm@.pptr,
        perm@.value.is_Some(),
        perm@.value.get_Some_0().table.wf(),
        forall|j:usize| 0<=j<512 && j != i ==> 
            perm@.value.get_Some_0().table@[j as int] == old(perm)@.value.get_Some_0().table@[j as int],
        perm@.value.get_Some_0().table@[i as int] == value,
{
    unsafe {
        let uptr = pptr.to_usize() as *mut MaybeUninit<LookUpTable>;
        (*uptr).assume_init_mut().table.set(i,value);
    }
}

pub struct LookUpTable{
    pub table : MarsArray<usize,512>,
}
pub struct PageTable{
    pub cr3: usize,
    
    pub l4_table: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l3_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l2_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l1_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,

    pub mapping: Ghost<Map<usize,usize>>,
}

pub open spec fn spec_va_valid(va: usize) -> bool
{
    va & VA_MASK as usize == 0
}

pub open spec fn spec_v2l1index(va: usize) -> L1Index
{
    (va >> 12 & 0x1ff) as usize
}

pub open spec fn spec_v2l2index(va: usize) -> L2Index
{
    (va >> 21 & 0x1ff) as usize
}

pub open spec fn spec_v2l3index(va: usize) -> L3Index
{
    (va >> 30 & 0x1ff) as usize
}

pub open spec fn spec_v2l4index(va: usize) -> L4Index
{
    (va >> 39 & 0x1ff) as usize
}

pub open spec fn spec_va2index(va: usize) -> (L4Index,L3Index,L2Index,L1Index)
{
    (spec_v2l4index(va),spec_v2l3index(va),spec_v2l2index(va),spec_v2l1index(va))
}

pub open spec fn spec_index2va(i:(L4Index,L3Index,L2Index,L1Index)) -> usize
    recommends 
    i.0 <= 0x1ff,
    i.1 <= 0x1ff, 
    i.2 <= 0x1ff,
    i.3 <= 0x1ff,           
{
    (i.0 as usize)<<39 & (i.1 as usize)<<30 & (i.2 as usize)<<21 & (i.3 as usize)<<12 
} 


pub fn va_valid(va: usize) -> (ret: bool)
    ensures ret == spec_va_valid(va),
{
    va & VA_MASK as usize == 0
}

#[verifier(external_body)]
pub fn v2l1index(va: usize) -> (ret: L1Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l1index(va),
             ret <= 0x1ff,
{
    (va as u64 >> 12u64 & 0x1ffu64) as usize
}

#[verifier(external_body)]
pub fn v2l2index(va: usize) -> (ret: L2Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l2index(va),
            ret <= 0x1ff,
{
    (va as u64 >> 21u64 & 0x1ffu64) as usize
}

#[verifier(external_body)]
pub fn v2l3index(va: usize) -> (ret: L3Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l3index(va),
            ret <= 0x1ff,
{
    (va as u64 >> 30u64 & 0x1ffu64) as usize
}

#[verifier(external_body)]
pub fn v2l4index(va: usize) -> (ret: L4Index)
    requires spec_va_valid(va),
    ensures  ret == spec_v2l4index(va),
                ret <= 0x1ff,
{
    (va as u64 >> 39u64 & 0x1ffu64) as usize
}


pub fn va2index(va: usize) -> (ret : (L4Index,L3Index,L2Index,L1Index))
    requires
        spec_va_valid(va),
    ensures
        ret.0 == spec_v2l4index(va) && ret.0 <= 0x1ff,
        ret.1 == spec_v2l3index(va) && ret.1 <= 0x1ff,
        ret.2 == spec_v2l2index(va) && ret.2 <= 0x1ff,
        ret.3 == spec_v2l1index(va) && ret.3 <= 0x1ff,
{
    (v2l4index(va),v2l3index(va),v2l2index(va),v2l1index(va))
}


#[verifier(external_body)]
pub proof fn lemma_1()
    ensures
        (forall|l4i: usize, l3i: usize, l2i: usize, l1i: usize|  #![auto] (
            l4i <= 0x1ff && l3i <= 0x1ff && l2i <= 0x1ff && l1i <= 0x1ff 
            ) ==>
                spec_va_valid(spec_index2va((l4i,l3i,l2i,l1i)))
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).0 == l4i
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).1 == l3i
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).2 == l2i
                &&
                spec_va2index(spec_index2va((l4i,l3i,l2i,l1i))).3 == l1i
        ),
        (forall|va_1:usize| #![auto] spec_va_valid(va_1) ==> (
            spec_va2index(va_1).0 <= 0x1ff
            &&
            spec_va2index(va_1).1 <= 0x1ff
            &&
            spec_va2index(va_1).2 <= 0x1ff
            &&
            spec_va2index(va_1).3 <= 0x1ff
            &&
            spec_index2va(spec_va2index(va_1)) == va_1
        )),
        (forall|va_1:usize, va_2:usize| #![auto] spec_va_valid(va_1) && spec_va_valid(va_2) && va_1 == va_2 ==> (
            spec_va2index(va_1).0 == spec_va2index(va_2).0 
            &&
            spec_va2index(va_1).1 == spec_va2index(va_2).1  
            &&
            spec_va2index(va_1).2 == spec_va2index(va_2).2 
            &&
            spec_va2index(va_1).3 == spec_va2index(va_2).3
        )),
        (forall|va_1:usize, va_2:usize| #![auto] spec_va_valid(va_1) && spec_va_valid(va_2) && va_1 != va_2 ==> (
            spec_va2index(va_1).0 != spec_va2index(va_2).0 
            ||
            spec_va2index(va_1).1 != spec_va2index(va_2).1  
            ||
            spec_va2index(va_1).2 != spec_va2index(va_2).2 
            ||
            spec_va2index(va_1).3 != spec_va2index(va_2).3
        )),
        (forall|l4i: usize, l3i: usize, l2i: usize, l1i: usize,l4j: usize, l3j: usize, l2j: usize, l1j: usize|  #![auto] (
            l4i <= 0x1ff && l3i <= 0x1ff && l2i <= 0x1ff && l1i <= 0x1ff && l4j <= 0x1ff && l3j <= 0x1ff && l2j <= 0x1ff && l1j <= 0x1ff &&
            l4i == l4j && l3i == l3j && l2i == l2j && l1i == l1j  
        ) ==>
            spec_index2va((l4i,l3i,l2i,l1i)) == spec_index2va((l4j,l3j,l2j,l1j))
        ),
        (forall|l4i: usize, l3i: usize, l2i: usize, l1i: usize,l4j: usize, l3j: usize, l2j: usize, l1j: usize|  #![auto] (
            l4i <= 0x1ff && l3i <= 0x1ff && l2i <= 0x1ff && l1i <= 0x1ff && l4j <= 0x1ff && l3j <= 0x1ff && l2j <= 0x1ff && l1j <= 0x1ff &&
            l4i != l4j || l3i != l3j || l2i != l2j || l1i != l1j  
        ) ==>
            spec_index2va((l4i,l3i,l2i,l1i)) != spec_index2va((l4j,l3j,l2j,l1j))
        )
        
{

}


impl PageTable {

    
    pub open spec fn all_pages(&self) -> Set<usize>{
        (self.l3_tables@.dom() + self.l2_tables@.dom() + self.l1_tables@.dom()).insert(self.cr3)
    }

    pub open spec fn all_mapped_pages(&self) -> Set<usize>{
        Set::<usize>::new(|pa: usize| self.pa_mapped(pa))
    }

    pub open spec fn pa_mapped(&self, pa:usize) -> bool
    {
        pa != 0
        &&
        exists|va:usize|#![auto] spec_va_valid(va) && self.mapping@[va] == pa 
    }

    pub open spec fn wf_l4(&self) -> bool{
        self.cr3 != 0
        &&
        self.l4_table@.dom() =~=  Set::<usize>::empty().insert(self.cr3)
        &&
        self.cr3 == self.l4_table@[self.cr3]@.pptr
        &&
        self.l4_table@[self.cr3]@.value.is_Some()
        &&
        self.l4_table@[self.cr3]@.value.get_Some_0().table.wf()
        //L4 table only maps to L3
        &&
        (forall|i: L4Index, j: L4Index| #![auto] i != j && 0 <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 && 0 <= j < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[j as int] != 0 ==> 
            self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != self.l4_table@[self.cr3]@.value.get_Some_0().table@[j as int])
        &&
        (forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 ==> self.l2_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int]) == false)
        &&
        (forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 ==> self.l1_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int]) == false)
        &&
        (forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0  ==> self.cr3 != self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int])
    }

    pub open spec fn wf_l3(&self) -> bool{
        //all l4 mappings exist in l3
        (
            forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int] != 0 ==> 
                self.l3_tables@.dom().contains(self.l4_table@[self.cr3]@.value.get_Some_0().table@[i as int])
        )
        &&
        (
            self.l3_tables@.dom().contains(0) == false
        )       
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> self.l3_tables@[i]@.value.get_Some_0().table.wf()
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(i)
        )

        //L3 table only maps to L2
        //L3 tables are disjoint
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i)
                ==> 
                (
                    forall|l3i: L3Index, l3j: L3Index| #![auto] l3i != l3j && 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != 0 && self.l3_tables@[i]@.value.get_Some_0().table@[l3j as int] != 0 ==>
                        self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != self.l3_tables@[i]@.value.get_Some_0().table@[l3j as int]
                )
        )
        &&
        (
            forall|i: usize,j: usize| #![auto] i != j && self.l3_tables@.dom().contains(i) && self.l3_tables@.dom().contains(j)
                ==> 
                (
                    forall|l3i: L3Index, l3j: L3Index| #![auto] 0 <= l3i < 512 && 0 <= l3j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != 0 && self.l3_tables@[j]@.value.get_Some_0().table@[l3j as int] != 0 ==>
                        self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != self.l3_tables@[j]@.value.get_Some_0().table@[l3j as int]
                )
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[j as int] != 0 ==>
                    self.l3_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (   forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[j as int] != 0 ==>
                    self.l1_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.cr3 != self.l3_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }
    
    pub open spec fn wf_l2(&self) -> bool{
      //all l3 mappings exist in l2
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> (
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
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> self.l2_tables@[i]@.value.get_Some_0().table.wf()
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                (
                    exists|j:usize| #![auto] self.l3_tables@.dom().contains(j) && self.l3_tables@[j]@.value.get_Some_0().table@.contains(i)
                )
        )


                
        //L2 table only maps to L1
        //L2 tables are disjoint
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==>
            (
                forall|l2i: L2Index, l2j: L2Index| #![auto] l2i != l2j && 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != 0 && self.l2_tables@[i]@.value.get_Some_0().table@[l2j as int] != 0 ==>
                    self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != self.l2_tables@[i]@.value.get_Some_0().table@[l2j as int]
            )
        )
        &&
        (
            forall|i: usize,j: usize| #![auto] i != j && self.l2_tables@.dom().contains(i) && self.l2_tables@.dom().contains(j) ==>
            (
                forall|l2i: L2Index, l2j: L2Index| #![auto] 0 <= l2i < 512 && 0 <= l2j < 512 && self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != 0 && self.l2_tables@[j]@.value.get_Some_0().table@[l2j as int] != 0 ==>
                    self.l2_tables@[i]@.value.get_Some_0().table@[l2i as int] != self.l2_tables@[j]@.value.get_Some_0().table@[l2j as int]
            )
        )
        &&
        (forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto]  0 <= j < 512 ==>
                self.l2_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.l3_tables@.dom().contains(self.l2_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.cr3 != self.l2_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }

    pub open spec fn wf_l1(&self) -> bool{
        //all l2 mappings exist in l1
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                (forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                     self.l1_tables@.dom().contains(j)
                )
        )
        &&
        (
            forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.pptr == i
                
        )
        &&
        (
            forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> self.l1_tables@[i]@.value.get_Some_0().table.wf()
        )
    }

    pub open spec fn no_self_mapping(&self) -> bool
    {   
        //L1 table only maps to outside of this pagetable
        //L1 tables do not have to be disjoint
        (
            forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l1_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                    self.l3_tables@.dom().contains(j) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.l2_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
                forall|j: usize|  #![auto] 0 <= j < 512 ==>
                    self.l1_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false 
        )
        && 
        (forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
            forall|j: usize|  #![auto] 0 <= j < 512 ==>
                self.cr3 != self.l1_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }

    pub open spec fn resolve_mapping_l4(&self, l4i: usize) -> usize
        recommends
            0<= l4i < 512, 
    {
        self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int]
    }

    pub open spec fn resolve_mapping_l3(&self, l4i: usize, l3i: usize) -> usize
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
    {
        if self.resolve_mapping_l4(l4i) == 0 {
            0
        }else{
            self.l3_tables@[self.resolve_mapping_l4(l4i)]@.value.get_Some_0().table@[l3i as int]
        }
    }

    pub open spec fn resolve_mapping_l2(&self, l4i: usize, l3i: usize, l2i: usize) -> usize
    recommends
        0<= l4i < 512,
        0<= l3i < 512,
        0<= l2i < 512,
    {
        if self.resolve_mapping_l3(l4i,l3i) == 0 {
            0
        }else{
            self.l2_tables@[self.resolve_mapping_l3(l4i,l3i)]@.value.get_Some_0().table@[l2i as int]
        }
    }

    pub open spec fn resolve_mapping_l1(&self, l4i: usize, l3i: usize, l2i: usize, l1i: usize) -> usize
    recommends
        0<= l4i < 512,
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
    {
        assert(self.wf_l4_mapping());
        assert(self.wf_l3_mapping());
        assert(self.wf_l2_mapping());
    }

    
    pub open spec fn wf_l4_mapping(&self) -> bool{
        forall|l4i: L4Index, l4j: L4Index| #![auto] (0<= l4i < 512) && (0<= l4j < 512) && !(l4i == l4j) ==> 
        (self.resolve_mapping_l4(l4i) == 0 || self.resolve_mapping_l4(l4j) == 0 || self.resolve_mapping_l4(l4i) != self.resolve_mapping_l4(l4j))
    }

    pub open spec fn wf_l3_mapping(&self) -> bool{
        forall|l4i: L4Index, l3i: L3Index, l4j: L4Index,l3j: L3Index| #![auto] (0<= l4i < 512 && 0<= l3i < 512) 
            && (0<= l4j < 512 && 0<= l3j < 512) 
            && !(l4i == l4j && l3i == l3j) ==> 
                (self.resolve_mapping_l3(l4i,l3i) == 0 || self.resolve_mapping_l3(l4j,l3j) == 0 || self.resolve_mapping_l3(l4i,l3i) != self.resolve_mapping_l3(l4j,l3j))
    }


    pub open spec fn wf_l2_mapping(&self) -> bool{
        forall|l4i: usize,l3i: usize,l2i: usize,l4j: usize,l3j: usize,l2j: usize| #![auto] (0<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512) 
        && (0<= l4j < 512 && 0<= l3j < 512 && 0<= l2j < 512) 
        && !(l4i == l4j && l3i == l3j && l2i == l2j ) ==> 
        self.resolve_mapping_l2(l4i,l3i,l2i) == 0 || self.resolve_mapping_l2(l4j,l3j,l2j) == 0 || self.resolve_mapping_l2(l4i,l3i,l2i) != self.resolve_mapping_l2(l4j,l3j,l2j)
            

    }

    pub open spec fn wf_mapping(&self) -> bool{
        (
            forall|va: usize| #![auto] spec_va_valid(va) ==> self.mapping@.dom().contains(va) 
        )
        // &&
        // (forall|va: usize| #![auto] spec_va_valid(va) ==> self.mapping@[va] == self.resolve_mapping_l1(spec_v2l4index(va),spec_v2l3index(va),spec_v2l2index(va),spec_v2l1index(va)))
        &&
        (forall|l4i: usize,l3i: usize,l2i: usize, l1i: usize| #![auto] (0<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512 && 0<= l1i < 512) 
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
    }

    pub open spec fn l4_entry_exists(&self, l4i: usize) -> bool
        recommends self.wf(),
    {
        self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int] != 0
    }

    pub open spec fn l3_entry_exists(&self, l4i: usize, l3i :usize) -> bool
        recommends self.wf(),
                    self.l4_entry_exists(l4i)
    {
        self.l3_tables@[
            self.l4_table@[self.cr3]@.value.get_Some_0().table@[l4i as int]
        ]@.value.get_Some_0().table@[l3i as int] != 0
    }

    pub open spec fn l2_entry_exists(&self, l4i: usize, l3i: usize, l2i: usize) -> bool
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

    pub open spec fn va_exists(&self, va:usize) -> bool
        recommends spec_va_valid(va),    
    {
        let (l4i,l3i,l2i,_) = spec_va2index(va);

        self.l4_entry_exists(l4i)
        &&
        self.l3_entry_exists(l4i,l3i)
        &&
        self.l2_entry_exists(l4i,l3i,l2i)
    }

    pub fn add_l4_mapping(&mut self, va: usize, pptr: PPtr<LookUpTable>, Tracked(perm): Tracked<PointsTo<LookUpTable>>)
        requires
            old(self).wf(),
            spec_va_valid(va),
            old(self).all_mapped_pages().contains((#[verifier(truncate)] (pptr.id() as usize))) == false,
            old(self).all_pages().contains(#[verifier(truncate)] (pptr.id() as usize)) == false,
            old(self).l4_entry_exists(spec_v2l4index(va)) == false,
            pptr.id() != 0,
            perm@.pptr == pptr.id(),
            perm@.value.is_Some(),
            perm@.value.get_Some_0().table.wf(),
            //forall|i:usize| #![auto] 0<=i<512 ==> perm@.value.get_Some_0().table@[i as int] == 0,
        ensures
            self.wf(),
            self.l4_entry_exists(spec_v2l4index(va)),
            self.mapping@ =~= old(self).mapping@,
            self.all_pages() =~= old(self).all_pages().insert(#[verifier(truncate)] (pptr.id() as usize)),
    {
        let tracked mut perm = perm;
        let mut _i = 0;
        while _i < 512
            invariant
                0<= _i <= 512,
                old(self).wf(),
                spec_va_valid(va),
                old(self).pa_mapped((#[verifier(truncate)] (pptr.id() as usize))) == false,
                old(self).all_pages().contains(#[verifier(truncate)] (pptr.id() as usize)) == false,
                old(self).l4_entry_exists(spec_v2l4index(va)) == false,
                pptr.id() != 0,
                perm@.pptr == pptr.id(),
                perm@.value.is_Some(),
                perm@.value.get_Some_0().table.wf(),
                forall|j:usize| #![auto] 0<=j<_i ==> perm@.value.get_Some_0().table@[j as int] == 0,
            ensures
                old(self).wf(),
                spec_va_valid(va),
                old(self).pa_mapped((#[verifier(truncate)] (pptr.id() as usize))) == false,
                old(self).all_pages().contains(#[verifier(truncate)] (pptr.id() as usize)) == false,
                old(self).l4_entry_exists(spec_v2l4index(va)) == false,
                pptr.id() != 0,
                perm@.pptr == pptr.id(),
                perm@.value.is_Some(),
                perm@.value.get_Some_0().table.wf(),
                _i == 512,
                forall|j:usize| #![auto] 0<=j<512 ==> perm@.value.get_Some_0().table@[j as int] == 0,
        {
            LookUpTable_set(&pptr, Tracked(&mut perm),_i,0);
            _i = _i + 1;
        }

        
        proof{lemma_1();}
        let l4i = v2l4index(va);

        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        assert(self.cr3 == l4_perm@.pptr);
        let l4_pptr = PPtr::<LookUpTable>::from_usize(self.cr3);

        let ptr = pptr.to_usize();

        LookUpTable_set(&l4_pptr, Tracked(&mut l4_perm),l4i,pptr.to_usize());
        proof {
            self.l4_table.borrow_mut().tracked_insert(self.cr3, l4_perm);
            assert(self.l3_tables@.dom().contains(ptr) == false);
            self.l3_tables.borrow_mut().tracked_insert(ptr, perm);
        }
        assert(self.wf_l4());

        assert(self.wf_l3());
        
        assert(self.wf_l2());

        assert(self.wf_l1());

        proof{
            self.wf_to_wf_mapping();
        }

        // assert(self.l3_tables@.dom().contains(0) == false);

        // assert(
        //     forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
        //         forall|j: usize| #![auto] 0 <= j < 512 ==>
        //             self.l3_tables@.dom().contains((self.l1_tables@[i]@.value.get_Some_0().table@[j as int])) == false  
        // );
        
        // assert(
        //     forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
        //         forall|j: usize| #![auto] 0 <= j < 512 ==>
        //             self.l2_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        // );
        
        // assert(
        //     forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
        //         forall|j: usize|  #![auto] 0 <= j < 512 ==>
        //             self.l1_tables@.dom().contains(self.l1_tables@[i]@.value.get_Some_0().table@[j as int]) == false 
        // );
         
        // assert(forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
        //     forall|j: usize|  #![auto] 0 <= j < 512 ==>
        //         self.cr3 != self.l1_tables@[i]@.value.get_Some_0().table@[j as int]
        // );

        //assert(self.no_self_mapping());

        assert((forall|_l4i: usize,_l3i: usize,_l2i: usize, _l1i: usize| #![auto] (0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512)  && _l4i != l4i
            ==> old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i)));

        // assert((forall|_l4i: usize,_l3i: usize,_l2i: usize, _l1i: usize| #![auto] (0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512)  && l4i != l4i
        //     ==> self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i)));

        assert(self.wf_mapping());

        assert(self.wf());

        //assert(false);

    }


    pub fn add_mapping(&mut self, va:usize, dst:usize) -> (ret: bool)
        requires 
            old(self).wf(),
            spec_va_valid(va),
            //old(self).va_exists(va),
            old(self).all_pages().contains(dst) == false,
            old(self).mapping@[va] == 0,
        ensures
            self.wf(),
            old(self).va_exists(va) == ret ,
            old(self).va_exists(va) ==> 
                self.mapping@ =~= old(self).mapping@.insert(va,dst),
            !old(self).va_exists(va) ==> 
                self.mapping@ =~= old(self).mapping@,
    {
        let (l4i,l3i,l2i,l1i) = va2index(va);
        assert(self.cr3 == self.l4_table@[self.cr3]@.pptr);
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l3_ptr = *l4_tbl.table.get(l4i);
        if(l3_ptr == 0){
            assert(!old(self).va_exists(va));
            return false;
        }
        assert(self.l4_table@[self.cr3]@.value.get_Some_0().table@.contains(l3_ptr));
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_ptr = *l3_tbl.table.get(l3i);
        if(l2_ptr == 0){
            assert(!old(self).va_exists(va));
            return false;
        }

        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(self.l3_tables@[l3_ptr]@.value.get_Some_0().table@.contains(l2_ptr));
        assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_ptr = *l2_tbl.table.get(l2i);
        if(l1_ptr == 0){
            assert(!old(self).va_exists(va));
            return false;
        }
        assert(self.va_exists(va));
        assert(old(self).va_exists(va));

        assert(self.l2_tables@.dom().contains(l2_ptr));
        assert(self.l2_tables@[l2_ptr]@.value.get_Some_0().table@.contains(l1_ptr));
        assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<LookUpTable>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().table.wf());
        //assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

        LookUpTable_set(&l1_pptr,Tracked(&mut l1_perm),l1i,dst);
        assert(l1_perm@.value.get_Some_0().table@[l1i as int] == dst);
        assert(l1_perm@.pptr == l1_ptr);
        proof {
            self.mapping@ = self.mapping@.insert(spec_index2va((l4i,l3i,l2i,l1i)),dst);}
        assert(self.mapping@[spec_index2va((l4i,l3i,l2i,l1i))]==dst);

        proof {
            self.l1_tables.borrow_mut().tracked_insert(l1_ptr, l1_perm);
    
        }

        assert(self.wf_l4());
        
        assert(self.wf_l3());
        
        assert(self.wf_l2());

        assert(self.wf_l1());

        proof{
            self.wf_to_wf_mapping();
            lemma_1();    
        }

        assert(self.no_self_mapping());


        assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) == dst);

        let g_va:Ghost<usize> = Ghost(spec_index2va((l4i,l3i,l2i,l1i)));
        assert(forall|va:usize| #![auto] spec_va_valid(va) && va != g_va ==> 
            self.mapping@[va] == old(self).mapping@[va]);

        assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i))==> 
                self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))] == old(self).mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))]);

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) == l1_ptr && _l1i != l1i==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == old(self).resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i))
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && !((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );

        assert(forall|_l4i: usize,_l3i: usize,_l2i: usize,_l1i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && 0<= _l1i < 512  && ((_l4i,_l3i,_l2i,_l1i) =~= (l4i,l3i,l2i,l1i)) ==> (
            self.resolve_mapping_l1(_l4i,_l3i,_l2i,_l1i) == self.mapping@[spec_index2va((_l4i,_l3i,_l2i,_l1i))])
        );
        assert(self.wf_mapping());

        assert(self.wf());

        //  assert(false);

        return true;

    }
}


}