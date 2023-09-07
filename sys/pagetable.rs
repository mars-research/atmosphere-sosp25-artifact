use super::*;

verus! {


pub type L4Index = usize;
pub type L3Index = usize;
pub type L2Index = usize;
pub type L1Index = usize;
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
    
    pub l4_table: Tracked<PointsTo<LookUpTable>>,
    pub l3_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l2_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l1_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,

    // pub mapping: Ghost<Map<L4Index,Map<
    //         Map<L3Index,Map<
    //             Map<L2Index,Map<
    //                 Map<L1Index,Map<usize>>
    //             >>
    //         >>
    //     >>>,

    pub mapping_map: Ghost<Map<L4Index,Map<L3Index,usize>>>,

    pub mapping: Ghost<Map<(usize,usize,usize,usize),usize>>,
}

impl PageTable {

    pub open spec fn wf_l4(&self) -> bool{
        self.cr3 == self.l4_table@@.pptr
        &&
        self.l4_table@@.value.is_Some()
        &&
        self.l4_table@@.value.get_Some_0().table.wf()
        //L4 table only maps to L3
        &&
        (forall|i: L4Index, j: L4Index| #![auto] i != j && 0 <= i < 512 && self.l4_table@@.value.get_Some_0().table@[i as int] != 0 && 0 <= j < 512 && self.l4_table@@.value.get_Some_0().table@[j as int] != 0 ==> 
            self.l4_table@@.value.get_Some_0().table@[i as int] != self.l4_table@@.value.get_Some_0().table@[j as int])
        &&
        (forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@@.value.get_Some_0().table@[i as int] != 0 ==> self.l2_tables@.dom().contains(self.l4_table@@.value.get_Some_0().table@[i as int]) == false)
        &&
        (forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@@.value.get_Some_0().table@[i as int] != 0 ==> self.l1_tables@.dom().contains(self.l4_table@@.value.get_Some_0().table@[i as int]) == false)
        &&
        (forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@@.value.get_Some_0().table@[i as int] != 0  ==> self.cr3 != self.l4_table@@.value.get_Some_0().table@[i as int])
    }

    pub open spec fn wf_l3(&self) -> bool{
        //all l4 mappings exist in l3
        (
            forall|i: L4Index| #![auto] 0 <= i < 512 && self.l4_table@@.value.get_Some_0().table@[i as int] != 0 ==> 
                self.l3_tables@.dom().contains(self.l4_table@@.value.get_Some_0().table@[i as int])
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
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                (
                    forall|l3i: L3Index| #![auto] 0 <= l3i < 512 && self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int] != 0 ==>
                        self.l4_table@@.value.get_Some_0().table@.contains(self.l3_tables@[i]@.value.get_Some_0().table@[l3i as int])
                )
        )

        //L3 table only maps to L2
        //L3 tables are disjoint
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
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.l3_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (   forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.l1_tables@.dom().contains(self.l3_tables@[i]@.value.get_Some_0().table@[j as int]) == false  
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] 0 <= j < 512 ==>
                    self.cr3 !=self.l3_tables@[i]@.value.get_Some_0().table@[j as int]
        )
    }
    
    pub open spec fn wf_l2(&self) -> bool{
      //all l3 mappings exist in l2
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> (
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0 ==>
                     self.l2_tables@.dom().contains(j)
            )
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@[j]@.pptr == j
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@[j]@.value.is_Some()
        )
        &&
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@[j]@.value.get_Some_0().table.wf()
        )

                
        //L2 table only maps to L1
        //L2 tables are disjoint
        &&
        (
            forall|i: usize,j: usize| #![auto] i != j && self.l2_tables@.dom().contains(i) && self.l2_tables@.dom().contains(j)
                ==> self.l2_tables@[i]@.value.get_Some_0().table@.to_set().remove(0).disjoint(self.l2_tables@[j]@.value.get_Some_0().table@.to_set().remove(0))
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
        self.l4_table@@.value.get_Some_0().table@[l4i as int]
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
                 self.wf_l3()
    {
        assert(self.wf_l4_mapping());
        assert(self.wf_l3_mapping());
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
        forall|l4i: usize,l3i: usize,l2i: usize,l1i: usize| #![auto] (0<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512 && 0<= l1i < 512) ==> 
            self.mapping@[(l4i,l3i,l2i,l1i)] == self.resolve_mapping_l1(l4i,l3i,l2i,l1i)

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

    pub fn add_mapping(&mut self,l4i: usize,l3i: usize,l2i: usize,l1i: usize, dst:usize)
        requires 
            //old(self).wf(),
            old(self).wf_l4(),
            old(self).wf_l3(),
            old(self).wf_l2(),
            old(self).wf_l1(),
            old(self).no_self_mapping(),
            old(self).wf_mapping(),
            0<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512 && 0<= l1i < 512 ,
            old(self).mapping@.contains_key((l4i,l3i,l2i,l1i)) == false,
            old(self).l4_table@@.value.get_Some_0().table@[l4i as int] != 0,
            old(self).l3_tables@[
                    old(self).l4_table@@.value.get_Some_0().table@[l4i as int]
                ]@.value.get_Some_0().table@[l3i as int] != 0,
            old(self).l2_tables@[
                old(self).l3_tables@[
                    old(self).l4_table@@.value.get_Some_0().table@[l4i as int]
                        ]@.value.get_Some_0().table@[l3i as int]
                    ]@.value.get_Some_0().table@[l2i as int] != 0,
            old(self).l1_tables@[
                old(self).l2_tables@[
                    old(self).l3_tables@[
                        old(self).l4_table@@.value.get_Some_0().table@[l4i as int]
                        ]@.value.get_Some_0().table@[l3i as int]
                    ]@.value.get_Some_0().table@[l2i as int]
                ]@.value.get_Some_0().table@[l1i as int] == 0,
            old(self).cr3 != dst,
            old(self).l3_tables@.dom().contains(dst) == false,
            old(self).l2_tables@.dom().contains(dst) == false,
            old(self).l1_tables@.dom().contains(dst) == false,
            old(self).mapping@[(l4i,l3i,l2i,l1i)] == 0,
    {
        assert(self.cr3 == self.l4_table@@.pptr);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(&self.l4_table.borrow()));
        let l3_ptr = *l4_tbl.table.get(l4i);
        assert(l3_ptr != 0);
        assert(self.l4_table@@.value.get_Some_0().table@.contains(l3_ptr));
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l3_ptr);
        assert(l3_ptr == l3_perm@.pptr);
        let l3_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l3_ptr).borrow(Tracked(l3_perm));
        let l2_ptr = *l3_tbl.table.get(l3i);

        assert(self.l3_tables@.dom().contains(l3_ptr));
        assert(self.l3_tables@[l3_ptr]@.value.get_Some_0().table@.contains(l2_ptr));
        assert(l2_ptr != 0);
        assert(self.l2_tables@.dom().contains(l2_ptr));
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l2_ptr);
        assert(l2_ptr == l2_perm@.pptr);
        let l2_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(l2_ptr).borrow(Tracked(l2_perm));
        let l1_ptr = *l2_tbl.table.get(l2i);

        assert(self.l2_tables@.dom().contains(l2_ptr));
        assert(self.l2_tables@[l2_ptr]@.value.get_Some_0().table@.contains(l1_ptr));
        assert(l1_ptr != 0);
        assert(self.l1_tables@.dom().contains(l1_ptr));
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(l1_ptr);
        assert(l1_ptr == l1_perm@.pptr);
        let l1_pptr = PPtr::<LookUpTable>::from_usize(l1_ptr);

        assert(l1_perm@.value.get_Some_0().table.wf());
        assert(l1_perm@.value.get_Some_0().table@[l1i as int] == 0);

        LookUpTable_set(&l1_pptr,Tracked(&mut l1_perm),l1i,dst);
        assert(l1_perm@.value.get_Some_0().table@[l1i as int] == dst);
        assert(l1_perm@.pptr == l1_ptr);
        //proof {self.mapping@ = self.mapping@.insert((l4i,l3i,l2i,l1i),dst);}

        proof {
            self.l1_tables.borrow_mut().tracked_insert(l1_ptr, l1_perm);
    
        }


        // assert(self.l1_tables =~= old(self).l1_tables);

        assert(self.wf_l4());
        
        assert(self.wf_l3());
        
        assert(self.wf_l2());

        assert(self.wf_l1());

        assert(self.no_self_mapping());


        // assert(self.resolve_mapping_l1(l4i,l3i,l2i,l1i) == dst);

        // assert(forall|_l4i: usize, _l3i: usize,_l2i: usize,_l1i: usize| #![auto] (0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && 0<= _l1i < 512) && !(l4i == _l4i && l3i == _l3i && l2i == _l2i && l1i == _l1i )==> 
        //         self.mapping@[(_l4i,_l3i,_l2i,_l1i)] == old(self).mapping@[(_l4i,_l3i,_l2i,_l1i)]);

        // assert(forall|_l4i: usize| #![auto] 0<= _l4i < 512 ==>
        //         self.resolve_mapping_l4(_l4i) == old(self).resolve_mapping_l4(_l4i) );
        // assert(forall|_l4i: usize,_l3i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512==>
        //     self.resolve_mapping_l3(_l4i,_l3i) == old(self).resolve_mapping_l3(_l4i,_l3i));
        // assert(forall|_l4i: usize,_l3i: usize,_l2i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512==>
        //     self.resolve_mapping_l2(_l4i,_l3i,_l2i) == old(self).resolve_mapping_l2(_l4i,_l3i,_l2i));
        
        // assert(self.resolve_mapping_l2(l4i,l3i,l2i) == l1_ptr);

        // assert(forall|_l4i: usize,_l3i: usize,_l2i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512 && !(l4i == _l4i && l3i == _l3i && l2i == _l2i )==>
        //     self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr);

        // assert(forall|ptr:usize|#![auto] self.l1_tables@.dom().contains(ptr) && ptr != l1_ptr ==>
        //         self.l1_tables@[ptr]@ == old(self).l1_tables@[ptr]@
        // );

        // assert(forall|_l4i: usize,_l3i: usize,_l2i: usize| #![auto] 0<= _l4i < 512 && 0<= _l3i < 512 && 0<= _l2i < 512  && self.resolve_mapping_l2(_l4i,_l3i,_l2i) != l1_ptr ==> (
        //     self.resolve_mapping_l2(_l4i,_l3i,_l2i) == 0 ||
        //     self.l1_tables@[self.resolve_mapping_l2(_l4i,_l3i,_l2i)]@ == old(self).l1_tables@[old(self).resolve_mapping_l2(_l4i,_l3i,_l2i)]@)
        
        // );
        
        //assert(self.wf_mapping());

        //assert(false);

    }
}


}