use super::*;

verus! {



// pub struct LookUpTable{
//     pub table : MarsArray<usize,512>,
// }

// pub struct PageTable{
//     pub cr3: usize,
    
//     pub l4_table: Ghost<PointsTo<LookUpTable>>,
//     pub l3_tables: Ghost<Map<usize,PointsTo<LookUpTable>>>,
//     pub l2_tables: Ghost<Map<(usize,usize),PointsTo<LookUpTable>>>,
//     pub l1_tables: Ghost<Map<(usize,usize,usize),PointsTo<LookUpTable>>>,

//     pub mapping: Ghost<Map<(usize,usize,usize,usize,usize),usize>>,
// }

// impl PageTable {

//     pub open spec fn wf_l4(&self) -> bool{
//         self.cr3 == self.l4_table@@.pptr
//         &&
//         self.l4_table@@.value.is_Some()
//         &&
//         self.l4_table@@.value.get_Some_0().table.wf()
//     }

//     pub open spec fn wf_l3(&self) -> bool{
//         self.wf_l4()
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@.dom().contains(i)
//         )        
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@[i]@.pptr == i
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@[i]@.value.is_Some()
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@[i]@.value.get_Some_0().table.wf()
//         )
//     }

//     pub open spec fn wf_l2(&self) -> bool{
//         self.wf_l3()
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@.dom().contains((i,j))
//         )  
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@[(i,j)]@.pptr == j
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@[(i,j)]@.value.is_Some()
//         )   
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@[(i,j)]@.value.get_Some_0().table.wf()
//         )  
//     }


//     pub open spec fn wf_l1(&self) -> bool{
//         self.wf_l2()
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
//                         self.l1_tables@.dom().contains((i,j,k))
//         )        
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
//                         self.l1_tables@[(i,j,k)]@.pptr == k
//         )    
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
//                         self.l1_tables@[(i,j,k)]@.value.is_Some()
//         )    
//         &&
//         (
//             forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
//                         self.l1_tables@[(i,j,k)]@.value.get_Some_0().table.wf()
//         )    
//     }

    // pub open spec fn wf(&self) -> bool{

    //     forall|l4i: usize,l3i: usize,l2i: usize,l1i: usize, offset: usize| #![auto] self.mapping@.dom().contains((l4i,l3i,l2i,l1i,offset))

    // }

// }
pub struct LookUpTable{
    pub table : MarsArray<usize,512>,
}
pub struct PageTable{
    pub cr3: usize,
    
    pub l4_table: Tracked<PointsTo<LookUpTable>>,
    pub l3_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l2_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,
    pub l1_tables: Tracked<Map<usize,PointsTo<LookUpTable>>>,

    pub mapping: Ghost<Map<(usize,usize,usize,usize),usize>>,
}

impl PageTable {

    pub open spec fn wf_l4(&self) -> bool{
        self.cr3 == self.l4_table@@.pptr
        &&
        self.l4_table@@.value.is_Some()
        &&
        self.l4_table@@.value.get_Some_0().table.wf()
    }

    pub open spec fn wf_l3(&self) -> bool{
        //all l4 mappings exist in l2
        (
            self.l4_table@@.value.get_Some_0().table@.to_set().remove(0) =~= self.l3_tables@.dom()
        )        
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@[i]@.pptr == i
        )
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@[i]@.value.is_Some()
        )
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@[i]@.value.get_Some_0().table.wf()
        )
    }
    
    pub open spec fn wf_l2(&self) -> bool{
      //all l3 mappings exist in l2
        (
            forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0 ==>
                     self.l2_tables@.dom().contains((j))
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
                    self.l2_tables@[i]@.value.get_Some_0().table.wf()
        )
    }

    pub open spec fn wf_l1(&self) -> bool{
        //all l2 mappings exist in l1
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                     self.l1_tables@.dom().contains((j))
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l1_tables@[j]@.pptr == j
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l1_tables@[j]@.value.is_Some()
        )
        &&
        (
            forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
                forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l1_tables@[i]@.value.get_Some_0().table.wf()
        )
    }

    pub open spec fn no_self_mapping(&self) -> bool
    {
        //L4 table only maps to L3
        forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) && i != 0 ==> self.l2_tables@.dom().contains(i) == false
        &&
        forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) && i != 0 ==> self.l1_tables@.dom().contains(i) == false
        &&
        forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) && i != 0 ==> self.cr3 != i
        &&

        //L3 table only maps to L2
        //L3 tables are disjoint
        (
            forall|i: usize,j: usize| #![auto] i != j && self.l3_tables@.dom().contains(i) && self.l3_tables@.dom().contains(j)
                ==> self.l3_tables@[i]@.value.get_Some_0().table@.to_set().remove(0).disjoint(self.l3_tables@[j]@.value.get_Some_0().table@.to_set().remove(0))
        )
        &&
        forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l3_tables@.dom().contains(j) == false  
        &&
        forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l1_tables@.dom().contains(j) == false  
        &&
        forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.cr3 != j
        && 

        //L2 table only maps to L1
        //L2 tables are disjoint
        (
            forall|i: usize,j: usize| #![auto] i != j && self.l2_tables@.dom().contains(i) && self.l2_tables@.dom().contains(j)
                ==> self.l2_tables@[i]@.value.get_Some_0().table@.to_set().remove(0).disjoint(self.l2_tables@[j]@.value.get_Some_0().table@.to_set().remove(0))
        )
        &&
        forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l3_tables@.dom().contains(j) == false  
        &&
        forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l2_tables@.dom().contains(j) == false  
        &&
        forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.cr3 != j
        && 
        
        //L1 table only maps to outside of this pagetable
        //L1 tables do not have to be disjoint
        forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l1_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l3_tables@.dom().contains(j) == false  
        &&
        forall|i: usize| #![auto] self.l1_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l1_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l2_tables@.dom().contains(j) == false  
        &&
        forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.l1_tables@.dom().contains(j) == false 
        && 
        forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
            forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) && j != 0==>
                self.cr3 != j
    }

    pub open spec fn wf_mapping(&self) -> bool{
        forall|l4i: usize,l3i: usize,l2i: usize,l1i: usize| #![auto] self.mapping@.dom().contains((l4i,l3i,l2i,l1i)) ==> 
            0<= l4i < 512 && 0<= l3i < 512 && 0<= l2i < 512 && 0<= l1i < 512 
            &&
            self.l4_table@@.value.get_Some_0().table@[l4i as int] != 0
            && 
            self.l3_tables@[
                self.l4_table@@.value.get_Some_0().table@[l4i as int]
            ]@.value.get_Some_0().table@[l3i as int] != 0
            &&
            self.l2_tables@[
                    self.l3_tables@[
                            self.l4_table@@.value.get_Some_0().table@[l4i as int]
                        ]@.value.get_Some_0().table@[l3i as int]
                    ]@.value.get_Some_0().table@[l2i as int] != 0
            &&
            self.l1_tables@[
                self.l2_tables@[
                    self.l3_tables@[
                            self.l4_table@@.value.get_Some_0().table@[l4i as int]
                        ]@.value.get_Some_0().table@[l3i as int]
                    ]@.value.get_Some_0().table@[l2i as int]
                ]@.value.get_Some_0().table@[l1i as int]
                == self.mapping@[(l4i,l3i,l2i,l1i)]

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
            old(self).wf(),
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
    {
        assert(self.cr3 == self.l4_table@@.pptr);
        let l4_tbl : &LookUpTable = PPtr::<LookUpTable>::from_usize(self.cr3).borrow(Tracked(&self.l4_table.borrow()));
        let l3_ptr = l4_tbl.table.get(l4i);
        assert(l3_ptr != 0);
    }
}

// pub struct LookUpTable{
//     pub table : MarsArray<usize,512>,
    
//     pub level: Ghost<u8>,
//     pub parent: Ghost<usize>, 
// }

// pub struct PageTable{
//     pub cr3: usize,
    
//     pub perms: Ghost<Map<usize,PointsTo<LookUpTable>>>,

//     pub mapping: Ghost<Map<(usize,usize,usize,usize),usize>>,
// }
// impl PageTable {

//     pub open spec fn wf_perms(&self) -> bool{
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[i]@.pptr == i
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[i]@.value.is_Some()
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> 1 <= self.perms@[i]@.value.get_Some_0().level@ <= 4
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[i]@.value.get_Some_0().table.wf()
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ != 1 ==> self.perms@[i]@.value.get_Some_0().table.is_unique()
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[self.perms@[i]@.value.get_Some_0().parent@]@.value.get_Some_0().level@ == self.perms@[i]@.value.get_Some_0().level@ + 1
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[self.perms@[i]@.value.get_Some_0().parent@]@.value.get_Some_0().table@.contains(i)
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ != 1 ==> 
//             forall|j:usize| #![auto] self.perms@[i]@.value.get_Some_0().table@.contains(j) && j != 0 ==>
//                 self.perms@.dom().contains(j)
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ != 1 ==> 
//             forall|j:usize| #![auto] self.perms@[i]@.value.get_Some_0().table@.contains(j) ==> 
//                 self.perms@[j]@.value.get_Some_0().level@ == self.perms@[i]@.value.get_Some_0().level@ - 1
//         &&
//         forall|i:usize,j:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@.dom().contains(j) && self.perms@[i]@.value.get_Some_0().level@ != 1 && self.perms@[j]@.value.get_Some_0().level@ != 1 ==> 
//             self.perms@[i]@.value.get_Some_0().table@.to_set().disjoint(self.perms@[j]@.value.get_Some_0().table@.to_set())
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> 
//             forall|j:usize| #![auto] self.perms@.dom().contains(j) && self.perms@[i]@.value.get_Some_0().parent@ != j ==> 
//                 self.perms@[j]@.value.get_Some_0().table@.contains(i) == false
//         &&
//         forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ == 1 ==>  self.perms@[i]@.value.get_Some_0().table@.to_set().disjoint(self.perms@.dom())
//     }

//     pub open spec fn wf_l4(&self) -> bool{
//         self.perms@.dom().contains(self.cr3)
//         &&
//         self.perms@[self.cr3]@.value.get_Some_0().level@ == 4
//         &&
//         self.perms@[self.cr3]@.value.get_Some_0().parent@ == self.cr3
//     }

    
//     pub open spec fn wf_mapping(&self) -> bool{
//         forall|l4:usize,l3:usize,l2:usize,l1:usize| #![auto]  self.mapping@.dom().contains((l4,l3,l2,l1))
//             ==> (0<=l4<512 && 0<=l3<512 && 0<=l2<512 && 0<=l1<512) 
//                 &&
//                 self.perms@[self.cr3]@.value.get_Some_0().table@[l4 as int] != 0
//                 &&
//                 self.perms@[self.perms@[self.cr3]@.value.get_Some_0().table@[l4 as int]]@.value.get_Some_0().table@[l3 as int] != 0
//                 &&
//                 self.perms@[self.perms@[self.perms@[self.cr3]@.value.get_Some_0().table@[l4 as int]]@.value.get_Some_0().table@[l3 as int]]@.value.get_Some_0().table@[l2 as int] != 0
//                 &&
//                 self.perms@[self.perms@[self.perms@[self.perms@[self.cr3]@.value.get_Some_0().table@[l4 as int]]@.value.get_Some_0().table@[l3 as int]]@.value.get_Some_0().table@[l2 as int]]@.value.get_Some_0().table@[l1 as int] != 0
//     } 

// }

}