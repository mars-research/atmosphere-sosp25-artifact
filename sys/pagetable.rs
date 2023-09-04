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

// pub struct PageTable{
//     pub cr3: usize,
    
//     pub l4_table: Ghost<PointsTo<LookUpTable>>,
//     pub l3_tables: Ghost<Map<usize,PointsTo<LookUpTable>>>,
//     pub l2_tables: Ghost<Map<usize,PointsTo<LookUpTable>>>,
//     pub l1_tables: Ghost<Map<usize,PointsTo<LookUpTable>>>,

//     pub mapping: Ghost<Map<(usize,usize,usize,usize),usize>>,
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
//             self.l4_table@@.value.get_Some_0().table@.to_set() =~= self.l3_tables@.dom()
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
//         // &&
//         // (
//         //     Set::new(|i: usize| exists |j: usize| #![auto] self.l3_tables@.dom().contains(j) && self.l3_tables@[j]@.value.get_Some_0().table@.contains(i)) =~= self.l2_tables@.dom()
//         // )
//         &&
//         (
//             forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                      self.l2_tables@.dom().contains((j))
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@[j]@.pptr == j
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@[j]@.value.is_Some()
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l3_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l2_tables@[i]@.value.get_Some_0().table.wf()
//         )
//     }

//     pub open spec fn wf_l1(&self) -> bool{
//         self.wf_l2()
//         &&
//         (
//             forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                      self.l1_tables@.dom().contains((j))
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l1_tables@[j]@.pptr == j
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l1_tables@[j]@.value.is_Some()
//         )
//         &&
//         (
//             forall|i: usize| #![auto] self.l2_tables@.dom().contains(i) ==> 
//                 forall|j: usize| #![auto] self.l2_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
//                     self.l1_tables@[i]@.value.get_Some_0().table.wf()
//         )
//     }

//     pub open spec fn wf(&self) -> bool{
//         self.wf_l1()
//         &&
//         forall|l4i: usize,l3i: usize,l2i: usize,l1i: usize| #![auto] self.mapping@.dom().contains((l4i,l3i,l2i,l1i)) ==> 
//             self.l1_tables@[
//                 self.l2_tables@[
//                     self.l3_tables@[
//                             self.l4_table@@.value.get_Some_0().table@[l4i as int]
//                         ]@.value.get_Some_0().table@[l3i as int]
//                     ]@.value.get_Some_0().table@[l2i as int]
//                 ]@.value.get_Some_0().table@[l1i as int]
//             == self.mapping@[(l4i,l3i,l2i,l1i)]

//     }
// }

pub struct LookUpTable{
    pub table : MarsArray<usize,512>,
    
    pub level: Ghost<u8>,
    pub parent: Ghost<usize>, 
}

pub struct PageTable{
    pub cr3: usize,
    
    pub perms: Ghost<Map<usize,PointsTo<LookUpTable>>>,


}
impl PageTable {

    pub open spec fn wf_perms(&self) -> bool{
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[i]@.pptr == i
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[i]@.value.is_Some()
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> 1 <= self.perms@[i]@.value.get_Some_0().level@ <= 4
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[i]@.value.get_Some_0().table.wf()
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ != 1 ==> self.perms@[i]@.value.get_Some_0().table.is_unique()
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[self.perms@[i]@.value.get_Some_0().parent@]@.value.get_Some_0().level@ == self.perms@[i]@.value.get_Some_0().level@ + 1
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> self.perms@[self.perms@[i]@.value.get_Some_0().parent@]@.value.get_Some_0().table@.contains(i)
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ != 1 ==> 
            self.perms@[i]@.value.get_Some_0().table@.to_set().subset_of(self.perms@.dom())
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@[i]@.value.get_Some_0().level@ != 1 ==> 
            forall|j:usize| #![auto] self.perms@[i]@.value.get_Some_0().table@.contains(j) ==> 
                self.perms@[j]@.value.get_Some_0().level@ == self.perms@[i]@.value.get_Some_0().level@ - 1
        &&
        forall|i:usize,j:usize| #![auto]  self.perms@.dom().contains(i) && self.perms@.dom().contains(j) && self.perms@[i]@.value.get_Some_0().level@ != 1 && self.perms@[j]@.value.get_Some_0().level@ != 1 ==> 
            self.perms@[i]@.value.get_Some_0().table@.to_set().disjoint(self.perms@[j]@.value.get_Some_0().table@.to_set())
        &&
        forall|i:usize| #![auto]  self.perms@.dom().contains(i) ==> 
            forall|j:usize| #![auto] self.perms@.dom().contains(j) && self.perms@[i]@.value.get_Some_0().parent@ != j ==> 
                self.perms@[j]@.value.get_Some_0().table@.contains(i) == false
    }

    pub open spec fn wf_l4(&self) -> bool{
        self.perms@.dom().contains(self.cr3)
        &&
        self.perms@[self.cr3]@.value.get_Some_0().level@ == 4
        &&
        self.perms@[self.cr3]@.value.get_Some_0().parent@ == self.cr3
    }

    
    // pub open spec fn wf_l3(&self) -> bool{
    //     forall|i:usize| #![auto] 
    // }

}

}