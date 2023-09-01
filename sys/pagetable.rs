use super::*;

verus! {



pub struct LookUpTable{
    pub table : MarsArray<usize,512>,
}

pub struct PageTable{
    pub cr3: usize,
    
    pub l4_table: Ghost<PointsTo<LookUpTable>>,
    pub l3_tables: Ghost<Map<usize,PointsTo<LookUpTable>>>,
    pub l2_tables: Ghost<Map<(usize,usize),PointsTo<LookUpTable>>>,
    pub l1_tables: Ghost<Map<(usize,usize,usize),PointsTo<LookUpTable>>>,

    pub mapping: Ghost<Map<(usize,usize,usize,usize,usize),usize>>,
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
        self.wf_l4()
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==> self.l3_tables@.dom().contains(i)
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
        self.wf_l3()
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@.dom().contains((i,j))
        )  
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@[(i,j)]@.pptr == j
        )
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@[(i,j)]@.value.is_Some()
        )   
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    self.l2_tables@[(i,j)]@.value.get_Some_0().table.wf()
        )  
    }


    pub open spec fn wf_l1(&self) -> bool{
        self.wf_l2()
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
                        self.l1_tables@.dom().contains((i,j,k))
        )        
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
                        self.l1_tables@[(i,j,k)]@.pptr == k
        )    
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
                        self.l1_tables@[(i,j,k)]@.value.is_Some()
        )    
        &&
        (
            forall|i: usize| #![auto] self.l4_table@@.value.get_Some_0().table@.contains(i) ==>
                forall|j: usize| #![auto] self.l3_tables@[i]@.value.get_Some_0().table@.contains(j) ==>
                    forall|k: usize| #![auto] self.l2_tables@[(i,j)]@.value.get_Some_0().table@.contains(k) ==>
                        self.l1_tables@[(i,j,k)]@.value.get_Some_0().table.wf()
        )    
    }

    // pub open spec fn wf(&self) -> bool{

    //     forall|l4i: usize,l3i: usize,l2i: usize,l1i: usize, offset: usize| #![auto] self.mapping@.dom().contains((l4i,l3i,l2i,l1i,offset))

    // }

}

}