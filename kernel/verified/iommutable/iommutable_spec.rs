use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;

use crate::pagetable::*;

verus!{
pub struct IOMMUTable{
    pub mapping: Ghost<Map<VAddr,PAddr>>,
}

impl IOMMUTable{
    pub open spec fn wf(&self) -> bool{
        &&&
        self.wf_mapping()
    }

    pub open spec fn wf_mapping(&self) -> bool{
        (
            forall|va: VAddr| #![auto] spec_va_valid(va) ==> self.mapping@.dom().contains(va) 
        )
    }


    pub closed spec fn get_iommutable_page_closure(&self) -> Set<PagePtr> {
        Set::empty()
    }

    
    pub open spec fn get_iommutable_mappings(&self) -> Map<usize,usize> {
        self.mapping@
    }

}

}