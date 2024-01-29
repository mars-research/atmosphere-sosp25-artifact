use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::define::*;

verus!{
pub struct IOMMUTable{}

impl IOMMUTable{
    pub open spec fn wf(&self) -> bool{
        arbitrary()
    }

    pub closed spec fn iommutable_page_closure(&self) -> Set<PagePtr> {
        Set::empty()
    }

    pub closed spec fn iommutable_mappings(&self) -> Map<VAddr,PAddr> {
        Map::empty()
    }

}

}