use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{Pcid};

pub const PCID_MAX:usize = 1usize<<12;

pub struct PcidAllocator{
}

verus! {
impl PcidAllocator {

    pub closed spec fn allocated_pcids(&self) -> Set<Pcid>
    {
        Set::empty()
    }

    pub closed spec fn free_pcids(&self) -> Set<Pcid>
    {
        Set::empty()
    }

    pub closed spec fn all_pcids(&self) -> Set<Pcid>
    {
        Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
    }

    pub closed spec fn pcid_wf(&self) -> bool
    {
        &&&
        (self.allocated_pcids() * self.free_pcids() =~= Set::empty())
        &&&
        ((self.allocated_pcids() + self.free_pcids()) =~= self.all_pcids()) 
    }

}
}