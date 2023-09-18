use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{VAddr,PAddr,Pcid};
use crate::pcid_alloc::PCID_MAX;
use crate::proc::ThreadPtr;
use crate::mars_array::MarsArray;

pub const NUM_CPUS:usize = 32;

verus! {
pub struct Cpu{
    current_t: ThreadPtr,
    tlb: Ghost<Map<Pcid,Map<VAddr,PAddr>>>
}
impl Cpu {
    pub closed spec fn wf(&self) -> bool{
        self.tlb@.dom() =~= Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
    }
    pub closed spec fn get_current_thread(&self) -> ThreadPtr
    {
        self.current_t
    }
    
    pub closed spec fn get_tlb_for_pcid(&self, pcid:Pcid) -> Map<VAddr,PAddr>
        recommends self.wf(),
                   0 <= pcid< PCID_MAX,
    {
        self.tlb@[pcid]
    }
}

pub struct CpuList{
    cpus: MarsArray<Cpu,NUM_CPUS>,
}

impl CpuList {
    pub closed spec fn view(&self) -> Seq<Cpu>{
        self.cpus@
    }
}

}
