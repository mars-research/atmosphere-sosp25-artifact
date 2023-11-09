use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{VAddr,PAddr,Pcid};
use crate::pcid_alloc::PCID_MAX;
use crate::proc::ThreadPtr;
// use crate::mars_array::MarsArray;

pub type CPUID = usize;

verus! {
pub struct Cpu{
    pub current_t: Option<ThreadPtr>,
    pub tlb: Ghost<Map<Pcid,Map<VAddr,PAddr>>>
}
impl Cpu {
    pub open spec fn wf(&self) -> bool{
        self.tlb@.dom() =~= Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
    }
    pub open spec fn get_current_thread(&self) -> Option<ThreadPtr>
    {
        self.current_t
    }

    pub open spec fn is_idle(&self) -> bool{
        self.current_t.is_Some() == false
    }
    
    pub open spec fn get_tlb_for_pcid(&self, pcid:Pcid) -> Map<VAddr,PAddr>
        recommends self.wf(),
                   0 <= pcid< PCID_MAX,
    {
        self.tlb@[pcid]
    }
}

// pub struct CpuList{
//     cpus: MarsArray<Cpu,NUM_CPUS>,
// }

// impl CpuList {
//     pub open spec fn view(&self) -> Seq<Cpu>{
//         self.cpus@
//     }

//     pub open spec fn view_as_thread_ptrs(&self) -> Seq<ThreadPtr>{
//         self.cpus@.fold_left(Seq::<ThreadPtr>::empty(), |acc: Seq::<ThreadPtr>, e: Cpu| -> Seq::<ThreadPtr> {
//             acc.push(e.current_t)
//         })
//     }
// }

}
