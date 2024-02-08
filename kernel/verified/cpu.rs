use vstd::prelude::*;
// use vstd::ptr::PointsTo;

use crate::mars_array::MarsArray;
use crate::pagetable::PageEntry;
use crate::define::*;

use core::mem::MaybeUninit;

pub type CPUID = usize;

verus! {
pub struct CPUStack{
    pub kernel_stack: [u8;4096],
    pub tlb_stack: [u8;4096],
}

pub struct CPUStackList{
    pub stack_ar: [CPUStack;NUM_CPUS],
}

impl CPUStackList{

    #[verifier(external_body)]
    pub fn new() -> (ret: Self)
    {
        let ret = Self {
            stack_ar: MaybeUninit::uninit().assume_init(),
        };

        ret
    }

    #[verifier(external_body)]
    pub fn get_kernel_stack(&self, cpu_id:CPUID) -> usize
    {
        unsafe{
            return &self.stack_ar[cpu_id].kernel_stack as *const u8 as usize
        }
    }

    #[verifier(external_body)]
    pub fn get_tlb_stack(&self, cpu_id:CPUID) -> usize
    {
        unsafe{
            return &self.stack_ar[cpu_id].tlb_stack as *const u8 as usize
        }
    }
}

pub struct Cpu{
    pub current_t: Option<ThreadPtr>,
    pub tlb: Ghost<Map<Pcid,Map<VAddr,PageEntry>>>,
    pub iotlb: Ghost<Map<IOid,Map<VAddr,PAddr>>>,
}
impl Cpu {
    pub open spec fn wf(&self) -> bool{
        self.tlb@.dom() =~= Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
    }
    pub open spec fn get_current_thread(&self) -> Option<ThreadPtr>
    {
        self.current_t
    }

    pub open spec fn get_is_idle(&self) -> bool{
        self.current_t.is_Some() == false
    }
    
    #[verifier(inline)]
    pub open spec fn get_tlb_for_pcid(&self, pcid:Pcid) -> Map<VAddr,PageEntry>
        recommends self.wf(),
            0 <= pcid< PCID_MAX,
    {
        self.tlb@[pcid]
    }

    pub open spec fn get_tlb_for_ioid(&self, ioid:IOid) -> Map<VAddr,PAddr>
        recommends self.wf(),
    {
        self.iotlb@[ioid]
    }
}

impl MarsArray<Cpu,NUM_CPUS>{
    pub fn init_to_none(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].get_is_idle(),
    {
        let mut i = 0;
        while i != NUM_CPUS
            invariant
                0<= i <= NUM_CPUS,
                self.wf(),
                forall |j:int| #![auto] 0<=j<i ==> self@[j].current_t.is_None() && self@[j].tlb@ =~= Map::empty() ,
            ensures
                i == NUM_CPUS,
                self.wf(),
                forall |j:int| #![auto] 0<=j<NUM_CPUS ==> self@[j].current_t.is_None() && self@[j].tlb@ =~= Map::empty() ,
        {
            let cpu = Cpu{
                current_t: None,
                tlb: Ghost(Map::empty()),
                iotlb: Ghost(Map::empty()),
            };
            let tmp:Ghost<Seq<Cpu>> = Ghost(self@); 
            self.set(i,cpu);
            assert(self.seq@ =~= tmp@.update(i as int, cpu));
            i = i + 1;
        }
    }

    #[verifier(external_body)]
    pub fn flush_address(&mut self, pcid:Pcid, va: VAddr)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].iotlb =~= old(self)@[i as int].iotlb,
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].current_t =~= old(self)@[i as int].current_t,
            forall|i:CPUID, _pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=_pcid<PCID_MAX && _pcid != pcid 
                ==> self@[i as int].tlb@[_pcid] =~= old(self)@[i as int].tlb@[_pcid],
            forall|i:CPUID, _pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=_pcid<PCID_MAX && _pcid != pcid 
                ==> self@[i as int].tlb@[_pcid].dom() =~= old(self)@[i as int].tlb@[_pcid].dom(),
            forall|i:CPUID, _pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=_pcid<PCID_MAX && _pcid == pcid 
                ==> self@[i as int].tlb@[_pcid] =~= old(self)@[i as int].tlb@[_pcid].remove(va),
            forall|i:CPUID, _pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=_pcid<PCID_MAX && _pcid == pcid 
                ==> self@[i as int].tlb@[_pcid].dom().contains(va) == false,

    {

    }

    #[verifier(external_body)]
    pub fn flush_pcid(&mut self, pcid:Pcid)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].iotlb@.dom() =~= old(self)@[i as int].iotlb@.dom(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].current_t =~= old(self)@[i as int].current_t,
            forall|i:CPUID, _pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=_pcid<PCID_MAX && _pcid != pcid ==> self@[i as int].tlb@[_pcid] =~= old(self)@[i as int].tlb@[_pcid],
            forall|i:CPUID, _ioid:IOid| #![auto] 0<=i<NUM_CPUS && self@[i as int].iotlb@.dom().contains(_ioid) ==> 
                self@[i as int].iotlb@[_ioid] =~= old(self)@[i as int].iotlb@[_ioid],
            forall|i:CPUID| #![auto] self@[i as int].tlb@[pcid] =~= Map::empty(),
    {

    }

    #[verifier(external_body)]
    pub fn flush_ioid(&mut self, ioid:IOid)
        requires
            old(self).wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> old(self)@[i as int].iotlb@.dom().contains(ioid),
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].iotlb@.dom() =~= old(self)@[i as int].iotlb@.dom(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].current_t =~= old(self)@[i as int].current_t,
            forall|i:CPUID, _pcid:Pcid| #![auto] 0<=i<NUM_CPUS && 0<=_pcid<PCID_MAX ==> self@[i as int].tlb@[_pcid] =~= old(self)@[i as int].tlb@[_pcid],
            forall|i:CPUID, _ioid:IOid| #![auto] 0<=i<NUM_CPUS && self@[i as int].iotlb@.dom().contains(_ioid) && _ioid != ioid ==> 
                self@[i as int].iotlb@[_ioid] =~= old(self)@[i as int].iotlb@[_ioid],
            forall|i:CPUID| #![auto] self@[i as int].iotlb@[ioid] =~= Map::empty(),
    {

    }
}

}
