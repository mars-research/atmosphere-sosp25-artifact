use vstd::prelude::*;
verus!{
// use vstd::ptr::PointsTo;

use crate::mars_array::MarsArray;
use crate::pagetable::PageEntry;
use crate::define::*;

use core::mem::MaybeUninit;

pub type CPUID = usize;


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
        unsafe{let ret = Self {
            stack_ar: MaybeUninit::uninit().assume_init(),
        };

        ret}
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
        &&&
        self.tlb@.dom() =~= Set::new(|pcid: Pcid| {0 <= pcid< PCID_MAX})
        &&&
        self.iotlb@.dom() =~= Set::new(|ioid: IOid| {0 <= ioid< IOID_MAX} )
    }
    pub open spec fn spec_get_current_thread(&self) -> Option<ThreadPtr>
    {
        self.current_t
    }

    #[verifier(when_used_as_spec(spec_get_current_thread))]
    pub fn get_current_thread(&self) -> (ret:Option<ThreadPtr>)
        ensures
            ret =~= self.get_current_thread()
    {
        self.current_t
    }

    pub open spec fn spec_get_is_idle(&self) -> bool{
        self.current_t.is_Some() == false
    }

    #[verifier(when_used_as_spec(spec_get_is_idle))]
    pub fn get_is_idle(&self) -> (ret:bool)
        ensures
            self.get_is_idle() == ret,
    {
        self.current_t.is_some() == false
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
            0 <= ioid< IOID_MAX,
    {
        self.iotlb@[ioid]
    }

}

impl MarsArray<Cpu,NUM_CPUS>{

    pub fn set_current_thread(&mut self, cpu_id:CPUID, current_thread: Option<ThreadPtr>)
        requires
            old(self).wf(),
            0<=cpu_id<NUM_CPUS
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS && i != cpu_id  ==> self@[i as int] =~= old(self)@[i as int],
            self@[cpu_id as int].current_t == current_thread,
            self@[cpu_id as int].tlb =~= old(self)@[cpu_id as int].tlb,
            self@[cpu_id as int].iotlb =~= old(self)@[cpu_id as int].iotlb,
    {
        let old_tlb = self.get(cpu_id).tlb;
        let old_iotlb = self.get(cpu_id).iotlb;
        self.set(cpu_id, Cpu{
            current_t: current_thread,
            tlb: old_tlb,
            iotlb: old_iotlb,
        });
    }

    pub fn init_to_none(&mut self)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].wf(),
            forall|i:CPUID| #![auto] 0<=i<NUM_CPUS ==> self@[i as int].get_is_idle() == true,
            forall|i:CPUID, pcid: Pcid| #![auto] 0<=i<NUM_CPUS && 0 <= pcid< PCID_MAX ==> self@[i as int].tlb@[pcid] =~= Map::empty(),
            forall|i:CPUID, ioid: IOid| #![auto] 0<=i<NUM_CPUS && 0 <= ioid< IOID_MAX ==> self@[i as int].iotlb@[ioid] =~= Map::empty(),
    {
        let mut i = 0;
        while i != NUM_CPUS
            invariant
                0<= i <= NUM_CPUS,
                self.wf(),
                forall |j:int| #![auto] 0<=j<i ==> self@[j].current_t.is_None() && self@[j].wf(),
                forall|j:CPUID, pcid: Pcid| #![auto] 0<=j<i && 0 <= pcid< PCID_MAX ==> self@[j as int].tlb@[pcid] =~= Map::empty(),
                forall|j:CPUID, ioid: IOid| #![auto] 0<=j<i && 0 <= ioid< IOID_MAX ==> self@[j as int].iotlb@[ioid] =~= Map::empty(),
            ensures
                i == NUM_CPUS,
                self.wf(),
                forall |j:int| #![auto] 0<=j<NUM_CPUS ==> self@[j].current_t.is_None() && self@[j].wf(),
                forall|j:CPUID, pcid: Pcid| #![auto] 0<=j<i && 0 <= pcid< PCID_MAX ==> self@[j as int].tlb@[pcid] =~= Map::empty(),
                forall|j:CPUID, ioid: IOid| #![auto] 0<=j<i && 0 <= ioid< IOID_MAX ==> self@[j as int].iotlb@[ioid] =~= Map::empty(),
        {
            let cpu = Cpu{
                current_t: None,
                tlb: Ghost(Map::new(|pcid: Pcid| {0 <= pcid< PCID_MAX}, |pcid: Pcid| {Map::empty()})),
                iotlb: Ghost(Map::new(|ioid: IOid| {0 <= ioid< IOID_MAX }, |ioid: IOid| {Map::empty()})),
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
            forall|i:CPUID, _ioid:IOid| #![auto] 0<=i<NUM_CPUS && 0 <= _ioid< IOID_MAX ==> 
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
            forall|i:CPUID, _ioid:IOid| #![auto] 0<=i<NUM_CPUS && 0 <= ioid< IOID_MAX && _ioid != ioid ==> 
                self@[i as int].iotlb@[_ioid] =~= old(self)@[i as int].iotlb@[_ioid],
            forall|i:CPUID| #![auto] self@[i as int].iotlb@[ioid] =~= Map::empty(),
    {

    }
}

}
