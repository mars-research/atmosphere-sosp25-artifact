use vstd::prelude::*;
// use vstd::ptr::PointsTo;
use crate::page::{Pcid,VAddr,PAddr,PagePtr};
use crate::paging::AddressSpace;
use crate::mars_array::MarsArray;
use vstd::ptr::PointsTo;
use vstd::ptr::PPtr;

verus! {
pub const PCID_MAX:usize = 4096;

pub struct PcidAllocator{

    pub page_table_pptrs: MarsArray<PPtr<AddressSpace>,PCID_MAX>,
    pub page_table_perms: Tracked<Map<Pcid,PointsTo<AddressSpace>>>,
}


///Pcid Allocator allocates, frees pcid and constructs pagetabels
///Spec: 
///For each free pcid, they have no corresponding pagetable, hence no mapping 
///For each allocated pcid, they have one distinct pagetable
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

    pub closed spec fn get_va2pa_mapping_for_pcid(&self,pcid:Pcid) ->  Map<VAddr,PAddr>
        recommends 
            0<=pcid<PCID_MAX,
    {
        self.page_table_perms@[pcid]@.value.get_Some_0().0.tmp_va2pa_mapping()
    }

    pub closed spec fn data_page_closure(&self) -> Set<PagePtr>
    {
        Seq::new(PCID_MAX as nat, |i: int| i as Pcid)
            .fold_left(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: Pcid| -> Set::<PagePtr> {
                if self.allocated_pcids().contains(e){
                    acc + self.page_table_perms@[e]@.value.get_Some_0().0.tmp_data_page_closure()
                }else{
                    acc
                }
            })
    }

    closed spec fn local_page_closure(&self) -> Set<PagePtr>{
        Set::empty()
    }

    pub closed spec fn page_closure(&self) -> Set<PagePtr>
    {
        Seq::new(PCID_MAX as nat, |i: int| i as Pcid)
            .fold_left(Set::<PagePtr>::empty(), |acc: Set::<PagePtr>, e: Pcid| -> Set::<PagePtr> {
                if self.allocated_pcids().contains(e){
                    acc + self.page_table_perms@[e]@.value.get_Some_0().0.tmp_table_page_closure()
                }else{
                    acc
                }
            })
        + 
        self.local_page_closure()
    }

}
}